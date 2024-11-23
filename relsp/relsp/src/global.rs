use parking_lot::RwLock;
use rb_diagnostic::{emit, Diagnostic, Source, Sources, Span};
use rb_syntax::{cst, TextSize};
use rl_analysis::{Analysis, AnalysisHost, FileId};
use std::{collections::HashMap, error::Error, path::PathBuf, sync::Arc};

use crossbeam_channel::{Receiver, Select, Sender};
use lsp_server::ErrorCode;
use lsp_types::{notification::Notification, Url};

use crate::files::Files;

// TODO: Store a salsa state in here. For now, I'm lazy and re-do everything on
// every character press.
pub struct GlobalState {
  pub sender: Sender<lsp_server::Message>,

  pub files:               Arc<RwLock<Files>>,
  pub file_to_source_root: HashMap<FileId, Option<()>>,

  pub host:               AnalysisHost,
  pub diagnostics:        HashMap<FileId, Vec<lsp_types::Diagnostic>>,
  pub diagnostic_changes: Vec<FileId>,

  #[allow(dead_code)]
  response_sender:   Sender<lsp_server::Message>,
  response_receiver: Receiver<lsp_server::Message>,

  #[allow(dead_code)]
  pool_sender: Sender<Box<dyn FnOnce() + Send>>,
  #[allow(unused)]
  pool:        Vec<std::thread::JoinHandle<()>>,
}

pub(crate) struct GlobalStateSnapshot {
  pub analysis: Analysis,
  pub files:    Arc<RwLock<Files>>,
}

enum Event {
  Message(lsp_server::Message),
  Response(lsp_server::Message),
}

impl GlobalState {
  pub fn new(sender: Sender<lsp_server::Message>) -> Self {
    let (pool_tx, pool_rx) = crossbeam_channel::bounded::<Box<dyn FnOnce() + Send>>(0);

    let pool = (0..16)
      .map(|_| {
        let rx = pool_rx.clone();
        std::thread::spawn(move || {
          while let Ok(f) = rx.recv() {
            f();
          }
        })
      })
      .collect();

    let (tx, rx) = crossbeam_channel::bounded(0);

    GlobalState {
      sender,

      files: Arc::new(RwLock::new(Files::new())),
      file_to_source_root: HashMap::new(),

      host: AnalysisHost::new(),
      diagnostics: HashMap::new(),
      diagnostic_changes: vec![],

      response_sender: tx,
      response_receiver: rx,

      pool_sender: pool_tx,
      pool,
    }
  }

  pub fn run(mut self, receiver: Receiver<lsp_server::Message>) -> Result<(), Box<dyn Error>> {
    while let Some(e) = self.next_event(&receiver) {
      match e {
        Event::Message(lsp_server::Message::Notification(lsp_server::Notification {
          method,
          ..
        }))
          if method == lsp_types::notification::Exit::METHOD =>
        {
          info!("shutting down due to exit notification");

          return Ok(());
        }

        _ => self.handle_event(e)?,
      }
    }

    error!("shutting down, client failed to send shutdown request");

    Ok(())
  }

  pub fn snapshot(&self) -> GlobalStateSnapshot {
    GlobalStateSnapshot { analysis: self.host.snapshot(), files: self.files.clone() }
  }

  fn next_event(&self, receiver: &Receiver<lsp_server::Message>) -> Option<Event> {
    let mut sel = Select::new();
    sel.recv(receiver);
    sel.recv(&self.response_receiver);

    let op = sel.select();

    match op.index() {
      0 => Some(Event::Message(op.recv(receiver).unwrap())),
      1 => Some(Event::Response(op.recv(&self.response_receiver).unwrap())),
      _ => None,
    }
  }

  fn handle_event(&mut self, e: Event) -> Result<(), Box<dyn Error>> {
    match e {
      Event::Message(lsp_server::Message::Request(req)) => self.handle_request(req),
      Event::Message(lsp_server::Message::Notification(not)) => self.handle_notification(not),
      Event::Message(lsp_server::Message::Response(_)) => (),
      Event::Response(e) => {
        self.sender.send(e)?;
      }
    }

    self.process_changes();

    Ok(())
  }

  fn handle_request(&mut self, req: lsp_server::Request) {
    let mut dispatcher = RequestDispatcher { global: self, req };
    use crate::handler::request;
    use lsp_types::request as lsp_request;

    dispatcher
      // Not sure if we really need to do anything about a shutdown.
      .on_sync::<lsp_request::Shutdown>(|_, ()| Ok(()))
      .on::<lsp_request::SemanticTokensFullRequest>(request::handle_semantic_tokens_full);
    // .on::<lsp_request::GotoDefinition>(request::handle_goto_definition)
    // .on::<lsp_request::DocumentHighlightRequest>(request::handle_document_highlight)
    // .on::<lsp_request::HoverRequest>(request::handle_hover)
    // .on::<lsp_request::Completion>(request::handle_completion);
  }

  fn handle_notification(&mut self, not: lsp_server::Notification) {
    let mut dispatcher = NotificationDispatcher { global: self, not };

    use crate::handler::notification;
    use lsp_types::notification as lsp_notification;

    dispatcher
      .on_sync::<lsp_notification::DidOpenTextDocument>(notification::handle_open_text_document)
      .on_sync::<lsp_notification::DidChangeTextDocument>(notification::handle_change_text_document)
      .on_sync::<lsp_notification::DidSaveTextDocument>(notification::handle_save_text_document);
  }

  fn process_changes(&mut self) {
    // TODO

    let mut files = self.files.write();
    let changes = files.take_changes();

    for &file_id in &changes {
      if let std::collections::hash_map::Entry::Vacant(e) = self.file_to_source_root.entry(file_id)
      {
        e.insert(None);
        // TODO
        // self.analysis_host.add_file(file_id);
      }

      self.host.change_file(file_id, files.read(file_id));
    }

    let snap = self.host.snapshot();

    for file_id in changes.iter().copied().chain(self.diagnostic_changes.drain(..)) {
      let source = files.read(file_id);
      let diagnostics = check(&source);

      // TODO
      let line_index = snap.line_index(file_id).unwrap();
      // let diagnostics = snap.diagnostics(file_id).unwrap();

      self
        .sender
        .send(lsp_server::Message::Notification(lsp_server::Notification {
          method: lsp_types::notification::PublishDiagnostics::METHOD.into(),
          params: serde_json::to_value(lsp_types::PublishDiagnosticsParams {
            uri:         Url::from_file_path(files.id_to_path(file_id)).unwrap(),
            diagnostics: diagnostics
              .into_iter()
              .filter_map(|d| {
                let start = line_index.try_line_col(d.span.range.start())?;

                let end = if d.span.range.is_empty() {
                  // Underline the next character for empty spans.
                  line_index.try_line_col(TextSize::from(u32::from(d.span.range.end()) + 1))?
                } else {
                  line_index.try_line_col(d.span.range.end())?
                };

                Some(lsp_types::Diagnostic {
                  message: d.message,
                  range: lsp_types::Range {
                    start: lsp_types::Position { line: start.line, character: start.col },
                    end:   lsp_types::Position { line: end.line, character: end.col },
                  },
                  ..Default::default()
                })
              })
              .chain(self.diagnostics.get(&file_id).unwrap_or(&vec![]).iter().cloned())
              .collect(),
            version:     None,
          })
          .unwrap(),
        }))
        .unwrap();
    }
  }
}

impl GlobalState {
  // TODO: There are multiple workspaces! This concept doesn't really work.
  pub fn workspace_path(&self, uri: &Url) -> Option<PathBuf> {
    if uri.scheme() != "file" {
      return None;
    }

    let path = uri.to_file_path().ok()?;
    path.canonicalize().ok()
  }
}

// FIXME: Dedupe from `GlobalState`.
impl GlobalStateSnapshot {
  pub fn workspace_path(&self, uri: &Url) -> Option<PathBuf> {
    if uri.scheme() != "file" {
      return None;
    }

    let path = uri.to_file_path().ok()?;
    path.canonicalize().ok()
  }
}

struct RequestDispatcher<'a> {
  global: &'a mut GlobalState,
  req:    lsp_server::Request,
}

impl RequestDispatcher<'_> {
  fn log_error<R>(&self, e: impl Error)
  where
    R: lsp_types::request::Request,
  {
    error!(
      "in request dispatcher for {}: failed to deserialize params: {} from the request {:#?}",
      R::METHOD,
      e,
      self.req
    );
  }

  fn on_sync<R>(
    &mut self,
    f: fn(&GlobalState, R::Params) -> Result<R::Result, Box<dyn Error>>,
  ) -> &mut Self
  where
    R: lsp_types::request::Request,
  {
    if self.req.method != R::METHOD {
      return self;
    }

    let params = match serde_json::from_value::<R::Params>(self.req.params.clone()) {
      Ok(p) => p,
      Err(e) => {
        self.log_error::<R>(e);
        return self;
      }
    };

    // TODO: Dispatch this to a thread pool.
    let id = self.req.id.clone();
    let response = f(self.global, params).unwrap();
    self
      .global
      .sender
      .send(lsp_server::Message::Response(lsp_server::Response {
        id,
        result: Some(serde_json::to_value(response).unwrap()),
        error: None,
      }))
      .unwrap();

    self
  }

  #[allow(dead_code)]
  fn on<R>(
    &mut self,
    f: fn(GlobalStateSnapshot, R::Params) -> Result<R::Result, Box<dyn Error>>,
  ) -> &mut Self
  where
    R: lsp_types::request::Request,
  {
    if self.req.method != R::METHOD {
      return self;
    }

    let params = match serde_json::from_value::<R::Params>(self.req.params.clone()) {
      Ok(p) => p,
      Err(e) => {
        self.log_error::<R>(e);
        return self;
      }
    };

    let snapshot = self.global.snapshot();

    let responder = self.global.response_sender.clone();
    let id = self.req.id.clone();
    self
      .global
      .pool_sender
      .send(Box::new(move || match f(snapshot, params) {
        Ok(r) => responder
          .send(lsp_server::Message::Response(lsp_server::Response {
            id,
            result: Some(serde_json::to_value(r).unwrap()),
            error: None,
          }))
          .unwrap(),
        Err(_) => responder
          .send(lsp_server::Message::Response(lsp_server::Response {
            id,
            result: None,
            error: Some(lsp_server::ResponseError {
              code:    ErrorCode::RequestCanceled as i32,
              message: "request canceled".to_string(),
              data:    None,
            }),
          }))
          .unwrap(),
      }))
      .unwrap();

    self
  }
}

struct NotificationDispatcher<'a> {
  global: &'a mut GlobalState,
  not:    lsp_server::Notification,
}

impl NotificationDispatcher<'_> {
  fn log_error<N>(&self, e: impl Error)
  where
    N: lsp_types::notification::Notification,
  {
    error!(
      "in notification dispatcher for {}: failed to deserialize params: {} from the notification {:#?}",
      N::METHOD,
      e,
      self.not
    );
  }

  fn on_sync<N>(
    &mut self,
    f: fn(&mut GlobalState, N::Params) -> Result<(), Box<dyn Error>>,
  ) -> &mut Self
  where
    N: lsp_types::notification::Notification,
  {
    if self.not.method != N::METHOD {
      return self;
    }

    let params = match serde_json::from_value::<N::Params>(self.not.params.clone()) {
      Ok(p) => p,
      Err(e) => {
        self.log_error::<N>(e);
        return self;
      }
    };
    // TODO: Dispatch this to a thread pool.
    f(self.global, params).unwrap();

    self
  }
}

fn check(src: &str) -> Vec<Diagnostic> {
  let mut sources = Sources::new();
  let id = sources.add(Source::new("inline.rbr".into(), src.into()));
  let sources = Arc::new(sources);

  let res = rb_diagnostic::run(sources.clone(), || {
    let res = cst::SourceFile::parse(src);

    if res.errors().is_empty() {
      rb_hir_lower::lower_source(res.tree(), id)
    } else {
      for error in res.errors() {
        emit!(error.message(), Span { file: id, range: error.span() });
      }

      Default::default()
    }
  });

  let hir = match res {
    Ok(hir) => hir,
    Err(errs) => return errs,
  };

  let env = rb_runtime::Environment::std();
  let static_env = env.static_env();

  let res = rb_diagnostic::run(sources, || {
    let (hir, span_maps) = hir;

    for (idx, function) in hir.functions {
      let span_map = &span_maps[idx.into_raw().into_u32() as usize];

      rb_typer::Typer::check(&static_env, &function, &span_map);
    }
  });

  match res {
    Ok(_) => vec![],
    Err(errs) => errs,
  }
}
