//! The language server for Rebar.

use std::{fs, path::PathBuf};

mod files;
mod global;
mod handler;
mod info;

#[macro_use]
extern crate log;

fn main() {
  match run() {
    Ok(()) => {
      info!("exiting");
    }
    Err(e) => {
      error!("{}", e);
      std::process::exit(1);
    }
  }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
  setup_logging();

  let (connection, io_threads) = lsp_server::Connection::stdio();

  let (initialize_id, initialize_params) = match connection.initialize_start() {
    Ok(it) => it,
    Err(e) => {
      if e.channel_is_disconnected() {
        io_threads.join()?;
      }
      return Err(e.into());
    }
  };
  let _initialize_params =
    serde_json::from_value::<lsp_types::InitializeParams>(initialize_params)?;

  info!("starting LSP server");

  let server_capabilities = info::server_capabilities();

  let initialize_result = lsp_types::InitializeResult {
    capabilities: server_capabilities,
    server_info:  Some(lsp_types::ServerInfo {
      name:    String::from("relsp"),
      version: Some(info::version().to_string()),
    }),
  };

  let initialize_result = serde_json::to_value(initialize_result).unwrap();

  if let Err(e) = connection.initialize_finish(initialize_id, initialize_result) {
    if e.channel_is_disconnected() {
      io_threads.join()?;
    }
    return Err(e.into());
  }

  let global = global::GlobalState::new(connection.sender);
  global.run(connection.receiver)?;

  Ok(())
}

fn setup_logging() {
  let dir = PathBuf::from("/home/macmv/.cache/relsp");
  fs::create_dir_all(&dir).unwrap();

  simple_logging::log_to_file(dir.join("relsp.log"), log::LevelFilter::Info).unwrap();

  // Copied the stdlibs panic hook, but uses `error!()` instead of stdout.
  std::panic::set_hook(Box::new(|info| {
    let location = info.location().unwrap_or_else(|| std::panic::Location::caller());

    let msg = match info.payload().downcast_ref::<&'static str>() {
      Some(s) => *s,
      None => match info.payload().downcast_ref::<String>() {
        Some(s) => &s[..],
        None => "Box<dyn Any>",
      },
    };

    let thread = std::thread::current();
    let name = thread.name().unwrap_or("<unnamed>");

    error!("thread '{name}' panicked at {location}:\n{msg}");
  }));
}
