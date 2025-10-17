use std::{any::Any, collections::HashMap};

use rb_codegen::Function;

#[derive(Default)]
pub struct Analysis {
  passes: HashMap<AnalysisPassId, Box<dyn Any>>,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct AnalysisPassId(pub &'static str);

pub trait AnalysisPass: Default {
  fn id() -> AnalysisPassId;

  fn pass(&mut self, analysis: &mut Analysis, function: &Function);
}

impl Analysis {
  pub fn load(&mut self, id: AnalysisPassId, function: &Function) {
    if self.passes.contains_key(&id) {
      return;
    }

    let pass = self.pass_from_id(id, function);
    self.passes.insert(id, pass);
  }

  pub fn get<T: AnalysisPass + 'static>(&self) -> &T {
    self.passes.get(&T::id()).expect("analysis pass was not loaded").downcast_ref::<T>().unwrap()
  }

  pub fn invalidate(&mut self, id: AnalysisPassId) { self.passes.remove(&id); }

  fn pass<T: AnalysisPass + 'static>(&mut self, function: &Function) -> Box<dyn Any> {
    let mut pass = T::default();
    pass.pass(self, function);
    Box::new(pass)
  }
}

macro_rules! passes {
  ($($mod:ident::$pass:ident),* $(,)?) => {
    $(
      pub mod $mod;
    )*

    impl Analysis {
      fn pass_from_id(&mut self, id: AnalysisPassId, function: &Function) -> Box<dyn Any> {
        match id {
          $(
            <$mod::$pass>::ID => self.pass::<$mod::$pass>(function),
          )*

          _ => panic!("unknown analysis pass id"),
        }
      }
    }
  };
}

passes![
  control_flow_graph::ControlFlowGraph,
  // control_flow_hints::ControlFlowHints,
  dominator_tree::DominatorTree,
  value_uses::ValueUses
];
