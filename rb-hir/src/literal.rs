#[derive(Debug)]
pub enum Literal {
  Int(i64),
  Bool(bool),
  Unit,
}
