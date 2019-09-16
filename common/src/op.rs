// maybe a better location for these 2 enums is in crate `syntax`?
// but several other crates also use them, and don't use anything else in `syntax`
// place them here can eliminate this dependency and(maybe?) reduce compile time
#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum BinOp { Add, Sub, Mul, Div, Mod, And, Or, Eq, Ne, Lt, Le, Gt, Ge }

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum UnOp { Neg, Not }

impl BinOp {
  // an operator style string, used in printing tac
  pub fn to_op_str(self) -> &'static str {
    use BinOp::*;
    match self { Add => "+", Sub => "-", Mul => "*", Div => "/", Mod => "%", And => "&&", Or => "||", Eq => "==", Ne => "!=", Lt => "<", Le => "<=", Gt => ">", Ge => ">=" }
  }

  // an abbreviate word for, used in printing ast
  pub fn to_word_str(self) -> &'static str {
    use BinOp::*;
    match self { Add => "ADD", Sub => "SUB", Mul => "MUL", Div => "DIV", Mod => "MOD", And => "AND", Or => "OR", Eq => "EQ", Ne => "NE", Lt => "LT", Le => "LE", Gt => "GT", Ge => "GE" }
  }

  // e.g.: x op1 y <=> y op2 x, this can be helpful because mips's I instructions use imm as rhs
  // self.invert() == Some(self) <=> self is commutative
  pub fn invert(self) -> Option<BinOp> {
    use BinOp::*;
    match self { Add => Some(Add), Mul => Some(Mul), And => Some(And), Or => Some(Or), Eq => Some(Eq), Ne => Some(Ne), Lt => Some(Gt), Le => Some(Ge), Gt => Some(Lt), Ge => Some(Le), Sub | Div | Mod => None, }
  }

  // return None if self = Div or Mod and r = 0
  pub fn try_eval(self, l: i32, r: i32) -> Option<i32> {
    use BinOp::*;
    match self {
      Add => Some(l.wrapping_add(r)),
      Sub => Some(l.wrapping_sub(r)),
      Mul => Some(l.wrapping_mul(r)),
      Div => l.checked_div(r),
      Mod => l.checked_rem(r),
      And => Some(((l != 0) && (r != 0)) as i32),
      Or => Some(((l != 0) || (r != 0)) as i32),
      Eq => Some((l == r) as i32),
      Ne => Some((l != r) as i32),
      Lt => Some((l < r) as i32),
      Le => Some((l <= r) as i32),
      Gt => Some((l > r) as i32),
      Ge => Some((l >= r) as i32),
    }
  }

  // div 0 or mod 0 is regarded as ub here, just use 0 to represent the value
  pub fn eval(self, l: i32, r: i32) -> i32 { self.try_eval(l, r).unwrap_or(0) }
}

impl UnOp {
  pub fn to_op_str(self) -> &'static str {
    match self { UnOp::Neg => "-", UnOp::Not => "!" }
  }

  pub fn to_word_str(self) -> &'static str {
    match self { UnOp::Neg => "NEG", UnOp::Not => "NOT" }
  }

  pub fn eval(self, r: i32) -> i32 {
    match self { UnOp::Neg => r.wrapping_neg(), UnOp::Not => (r == 0) as i32, }
  }
}