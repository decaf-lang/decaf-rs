use crate::{loc::{Loc, NO_LOC}, MAIN_CLASS};
use std::fmt;

pub struct Error<'a, Ty>(pub Loc, pub ErrorKind<'a, Ty>);

// Errors implements Debug, it prints errors line by line
pub struct Errors<'a, Ty>(pub Vec<Error<'a, Ty>>);

impl<Ty> Default for Errors<'_, Ty> {
  fn default() -> Self { Self(vec![]) }
}

impl<'a, Ty> Errors<'a, Ty> {
  // can save some typing in checking the program
  // because when issuing an error, it often follows return a false / error type, which is the default
  // if the compiler complains that it needs type hint, in many cases you can omit the ;, and it will be deduced to ()
  pub fn issue<T: Default>(&mut self, loc: Loc, e: ErrorKind<'a, Ty>) -> T {
    self.0.push(Error(loc, e));
    Default::default()
  }

  pub fn sorted(mut self) -> Self {
    self.0.sort_unstable_by_key(|e| e.0);
    self
  }
}

impl<Ty: fmt::Debug> fmt::Debug for Error<'_, Ty> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self.0 {
      NO_LOC => write!(f, "*** Error: {:?}", self.1),
      loc => write!(f, "*** Error at {:?}: {:?}", loc, self.1),
    }
  }
}

pub enum ErrorKind<'a, Ty> {
  UnclosedStr(&'a str),
  NewlineInStr(&'a str),
  InvalidEscape,
  IntTooLarge(&'a str),
  UnrecognizedChar(char),
  SyntaxError,
  ConflictDeclaration { prev: Loc, name: &'a str },
  NoSuchClass(&'a str),
  CyclicInheritance,
  NoMainClass,
  VoidArrayElement,
  VoidVar(&'a str),
  OverrideVar(&'a str),
  OverrideMismatch { func: &'a str, p: &'a str },
  IncompatibleUnary { op: &'a str, r: Ty },
  IncompatibleBinary { l: Ty, op: &'a str, r: Ty },
  TestNotBool,
  BreakOutOfLoop,
  UndeclaredVar(&'a str),
  RefInStatic { field: &'a str, func: &'a str },
  BadFieldAccess { name: &'a str, owner: Ty },
  PrivateFieldAccess { name: &'a str, owner: Ty },
  NoSuchField { name: &'a str, owner: Ty },
  NotFunc { name: &'a str, owner: Ty },
  LengthWithArgument(u32),
  ArgcMismatch { name: &'a str, expect: u32, actual: u32 },
  ArgMismatch { loc: u32, arg: Ty, param: Ty },
  ThisInStatic,
  NotObject { owner: Ty },
  BadPrintArg { loc: u32, ty: Ty },
  ReturnMismatch { expect: Ty, actual: Ty },
  NewArrayNotInt,
  IndexNotArray,
  IndexNotInt,
  UnreachableCode,
  NoReturn,
}

impl<Ty: fmt::Debug> fmt::Debug for ErrorKind<'_, Ty> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    use ErrorKind::*;
    match self {
      UnclosedStr(s) => write!(f, "unterminated string constant \"{}", s),
      NewlineInStr(s) => write!(f, "illegal newline in string constant \"{}", s),
      InvalidEscape => write!(f, "illegal escape character"),
      IntTooLarge(s) => write!(f, "integer literal {} is too large", s),
      UnrecognizedChar(ch) => write!(f, "unrecognized character '{}'", ch),
      SyntaxError => write!(f, "syntax error"),
      ConflictDeclaration { prev, name } => write!(f, "declaration of '{}' here conflicts with earlier declaration at {:?}", name, prev),
      NoSuchClass(name) => write!(f, "class '{}' not found", name),
      CyclicInheritance => write!(f, "illegal class inheritance (should be acyclic)"),
      NoMainClass => write!(f, "no legal Main class named '{}' was found", MAIN_CLASS),
      VoidArrayElement => write!(f, "array element type must be non-void known type"),
      VoidVar(name) => write!(f, "cannot declare identifier '{}' as void type", name),
      OverrideVar(name) => write!(f, "overriding variable is not allowed for var '{}'", name),
      OverrideMismatch { func, p } => write!(f, "overriding method '{}' doesn't match the type signature in class '{}'", func, p),
      IncompatibleUnary { op, r } => write!(f, "incompatible operand: {} {:?}", op, r),
      IncompatibleBinary { l, op, r } => write!(f, "incompatible operands: {:?} {} {:?}", l, op, r),
      TestNotBool => write!(f, "test expression must have bool type"),
      BreakOutOfLoop => write!(f, "'break' is only allowed inside a loop"),
      UndeclaredVar(name) => write!(f, "undeclared variable '{}'", name),
      RefInStatic { field, func } => write!(f, "can not reference a non-static field '{}' from static method '{}'", field, func),
      BadFieldAccess { name, owner } => write!(f, "cannot access field '{}' from '{:?}'", name, owner),
      PrivateFieldAccess { name, owner } => write!(f, "field '{}' of '{:?}' not accessible here", name, owner),
      NoSuchField { name, owner } => write!(f, "field '{}' not found in '{:?}'", name, owner),
      LengthWithArgument(cnt) => write!(f, "function 'length' expects 0 argument(s) but {} given", cnt),
      NotFunc { name, owner } => write!(f, "'{}' is not a method in class '{:?}'", name, owner),
      ArgcMismatch { name, expect, actual } => write!(f, "function '{}' expects {} argument(s) but {} given", name, expect, actual),
      ArgMismatch { loc, arg, param } => write!(f, "incompatible argument {}: {:?} given, {:?} expected", loc, arg, param),
      ThisInStatic => write!(f, "can not use this in static function"),
      NotObject { owner } => write!(f, "{:?} is not a class type", owner),
      BadPrintArg { loc, ty } => write!(f, "incompatible argument {}: {:?} given, int/bool/string expected", loc, ty),
      ReturnMismatch { expect, actual } => write!(f, "incompatible return: {:?} given, {:?} expected", actual, expect),
      NewArrayNotInt => write!(f, "new array length must be an integer"),
      IndexNotArray => write!(f, "[] can only be applied to arrays"),
      IndexNotInt => write!(f, "array subscript must be an integer"),
      UnreachableCode => write!(f, "unreachable code"),
      NoReturn => write!(f, "missing return statement: control reaches end of non-void block"),
    }
  }
}

impl<Ty: fmt::Debug> fmt::Debug for Errors<'_, Ty> {
  fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
    for e in &self.0 { writeln!(f, "{:?}", e)? }
    Ok(())
  }
}