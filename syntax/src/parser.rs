use crate::{ast::*, ty::*, VecExt, dft, check_str, mk_stmt, mk_expr, mk_int_lit, mk_block};
use parser_macros::lalr1;
use common::{ErrorKind, Loc, BinOp, UnOp, Errors, NO_LOC};

pub fn work<'p>(code: &'p str, alloc: &'p ASTAlloc<'p>) -> Result<&'p Program<'p>, Errors<'p, Ty<'p>>> {
  let mut parser = Parser { alloc, error: Errors::default() };
  let mut lexer = Lexer::new(code.as_bytes()); // Lexer can be used independently from Parser, you can use it to debug
  match parser.parse(&mut lexer) {
    Ok(program) if parser.error.0.is_empty() => Ok(program),
    Err(token) => {
      let mut error = parser.error;
      let loc = Loc(token.line, token.col);
      match token.ty {
        TokenKind::_Err => error.issue(loc, ErrorKind::UnrecognizedChar(token.piece[0] as char)),
        TokenKind::UntermString => {
          check_str(token.str(), &mut error, loc);
          error.issue(lexer.loc(), ErrorKind::SyntaxError)
        }
        _ => error.issue(loc, ErrorKind::SyntaxError),
      }
      Err(error)
    }
    _ => Err(parser.error),
  }
}

pub struct Parser<'p> {
  pub alloc: &'p ASTAlloc<'p>,
  // just some simple errors like IntTooLarger, cannot recover or record parser errors
  pub error: Errors<'p, Ty<'p>>,
}

impl<'p> Token<'p> {
  pub fn str(&self) -> &'p str { std::str::from_utf8(self.piece).unwrap() }
  pub fn loc(&self) -> Loc { Loc(self.line, self.col) }
}

impl Lexer<'_> {
  pub fn loc(&self) -> Loc { Loc(self.line, self.col) }
}

fn mk_bin<'p>(l: Expr<'p>, r: Expr<'p>, loc: Loc, op: BinOp) -> Expr<'p> {
  mk_expr(loc, Binary { l: Box::new(l), op, r: Box::new(r) }.into())
}

#[lalr1(Program)]
#[lex(r##"
priority = [
  { assoc = 'left', terms = ['Or'] },
  { assoc = 'left', terms = ['And'] },
  { assoc = 'left', terms = ['Eq', 'Ne'] },
  { assoc = 'no_assoc', terms = ['Le', 'Ge', 'Lt', 'Gt'] },
  { assoc = 'left', terms = ['Add', 'Sub'] },
  { assoc = 'left', terms = ['Mul', 'Div', 'Mod'] },
  { assoc = 'left', terms = ['UMinus', 'Not', 'RPar'] },
  { assoc = 'left', terms = ['LBrk', 'Dot', 'LPar'] },
  { assoc = 'left', terms = ['Empty'] },
  { assoc = 'left', terms = ['Else'] },
]

[lexical]
'void' = 'Void'
'int' = 'Int'
'bool' = 'Bool'
'string' = 'String'
'new' = 'New'
'null' = 'Null'
'true' = 'True'
'false' = 'False'
'class' = 'Class'
'extends' = 'Extends'
'this' = 'This'
'while' = 'While'
'for' = 'For'
'if' = 'If'
'else' = 'Else'
'return' = 'Return'
'break' = 'Break'
'Print' = 'Print'
'ReadInteger' = 'ReadInteger'
'ReadLine' = 'ReadLine'
'static' = 'Static'
'instanceof' = 'InstanceOf'
'<=' = 'Le'
'>=' = 'Ge'
'==' = 'Eq'
'!=' = 'Ne'
'&&' = 'And'
'\|\|' = 'Or'
'\+' = 'Add'
'-' = 'Sub'
'\*' = 'Mul'
'/' = 'Div'
'%' = 'Mod'
'=' = 'Assign'
'<' = 'Lt'
'>' = 'Gt'
'\.' = 'Dot'
',' = 'Comma'
';' = 'Semi' # short for semicolon
'!' = 'Not'
'\(' = 'LPar' # short for parenthesis
'\)' = 'RPar'
'\[' = 'LBrk' # short for bracket
'\]' = 'RBrk'
'\{' = 'LBrc' # short for brace
'\}' = 'RBrc'
':' = 'Colon'
# line break in a StringLit will be reported by parser's semantic act
'"[^"\\]*(\\.[^"\\]*)*"' = 'StringLit'
'"[^"\\]*(\\.[^"\\]*)*' = 'UntermString'
'//[^\n]*' = '_Eps'
'\s+' = '_Eps'
'\d+|(0x[0-9a-fA-F]+)' = 'IntLit'
'[A-Za-z]\w*' = 'Id'
'.' = '_Err'
"##)]
impl<'p> Parser<'p> {
  #[rule(Program -> ClassList)]
  fn program(&self, class: Vec<&'p ClassDef<'p>>) -> &'p Program<'p> {
    self.alloc.program.alloc(Program { class, main: dft(), scope: dft() })
  }

  #[rule(ClassList -> ClassList ClassDef)]
  fn class_list(l: Vec<&'p ClassDef<'p>>, r: &'p ClassDef<'p>) -> Vec<&'p ClassDef<'p>> { l.pushed(r) }
  #[rule(ClassList -> ClassDef)]
  fn class_list1(c: &'p ClassDef<'p>) -> Vec<&'p ClassDef<'p>> { vec![c] }

  #[rule(ClassDef -> Class Id MaybeExtends LBrc FieldList RBrc)]
  fn class_def(&self, c: Token, name: Token, parent: Option<&'p str>, _l: Token, field: Vec<FieldDef<'p>>, _r: Token) -> &'p ClassDef<'p> {
    self.alloc.class.alloc(ClassDef { loc: c.loc(), name: name.str(), parent, field, parent_ref: dft(), scope: dft() })
  }

  #[rule(MaybeExtends -> Extends Id)]
  fn maybe_extends1(_e: Token, name: Token) -> Option<&'p str> { Some(name.str()) }
  #[rule(MaybeExtends ->)]
  fn maybe_extends0() -> Option<&'p str> { None }

  #[rule(FieldList -> FieldList VarDef Semi)]
  fn field_list_v(l: Vec<FieldDef<'p>>, r: &'p VarDef<'p>, _s: Token) -> Vec<FieldDef<'p>> { l.pushed(r.into()) }
  #[rule(FieldList -> FieldList FuncDef)]
  fn field_list_f(l: Vec<FieldDef<'p>>, r: &'p FuncDef<'p>) -> Vec<FieldDef<'p>> { l.pushed(r.into()) }
  #[rule(FieldList ->)]
  fn field_list0() -> Vec<FieldDef<'p>> { vec![] }

  #[rule(FuncDef -> Static Type Id LPar VarDefListOrEmpty RPar Block)]
  fn func_def1(&self, _s: Token, ret: SynTy<'p>, name: Token, _l: Token, param: Vec<&'p VarDef<'p>>, _r: Token, body: Block<'p>) -> &'p FuncDef<'p> {
    self.alloc.func.alloc(FuncDef { loc: name.loc(), name: name.str(), ret, param, static_: true, body, ret_param_ty: dft(), class: dft(), scope: dft() })
  }
  #[rule(FuncDef -> Type Id LPar VarDefListOrEmpty RPar Block)]
  fn func_def0(&self, ret: SynTy<'p>, name: Token, _l: Token, param: Vec<&'p VarDef<'p>>, _r: Token, body: Block<'p>) -> &'p FuncDef<'p> {
    self.alloc.func.alloc(FuncDef { loc: name.loc(), name: name.str(), ret, param, static_: false, body, ret_param_ty: dft(), class: dft(), scope: dft() })
  }

  // the `VarDef` in grammar only supports VarDef without init value
  #[rule(VarDef -> Type Id)]
  fn var_def(&self, syn_ty: SynTy<'p>, name: Token) -> &'p VarDef<'p> {
    self.alloc.var.alloc(VarDef { loc: name.loc(), name: name.str(), syn_ty, init: None, ty: dft(), owner: dft() })
  }

  #[rule(VarDefListOrEmpty -> VarDefList)]
  fn var_def_list_or_empty1(l: Vec<&'p VarDef<'p>>) -> Vec<&'p VarDef<'p>> { l }
  #[rule(VarDefListOrEmpty ->)]
  fn var_def_list_or_empty0() -> Vec<&'p VarDef<'p>> { vec![] }

  #[rule(VarDefList -> VarDefList Comma VarDef)]
  fn var_def_list(l: Vec<&'p VarDef<'p>>, _c: Token, r: &'p VarDef<'p>) -> Vec<&'p VarDef<'p>> { l.pushed(r) }
  #[rule(VarDefList -> VarDef)]
  fn var_def_list1(v: &'p VarDef<'p>) -> Vec<&'p VarDef<'p>> { vec![v] }

  #[rule(Block -> LBrc StmtList RBrc)]
  fn block(l: Token, stmt: Vec<Stmt<'p>>, _r: Token) -> Block<'p> { Block { loc: l.loc(), stmt, scope: dft() } }

  #[rule(StmtList -> StmtList Stmt)]
  fn stmt_list(l: Vec<Stmt<'p>>, r: Stmt<'p>) -> Vec<Stmt<'p>> { l.pushed(r) }
  #[rule(StmtList ->)]
  fn stmt_list0() -> Vec<Stmt<'p>> { vec![] }

  #[rule(Stmt -> Simple Semi)]
  fn stmt_simple(s: Stmt<'p>, _s: Token) -> Stmt<'p> { s }
  #[rule(Stmt -> If LPar Expr RPar Stmt MaybeElse)]
  fn stmt_if(i: Token, _l: Token, cond: Expr<'p>, _r: Token, on_true: Stmt<'p>, on_false: Option<Block<'p>>) -> Stmt<'p> {
    mk_stmt(i.loc(), Box::new(If { cond, on_true: mk_block(on_true), on_false }).into())
  }
  #[rule(Stmt -> While LPar Expr RPar Stmt)]
  fn stmt_while(w: Token, _l: Token, cond: Expr<'p>, _r: Token, body: Stmt<'p>) -> Stmt<'p> {
    mk_stmt(w.loc(), While { cond, body: mk_block(body) }.into())
  }
  #[rule(Stmt -> For LPar Simple Semi Expr Semi Simple RPar Stmt)]
  fn stmt_for(f: Token, _l: Token, init: Stmt<'p>, _s1: Token, cond: Expr<'p>, _s2: Token, update: Stmt<'p>, _r: Token, body: Stmt<'p>) -> Stmt<'p> {
    mk_stmt(f.loc(), For { init: Box::new(init), cond, update: Box::new(update), body: mk_block(body) }.into())
  }
  #[rule(Stmt -> Return Expr Semi)]
  fn stmt_return1(r: Token, expr: Expr<'p>, _s: Token) -> Stmt<'p> { mk_stmt(r.loc(), Some(expr).into()) }
  #[rule(Stmt -> Return Semi)]
  fn stmt_return0(r: Token, _s: Token) -> Stmt<'p> { mk_stmt(r.loc(), None.into()) }
  #[rule(Stmt -> Print LPar ExprList RPar Semi)]
  fn stmt_print(p: Token, _l: Token, print: Vec<Expr<'p>>, _r: Token, _s: Token) -> Stmt<'p> { mk_stmt(p.loc(), print.into()) }
  #[rule(Stmt -> Break Semi)]
  fn stmt_break(b: Token, _s: Token) -> Stmt<'p> { mk_stmt(b.loc(), Break.into()) }
  #[rule(Stmt -> Block)]
  fn stmt_block(b: Block<'p>) -> Stmt<'p> { mk_stmt(b.loc, b.into()) }

  #[rule(MaybeElse -> Else Stmt)]
  fn maybe_else1(_e: Token, b: Stmt<'p>) -> Option<Block<'p>> { Some(mk_block(b)) }
  #[rule(MaybeElse ->)]
  #[prec(Empty)]
  fn maybe_else0() -> Option<Block<'p>> { None }

  #[rule(Simple -> LValue Assign Expr)]
  fn simple_assign(dst: Expr<'p>, a: Token, src: Expr<'p>) -> Stmt<'p> { mk_stmt(a.loc(), Assign { dst, src }.into()) }
  #[rule(Simple -> VarDef)] // the VarDef without init
  fn simple_var_def(v: &'p VarDef<'p>) -> Stmt<'p> { mk_stmt(v.loc, v.into()) }
  #[rule(Simple -> Type Id Assign Expr)] // the VarDef with init
  fn simple_var_def_init(&self, syn_ty: SynTy<'p>, name: Token, a: Token, init: Expr<'p>) -> Stmt<'p> {
    let loc = name.loc();
    mk_stmt(loc, (&*self.alloc.var.alloc(VarDef { loc, name: name.str(), syn_ty, init: Some((a.loc(), init)), ty: dft(), owner: dft() })).into())
  }
  #[rule(Simple -> Expr)]
  fn simple_mk_expr(e: Expr<'p>) -> Stmt<'p> { mk_stmt(e.loc, e.into()) }
  #[rule(Simple ->)]
  fn simple_skip() -> Stmt<'p> { mk_stmt(NO_LOC, Skip.into()) }

  #[rule(Expr -> LValue)]
  fn expr_lvalue(l: Expr<'p>) -> Expr<'p> { l }
  #[rule(Expr -> VarSel LPar ExprListOrEmpty RPar)]
  fn expr_call(func: Expr<'p>, l: Token, arg: Vec<Expr<'p>>, _r: Token) -> Expr<'p> {
    mk_expr(l.loc(), Call { func: Box::new(func), arg, func_ref: dft() }.into())
  }
  #[rule(Expr -> IntLit)]
  fn expr_int(&mut self, i: Token) -> Expr<'p> { mk_int_lit(i.loc(), i.str(), &mut self.error) }
  #[rule(Expr -> True)]
  fn expr_true(t: Token) -> Expr<'p> { mk_expr(t.loc(), true.into()) }
  #[rule(Expr -> False)]
  fn expr_false(f: Token) -> Expr<'p> { mk_expr(f.loc(), false.into()) }
  #[rule(Expr -> StringLit)]
  fn expr_string(&mut self, s: Token) -> Expr<'p> {
    let (loc, str) = (s.loc(), s.str());
    check_str(str, &mut self.error, loc);
    mk_expr(loc, str[1..str.len() - 1].into())
  }
  #[rule(Expr -> Null)]
  fn expr_null(n: Token) -> Expr<'p> { mk_expr(n.loc(), NullLit.into()) }
  #[rule(Expr -> LPar Expr RPar)]
  fn expr_paren(_l: Token, m: Expr<'p>, _r: Token) -> Expr<'p> { m }
  #[rule(Expr -> Expr Add Expr)]
  fn expr_add(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Add) }
  #[rule(Expr -> Expr Sub Expr)]
  fn expr_sub(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Sub) }
  #[rule(Expr -> Expr Mul Expr)]
  fn expr_mul(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Mul) }
  #[rule(Expr -> Expr Div Expr)]
  fn expr_div(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Div) }
  #[rule(Expr -> Expr Mod Expr)]
  fn expr_mod(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Mod) }
  #[rule(Expr -> Expr Eq Expr)]
  fn expr_eq(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Eq) }
  #[rule(Expr -> Expr Ne Expr)]
  fn expr_ne(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Ne) }
  #[rule(Expr -> Expr Lt Expr)]
  fn expr_lt(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Lt) }
  #[rule(Expr -> Expr Le Expr)]
  fn expr_le(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Le) }
  #[rule(Expr -> Expr Ge Expr)]
  fn expr_ge(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Ge) }
  #[rule(Expr -> Expr Gt Expr)]
  fn expr_gt(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Gt) }
  #[rule(Expr -> Expr And Expr)]
  fn expr_and(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::And) }
  #[rule(Expr -> Expr Or Expr)]
  fn expr_or(l: Expr<'p>, op: Token, r: Expr<'p>) -> Expr<'p> { mk_bin(l, r, op.loc(), BinOp::Or) }
  #[rule(Expr -> ReadInteger LPar RPar)]
  fn expr_read_int(r: Token, _l: Token, _r: Token) -> Expr<'p> { mk_expr(r.loc(), ReadInt.into()) }
  #[rule(Expr -> ReadLine LPar RPar)]
  fn expr_read_line(r: Token, _l: Token, _r: Token) -> Expr<'p> { mk_expr(r.loc(), ReadLine.into()) }
  #[rule(Expr -> This)]
  fn expr_this(t: Token) -> Expr<'p> { mk_expr(t.loc(), This.into()) }
  #[rule(Expr -> New Id LPar RPar)]
  fn expr_new_class(n: Token, name: Token, _l: Token, _r: Token) -> Expr<'p> {
    mk_expr(n.loc(), NewClass { name: name.str(), class: dft() }.into())
  }
  #[rule(Expr -> New Type LBrk Expr RBrk)]
  fn expr_new_array(n: Token, elem: SynTy<'p>, _l: Token, len: Expr<'p>, _r: Token) -> Expr<'p> {
    mk_expr(n.loc(), NewArray { elem, len: Box::new(len) }.into())
  }
  #[rule(Expr -> InstanceOf LPar Expr Comma Id RPar)]
  fn expr_instanceof(i: Token, _l: Token, e: Expr<'p>, _c: Tokenm, name: Token, _r: Token) -> Expr<'p> {
    mk_expr(i.loc(), ClassTest { expr: Box::new(e), name: name.str(), class: dft() }.into())
  }
  #[rule(Expr -> LPar Class Id RPar Expr)]
  fn expr_cast(_l: Token, _c: Token, name: Token, _r: Token, e: Expr<'p>) -> Expr<'p> {
    mk_expr(e.loc, ClassCast { expr: Box::new(e), name: name.str(), class: dft() }.into())
  }
  #[rule(Expr -> Sub Expr)]
  #[prec(UMinus)]
  fn expr_neg(s: Token, r: Expr<'p>) -> Expr<'p> {
    mk_expr(s.loc(), Unary { op: UnOp::Neg, r: Box::new(r) }.into())
  }
  #[rule(Expr -> Not Expr)]
  fn expr_not(n: Token, r: Expr<'p>) -> Expr<'p> {
    mk_expr(n.loc(), Unary { op: UnOp::Not, r: Box::new(r) }.into())
  }

  #[rule(ExprList -> ExprList Comma Expr)]
  fn expr_list(l: Vec<Expr<'p>>, _c: Token, r: Expr<'p>) -> Vec<Expr<'p>> { l.pushed(r) }
  #[rule(ExprList -> Expr)]
  fn expr_list1(e: Expr<'p>) -> Vec<Expr<'p>> { vec![e] }

  #[rule(ExprListOrEmpty -> ExprList)]
  fn expr_list_or_empty1(e: Vec<Expr<'p>>) -> Vec<Expr<'p>> { e }
  #[rule(ExprListOrEmpty ->)]
  fn expr_list_or_empty0() -> Vec<Expr<'p>> { vec![] }

  #[rule(MaybeOwner -> Expr Dot)]
  fn maybe_owner1(e: Expr<'p>, _d: Token) -> Option<Box<Expr<'p>>> { Some(Box::new(e)) }
  #[rule(MaybeOwner ->)]
  fn maybe_owner0() -> Option<Box<Expr<'p>>> { None }

  #[rule(VarSel -> MaybeOwner Id)]
  fn var_sel(owner: Option<Box<Expr<'p>>>, name: Token) -> Expr<'p> {
    mk_expr(name.loc(), VarSel { owner, name: name.str(), var: dft() }.into())
  }

  #[rule(LValue -> VarSel)]
  fn lvalue_var_sel(e: Expr<'p>) -> Expr<'p> { e }
  #[rule(LValue -> Expr LBrk Expr RBrk)]
  fn lvalue_index(arr: Expr<'p>, l: Token, idx: Expr<'p>, _r: Token) -> Expr<'p> {
    mk_expr(l.loc(), IndexSel { arr: Box::new(arr), idx: Box::new(idx) }.into())
  }

  #[rule(Type -> Int)]
  fn type_int(i: Token) -> SynTy<'p> { SynTy { loc: i.loc(), arr: 0, kind: SynTyKind::Int } }
  #[rule(Type -> Bool)]
  fn type_bool(b: Token) -> SynTy<'p> { SynTy { loc: b.loc(), arr: 0, kind: SynTyKind::Bool } }
  #[rule(Type -> Void)]
  fn type_void(v: Token) -> SynTy<'p> { SynTy { loc: v.loc(), arr: 0, kind: SynTyKind::Void } }
  #[rule(Type -> String)]
  fn type_string(s: Token) -> SynTy<'p> { SynTy { loc: s.loc(), arr: 0, kind: SynTyKind::String } }
  #[rule(Type -> Class Id)]
  fn type_class(c: Token, name: Token) -> SynTy<'p> { SynTy { loc: c.loc(), arr: 0, kind: SynTyKind::Named(name.str()) } }
  #[rule(Type -> Type LBrk RBrk)]
  fn type_array(mut ty: SynTy<'p>, _l: Token, _r: Token) -> SynTy<'p> { (ty.arr += 1, ty).1 }
}
