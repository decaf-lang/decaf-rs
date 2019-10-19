// many lines are just copied from parser.rs
// though these types have the same name(Parser, Token, Lexer, ...), actually they are different types
use crate::{ast::*, ty::*, VecExt, dft, check_str, mk_expr, mk_stmt, mk_int_lit, mk_block};
use parser_macros::ll1;
use common::{ErrorKind, Loc, NO_LOC, BinOp, UnOp, Errors, HashSet, HashMap};

pub fn work<'p>(code: &'p str, alloc: &'p ASTAlloc<'p>) -> Result<&'p Program<'p>, Errors<'p, Ty<'p>>> {
  let mut parser = Parser { alloc, error: Errors::default() };
  match parser.parse(&mut Lexer::new(code.as_bytes())) {
    Some(program) if parser.error.0.is_empty() => Ok(program),
    _ => Err(parser.error)
  }
}

pub struct Parser<'p> {
  pub alloc: &'p ASTAlloc<'p>,
  pub error: Errors<'p, Ty<'p>>,
}

impl<'p> Parser<'p> {
  fn error(&mut self, token: &Token<'p>, lexer_loc: Loc) {
    let loc = token.loc();
    match token.ty {
      TokenKind::_Err => if self.error.0.last().map(|x| x.0) != Some(loc) {
        self.error.issue(loc, ErrorKind::UnrecognizedChar(token.piece[0] as char))
      }
      TokenKind::UntermString => {
        check_str(token.str(), &mut self.error, loc);
        self.error.issue(lexer_loc, ErrorKind::SyntaxError)
      }
      _ => if self.error.0.last().map(|x| x.0) != Some(loc) {
        self.error.issue(loc, ErrorKind::SyntaxError)
      }
    }
  }

  // parse impl with some error recovering, called be the generated `parse` function
  fn _parse<'l: 'p>(&mut self, target: u32, lookahead: &mut Token<'l>, lexer: &mut Lexer<'l>, f: &HashSet<u32>) -> StackItem<'p> {
    let target = target as usize;
    // these are some global variables which may be invisible to IDE, so fetch them here for convenience
    let follow: &[HashSet<u32>] = &*FOLLOW;
    let table: &[HashMap<u32, (u32, Vec<u32>)>] = &*TABLE;
    let is_nt = |x: u32| x < NT_NUM;

    let mut end = f.clone();
    end.extend(follow[target].iter());
    let table = &table[target];
    let (prod, rhs) = if let Some(x) = table.get(&(lookahead.ty as u32)) { x } else {
      self.error(lookahead, lexer.loc());
      unimplemented!()
    };
    let value_stk = rhs.iter().map(|&x| {
      if is_nt(x) {
        self._parse(x, lookahead, lexer, &end)
      } else if lookahead.ty as u32 == x {
        let token = *lookahead;
        *lookahead = lexer.next();
        StackItem::_Token(token)
      } else {
        self.error(lookahead, lexer.loc());
        StackItem::_Fail
      }
    }).collect::<Vec<_>>();
    self.act(*prod, value_stk)
  }
}

impl<'p> Token<'p> {
  pub fn str(&self) -> &'p str { std::str::from_utf8(self.piece).unwrap() }
  pub fn loc(&self) -> Loc { Loc(self.line, self.col) }
}

impl Lexer<'_> {
  pub fn loc(&self) -> Loc { Loc(self.line, self.col) }
}

type Terms<'p> = Vec<(Expr<'p>, (Loc, BinOp))>;

fn merge_terms<'p>(mut l: Expr<'p>, ts: Terms<'p>) -> Expr<'p> {
  for (r, (loc, op)) in ts.into_iter().rev() {
    l = mk_expr(loc, Binary { op, l: Box::new(l), r: Box::new(r) }.into());
  }
  l
}

fn merge_idx_id_call<'p>(mut l: Expr<'p>, ts: Vec<IndexOrIdOrCall<'p>>) -> Expr<'p> {
  for t in ts.into_iter().rev() {
    match t {
      IndexOrIdOrCall::Index(loc, idx) =>
        l = mk_expr(loc, IndexSel { arr: Box::new(l), idx: Box::new(idx) }.into()),
      IndexOrIdOrCall::IdOrCall(loc, name, maybe_call) => match maybe_call {
        Some((call_loc, arg)) => {
          let func = Box::new(mk_expr(loc, VarSel { owner: Some(Box::new(l)), name, var: dft() }.into()));
          l = mk_expr(call_loc, Call { func, arg, func_ref: dft() }.into());
        }
        None => l = mk_expr(loc, VarSel { owner: Some(Box::new(l)), name, var: dft() }.into()),
      }
    }
  }
  l
}

// this is pub because StackItem is pub(maybe you need it? though not very likely)
pub enum IndexOrIdOrCall<'p> {
  Index(Loc, Expr<'p>),
  IdOrCall(Loc, &'p str, Option<(Loc, Vec<Expr<'p>>)>),
}

pub enum NewClassOrArray<'p> {
  NewClass(&'p str),
  NewArray(SynTy<'p>, Expr<'p>),
}

#[ll1(Program)]
#[lex(r##"
priority = []

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
    self.alloc.program.alloc(Program { class: class.reversed(), main: dft(), scope: dft() })
  }

  // in this way, the classes will be pushed from left to right, so the order is wrong
  // but in Program -> ClassList, a `class.reverse()` makes it correct
  // the same method is applied in many places(for consistency, I recommend all XxxList to be reversed)
  #[rule(ClassList -> ClassDef ClassList)]
  fn class_list(l: &'p ClassDef<'p>, r: Vec<&'p ClassDef<'p>>) -> Vec<&'p ClassDef<'p>> { r.pushed(l) }
  #[rule(ClassList ->)]
  fn class_list1() -> Vec<&'p ClassDef<'p>> { vec![] }

  #[rule(ClassDef -> Class Id MaybeExtends LBrc FieldList RBrc)]
  fn class_def(&self, c: Token, name: Token, parent: Option<&'p str>, _l: Token, field: Vec<FieldDef<'p>>, _r: Token) -> &'p ClassDef<'p> {
    self.alloc.class.alloc(ClassDef { loc: c.loc(), name: name.str(), parent, field: field.reversed(), parent_ref: dft(), scope: dft() })
  }

  #[rule(MaybeExtends -> Extends Id)]
  fn maybe_extends1(_e: Token, name: Token) -> Option<&'p str> { Some(name.str()) }
  #[rule(MaybeExtends ->)]
  fn maybe_extends0() -> Option<&'p str> { None }

  #[rule(FieldList -> FieldDef FieldList)]
  fn field_list(l: FieldDef<'p>, r: Vec<FieldDef<'p>>) -> Vec<FieldDef<'p>> { r.pushed(l) }
  #[rule(FieldList ->)]
  fn field_list0() -> Vec<FieldDef<'p>> { vec![] }

  #[rule(FieldDef -> Static Type Id LPar VarDefListOrEmpty RPar Block)]
  fn filed_def_f1(&self, _s: Token, ret: SynTy<'p>, name: Token, _l: Token, param: Vec<&'p VarDef<'p>>, _r: Token, body: Block<'p>) -> FieldDef<'p> {
    let (loc, name) = (name.loc(), name.str());
    FieldDef::FuncDef(self.alloc.func.alloc(FuncDef { loc, name, ret, param: param.reversed(), static_: true, body, ret_param_ty: dft(), class: dft(), scope: dft() }))
  }
  #[rule(FieldDef -> Type Id FuncOrVar)]
  fn filed_def_fv(&self, syn_ty: SynTy<'p>, name: Token, fov: Option<(Vec<&'p VarDef<'p>>, Block<'p>)>) -> FieldDef<'p> {
    let (loc, name) = (name.loc(), name.str());
    if let Some((param, body)) = fov {
      FieldDef::FuncDef(self.alloc.func.alloc(FuncDef { loc, name, ret: syn_ty, param: param.reversed(), static_: false, body, ret_param_ty: dft(), class: dft(), scope: dft() }))
    } else {
      FieldDef::VarDef(self.alloc.var.alloc(VarDef { loc, name, syn_ty, init: None, ty: dft(), owner: dft() }))
    }
  }

  #[rule(FuncOrVar -> LPar VarDefListOrEmpty RPar Block)]
  fn func_or_var_f(_l: Token, param: Vec<&'p VarDef<'p>>, _r: Token, body: Block<'p>) -> Option<(Vec<&'p VarDef<'p>>, Block<'p>)> { Some((param, body)) }
  #[rule(FuncOrVar -> Semi)]
  fn func_or_var_v(_s: Token) -> Option<(Vec<&'p VarDef<'p>>, Block<'p>)> { None }

  #[rule(VarDefListOrEmpty -> VarDefList)]
  fn var_def_list_or_empty1(l: Vec<&'p VarDef<'p>>) -> Vec<&'p VarDef<'p>> { l }
  #[rule(VarDefListOrEmpty ->)]
  fn var_def_list_or_empty0() -> Vec<&'p VarDef<'p>> { vec![] }
  #[rule(VarDefList -> VarDef VarDefListRem)]
  fn var_def_list(l: &'p VarDef<'p>, r: Vec<&'p VarDef<'p>>) -> Vec<&'p VarDef<'p>> { r.pushed(l) }
  #[rule(VarDefListRem -> Comma VarDef VarDefListRem)]
  fn var_def_list_rem(_c: Token, l: &'p VarDef<'p>, r: Vec<&'p VarDef<'p>>) -> Vec<&'p VarDef<'p>> { r.pushed(l) }
  #[rule(VarDefListRem ->)]
  fn var_def_list_rem0() -> Vec<&'p VarDef<'p>> { vec![] }

  // the logic of ExprList is completely the same as VarDefList...
  #[rule(ExprListOrEmpty -> ExprList)]
  fn expr_list_or_empty1(l: Vec<Expr<'p>>) -> Vec<Expr<'p>> { l }
  #[rule(ExprListOrEmpty ->)]
  fn expr_list_or_empty0() -> Vec<Expr<'p>> { vec![] }
  #[rule(ExprList -> Expr ExprListRem)]
  fn expr_list(l: Expr<'p>, r: Vec<Expr<'p>>) -> Vec<Expr<'p>> { r.pushed(l) }
  #[rule(ExprListRem -> Comma Expr ExprListRem)]
  fn expr_list_rem(_c: Token, l: Expr<'p>, r: Vec<Expr<'p>>) -> Vec<Expr<'p>> { r.pushed(l) }
  #[rule(ExprListRem ->)]
  fn expr_list_rem0() -> Vec<Expr<'p>> { vec![] }

  #[rule(VarDef -> Type Id)]
  fn var_def(&self, syn_ty: SynTy<'p>, name: Token) -> &'p VarDef<'p> {
    self.alloc.var.alloc(VarDef { loc: name.loc(), name: name.str(), syn_ty, init: None, ty: dft(), owner: dft() })
  }

  #[rule(Block -> LBrc StmtList RBrc)]
  fn block(l: Token, stmt: Vec<Stmt<'p>>, _r: Token) -> Block<'p> {
    Block { loc: l.loc(), stmt: stmt.reversed(), scope: dft() }
  }

  #[rule(StmtList -> Stmt StmtList)]
  fn stmt_list(l: Stmt<'p>, r: Vec<Stmt<'p>>) -> Vec<Stmt<'p>> { r.pushed(l) }
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
  #[rule(Stmt -> Return MaybeExpr Semi)]
  fn stmt_return(r: Token, expr: Option<Expr<'p>>, _s: Token) -> Stmt<'p> { mk_stmt(r.loc(), expr.into()) }
  #[rule(Stmt -> Print LPar ExprList RPar Semi)]
  fn stmt_print(p: Token, _l: Token, print: Vec<Expr<'p>>, _r: Token, _s: Token) -> Stmt<'p> { mk_stmt(p.loc(), print.reversed().into()) }
  #[rule(Stmt -> Break Semi)]
  fn stmt_break(b: Token, _s: Token) -> Stmt<'p> { mk_stmt(b.loc(), Break.into()) }
  #[rule(Stmt -> Block)]
  fn stmt_block(b: Block<'p>) -> Stmt<'p> { mk_stmt(b.loc, b.into()) }

  #[rule(Simple -> Expr MaybeAssign)]
  fn simple_assign_or_expr(e: Expr<'p>, assign: Option<(Loc, Expr<'p>)>) -> Stmt<'p> {
    if let Some((loc, src)) = assign {
      mk_stmt(loc, Assign { dst: e, src }.into())
    } else {
      mk_stmt(e.loc, e.into())
    }
  }
  #[rule(Simple -> Type Id MaybeAssign)]
  fn simple_var_def(&self, syn_ty: SynTy<'p>, name: Token, init: Option<(Loc, Expr<'p>)>) -> Stmt<'p> {
    let loc = name.loc();
    mk_stmt(loc, (&*self.alloc.var.alloc(VarDef { loc, name: name.str(), syn_ty, init, ty: dft(), owner: dft() })).into())
  }
  #[rule(Simple ->)]
  fn simple_skip() -> Stmt<'p> { mk_stmt(NO_LOC, Skip.into()) }

  #[rule(MaybeAssign -> Assign Expr)]
  fn maybe_assign1(a: Token, src: Expr<'p>) -> Option<(Loc, Expr<'p>)> { Some((a.loc(), src)) }
  #[rule(MaybeAssign ->)]
  fn maybe_assign0() -> Option<(Loc, Expr<'p>)> { None }

  #[rule(Blocked -> Stmt)]
  fn blocked(s: Stmt<'p>) -> Block<'p> {
    if let StmtKind::Block(b) = s.kind { b } else { Block { loc: s.loc, stmt: vec![s], scope: dft() } }
  }

  // maybe_else1/0 will cause a conflict, and will choose this production because it appears earlier
  // this is the ONLY conflict allowed in our parser
  #[rule(MaybeElse -> Else Blocked)]
  fn maybe_else1(_e: Token, b: Block<'p>) -> Option<Block<'p>> { Some(b) }
  #[rule(MaybeElse ->)]
  fn maybe_else0() -> Option<Block<'p>> { None }

  #[rule(MaybeExpr -> Expr)]
  fn maybe_expr1(e: Expr<'p>) -> Option<Expr<'p>> { Some(e) }
  #[rule(MaybeExpr ->)]
  fn maybe_expr0() -> Option<Expr<'p>> { None }

  #[rule(Op1 -> Or)]
  fn op1(o: Token) -> (Loc, BinOp) { (o.loc(), BinOp::Or) }

  #[rule(Op2 -> And)]
  fn op2(a: Token) -> (Loc, BinOp) { (a.loc(), BinOp::And) }

  #[rule(Op3 -> Eq)]
  fn op3_eq(e: Token) -> (Loc, BinOp) { (e.loc(), BinOp::Eq) }
  #[rule(Op3 -> Ne)]
  fn op3_ne(n: Token) -> (Loc, BinOp) { (n.loc(), BinOp::Ne) }

  #[rule(Op4 -> Lt)]
  fn op4_lt(l: Token) -> (Loc, BinOp) { (l.loc(), BinOp::Lt) }
  #[rule(Op4 -> Le)]
  fn op4_le(l: Token) -> (Loc, BinOp) { (l.loc(), BinOp::Le) }
  #[rule(Op4 -> Ge)]
  fn op4_ge(g: Token) -> (Loc, BinOp) { (g.loc(), BinOp::Ge) }
  #[rule(Op4 -> Gt)]
  fn op4_gt(g: Token) -> (Loc, BinOp) { (g.loc(), BinOp::Gt) }

  #[rule(Op5 -> Add)]
  fn op5_add(a: Token) -> (Loc, BinOp) { (a.loc(), BinOp::Add) }
  #[rule(Op5 -> Sub)]
  fn op5_sub(s: Token) -> (Loc, BinOp) { (s.loc(), BinOp::Sub) }

  #[rule(Op6 -> Mul)]
  fn op6_add(m: Token) -> (Loc, BinOp) { (m.loc(), BinOp::Mul) }
  #[rule(Op6 -> Div)]
  fn op6_div(d: Token) -> (Loc, BinOp) { (d.loc(), BinOp::Div) }
  #[rule(Op6 -> Mod)]
  fn op6_mod(m: Token) -> (Loc, BinOp) { (m.loc(), BinOp::Mod) }

  #[rule(Op7 -> Sub)]
  fn op7_neg(n: Token) -> (Loc, UnOp) { (n.loc(), UnOp::Neg) }
  #[rule(Op7 -> Not)]
  fn op7_not(n: Token) -> (Loc, UnOp) { (n.loc(), UnOp::Not) }

  #[rule(Expr -> Expr1)]
  fn expr(e: Expr<'p>) -> Expr<'p> { e }

  #[rule(Expr1 -> Expr2 Term1)]
  fn expr1(l: Expr<'p>, ts: Terms<'p>) -> Expr<'p> { merge_terms(l, ts) }
  #[rule(Term1 -> Op1 Expr2 Term1)] // or
  fn term1(o: (Loc, BinOp), l: Expr<'p>, r: Terms<'p>) -> Terms<'p> { r.pushed((l, o)) }
  #[rule(Term1 ->)]
  fn term1_0() -> Terms<'p> { vec![] }

  // the logic of Expr2 is completely the same as Expr1...
  #[rule(Expr2 -> Expr3 Term2)]
  fn expr2(l: Expr<'p>, ts: Terms<'p>) -> Expr<'p> { merge_terms(l, ts) }
  #[rule(Term2 -> Op2 Expr3 Term2)] // and
  fn term2(o: (Loc, BinOp), l: Expr<'p>, r: Terms<'p>) -> Terms<'p> { r.pushed((l, o)) }
  #[rule(Term2 ->)]
  fn term2_0() -> Terms<'p> { vec![] }

  #[rule(Expr3 -> Expr4 Term3)]
  fn expr3(l: Expr<'p>, ts: Terms<'p>) -> Expr<'p> { merge_terms(l, ts) }
  #[rule(Term3 -> Op3 Expr4 Term3)] // eq, ne
  fn term3(o: (Loc, BinOp), l: Expr<'p>, r: Terms<'p>) -> Terms<'p> { r.pushed((l, o)) }
  #[rule(Term3 ->)]
  fn term3_0() -> Terms<'p> { vec![] }

  #[rule(Expr4 -> Expr5 Term4)]
  fn expr4(l: Expr<'p>, ts: Terms<'p>) -> Expr<'p> { merge_terms(l, ts) }
  #[rule(Term4 -> Op4 Expr5 Term4)] // lt, le, ge, gt
  fn term4(o: (Loc, BinOp), l: Expr<'p>, r: Terms<'p>) -> Terms<'p> { r.pushed((l, o)) }
  #[rule(Term4 ->)]
  fn term4_0() -> Terms<'p> { vec![] }

  #[rule(Expr5 -> Expr6 Term5)]
  fn expr5(l: Expr<'p>, ts: Terms<'p>) -> Expr<'p> { merge_terms(l, ts) }
  #[rule(Term5 -> Op5 Expr6 Term5)] // add sub
  fn term5(o: (Loc, BinOp), l: Expr<'p>, r: Terms<'p>) -> Terms<'p> { r.pushed((l, o)) }
  #[rule(Term5 ->)]
  fn term5_0() -> Terms<'p> { vec![] }

  #[rule(Expr6 -> Expr7 Term6)]
  fn expr6(l: Expr<'p>, ts: Terms<'p>) -> Expr<'p> { merge_terms(l, ts) }
  #[rule(Term6 -> Op6 Expr7 Term6)] // mul, div, mod
  fn term6(o: (Loc, BinOp), l: Expr<'p>, r: Terms<'p>) -> Terms<'p> { r.pushed((l, o)) }
  #[rule(Term6 ->)]
  fn term6_0() -> Terms<'p> { vec![] }

  #[rule(Expr7 -> Op7 Expr7)] // not, neg
  fn expr7_op8(o: (Loc, UnOp), r: Expr<'p>) -> Expr<'p> {
    mk_expr(o.0, Unary { op: o.1, r: Box::new(r) }.into())
  }
  #[rule(Expr7 -> LPar ParenOrCast)]
  fn expr7_par_or_cast(_l: Token, e: Expr<'p>) -> Expr<'p> { e }
  #[rule(Expr7 -> Expr8)]
  fn expr7_8(e: Expr<'p>) -> Expr<'p> { e }

  #[rule(ParenOrCast -> Expr RPar Term8)]
  fn paren_or_cast_p(l: Expr<'p>, _r: Token, ts: Vec<IndexOrIdOrCall<'p>>) -> Expr<'p> { merge_idx_id_call(l, ts) }
  #[rule(ParenOrCast -> Class Id RPar Expr7)]
  fn paren_or_cast_c(_c: Token, name: Token, _r: Token, e: Expr<'p>) -> Expr<'p> {
    mk_expr(e.loc, ClassCast { name: name.str(), expr: Box::new(e), class: dft() }.into())
  }

  #[rule(Expr8 -> Expr9 Term8)]
  fn expr8(l: Expr<'p>, ts: Vec<IndexOrIdOrCall<'p>>) -> Expr<'p> { merge_idx_id_call(l, ts) }

  #[rule(Term8 -> LBrk Expr RBrk Term8)]
  fn term8_index(l: Token, idx: Expr<'p>, _r: Token, r: Vec<IndexOrIdOrCall<'p>>) -> Vec<IndexOrIdOrCall<'p>> { r.pushed(IndexOrIdOrCall::Index(l.loc(), idx)) }
  #[rule(Term8 -> Dot Id IdOrCall Term8)]
  fn term8_id_or_call(_d: Token, name: Token, arg: Option<(Loc, Vec<Expr<'p>>)>, r: Vec<IndexOrIdOrCall<'p>>) -> Vec<IndexOrIdOrCall<'p>> {
    r.pushed(IndexOrIdOrCall::IdOrCall(name.loc(), name.str(), arg))
  }
  #[rule(Term8 ->)]
  fn term8_0() -> Vec<IndexOrIdOrCall<'p>> { vec![] }

  #[rule(IdOrCall -> LPar ExprListOrEmpty RPar)]
  fn id_or_call_c(l: Token, arg: Vec<Expr<'p>>, _r: Token) -> Option<(Loc, Vec<Expr<'p>>)> { Some((l.loc(), arg.reversed())) }
  #[rule(IdOrCall ->)]
  fn id_or_call_i() -> Option<(Loc, Vec<Expr<'p>>)> { None }

  #[rule(Expr9 -> IntLit)]
  fn expr9_int(&mut self, i: Token) -> Expr<'p> { mk_int_lit(i.loc(), i.str(), &mut self.error) }
  #[rule(Expr9 -> True)]
  fn expr9_true(t: Token) -> Expr<'p> { mk_expr(t.loc(), true.into()) }
  #[rule(Expr9 -> False)]
  fn expr9_false(f: Token) -> Expr<'p> { mk_expr(f.loc(), false.into()) }
  #[rule(Expr9 -> StringLit)]
  fn expr9_string(&mut self, s: Token) -> Expr<'p> {
    let (loc, str) = (s.loc(), s.str());
    check_str(str, &mut self.error, loc);
    mk_expr(loc, str[1..str.len() - 1].into())
  }
  #[rule(Expr9 -> Null)]
  fn expr9_null(n: Token) -> Expr<'p> { mk_expr(n.loc(), NullLit.into()) }
  #[rule(Expr9 -> ReadInteger LPar RPar)]
  fn expr9_read_integer(r: Token, _l: Token, _r: Token) -> Expr<'p> { mk_expr(r.loc(), ReadInt.into()) }
  #[rule(Expr9 -> ReadLine LPar RPar)]
  fn expr9_read_line(r: Token, _l: Token, _r: Token) -> Expr<'p> { mk_expr(r.loc(), ReadLine.into()) }
  #[rule(Expr9 -> This)]
  fn expr9_this(t: Token) -> Expr<'p> { mk_expr(t.loc(), This.into()) }
  #[rule(Expr9 -> InstanceOf LPar Expr Comma Id RPar)]
  fn expr9_instanceof(i: Token, _l: Token, expr: Expr<'p>, _c: Tokenm, name: Token, _r: Token) -> Expr<'p> {
    mk_expr(i.loc(), ClassTest { expr: Box::new(expr), name: name.str(), class: dft() }.into())
  }
  #[rule(Expr9 -> Id IdOrCall)]
  fn expr9_id_or_call(name: Token, ioc: Option<(Loc, Vec<Expr<'p>>)>) -> Expr<'p> {
    match ioc {
      Some((loc, arg)) => {
        let func = Box::new(mk_expr(name.loc(), VarSel { owner: None, name: name.str(), var: dft() }.into()));
        mk_expr(loc, Call { func, arg, func_ref: dft() }.into())
      }
      None => mk_expr(name.loc(), VarSel { owner: None, name: name.str(), var: dft() }.into()),
    }
  }
  #[rule(Expr9 -> New NewClassOrArray)]
  fn expr9_new(n: Token, noa: NewClassOrArray<'p>) -> Expr<'p> {
    let loc = n.loc();
    match noa {
      NewClassOrArray::NewClass(name) => mk_expr(loc, NewClass { name, class: dft() }.into()),
      NewClassOrArray::NewArray(elem, len) => mk_expr(loc, NewArray { elem, len: Box::new(len) }.into()),
    }
  }

  #[rule(NewClassOrArray -> Id LPar RPar)]
  fn new_class_or_array_c(name: Token, _l: Token, _r: Token) -> NewClassOrArray<'p> {
    NewClassOrArray::NewClass(name.str())
  }
  #[rule(NewClassOrArray -> SimpleType LBrk NewArrayRem)]
  fn new_class_or_array_a(mut ty: SynTy<'p>, _l: Token, dim_len: (u32, Expr<'p>)) -> NewClassOrArray<'p> {
    ty.arr = dim_len.0;
    NewClassOrArray::NewArray(ty, dim_len.1)
  }

  #[rule(NewArrayRem -> RBrk LBrk NewArrayRem)]
  fn new_array_rem(_r: Token, l: Token, mut dim_len: (u32, Expr<'p>)) -> (u32, Expr<'p>) { (dim_len.0 += 1, dim_len).1 }
  #[rule(NewArrayRem -> Expr RBrk)]
  fn new_array_rem0(len: Expr<'p>, _r: Token) -> (u32, Expr<'p>) { (0, len) }

  #[rule(SimpleType -> Int)]
  fn type_int(i: Token) -> SynTy<'p> { SynTy { loc: i.loc(), arr: 0, kind: SynTyKind::Int } }
  #[rule(SimpleType -> Bool)]
  fn type_bool(b: Token) -> SynTy<'p> { SynTy { loc: b.loc(), arr: 0, kind: SynTyKind::Bool } }
  #[rule(SimpleType -> Void)]
  fn type_void(v: Token) -> SynTy<'p> { SynTy { loc: v.loc(), arr: 0, kind: SynTyKind::Void } }
  #[rule(SimpleType -> String)]
  fn type_string(s: Token) -> SynTy<'p> { SynTy { loc: s.loc(), arr: 0, kind: SynTyKind::String } }
  #[rule(SimpleType -> Class Id)]
  fn type_class(c: Token, name: Token) -> SynTy<'p> { SynTy { loc: c.loc(), arr: 0, kind: SynTyKind::Named(name.str()) } }
  #[rule(Type -> SimpleType ArrayDim)]
  fn type_array(mut ty: SynTy<'p>, dim: u32) -> SynTy<'p> { (ty.arr = dim, ty).1 }

  #[rule(ArrayDim -> LBrk RBrk ArrayDim)]
  fn array_type(l: Token, _r: Token, dim: u32) -> u32 { dim + 1 }
  #[rule(ArrayDim ->)]
  fn array_type0() -> u32 { 0 }
}
