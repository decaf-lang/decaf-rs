use tac::{TacProgram, TacKind, Operand, CallKind};
use common::{IndentPrinter, IgnoreResult};
use std::fmt::Write;

pub fn program(pr: &TacProgram, p: &mut IndentPrinter) {
  for v in &pr.vtbl {
    write!(p, "VTBL(_{}) {{", v.class).ignore();
    p.indent(|p| {
      if let Some(pa) = v.parent {
        write!(p, "VTBL<_{}>", pr.vtbl[pa as usize].class).ignore();
      } else { write!(p, "0").ignore(); }
      write!(p, r#""{}""#, v.class).ignore();
      for &f in &v.func {
        write!(p, "FUNCTION<{:?}>", pr.func[f as usize].name).ignore();
      }
    });
    write!(p, "}}\n\n").ignore();
  }
  for f in &pr.func {
    write!(p, "FUNCTION({:?}) {{", f.name).ignore();
    p.indent(|p| for t in f.iter() {
      write_tac(&t.payload.borrow().kind, pr, p);
    });
    write!(p, "}}\n\n").ignore();
  }
}

pub fn write_tac(t: &TacKind, pr: &TacProgram, p: &mut IndentPrinter) {
  use TacKind::*;
  let opr = |o: &Operand| match o {
    Operand::Reg(r) => format!("_T{}", r),
    Operand::Const(c) => format!("{}", c),
  };
  match t {
    Bin { op, dst, lr } => { write!(p, "_T{} = ({} {} {})", dst, opr(&lr[0]), op.to_op_str(), opr(&lr[1])) }
    Un { op, dst, r } => { write!(p, "_T{} = {} {}", dst, op.to_op_str(), opr(&r[0])) }
    Assign { dst, src } => { write!(p, "_T{} =  {}", dst, opr(&src[0])) }
    Param { src } => { write!(p, "parm {}", opr(&src[0])) }
    Call { dst, kind, } => {
      write!(p, "{}call {}", match dst { Some(dst) => format!("_T{} = ", dst), None => "".to_owned() }, match kind {
        CallKind::Virtual(fp, _) => opr(&fp[0]),
        CallKind::Static(f, _) => format!("{:?}", pr.func[*f as usize].name),
        CallKind::Intrinsic(i) => i.name().to_owned(),
      })
    }
    Ret { src } => match src {
      Some(src) => { write!(p, "return {}", opr(&src[0])) }
      None => { write!(p, "return <empty>") }
    }
    Jmp { label } => { write!(p, "branch _L{}", label) }
    Jif { label, z, cond } =>
      write!(p, "if ({} {} 0) branch _L{}", opr(&cond[0]), if *z { "==" } else { "!=" }, label),
    Label { label } => { write!(p, "_L{}:", label) }
    Load { dst, base, off, .. } => if *off >= 0 {
      write!(p, "_T{} = *({} + {})", dst, opr(&base[0]), off)
    } else {
      write!(p, "_T{} = *({} - {})", dst, opr(&base[0]), -off)
    },
    Store { src_base, off, .. } => if *off >= 0 {
      write!(p, "*({} + {}) = {}", opr(&src_base[1]), off, opr(&src_base[0]))
    } else {
      write!(p, "*({} - {}) = {}", opr(&src_base[1]), -off, opr(&src_base[0]))
    },
    LoadInt { dst, i } => write!(p, "_T{} = {}", dst, i),
    LoadStr { dst, s } => write!(p, "_T{} = \"{}\"", dst, pr.str_pool.get_index(*s as usize).unwrap()),
    LoadVTbl { dst, v } => write!(p, "_T{} = VTBL <_{}>", dst, pr.vtbl[*v as usize].class),
  }.ignore();
}