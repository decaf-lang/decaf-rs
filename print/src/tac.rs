use tac::{TacProgram, Tac, CallKind};
use common::{IndentPrinter, IgnoreResult};
use std::fmt::Write;

pub fn program(pr: &TacProgram, p: &mut IndentPrinter) {
  for v in &pr.vtbl {
    write!(p, "VTBL<_{}> {{", v.class).ignore();
    p.indent(|p| {
      if let Some(pa) = v.parent {
        write!(p, "VTBL<_{}>", pr.vtbl[pa as usize].class).ignore();
      } else { write!(p, "0").ignore(); }
      write!(p, r#""{}""#, v.class).ignore();
      for &f in &v.func {
        write!(p, "FUNC<{}>", pr.func[f as usize].name).ignore();
      }
    });
    write!(p, "}}\n\n").ignore();
  }
  for f in &pr.func {
    write!(p, "FUNC<{}> {{", f.name).ignore();
    p.indent(|p| {
      let mut iter = f.first; // manually iterate, because we don't have TacIter to use
      while let Some(t) = iter {
        write_tac(t.tac.get(), pr, p);
        iter = t.next.get();
      }
    });
    write!(p, "}}\n\n").ignore();
  }
}

pub fn write_tac(t: Tac, pr: &TacProgram, p: &mut IndentPrinter) {
  use Tac::*;
  match t {
    Bin { op, dst, lr } => write!(p, "_T{} = ({:?} {} {:?})", dst, lr[0], op.to_op_str(), lr[1]),
    Un { op, dst, r } => write!(p, "_T{} = {} {:?}", dst, op.to_op_str(), r[0]),
    Assign { dst, src } => write!(p, "_T{} =  {:?}", dst, src[0]),
    Param { src } => write!(p, "parm {:?}", src[0]),
    Call { dst, kind, } => write!(p, "{}call {}", dst.map(|dst| format!("_T{} = ", dst)).unwrap_or(String::new()), match kind {
      CallKind::Virtual(fp, _) => format!("{:?}", fp[0]),
      CallKind::Static(f, _) => pr.func[f as usize].name.clone(),
      CallKind::Intrinsic(i) => i.name().to_owned(),
    }),
    Ret { src } => if let Some(src) = src { write!(p, "return {:?}", src[0]) } else { write!(p, "return") },
    Jmp { label } => write!(p, "branch _L{}", label),
    Jif { label, z, cond } => write!(p, "if ({:?} {} 0) branch _L{}", cond[0], if z { "==" } else { "!=" }, label),
    Label { label } => write!(p, "_L{}:", label),
    Load { dst, base, off, .. } => write!(p, "_T{} = *({:?} {} {})", dst, base[0], if off >= 0 { '+' } else { '-' }, off.abs()),
    Store { src_base, off, .. } => write!(p, "*({:?} {} {}) = {:?}", src_base[1], if off >= 0 { '+' } else { '-' }, off.abs(), src_base[0]),
    LoadInt { dst, i } => write!(p, "_T{} = {}", dst, i),
    LoadStr { dst, s } => write!(p, "_T{} = \"{}\"", dst, pr.str_pool.get_index(s as usize).unwrap()),
    LoadVTbl { dst, v } => write!(p, "_T{} = VTBL<_{}>", dst, pr.vtbl[v as usize].class),
    LoadFunc { dst, f } => write!(p, "_T{} = FUNC<{}>", dst, pr.func[f as usize].name),
  }.ignore();
}