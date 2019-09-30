use std::{io::{self, BufReader, BufWriter}, fs::{self, File}, fmt, panic, path::{Path, PathBuf}, any::Any, sync::{Arc, Mutex}, process::{Command, Stdio}};
use colored::*;
use crate::{CompileCfg, Parser, Stage, Alloc};

#[derive(Copy, Clone)]
pub enum Pa { Pa1a, Pa1b, Pa2, Pa3, Pa4, Pa5 }

impl Pa {
  pub fn to_cfg(self) -> CompileCfg {
    CompileCfg {
      stage: match self {
        Pa::Pa1a | Pa::Pa1b => Stage::Parse,
        Pa::Pa2 => Stage::TypeCk,
        Pa::Pa3 => Stage::Tac,
        Pa::Pa4 => Stage::TacOpt,
        Pa::Pa5 => Stage::Asm,
      },
      parser: match self { Pa::Pa1b => Parser::LL, _ => Parser::LR },
    }
  }
}

const SPIM_PATH: &str = "spim";
// ignore first SPIM_INFO_LINE line(s), don't compare them
const SPIM_INFO_LINE: usize = 1;

// `folder` should be the path of folder containing `pa_path` and other tools
// `pa_path` should be relevant to `folder`, i.e., `folder`/`pa_path` is the real path to pa folder
pub fn test_all(path: impl AsRef<Path>, pa: Pa) -> io::Result<Vec<TestResult>> {
  // make color work properly on windows(powershell)
  // if it still doesn't work, or you simply dislike the color, add `colored::control::set_override(false);` before calling `test_all`
  #[cfg(target_os = "windows")] let _ = control::set_virtual_terminal(true);

  let path = path.as_ref();
  let ans = path.join("result");
  let out = path.join("out");
  if !out.exists() { fs::create_dir_all(&out)?; }

  let mut files = fs::read_dir(path)?.filter_map(|f| {
    let path = f.ok()?.path();
    let name = path.file_name()?.to_str()?; // in normal case none of the above 3 ? will fail
    if path.is_file() && name.ends_with(".decaf") { Some(name.to_owned()) } else { None }
  }).collect::<Vec<_>>();
  files.sort_unstable(); // the order of fs::read_dir may be strange, sort them for better debugging
  let ret = files.iter().map(|f| {
    test_one_caught(path.join(f), out.join(f).with_extension("result"), ans.join(f).with_extension("result"), pa)
  }).collect();
  Ok(ret)
}

pub fn test_one_caught(i: impl AsRef<Path>, o: impl AsRef<Path>, ans: impl AsRef<Path>, pa: Pa) -> TestResult {
  let loc = Arc::new(Mutex::new(None));
  let loc1 = loc.clone();
  panic::set_hook(Box::new(move |panic_info| if let Some(l) = panic_info.location() {
    *loc1.lock().unwrap() = Some(PanicLoc { file: l.file().to_owned(), line: l.line(), col: l.column() });
  }));
  let ret = panic::catch_unwind(panic::AssertUnwindSafe(|| test_one(&i, &o, &ans, pa)))
    .unwrap_or_else(|e| TestResult::new(i, o, ans, ResultKind::RuntimeError(PanicInfo { payload: get_payload(e), loc: loc.lock().unwrap().clone() })));
  let _ = panic::take_hook();
  ret
}

pub fn test_one(i: impl AsRef<Path>, o: impl AsRef<Path>, ans: impl AsRef<Path>, pa: Pa) -> TestResult {
  let ignore_line = if let Pa::Pa5 = pa { SPIM_INFO_LINE } else { 0 }; // in pa5 we ignore first SPIM_INFO_LINE line(s)
  let kind = run(&i, &o, pa).and_then(|out| Ok((out, fs::read_to_string(&ans)?)))
    .map_or_else(ResultKind::IOError, |(out, ans)| ResultKind::new(&out, &ans, ignore_line));
  TestResult::new(i, o, ans, kind)
}

pub fn run(i: impl AsRef<Path>, o: impl AsRef<Path>, pa: Pa) -> io::Result<String> {
  let o = o.as_ref();
  let cfg = pa.to_cfg();
  let out = match crate::compile(&fs::read_to_string(i)?, &Alloc::default(), cfg) {
    Ok(p) => match cfg.stage {
      Stage::Parse | Stage::TypeCk => (fs::write(o, &p), p).1,
      Stage::Tac | Stage::TacOpt => {
        let (tac, out) = if cfg.stage == Stage::Tac {
          (o.with_extension("tac"), o.to_path_buf())
        } else {
          (o.to_path_buf(), o.with_extension("output")) // in pa4 we compare tac as result
        };
        fs::write(tac, &p)?;
        tacvm::work(&p, 100_000, 1000, true, true,
                    Box::new(BufReader::new(io::stdin())),
                    Box::new(BufWriter::new(File::create(&out)?)),
                    Box::new(BufWriter::new(File::create(o.with_extension("info"))?)),
        )?;
        fs::read_to_string(o)?
      }
      Stage::Asm => {
        fs::write(o.with_extension("s"), &p)?;
        Command::new(SPIM_PATH).arg("-file").arg(o.with_extension("s"))
          .stdout(Stdio::from(File::create(&o)?)).spawn()?.wait()?;
        fs::read_to_string(o)?
      }
    }
    Err(e) => {
      let out = format!("{:?}", e);
      fs::write(o, &out)?;
      out
    }
  };
  Ok(out)
}

pub struct TestResult {
  pub file: PathBuf,
  pub out: PathBuf,
  pub ans: PathBuf,
  pub kind: ResultKind,
}

impl TestResult {
  pub fn new(file: impl AsRef<Path>, out: impl AsRef<Path>, ans: impl AsRef<Path>, kind: ResultKind) -> TestResult {
    TestResult { file: file.as_ref().into(), out: out.as_ref().into(), ans: ans.as_ref().into(), kind }
  }
}

pub enum ResultKind {
  Pass,
  Fail { first_diff: usize, out: String, ans: String },
  IOError(io::Error),
  RuntimeError(PanicInfo),
}

impl ResultKind {
  pub fn new(out: &str, ans: &str, ignore_line: usize) -> ResultKind {
    let (mut out_lines, mut ans_lines) = (out.lines().skip(ignore_line), ans.lines().skip(ignore_line));
    let mut first_diff = ignore_line + 1;
    // it seems there is no builtin iter function that implement "zip and pad the shorter one"
    loop {
      match (out_lines.next(), ans_lines.next()) {
        (None, None) => break ResultKind::Pass,
        (out, ans) => {
          let (out, ans) = (out.unwrap_or(""), ans.unwrap_or(""));
          if out != ans {
            break ResultKind::Fail { first_diff, out: out.to_owned(), ans: ans.to_owned() };
          }
        }
      }
      first_diff += 1;
    }
  }
}

impl fmt::Debug for TestResult {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(f, "{}: ", self.file.display())?;
    match &self.kind {
      ResultKind::Pass => write!(f, "{}", "Pass".green()),
      ResultKind::Fail { first_diff, out, ans } => {
        writeln!(f, "{}: {}", "Fail".red(), format!("first different line on {}", first_diff).yellow())?;
        writeln!(f, "{}", format!("your line: \"{}\" ({}:{})", out, self.out.display(), first_diff).yellow())?;
        write!(f, "{}", format!("ans  line: \"{}\" ({}:{})", ans, self.ans.display(), first_diff).yellow())
      }
      ResultKind::IOError(e) => write!(f, "{}: {}", "IOError".red(), e.to_string().yellow()),
      ResultKind::RuntimeError(e) => {
        write!(f, "{}", "RuntimeError".red())?;
        if let Some(payload) = &e.payload {
          write!(f, ": {}", format!("panicked at `{}`", payload).yellow())?;
        }
        if let Some(loc) = &e.loc {
          write!(f, "{}", format!(", {:?}", loc).yellow())?;
        }
        Ok(())
      }
    }
  }
}

// std::panic::Location uses an borrowed `file`, which can't be conveniently stored
#[derive(Clone)]
pub struct PanicLoc {
  pub file: String,
  pub line: u32,
  pub col: u32,
}

// std::panic::PanicInfo's `payload` is a Box<Any>, which can't be printed(actually it can, but no useful information will be printed)
pub struct PanicInfo {
  pub payload: Option<String>,
  pub loc: Option<PanicLoc>,
}

impl fmt::Debug for PanicLoc {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
    write!(f, "{}:{}:{}", self.file, self.line, self.col)
  }
}

// try to get the String or str content from Any
fn get_payload(e: Box<dyn Any>) -> Option<String> {
  e.downcast::<String>().map(|s| *s)
    .or_else(|payload| payload.downcast::<&str>().map(|s| (*s).to_owned()))
    .ok()
}
