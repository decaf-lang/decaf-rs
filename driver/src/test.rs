use driver::*;

fn main() {
  for result in test_all("testcase/S3", Pa::Pa3).unwrap() {
    println!("{:?}", result);
  }
 //   eprintln!("{:?}", compile(r#"
 // class Main {
 //  static void f(class Main m) {}
 //  static void main() {
 //    f(Main)  ;
 //  }
 // }
 //   "#, &Alloc::default(), Pa::Pa2.to_cfg() ));
}
