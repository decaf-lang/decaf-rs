use driver::*;

fn main() {
  for result in test_all("testcase", "pa5", Pa::Pa5).unwrap() {
    println!("{:?}", result);
  }
}
