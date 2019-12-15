use driver::*;

fn main() {
  for result in test_all("testcase/S4", Pa::Pa4).unwrap() {
    println!("{:?}", result);
  }
}