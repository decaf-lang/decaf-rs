# Introduction

The public version of decaf pa.

The code involved in pa1a, pa2, pa3 are the same as the private version of decaf pa, because in them your task is only extending language features, which are different on different years. By contrast, the code involved in pa1b, pa4, pa5 may miss necessary code, because in them your task involves completing existing code, which are the same on different years.

# Testcases

It is on the way, now the `testcase` folder doesn't contain any testcase. We will later identify a set of testcases that are suitable for publication.

# Documentation (experiment guide)

[decaf-doc](https://mashplant.gitbook.io/decaf-doc/)

# Build & Run

You need a nightly rust compiler. It is tested on `rustc 1.38.0-nightly`, there is no guarantee about any older version (I believe that a newer version won't break the code).

Run:

```
cargo run --bin test # for testing your implemetation using the testcase folder
# or
cargo run --bin decaf # for a command line app
```

The command line app (with name `decaf`) support the following arguments:

```
<input> # required, the input decaf file path
--target=<target> # required, <target> can be pa1a, pa1b, pa2, pa3, pa4, pa5
--output=<output> # optional, the output path; if not specified, it prints to stdout
```

# Common problems

1. The color (printed by `test`) is not working properly on Windows

Add `colored::control::set_override(false);` before calling `test_all` to disable color.

2. --target=pa1b/pa4/pa5 panicked at `unimplemented!()`

Of course, they are simply not implemented. But there is also fallback code for the unimplemented code:

- to make pa1b work, in `syntax/src/parser_ll.rs`, change the line `unimplemented!()` to `return StackItem::_Fail;` 
- to make pa4 work, in `tacopt/src/bb.rs`, remove the line `crate::aliveness::work(self);`
- to make pa5 work, first make pa4 work, then in `driver/src/lib.rs`, change the line `let asm = FuncGen::work(&fu, &tp, codegen::AllocMethod::Graph);` to `let asm = FuncGen::work(&fu, &tp, codegen::AllocMethod::Brute);`

Of course the fallback code won't have exactly the same functionality as the code we expect you to implement, but as least they can make the compiler working. 