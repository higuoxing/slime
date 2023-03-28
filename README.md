# lambda-scheme

This is a simple implementation of a Scheme interpreter written in Rust. The interpreter supports a subset of the Scheme language, including basic arithmetic, boolean operations, conditionals, and function definition and application.

## Build

```bash
git clone https://github.com/higuoxing/lambda-scheme.git
cargo build --release
```

## Usage

To start the interpreter, simply run:

```bash
target/release/lsi
```

This will start a REPL (Read-Eval-Print Loop) where you can enter Scheme expressions and see their evaluation results. For example:

```scheme
=> (define (fact n) (if (= n 1) 1 (* n (fact (- n 1)))))

; Value: ()

=> (fact 4)

; Value: 24
```

You can also run Scheme programs from files by passing the file name as an argument:

```bash
lsi examples/hello.scm
```

This will load and execute the `hello.scm` program located in the `examples/` directory.

## Features

The interpreter supports the following features:

- Arithmetic operations: `+`, `-`, `*`, `/`
- Boolean operations: `and`, `or`, `not`
- Comparison operators: `=`, `<`, `>`
- Conditionals: `if`
- Function definition: `define`
- Function application: `lambda`, `apply`
- Lists: `cons`, `car`, `cdr`
- Quotation: `quote` (`'`), `quasiquote` (`` ` ``), `unquote` (`,`), `unquote-splicing` (`,@`).

The interpreter does not support the full Scheme language specification, but it should be enough to run basic Scheme programs.

## Contributing

Contributions to the project are welcome! If you find a bug or have a feature request, please open an issue on the GitHub repository. If you want to contribute code, please fork the repository and submit a pull request.

## License

This project is licensed under the MIT License. See the [LICENSE](./LICENSE) file for details.
