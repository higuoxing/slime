use std::error::Error;
use std::fs;
use std::path::Path;

use lambda::error::Errors;
use lambda::object;
use lambda::parser;
use lambda::vm;

use clap::Parser;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

#[derive(Parser)]
struct Cli {
    path: Option<std::path::PathBuf>,
}

fn repl_loop() -> Result<(), Box<dyn Error>> {
    let mut rl = DefaultEditor::new()?;
    let mut lisp_machine = vm::Machine::new();
    let mut script = String::from("");
    loop {
        let input = if script.is_empty() {
            rl.readline("=> ")
        } else {
            rl.readline(".. ")
        };

        match input {
            Ok(line) => {
                script += line.as_str();
                script += "\n";
                match parser::parse_program(script.as_str()) {
                    Ok(parsed_ast) => match lisp_machine.eval(parsed_ast) {
                        Ok(result) => match result {
                            object::Object::Unspecified => {
                                println!("\n; Unspecified return value\n")
                            }

                            _ => println!("\n; Value: {}\n", result),
                        },
                        Err(e) => println!("{}", e),
                    },
                    Err(e) => match e {
                        Errors::ExpectMoreToken => {
                            continue;
                        }
                        _ => {
                            println!("{}", e)
                        }
                    },
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("Interrupt!");
                println!("Input <C-d> to exit");
            }
            Err(ReadlineError::Eof) => {
                println!("Happy happy joy joy!");
                break;
            }
            Err(err) => {
                println!("{:?}", err);
                break;
            }
        }

        script.clear();
    }

    Ok(())
}

fn run_script(script_path: &Path) -> Result<(), Box<dyn Error>> {
    match script_path.extension() {
        Some(os_str) => {
            if os_str != "scm" {
                return Err(Box::new(Errors::RuntimeException(String::from(
                    "The input script file should end with .scm",
                ))));
            }
        }
        None => {
            return Err(Box::new(Errors::RuntimeException(String::from(
                "Cannot get the input file's extension",
            ))));
        }
    }

    let script = fs::read_to_string(script_path)?;
    let mut lisp_machine = vm::Machine::new();
    let parsed_ast = parser::parse_program(script.as_str())?;
    lisp_machine.eval(parsed_ast)?;

    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Cli::parse();
    match args.path {
        Some(p) => run_script(p.as_path()),
        None => repl_loop(),
    }
}
