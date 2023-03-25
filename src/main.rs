mod builtins;
mod error;
mod object;
mod parser;
mod tokenizer;
mod vm;

use rustyline::error::ReadlineError;
use rustyline::{DefaultEditor, Result};

fn main() -> Result<()> {
    let mut rl = DefaultEditor::new()?;
    let mut lisp_machine = vm::Machine::new();

    loop {
        let input = rl.readline("=> ");
        match input {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str())?;
                match parser::parse_program(line.as_str()) {
                    Ok(parsed_ast) => match lisp_machine.eval(parsed_ast) {
                        Ok(result) => match result {
                            object::Object::Unspecified => {
                                println!("\n; Unspecified return value\n")
                            }
                            _ => println!("\n; Value: {}\n", result),
                        },
                        Err(e) => println!("{:?}", e),
                    },
                    Err(e) => println!("{:?}", e),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("{:?}", err);
                break;
            }
        }
    }

    Ok(())
}
