use rustyline::error::ReadlineError;
use rustyline::{DefaultEditor, Result};

fn main() -> Result<()> {
    let mut rl = DefaultEditor::new()?;

    loop {
        let input = rl.readline("=> ");
        match input {
            Ok(line) => {
                let _ = rl.add_history_entry(line.as_str())?;
                println!("{}", line);
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
