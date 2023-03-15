use crate::error::Errors;
use crate::object::Object;

struct Machine {
    stack: Vec<Object>,
}

impl Machine {
    pub fn new() -> Self {
        Self { stack: vec![] }
    }

    fn eval_recursive(&mut self) -> Result<Object, Errors> {
        assert!(self.stack.len() >= 2);
        let stack_pointer = self.stack.len() - 1;
        let env = &self.stack[stack_pointer - 1];
        let program = &self.stack[stack_pointer];

        loop {
            match program {
                Object::Symbol(sym) => todo!(),
                _ => return Err(Errors::Unknown),
            }
        }
    }

    fn eval(&mut self, program: Object) -> Result<Object, Errors> {
        self.stack.clear();
        Ok(Object::Nil)
    }
}

#[cfg(test)]
mod tests {
    use crate::{eval::Machine, object::Object, parser::parse_program};

    #[test]
    fn test_eval() {
        let program = parse_program("(+ 1 2)").unwrap();
        let mut machine = Machine::new();
        assert_eq!(machine.eval(program).unwrap(), Object::Nil);
    }
}
