use std::cell::RefCell;
use std::rc::Rc;

use crate::error::Errors;
use crate::object::Object;

struct Machine {
    stack: Vec<Rc<RefCell<Object>>>,
}

impl Machine {
    pub fn new() -> Self {
        Self { stack: vec![] }
    }

    fn expand_macros(&mut self, expr: Object) -> Result<Object, Errors> {
        Ok(expr)
    }

    fn eval_recursive(&mut self) -> Result<Object, Errors> {
        let mut curr_expr = self.stack.pop().unwrap();
        let curr_env = self.stack.pop().unwrap();

        loop {
            match curr_expr.take() {
                Object::Begin(seq) => {
                    curr_expr = Rc::new(RefCell::new(seq.take()));

                    while let Object::Cons(car, cdr) = curr_expr.take() {
                        // Evaluate (begin E1 E2 E3 ... ) sequentially.
                        if cdr.borrow().is_cons() {
                            self.stack.push(cdr);

                            self.stack.push(curr_env.clone());
                            self.stack.push(car);

                            // Evaluate expressions.
                            let _ = self.eval_recursive()?;

                            // curr_expr = cdr.
                            curr_expr = self.stack.pop().unwrap();
                        } else {
                            curr_expr = car;
                            break;
                        }
                    }
                }
                atom => return Ok(atom),
            }
        }
    }

    fn eval(&mut self, expr: Object) -> Result<Object, Errors> {
        let expanded_expr = self.expand_macros(expr)?;

        self.stack
            .push(Rc::new(RefCell::new(/* env */ Object::Nil)));
        self.stack
            .push(Rc::new(RefCell::new(/* expr */ expanded_expr)));

        self.eval_recursive()
    }
}

#[cfg(test)]
mod tests {
    use crate::{object::Object, parser::parse_program, vm::Machine};

    #[test]
    fn test_eval() {
        let mut m = Machine::new();
        assert_eq!(m.eval(parse_program("()").unwrap()).unwrap(), Object::Nil);

        assert_eq!(
            // "(begin () ())"
            m.eval(Object::begin(Object::cons(
                Object::Nil,
                Object::cons(Object::Nil, Object::Nil)
            )))
            .unwrap(),
            Object::Nil
        );

        assert_eq!(
            // "(begin 1 2)"
            m.eval(Object::begin(Object::cons(
                Object::Int(1),
                Object::cons(Object::Int(2), Object::Nil)
            )))
            .unwrap(),
            Object::Int(2)
        );

        assert_eq!(
            // "(begin)"
            m.eval(Object::begin(Object::Nil)).unwrap(),
            Object::Nil
        );

        assert_eq!(
            // "(begin (begin 1 2 3))"
            m.eval(Object::begin(Object::cons(
                Object::begin(Object::cons(
                    Object::Int(1),
                    Object::cons(Object::Int(2), Object::cons(Object::Int(3), Object::Nil))
                )),
                Object::Nil
            )))
            .unwrap(),
            Object::Int(3)
        );
    }
}
