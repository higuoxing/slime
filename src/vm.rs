use std::borrow::BorrowMut;
use std::cell::RefCell;
use std::collections::{linked_list, HashMap, LinkedList};
use std::rc::Rc;

use crate::error::Errors;
use crate::object::Object;

struct Machine {
    env: HashMap<String, LinkedList<Rc<RefCell<Object>>>>,
    stack: Vec<Rc<RefCell<Object>>>,
}

impl Machine {
    pub fn new() -> Self {
        Self {
            env: HashMap::new(),
            stack: vec![],
        }
    }

    pub fn reset(&mut self) {
        self.env = HashMap::new();
        self.stack = vec![];
    }

    fn expand_macros(&mut self, expr: Object) -> Result<Object, Errors> {
        Ok(expr)
    }

    fn resolve_symbol(&self, sym: &str) -> Option<Rc<RefCell<Object>>> {
        self.env.get(sym)?.back().cloned()
    }

    fn eval_recursive(&mut self) -> Result<Object, Errors> {
        let mut curr_expr = self.stack.pop().unwrap();

        loop {
            match &*curr_expr.clone().borrow() {
                Object::Cons(ref car, ref cdr) => match *car.clone().borrow() {
                    Object::Symbol(ref sym) => {
                        let callable_sym = sym.to_uppercase();
                        match callable_sym.as_str() {
                            // Firstly, try to process pre-defined symbols.
                            "BEGIN" => {
                                curr_expr = Rc::new(RefCell::new(Object::Begin(cdr.clone())));
                                continue;
                            }
                            "DEFINE" => {
                                let define_body = Object::cons_to_vec(cdr.clone())?;

                                if define_body.len() != 2 || !define_body[0].borrow().is_symbol() {
                                    return Err(Errors::RuntimeException(format!(
                                        "'DEFINE' should be followed by a symbol and an expression"
                                    )));
                                }

                                curr_expr = Rc::new(RefCell::new(Object::make_define(
                                    define_body[0].borrow().symbol_name(),
                                    define_body[1].take(),
                                )));
                                continue;
                            }
                            "IF" => {
                                let if_body = Object::cons_to_vec(cdr.clone())?;

                                if if_body.len() != 3 {
                                    return Err(Errors::RuntimeException(format!("'IF' should be followed by a condition clause, a then clause and a else clause")));
                                }
                                curr_expr = Rc::new(RefCell::new(Object::make_if(
                                    if_body[0].take(),
                                    if_body[1].take(),
                                    if_body[2].take(),
                                )));
                                continue;
                            }
                            _ => todo!(),
                        }
                    }
                    ref o => {
                        return Err(Errors::RuntimeException(format!(
                            "The object '{:?}' is not applicable.",
                            o
                        )))
                    }
                },
                Object::Begin(ref seq) => {
                    let exprs = Object::cons_to_vec(seq.clone())?;
                    let mut result = Object::Nil;

                    for expr in exprs {
                        // Evaluate (begin E1 E2 E3 ...) sequentially.
                        self.stack.push(expr);
                        result = self.eval_recursive()?;
                    }

                    return Ok(result);
                }
                Object::Define(ref symbol_name, ref val) => {
                    self.stack.push(val.clone());

                    let evaluated_val = Rc::new(RefCell::new(self.eval_recursive()?));

                    match self.env.get_mut(symbol_name.as_str()) {
                        Some(list) => {
                            list.push_back(evaluated_val);
                        }
                        None => {
                            let mut list = LinkedList::new();
                            list.push_back(evaluated_val);
                            self.env.insert(symbol_name.clone(), list);
                        }
                    }

                    return Ok(Object::Nil);
                }
                Object::Symbol(ref symbol_name) => match self.resolve_symbol(&symbol_name.as_str())
                {
                    Some(expr) => {
                        curr_expr = expr;
                        continue;
                    }
                    None => {
                        return Err(Errors::RuntimeException(format!(
                            "Cannot resolve symbol '{}'",
                            symbol_name.as_str()
                        )))
                    }
                },
                atom => return Ok(atom.clone()),
            }
        }
    }

    fn eval(&mut self, expr: Object) -> Result<Object, Errors> {
        let expanded_expr = self.expand_macros(expr)?;

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
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            // "(begin () ())"
            m.eval(parse_program("(begin () ())").unwrap()).unwrap(),
            Object::Nil
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            // "(begin 1 2)"
            m.eval(parse_program("(begin 1 2)").unwrap()).unwrap(),
            Object::Int(2)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            // "(begin)"
            m.eval(parse_program("(BEGIN)").unwrap()).unwrap(),
            Object::Nil
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            // "(begin (begin 1 2 3))"
            m.eval(parse_program("(begin (BEGIN 1 2 3))").unwrap())
                .unwrap(),
            Object::Int(3)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(begin (begin 1))").unwrap()).unwrap(),
            Object::Int(1)
        );
        assert_eq!(m.stack.len(), 0);

        // assert_eq!(
        //     m.eval(parse_program("(if #t 1 2)").unwrap()).unwrap(),
        //     Object::Int(1)
        // );
        // assert_eq!(m.stack.len(), 0);
        //
        // assert_eq!(
        //     m.eval(parse_program("(if #f 1 2)").unwrap()).unwrap(),
        //     Object::Int(2)
        // );
        // assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(define foo 1)").unwrap()).unwrap(),
            Object::Nil
        );
        assert_eq!(m.stack.len(), 0);
        assert!(m
            .env
            .get("foo")
            .unwrap()
            .back()
            .unwrap()
            .borrow()
            .eq(&Object::Int(1)));

        assert_eq!(m.eval(parse_program("1").unwrap()).unwrap(), Object::Int(1));
        assert_eq!(
            m.eval(parse_program("foo").unwrap()).unwrap(),
            Object::Int(1)
        );
    }
}
