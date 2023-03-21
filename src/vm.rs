use std::cell::RefCell;
use std::collections::{HashMap, LinkedList};
use std::rc::Rc;

use crate::error::Errors;
use crate::object::Object;

struct Machine {
    // FIXME: The current implementation of env is not correct.
    env: LinkedList<HashMap<String, Rc<RefCell<Object>>>>,
    stack: Vec<Rc<RefCell<Object>>>,
}

impl Machine {
    pub fn new() -> Self {
        Self {
            env: LinkedList::new(),
            stack: vec![],
        }
    }

    pub fn reset(&mut self) {
        self.env = LinkedList::new();
        self.stack = vec![];
    }

    fn expand_macros(&mut self, expr: Object) -> Result<Object, Errors> {
        Ok(expr)
    }

    fn resolve_symbol(&self, sym: &str) -> Result<Rc<RefCell<Object>>, Errors> {
        for node in self.env.iter() {
            match node.get(sym) {
                Some(v) => return Ok(v.clone()),
                None => continue,
            }
        }
        return Err(Errors::RuntimeException(format!(
            "Cannot resolve symbol '{}'",
            sym
        )));
    }

    fn define_symbol(&mut self, sym: &str, val: Rc<RefCell<Object>>) -> Result<(), Errors> {
        match self.env.front_mut() {
            Some(env) => {
                if let Some(v) = env.get_mut(sym) {
                    *v = val.clone();
                } else {
                    env.insert(sym.to_string(), val.clone());
                }
                Ok(())
            }
            None => panic!("You should provide an enviroment first!"),
        }
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
                            "LAMBDA" => {
                                let lambda_body = Object::cons_to_vec(cdr.clone())?;

                                if lambda_body.len() != 2 {
                                    return Err(Errors::RuntimeException(format!("'LAMBDA' should be followed by a list of arguments and a function body")));
                                }

                                let args = Object::cons_to_vec(lambda_body[0].clone())?;
                                let mut args_names = vec![];
                                for arg in args {
                                    /* Check argument list. */
                                    if !arg.borrow().is_symbol() {
                                        return Err(Errors::RuntimeException(format!("'LAMBDA' should be followed by a list of arguments and a function body")));
                                    }

                                    args_names.push(arg.borrow().symbol_name());
                                }

                                return Ok(Object::Lambda(args_names, lambda_body[1].clone()));
                            }
                            _ => {
                                // Try to evaluate sym.
                                // FIXME: This is not perfect ... but it works ...
                                // Try to improve it tomorrow!
                                let resolved_sym = self.resolve_symbol(sym)?;
                                self.stack.push(resolved_sym);
                                let evaluated_sym = Rc::new(RefCell::new(self.eval_recursive()?));
                                curr_expr =
                                    Rc::new(RefCell::new(Object::Cons(evaluated_sym, cdr.clone())));
                                continue;
                            }
                        }
                    }
                    Object::Lambda(ref lambda_args, ref lambda_body) => {
                        // Lambda expression is callable and it will be evaluated here.
                        let args_exprs = Object::cons_to_vec(cdr.clone())?;
                        if lambda_args.len() != args_exprs.len() {
                            return Err(Errors::RuntimeException(format!(
                                "Incorrect number of arguments supplied to lambda expression"
                            )));
                        }

                        // Push a new env first.
                        self.env.push_front(HashMap::new());
                        for (arg_index, arg_expr) in args_exprs.iter().enumerate() {
                            self.stack.push(arg_expr.clone());
                            let evaluated_arg_expr = Rc::new(RefCell::new(self.eval_recursive()?));
                            self.define_symbol(
                                lambda_args[arg_index].as_str(),
                                evaluated_arg_expr,
                            )?;
                        }

                        self.stack.push(lambda_body.clone());
                        let result = self.eval_recursive()?;
                        // Pop the env.
                        self.env.pop_front();

                        return Ok(result);
                    }
                    _ => {
                        self.stack.push(car.clone());
                        let call_expr = self.eval_recursive()?;
                        curr_expr = Rc::new(RefCell::new(Object::Cons(
                            Rc::new(RefCell::new(call_expr)),
                            cdr.clone(),
                        )));
                        continue;
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

                    self.define_symbol(symbol_name.as_str(), evaluated_val)?;

                    return Ok(Object::Nil);
                }
                Object::Symbol(ref symbol_name) => {
                    curr_expr = self.resolve_symbol(&symbol_name.as_str())?;
                    continue;
                }
                Object::If(ref cond, ref then, ref otherwise) => {
                    self.stack.push(cond.clone());
                    match self.eval_recursive()? {
                        Object::Bool(cond_result) => {
                            if !cond_result {
                                curr_expr = otherwise.clone();
                            } else {
                                curr_expr = then.clone();
                            }
                            continue;
                        }
                        _ => {
                            // Any expression that cannot be evaluated to be #f is #t.
                            curr_expr = then.clone();
                            continue;
                        }
                    }
                }
                atom @ Object::Int(_)
                | atom @ Object::Bool(_)
                | atom @ Object::Char(_, _)
                | atom @ Object::Lambda(_, _)
                | atom @ Object::Real(_)
                | atom @ Object::Nil => return Ok(atom.clone()),
            }
        }
    }

    fn eval(&mut self, expr: Object) -> Result<Object, Errors> {
        let expanded_expr = self.expand_macros(expr)?;

        // Set up a new env.
        self.env.push_front(HashMap::new());
        self.stack
            .push(Rc::new(RefCell::new(/* expr */ expanded_expr)));

        let result = self.eval_recursive()?;

        // FIXME: Is this correct?
        while self.env.front().is_some() {
            if self.env.front().unwrap().is_empty() {
                self.env.pop_front();
                continue;
            }
            break;
        }

        Ok(result)
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

        assert_eq!(
            m.eval(parse_program("(if #t 1 2)").unwrap()).unwrap(),
            Object::Int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if #f 1 2)").unwrap()).unwrap(),
            Object::Int(2)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if 0 1 2)").unwrap()).unwrap(),
            Object::Int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if 1 1 2)").unwrap()).unwrap(),
            Object::Int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if #f (if #t 4 5) 2)").unwrap())
                .unwrap(),
            Object::Int(2)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if #t (if #t 4 5) 2)").unwrap())
                .unwrap(),
            Object::Int(4)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(define foo 1)").unwrap()).unwrap(),
            Object::Nil
        );
        assert_eq!(m.stack.len(), 0);
        assert!(m
            .env
            .front()
            .unwrap()
            .get("foo")
            .unwrap()
            .borrow()
            .eq(&Object::Int(1)));

        assert_eq!(m.eval(parse_program("1").unwrap()).unwrap(), Object::Int(1));
        assert_eq!(
            m.eval(parse_program("foo").unwrap()).unwrap(),
            Object::Int(1)
        );

        assert_eq!(
            m.eval(parse_program("(if (begin 1 2 #f) 2 3)").unwrap())
                .unwrap(),
            Object::Int(3)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(define foo (lambda (a b) #f)) (foo 2 3)").unwrap())
                .unwrap(),
            Object::Bool(false)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("((lambda (a b) #f) 2 3)").unwrap())
                .unwrap(),
            Object::Bool(false)
        );
        assert_eq!(m.stack.len(), 0);
        assert_eq!(m.env.len(), 2);

        assert_eq!(
            m.eval(parse_program("(define foo #f) foo").unwrap())
                .unwrap(),
            Object::Bool(false)
        );
        assert_eq!(m.stack.len(), 0);
        assert_eq!(m.env.len(), 3);
    }
}
