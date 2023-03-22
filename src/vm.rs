use std::cell::RefCell;
use std::collections::{HashMap, LinkedList};
use std::rc::Rc;

use crate::error::Errors;
use crate::object::Object;

pub struct Machine {
    // FIXME: The current implementation of env is not correct.
    env: LinkedList<HashMap<String, Rc<RefCell<Object>>>>,
    stack: Vec<Rc<RefCell<Object>>>,
}

impl Machine {
    pub fn new() -> Self {
        // Prepare a new environment.
        let mut env_list = LinkedList::new();
        env_list.push_front(HashMap::new());

        Self {
            env: env_list,
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
            None => panic!("You should provide an environment first!"),
        }
    }

    // Evaluate the condition expression and returns the 'then' clause
    // or the 'else' clause.
    fn eval_if_expr(
        &mut self,
        cond: Rc<RefCell<Object>>,
        then: Rc<RefCell<Object>>,
        otherwise: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        self.stack.push(cond);
        match self.eval_recursive()? {
            Object::Bool(cond_result) => {
                if !cond_result {
                    Ok((Object::Nil, Some(otherwise.clone())))
                } else {
                    Ok((Object::Nil, Some(then.clone())))
                }
            }
            // Any expression that cannot be evaluated to be #f is #t.
            _ => Ok((Object::Nil, Some(then.clone()))),
        }
    }

    // Evaluate a sequence of expressions and return the result of the last expression.
    // (begin E1 E2 E3 ...)
    fn eval_seq_expr(
        &mut self,
        seq_expr: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        let mut result = Object::Nil;
        let exprs = Object::cons_to_vec(seq_expr)?;
        for expr in exprs {
            // Evaluate (begin E1 E2 E3 ...) sequentially.
            self.stack.push(expr);
            result = self.eval_recursive()?;
        }

        Ok((result, None))
    }

    // Evaluate the 'define' expr and add the symbol to the current environment.
    fn eval_define_expr(
        &mut self,
        symbol_name: &str,
        expr: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        self.stack.push(expr);
        let evaluated = Rc::new(RefCell::new(self.eval_recursive()?));
        self.define_symbol(symbol_name, evaluated)?;

        Ok((Object::Nil, None))
    }

    fn eval_callable_symbol(
        &mut self,
        symbol_name: &str,
        expr: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        match symbol_name.to_uppercase().as_str() {
            // Build premitives.
            "BEGIN" => Ok((
                Object::Nil,
                Some(Rc::new(RefCell::new(Object::Begin(expr)))),
            )),
            "DEFINE" => {
                // There're 3 forms of define.
                // 1) (define <variable> <expression>)
                // 2) (define (<variable> <formals>) <body>) which is equivalent to
                //      (define <variable>
                //        (lambda (<formals>) <body>))
                // 3) (define (<variable> . <formal>) <body>) which is equivalent to
                //      (define <variable>
                //        (lambda <formal> <body>))
                // See: https://conservatory.scheme.org/schemers/Documents/Standards/R5RS/HTML/
                //
                // We only allows the first 2 forms here.
                let define_body = Object::cons_to_vec(expr)?;
                if define_body.len() != 2 {
                    return Err(Errors::RuntimeException(format!(
                        "'DEFINE' should be followed by a symbol and an expression"
                    )));
                }

                if define_body[0].borrow().is_symbol() {
                    let sym = define_body[0].borrow().symbol_name();
                    Ok((
                        Object::Nil,
                        Some(Rc::new(RefCell::new(Object::Define(
                            sym,
                            define_body[1].clone(),
                        )))),
                    ))
                } else if define_body[0].borrow().is_cons() {
                    // Simple form for defining function.
                    let fun_name_with_args = Object::cons_to_vec(define_body[0].clone())?;
                    let mut args = vec![];
                    // Check function name and arguments.
                    for (sym_index, sym) in fun_name_with_args.iter().enumerate() {
                        if !sym.borrow().is_symbol() {
                            return Err(Errors::RuntimeException(format!(
                                "'DEFINE' should be followed by a symbol and an expression"
                            )));
                        }

                        if sym_index != 0 {
                            args.push(sym.borrow().symbol_name());
                        }
                    }
                    // Construct a lambda expression.
                    let fun_name = fun_name_with_args[0].borrow().symbol_name();
                    let lambda_expr = Object::Lambda(args, define_body[1].clone());
                    Ok((
                        Object::Nil,
                        Some(Rc::new(RefCell::new(Object::Define(
                            fun_name,
                            Rc::new(RefCell::new(lambda_expr)),
                        )))),
                    ))
                } else {
                    Err(Errors::RuntimeException(format!(
                        "'DEFINE' should be followed by a symbol and an expression"
                    )))
                }
            }
            "IF" => {
                let if_body = Object::cons_to_vec(expr.clone())?;

                if if_body.len() != 3 {
                    return Err(Errors::RuntimeException(format!("'IF' should be followed by a condition clause, a then clause and a else clause")));
                }

                Ok((
                    Object::Nil,
                    Some(Rc::new(RefCell::new(Object::If(
                        if_body[0].clone(),
                        if_body[1].clone(),
                        if_body[2].clone(),
                    )))),
                ))
            }
            "LAMBDA" => {
                let lambda_body = Object::cons_to_vec(expr.clone())?;
                if lambda_body.len() != 2 {
                    return Err(Errors::RuntimeException(format!(
                        "'LAMBDA' should be followed by a list of arguments and a function body"
                    )));
                }

                let lambda_args = Object::cons_to_vec(lambda_body[0].clone())?;
                let mut args_names = vec![];

                for arg in lambda_args {
                    if !arg.borrow().is_symbol() {
                        return Err(Errors::RuntimeException(format!("'LAMBDA' should be followed by a list of arguments and a function body")));
                    }

                    args_names.push(arg.borrow().symbol_name());
                }

                Ok((
                    Object::Nil,
                    Some(Rc::new(RefCell::new(Object::Lambda(
                        args_names,
                        lambda_body[1].clone(),
                    )))),
                ))
            }
            _ => {
                // Try to evaluate sym.
                // FIXME: This is not perfect ... but it works ...
                // Try to improve it tomorrow!
                let resolved_symbol = self.resolve_symbol(symbol_name)?;
                self.stack.push(resolved_symbol);
                let evaluated = self.eval_recursive()?;
                Ok((
                    Object::Nil,
                    Some(Rc::new(RefCell::new(Object::Cons(
                        Rc::new(RefCell::new(evaluated)),
                        expr.clone(),
                    )))),
                ))
            }
        }
    }

    fn eval_lambda_expr(
        &mut self,
        lambda_args: &Vec<String>,
        lambda_expr: Rc<RefCell<Object>>,
        passed_args: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        let passed_args_vec = Object::cons_to_vec(passed_args.clone())?;
        if lambda_args.len() != passed_args_vec.len() {
            return Err(Errors::RuntimeException(format!(
                "Incorrect number of arguments supplied to lambda expression, expected: {}, provided: {}"
            , lambda_args.len(), passed_args_vec.len())));
        }

        // Push a new env first.
        self.env.push_front(HashMap::new());

        // Pass arguments by env.
        for arg_index in 0..lambda_args.len() {
            self.stack.push(passed_args_vec[arg_index].clone());
            let evaluated = self.eval_recursive()?;
            self.define_symbol(
                lambda_args[arg_index].as_str(),
                Rc::new(RefCell::new(evaluated)),
            )?;
        }

        self.stack.push(lambda_expr.clone());
        let result = self.eval_recursive()?;

        // Pop the env since we use it to pass arguments to the lambda expression,
        // and we should clean it up.
        self.env.pop_front();

        Ok((result, None))
    }

    fn eval_cons_expr(
        &mut self,
        car: Rc<RefCell<Object>>,
        cdr: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        match &*car.clone().borrow() {
            Object::Symbol(ref symbol_name) => {
                // Apply symbol against cdr.
                self.eval_callable_symbol(symbol_name.as_str(), cdr)
            }
            Object::Lambda(ref args, ref expr) => {
                // Apply lambda expression against 'cdr'.
                self.eval_lambda_expr(args, expr.clone(), cdr.clone())
            }
            Object::Cons(_, _) => {
                // The 'car' expression maybe callable, let's evaluate it and try to apply
                // it against 'cdr'.
                self.stack.push(car.clone());
                let evaluated = self.eval_recursive()?;
                Ok((
                    Object::Nil,
                    Some(Rc::new(RefCell::new(Object::Cons(
                        Rc::new(RefCell::new(evaluated)),
                        cdr.clone(),
                    )))),
                ))
            }
            ref o => Err(Errors::RuntimeException(format!(
                "Object '{:?}' is not callable",
                o
            ))),
        }
    }

    // Evaluate the current expression, dispatch the current expression to
    // appropriate 'eval' function.
    fn eval_current_expr(
        &mut self,
        curr_expr: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        match &*curr_expr.clone().borrow() {
            Object::Begin(ref seq) => self.eval_seq_expr(seq.clone()),
            Object::Cons(ref car, ref cdr) => self.eval_cons_expr(car.clone(), cdr.clone()),
            Object::Define(ref symbol_name, ref expr) => {
                self.eval_define_expr(symbol_name.as_str(), expr.clone())
            }
            Object::If(ref cond, ref then, ref otherwise) => {
                self.eval_if_expr(cond.clone(), then.clone(), otherwise.clone())
            }
            Object::Symbol(ref symbol_name) => Ok((
                Object::Nil,
                Some(self.resolve_symbol(symbol_name.as_str())?),
            )),
            // For atomic expressions, just copy them and return.
            atom @ Object::Int(_)
            | atom @ Object::Bool(_)
            | atom @ Object::Char(_, _)
            | atom @ Object::Lambda(_, _)
            | atom @ Object::Real(_)
            | atom @ Object::Nil => return Ok((atom.clone(), None)),
        }
    }

    // This function is the main entry for evaluating expressions and is called
    // recursively. Before calling this function, an expression should be pushed
    // into self.stack first.
    fn eval_recursive(&mut self) -> Result<Object, Errors> {
        let mut curr_expr = self.stack.pop().unwrap();

        loop {
            let result = self.eval_current_expr(curr_expr.clone())?;
            match result.1 {
                Some(next_expr) => {
                    curr_expr = next_expr.clone();
                    continue;
                }
                None => return Ok(result.0),
            }
        }
    }

    fn eval(&mut self, expr: Object) -> Result<Object, Errors> {
        let expanded_expr = self.expand_macros(expr)?;

        self.stack
            .push(Rc::new(RefCell::new(/* expr */ expanded_expr)));

        Ok(self.eval_recursive()?)
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
        assert_eq!(m.env.len(), 1);

        assert_eq!(
            m.eval(parse_program("(define foo #f) foo").unwrap())
                .unwrap(),
            Object::Bool(false)
        );
        assert_eq!(m.stack.len(), 0);
        assert_eq!(m.env.len(), 1);

        assert_eq!(
            m.eval(parse_program("(define (foo) #f) (foo)").unwrap())
                .unwrap(),
            Object::Bool(false)
        );
        assert_eq!(m.stack.len(), 0);
    }
}
