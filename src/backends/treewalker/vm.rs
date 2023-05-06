use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::builtins::{make_prelude_env, BuiltinFuncSig};
use crate::error::Errors;
use crate::object::{LambdaFormal, Object};

// Construct the 'begin' expression from a expr.
fn make_begin_expr(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    Ok(Object::Begin(expr))
}

// Construct the 'define' expression from a expr.
fn make_define_expr(env: Rc<RefCell<Object>>, expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
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
        Ok(Object::Define(sym, define_body[1].clone()))
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
        let lambda_expr = Object::Lambda {
            env: env.clone(),
            formals: Rc::new(RefCell::new(LambdaFormal::Fixed(args))),
            body: define_body[1].clone(),
        };
        Ok(Object::Define(fun_name, Rc::new(RefCell::new(lambda_expr))))
    } else {
        Err(Errors::RuntimeException(format!(
            "'DEFINE' should be followed by a symbol and an expression"
        )))
    }
}

// Construct the 'if' expression from a expr.
fn make_if_expr(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let if_body = Object::cons_to_vec(expr.clone())?;

    if if_body.len() < 2 {
        return Err(Errors::RuntimeException(format!(
            "'IF' should be followed by a condition clause, a then clause and an optional else clause"
        )));
    }

    Ok(Object::If {
        condition: if_body[0].clone(),
        then: if_body[1].clone(),
        otherwise: if if_body.len() == 3 {
            if_body[2].clone()
        } else {
            Rc::new(RefCell::new(Object::Unspecified))
        },
    })
}

// https://groups.csail.mit.edu/mac/ftpdir/scheme-reports/r5rs-html/r5rs_6.html
// Syntax: lambda <formals> <body>
// <formals> should have one of the following forms.
// 1) <variable>:
//      The procedure takes any number of arguments.
// 2) (<variable1> <variable2> ... <variable<N>>):
//      The procedure takes exactly the N number of arguments.
// 3) (<variable1> <variable2> ... <variable<N-1>> . <variable<N>>)
//      The procedure takes N or more arguments.
fn make_lambda_expr(env: Rc<RefCell<Object>>, expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let lambda_body = Object::cons_to_vec(expr.clone())?;
    if lambda_body.len() < 2 {
        return Err(Errors::RuntimeException(format!(
            "'LAMBDA' should be followed by a list of arguments and a function body"
        )));
    }

    let mut tail = Object::Nil;
    for body_expr in lambda_body[1..].iter() {
        tail = Object::Cons {
            car: body_expr.clone(),
            cdr: Rc::new(RefCell::new(tail)),
        };
    }
    tail = Object::make_begin(Object::reverse_list(tail));

    match &*lambda_body[0].clone().borrow() {
        // Any.
        Object::Symbol(ref formal) => Ok(Object::Lambda {
            env: env.clone(),
            formals: Rc::new(RefCell::new(LambdaFormal::Any(formal.clone()))),
            body: Rc::new(RefCell::new(tail)),
        }),
        Object::Cons { .. } => {
            let mut curr_cell = lambda_body[0].clone();
            let mut formals = vec![];
            let mut last_symbol = None;

            while let Object::Cons { ref car, ref cdr } = &*curr_cell.clone().borrow() {
                if let Object::Symbol(ref symbol_name) = &*car.clone().borrow() {
                    formals.push(symbol_name.clone());
                } else {
                    return Err(Errors::RuntimeException(format!(
                        "'LAMBDA' should be followed by a list of arguments and a function body"
                    )));
                }

                if let Object::Symbol(ref symbol_name) = &*cdr.clone().borrow() {
                    last_symbol = Some(symbol_name.clone());
                }

                curr_cell = cdr.clone();
            }

            match last_symbol {
                Some(last_sym) => Ok(Object::Lambda {
                    env: env.clone(),
                    formals: Rc::new(RefCell::new(LambdaFormal::AtLeastN(formals, last_sym))),
                    body: Rc::new(RefCell::new(tail)),
                }),
                None => Ok(Object::Lambda {
                    env: env.clone(),
                    formals: Rc::new(RefCell::new(LambdaFormal::Fixed(formals))),
                    body: Rc::new(RefCell::new(tail)),
                }),
            }
        }

        _ => Err(Errors::RuntimeException(format!(
            "'LAMBDA' should be followed by a list of arguments and a function body"
        ))),
    }
}

// Construct the 'let' expression from a expr.
// FIXME: 'let' should be implemented by macro???
fn make_let_expr(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let expr_vec = Object::cons_to_vec(expr)?;
    if expr_vec.len() != 2 {
        return Err(Errors::RuntimeException(format!(
            "Unexpected number of arguments for 'LET'"
        )));
    }

    let bindings_expr = Object::cons_to_vec(expr_vec[0].clone())?;
    let body_expr = expr_vec[1].clone();
    let mut binding_symbols = vec![];

    for bexpr in bindings_expr.iter() {
        match *bexpr.borrow() {
            Object::Cons { ref car, ref cdr } => match &*car.borrow() {
                Object::Symbol(ref symbol_name) => match &*cdr.borrow() {
                    Object::Cons { ref car, .. } => {
                        binding_symbols.push((symbol_name.clone(), car.clone()))
                    }
                    _ => {
                        return Err(Errors::RuntimeException(format!(
                            "Unexpected number of arguments for 'LET'"
                        )))
                    }
                },
                _ => {
                    return Err(Errors::RuntimeException(format!(
                        "Unexpected number of arguments for 'LET'"
                    )))
                }
            },
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "Unexpected number of arguments for 'LET'"
                )))
            }
        }
    }

    Ok(Object::Let {
        bindings: binding_symbols,
        body: body_expr,
    })
}

// Construct the 'quote' expression.
fn make_quote_expr(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    if args.len() != 1 {
        return Err(Errors::RuntimeException(format!("Ill-formed syntax")));
    }
    Ok(Object::Quote(args[0].clone()))
}

fn make_quasiquote_expr(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    if args.len() != 1 {
        return Err(Errors::RuntimeException(format!("Ill-formed syntax")));
    }
    Ok(Object::Quasiquote(args[0].clone()))
}

fn make_set_expr(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let set_body = Object::cons_to_vec(expr)?;
    if set_body.len() != 2 {
        return Err(Errors::RuntimeException(format!(
            "'SET' should be followed by a symbol and an expression"
        )));
    }

    if !set_body[0].borrow().is_symbol() {
        return Err(Errors::RuntimeException(format!(
            "'SET' should be followed by a symbol and an expression"
        )));
    }

    Ok(Object::Set(
        set_body[0].clone().borrow().symbol_name(),
        set_body[1].clone(),
    ))
}

pub struct Machine {
    env: Rc<RefCell<Object>>,
    stack: Vec<Rc<RefCell<Object>>>,
}

impl Machine {
    pub fn new() -> Self {
        Self {
            env: Rc::new(RefCell::new(Object::make_cons(
                Object::Env(Rc::new(RefCell::new(make_prelude_env()))),
                Object::Nil,
            ))),
            stack: vec![],
        }
    }

    #[allow(unused)]
    pub fn reset(&mut self) {
        self.env = Rc::new(RefCell::new(Object::make_cons(
            Object::Env(Rc::new(RefCell::new(make_prelude_env()))),
            Object::Nil,
        )));
        self.stack = vec![];
    }

    fn expand_macros(&mut self, expr: Object) -> Result<Object, Errors> {
        Ok(expr)
    }

    fn resolve_symbol(env: Rc<RefCell<Object>>, sym: &str) -> Result<Rc<RefCell<Object>>, Errors> {
        let mut curr_env = env.clone();

        while let Object::Cons { ref car, ref cdr } = &*curr_env.clone().borrow() {
            if let Object::Env(ref symtab) = &*car.clone().borrow() {
                match symtab.clone().borrow().get(sym) {
                    Some(v) => return Ok(v.clone()),
                    None => {
                        curr_env = cdr.clone();
                        continue;
                    }
                }
            } else {
                return Err(Errors::RuntimeException(format!(
                    "Cannot resolve symbol: '{}'",
                    sym
                )));
            }
        }

        return Err(Errors::RuntimeException(format!(
            "Cannot resolve symbol: '{}'",
            sym
        )));
    }

    fn define_symbol(
        env: Rc<RefCell<Object>>,
        sym: &str,
        val: Rc<RefCell<Object>>,
    ) -> Result<(), Errors> {
        if let Object::Cons { ref car, .. } = &*env.clone().borrow() {
            if let Object::Env(ref symtab) = &*car.clone().borrow() {
                if symtab.borrow().contains_key(sym) {
                    *symtab.clone().borrow_mut().get_mut(sym).unwrap() = val.clone();
                    return Ok(());
                } else {
                    symtab
                        .clone()
                        .borrow_mut()
                        .insert(sym.to_string(), val.clone());
                    return Ok(());
                }
            }
        }

        // Very unlikely to happend.
        panic!("Cannot define symbol '{}' in the current env", sym);
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
        Self::define_symbol(self.env.clone(), symbol_name, evaluated)?;
        Ok((Object::Nil, None))
    }

    // Evaluate the 'set!' expr and modify the environment.
    fn eval_set_expr(
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
        match Self::resolve_symbol(self.env.clone(), symbol_name) {
            Ok(sym) => {
                self.stack.push(expr);
                let new_val = self.eval_recursive()?;
                *sym.borrow_mut() = new_val;
                Ok((Object::Nil, None))
            }
            _ => Err(Errors::RuntimeException(format!(
                "Symbol '{}' is not defined",
                symbol_name,
            ))),
        }
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
                Some(Rc::new(RefCell::new(make_begin_expr(expr)?))),
            )),
            "DEFINE" => Ok((
                Object::Nil,
                Some(Rc::new(RefCell::new(make_define_expr(
                    self.env.clone(),
                    expr,
                )?))),
            )),
            "DEFINE-SYNTAX" => todo!(),
            "IF" => Ok((
                Object::Nil,
                Some(Rc::new(RefCell::new(make_if_expr(expr)?))),
            )),
            "LAMBDA" => Ok((
                Object::Nil,
                // For closures, we need to capture the environment in which the
                // closure is defined.
                Some(Rc::new(RefCell::new(make_lambda_expr(
                    self.env.clone(),
                    expr,
                )?))),
            )),
            "LET" => Ok((
                Object::Nil,
                Some(Rc::new(RefCell::new(make_let_expr(expr)?))),
            )),
            "QUOTE" => Ok((
                Object::Nil,
                Some(Rc::new(RefCell::new(make_quote_expr(expr)?))),
            )),
            "QUASIQUOTE" => Ok((
                Object::Nil,
                Some(Rc::new(RefCell::new(make_quasiquote_expr(expr)?))),
            )),
            "SET!" => Ok((
                Object::Nil,
                Some(Rc::new(RefCell::new(make_set_expr(expr)?))),
            )),
            "UNQUOTE" => Err(Errors::RuntimeException(String::from(
                "'UNQUOTE' should be used inside (QUASIQUOTE ..) expression",
            ))),
            "UNQUOTE-SPLICING" => Err(Errors::RuntimeException(String::from(
                "'UNQUOTE-SPLICING' should be used inside (QUASIQUOTE ..) expression",
            ))),
            _ => {
                // Try to evaluate sym.
                // FIXME: This is not perfect ... but it works ...
                // Try to improve it tomorrow!
                match Self::resolve_symbol(self.env.clone(), symbol_name) {
                    Ok(resolved_symbol) => Ok((
                        Object::Nil,
                        Some(Rc::new(RefCell::new(Object::Cons {
                            car: resolved_symbol,
                            cdr: expr.clone(),
                        }))),
                    )),
                    Err(_) => {
                        // Cannot resolve the symbol, is it a builtin function?
                        return Err(Errors::RuntimeException(format!(
                            "Cannot resolve symbol {}",
                            symbol_name
                        )));
                    }
                }
            }
        }
    }

    fn eval_lambda_expr(
        &mut self,
        env: Rc<RefCell<Object>>,
        formals: Rc<RefCell<LambdaFormal>>,
        body: Rc<RefCell<Object>>,
        args: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        match &*formals.clone().borrow() {
            LambdaFormal::Any(ref symbol_name) => {
                let passed_args = Object::cons_to_vec(args.clone())?;
                let mut tail = Object::Nil;

                for arg in passed_args {
                    self.stack.push(arg);
                    let evaluated = self.eval_recursive()?;

                    tail = Object::make_cons(evaluated, tail);
                }

                tail = Object::reverse_list(tail);

                // Prepare a new env.
                let new_env = Rc::new(RefCell::new(Object::Cons {
                    car: Rc::new(RefCell::new(Object::Env(Rc::new(RefCell::new(
                        HashMap::new(),
                    ))))),
                    cdr: env.clone(),
                }));
                Self::define_symbol(
                    new_env.clone(),
                    symbol_name.as_str(),
                    Rc::new(RefCell::new(tail)),
                )?;

                let old_env = self.env.clone();
                self.env = new_env.clone();

                // Evaluate the lambda expr.
                self.stack.push(body.clone());
                let result = self.eval_recursive()?;
                self.env = old_env;

                Ok((result, None))
            }
            LambdaFormal::Fixed(ref symbols) => {
                let passed_args_vec = Object::cons_to_vec(args.clone())?;
                if passed_args_vec.len() != symbols.len() {
                    return Err(Errors::RuntimeException(format!("Incorrect number of arguments supplied to lambda expression, expected: {}, provided: {}", symbols.len(), passed_args_vec.len())));
                }

                // Prepare a new env.
                let new_env = Rc::new(RefCell::new(Object::Cons {
                    car: Rc::new(RefCell::new(Object::Env(Rc::new(RefCell::new(
                        HashMap::new(),
                    ))))),
                    cdr: env.clone(),
                }));

                for arg_index in 0..symbols.len() {
                    self.stack.push(passed_args_vec[arg_index].clone());
                    let evaluated = self.eval_recursive()?;

                    Self::define_symbol(
                        new_env.clone(),
                        symbols[arg_index].as_str(),
                        Rc::new(RefCell::new(evaluated)),
                    )?;
                }

                let old_env = self.env.clone();
                self.env = new_env;
                self.stack.push(body.clone());
                let result = self.eval_recursive()?;

                // Pop the env since we use it to pass arguments to the lambda expression,
                // and we should clean it up.
                self.env = old_env;

                Ok((result, None))
            }
            LambdaFormal::AtLeastN(ref symbols, ref last_symbol) => {
                let passed_args_vec = Object::cons_to_vec(args.clone())?;
                if passed_args_vec.len() < symbols.len() {
                    return Err(
			Errors::RuntimeException(
			    format!("Incorrect number of arguments supplied to lambda expression, expected at least {}, provided: {}",
				    symbols.len(), passed_args_vec.len())));
                }

                // Prepare a new env.
                let new_env = Rc::new(RefCell::new(Object::Cons {
                    car: Rc::new(RefCell::new(Object::Env(Rc::new(RefCell::new(
                        HashMap::new(),
                    ))))),
                    cdr: env.clone(),
                }));

                let mut tail = Object::Nil;

                for (arg_index, arg) in passed_args_vec.iter().enumerate() {
                    self.stack.push(arg.clone());
                    let evaluated = self.eval_recursive()?;

                    if arg_index < symbols.len() {
                        Self::define_symbol(
                            new_env.clone(),
                            symbols[arg_index].as_str(),
                            Rc::new(RefCell::new(evaluated)),
                        )?;
                    } else {
                        tail = Object::make_cons(evaluated, tail);
                    }
                }

                // The last argument.
                Self::define_symbol(
                    new_env.clone(),
                    last_symbol.as_str(),
                    Rc::new(RefCell::new(Object::reverse_list(tail))),
                )?;

                let old_env = self.env.clone();

                self.env = new_env;
                self.stack.push(body.clone());
                let result = self.eval_recursive()?;

                self.env = old_env;

                Ok((result, None))
            }
        }
    }

    fn eval_let_expr(
        &mut self,
        bindings: &Vec<(String, Rc<RefCell<Object>>)>,
        body: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        // Prepare a new env.
        let new_env = Rc::new(RefCell::new(Object::Cons {
            car: Rc::new(RefCell::new(Object::Env(Rc::new(RefCell::new(
                HashMap::new(),
            ))))),
            cdr: self.env.clone(),
        }));

        for binding in bindings {
            self.stack.push(binding.1.clone());
            let evaluated = self.eval_recursive()?;
            Self::define_symbol(
                new_env.clone(),
                binding.0.as_str(),
                Rc::new(RefCell::new(evaluated)),
            )?;
        }

        let old_env = self.env.clone();
        self.env = new_env.clone();

        self.stack.push(body);
        let result = self.eval_recursive()?;

        // Pop the current env, since we don't need it again.
        self.env = old_env;

        Ok((result, None))
    }

    fn eval_builtin_func(
        &mut self,
        builtin_func: Rc<BuiltinFuncSig>,
        expr: Rc<RefCell<Object>>,
    ) -> Result<
        (
            /* curr_result */ Object,
            /* next_expr */ Option<Rc<RefCell<Object>>>,
        ),
        Errors,
    > {
        let args = Object::cons_to_vec(expr)?;
        let mut tail = Object::Nil;
        for arg in args.iter() {
            self.stack.push(arg.clone());
            let evaluated_arg = self.eval_recursive()?;
            tail = Object::make_cons(evaluated_arg, tail);
        }

        Ok((
            builtin_func(Rc::new(RefCell::new(Object::reverse_list(tail))))?,
            None,
        ))
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
            Object::Lambda {
                ref env,
                ref formals,
                ref body,
            } => {
                // Apply lambda expression against 'cdr'.
                self.eval_lambda_expr(env.clone(), formals.clone(), body.clone(), cdr.clone())
            }
            Object::Cons { .. } => {
                // The 'car' expression maybe callable, let's evaluate it and try to apply
                // it against 'cdr'.
                self.stack.push(car.clone());
                let evaluated = self.eval_recursive()?;
                Ok((
                    Object::Nil,
                    Some(Rc::new(RefCell::new(Object::Cons {
                        car: Rc::new(RefCell::new(evaluated)),
                        cdr: cdr.clone(),
                    }))),
                ))
            }
            Object::BuiltinFunc(ref builtin_func, _) => {
                self.eval_builtin_func(builtin_func.clone(), cdr.clone())
            }
            ref o => Err(Errors::RuntimeException(format!(
                "Object '{}' is not callable",
                o
            ))),
        }
    }

    // Evaluate the quasiquote expression.
    fn eval_quasiquote_expr(
        &mut self,
        curr_expr: Rc<RefCell<Object>>,
        quasiquote_dep: i64,
    ) -> Result<Object, Errors> {
        if quasiquote_dep == 0 {
            self.stack.push(curr_expr);
            self.eval_recursive()
        } else if quasiquote_dep < 0 {
            Err(Errors::RuntimeException(String::from(
                "UNQUOTE should be used within (quasiquote ..) expression",
            )))
        } else {
            match &*curr_expr.clone().borrow() {
                Object::Cons { ref car, ref cdr } => match &*car.clone().borrow() {
                    // Since we didn't expand expressions inside (quasiquote ..), we should
                    // identify these special symbols here.
                    Object::Symbol(ref symbol_name) => {
                        match symbol_name.to_uppercase().as_str() {
                            "QUASIQUOTE" => {
                                let arg = Object::cons_to_vec(cdr.clone())?;
                                if arg.len() != 1 {
                                    return Err(Errors::RuntimeException(String::from(
                                        "Ill-formed syntax",
                                    )));
                                }
                                Ok(Object::make_quasiquote(self.eval_quasiquote_expr(
                                    arg[0].clone(),
                                    quasiquote_dep + 1,
                                )?))
                            }
                            "UNQUOTE" => {
                                let arg = Object::cons_to_vec(cdr.clone())?;
                                if arg.len() != 1 {
                                    return Err(Errors::RuntimeException(String::from(
                                        "Ill-formed syntax",
                                    )));
                                }
                                if quasiquote_dep == 1 {
                                    Ok(self
                                        .eval_quasiquote_expr(arg[0].clone(), quasiquote_dep - 1)?)
                                } else {
                                    // Unquote expressions nested in multiple levels of quasiquote shouldn't be evaluated.
                                    Ok(Object::make_unquote(self.eval_quasiquote_expr(
                                        arg[0].clone(),
                                        quasiquote_dep - 1,
                                    )?))
                                }
                            }
                            "QUOTE" => {
                                let arg = Object::cons_to_vec(cdr.clone())?;
                                if arg.len() != 1 {
                                    return Err(Errors::RuntimeException(String::from(
                                        "Ill-formed syntax",
                                    )));
                                }
                                Ok(Object::Quote(arg[0].clone()))
                            }
                            "UNQUOTE-SPLICING" => {
                                let arg = Object::cons_to_vec(cdr.clone())?;
                                if arg.len() != 1 {
                                    return Err(Errors::RuntimeException(String::from(
                                        "Ill-formed syntax",
                                    )));
                                }

                                if quasiquote_dep == 1 {
                                    let result = self
                                        .eval_quasiquote_expr(arg[0].clone(), quasiquote_dep - 1)?;
                                    // Check if the result is a list.
                                    if !result.is_cons() {
                                        Err(Errors::RuntimeException(String::from(
                                            "'UNQUOTE-SPLICING' must be evaluated to list",
                                        )))
                                    } else {
                                        Ok(Object::make_evaluated_unquotesplice(result))
                                    }
                                } else {
                                    // Unquote expressions nested in multiple levels of quasiquote shouldn't be evaluated.
                                    Ok(Object::make_unquotesplice(self.eval_quasiquote_expr(
                                        arg[0].clone(),
                                        quasiquote_dep - 1,
                                    )?))
                                }
                            }
                            _ => Ok(Object::Cons {
                                car: car.clone(),
                                cdr: Rc::new(RefCell::new(
                                    self.eval_quasiquote_expr(cdr.clone(), quasiquote_dep)?,
                                )),
                            }),
                        }
                    }
                    _ => {
                        let evaluated_car =
                            self.eval_quasiquote_expr(car.clone(), quasiquote_dep)?;
                        let evaluated_cdr =
                            self.eval_quasiquote_expr(cdr.clone(), quasiquote_dep)?;
                        match evaluated_cdr {
                            Object::EvaluatedUnquoteSplice(_) => {
                                return Err(Errors::RuntimeException(String::from(
                                    "Invalid context for using 'UNQUOTE-SPLICING'",
                                )));
                            }
                            _ => match evaluated_car {
                                Object::EvaluatedUnquoteSplice(mut unqspl) => {
                                    // If this expression is evaluated from unquote-splicing, we should expand it here.
                                    let mut tail = Object::Nil;

                                    while let Object::Cons { ref car, ref cdr } =
                                        &*unqspl.clone().borrow()
                                    {
                                        tail = Object::Cons {
                                            car: car.clone(),
                                            cdr: Rc::new(RefCell::new(tail)),
                                        };
                                        unqspl = cdr.clone();
                                    }

                                    if !evaluated_cdr.is_nil() {
                                        tail = Object::make_cons(evaluated_cdr, tail);
                                    }

                                    Ok(Object::reverse_list(tail))
                                }
                                _ => Ok(Object::Cons {
                                    car: Rc::new(RefCell::new(evaluated_car)),
                                    cdr: Rc::new(RefCell::new(evaluated_cdr)),
                                }),
                            },
                        }
                    }
                },
                Object::Quasiquote(ref quasiquoted) => Ok(Object::make_quasiquote(
                    self.eval_quasiquote_expr(quasiquoted.clone(), quasiquote_dep + 1)?,
                )),
                Object::Unquote(ref unquoted) => {
                    if quasiquote_dep == 1 {
                        Ok(self.eval_quasiquote_expr(unquoted.clone(), quasiquote_dep - 1)?)
                    } else {
                        // Unquote expressions nested in multiple levels of quasiquote shouldn't be evaluated.
                        Ok(Object::make_unquote(self.eval_quasiquote_expr(
                            unquoted.clone(),
                            quasiquote_dep - 1,
                        )?))
                    }
                }
                Object::UnquoteSplice(ref unquoted) => {
                    if quasiquote_dep == 1 {
                        let result =
                            self.eval_quasiquote_expr(unquoted.clone(), quasiquote_dep - 1)?;
                        // Check if the result is a list.
                        if !result.is_cons() {
                            Err(Errors::RuntimeException(String::from(
                                "'UNQUOTE-SPLICING' must be evaluated to list",
                            )))
                        } else {
                            Ok(Object::make_evaluated_unquotesplice(result))
                        }
                    } else {
                        // Unquote expressions nested in multiple levels of quasiquote shouldn't be evaluated.
                        Ok(Object::make_unquotesplice(self.eval_quasiquote_expr(
                            unquoted.clone(),
                            quasiquote_dep - 1,
                        )?))
                    }
                }
                atom @ Object::Bool(_)
                | atom @ Object::Char { .. }
                | atom @ Object::Int(_)
                | atom @ Object::Nil
                | atom @ Object::Quote(_)
                | atom @ Object::Real(_)
                | atom @ Object::String(_) => Ok(atom.clone()),
                ref x => panic!(
                    "Unexpected expression '{}' in (QUASIQUOTE ...) expression",
                    x.to_string()
                ),
            }
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
            Object::Cons { ref car, ref cdr } => self.eval_cons_expr(car.clone(), cdr.clone()),
            Object::Define(ref symbol_name, ref expr) => {
                self.eval_define_expr(symbol_name.as_str(), expr.clone())
            }
            Object::Set(ref symbol_name, ref expr) => {
                self.eval_set_expr(symbol_name.as_str(), expr.clone())
            }
            Object::If {
                ref condition,
                ref then,
                ref otherwise,
            } => self.eval_if_expr(condition.clone(), then.clone(), otherwise.clone()),
            Object::Symbol(ref symbol_name) => {
                let resolved_sym = Self::resolve_symbol(self.env.clone(), symbol_name.as_str())?
                    .borrow()
                    .clone();
                Ok((resolved_sym, None))
            }
            Object::Quasiquote(ref quasiquoted_expr) => Ok((
                self.eval_quasiquote_expr(quasiquoted_expr.clone(), 1)?,
                None,
            )),
            Object::Unquote(_) => {
                // This is unlikely to happend, but we have to add it to silence compiler warnings.
                Err(Errors::RuntimeException(String::from(
                    "'UNQUOTE' should be used within (quasiquote ..) expression",
                )))
            }
            Object::UnquoteSplice(_) => {
                // This is unlikely to happend, but we have to add it to silence compiler warnings.
                Err(Errors::RuntimeException(String::from(
                    "'UNQUOTE-SPLICING' should be used within (quasiquote ..) expression",
                )))
            }
            Object::EvaluatedUnquoteSplice(_) => {
                panic!("Unexpected Object::EvaluatedUnquoteSplice node")
            }
            Object::Quote(ref quoted_expr) => Ok((quoted_expr.borrow().clone(), None)),
            Object::Let {
                ref bindings,
                ref body,
            } => self.eval_let_expr(bindings, body.clone()),
            // For atomic expressions, just copy them and return.
            atom @ Object::Int(_)
            | atom @ Object::Bool(_)
            | atom @ Object::Char { .. }
            | atom @ Object::String(_)
            | atom @ Object::Lambda { .. }
            | atom @ Object::Real(_)
            | atom @ Object::BuiltinFunc(_, _)
            | atom @ Object::Nil
            | atom @ Object::Unspecified => Ok((atom.clone(), None)),
            ref o => Err(Errors::RuntimeException(format!(
                "Unrecognized object: '{:?}'",
                o
            ))),
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
                None => {
                    return Ok(result.0);
                }
            }
        }
    }

    pub fn eval(&mut self, expr: Object) -> Result<Object, Errors> {
        let expanded_expr = self.expand_macros(expr)?;

        self.stack
            .push(Rc::new(RefCell::new(/* expr */ expanded_expr)));

        self.eval_recursive()
    }
}

#[cfg(test)]
mod tests {
    use crate::{backends::treewalker::vm::Machine, object::Object, parser::parse_program};

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
            Object::make_int(2)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            // "(begin)"
            m.eval(parse_program("(begin)").unwrap()).unwrap(),
            Object::Nil
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            // "(begin (begin 1 2 3))"
            m.eval(parse_program("(begin (begin 1 2 3))").unwrap())
                .unwrap(),
            Object::make_int(3)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(begin (begin 1))").unwrap()).unwrap(),
            Object::make_int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if #t 1 2)").unwrap()).unwrap(),
            Object::make_int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if #f 1 2)").unwrap()).unwrap(),
            Object::make_int(2)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if 0 1 2)").unwrap()).unwrap(),
            Object::make_int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if 1 1 2)").unwrap()).unwrap(),
            Object::make_int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if #f (if #t 4 5) 2)").unwrap())
                .unwrap(),
            Object::make_int(2)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(if #t (if #t 4 5) 2)").unwrap())
                .unwrap(),
            Object::make_int(4)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(define foo 1)").unwrap()).unwrap(),
            Object::Nil
        );
        assert_eq!(m.stack.len(), 0);
        assert_eq!(
            m.eval(parse_program("foo").unwrap()).unwrap(),
            Object::make_int(1)
        );

        assert_eq!(
            m.eval(parse_program("1").unwrap()).unwrap(),
            Object::make_int(1)
        );
        assert_eq!(
            m.eval(parse_program("foo").unwrap()).unwrap(),
            Object::make_int(1)
        );

        assert_eq!(
            m.eval(parse_program("(if (begin 1 2 #f) 2 3)").unwrap())
                .unwrap(),
            Object::make_int(3)
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
        assert_eq!(Object::cons_to_vec(m.env.clone()).unwrap().len(), 1);

        assert_eq!(
            m.eval(parse_program("(define foo #f) foo").unwrap())
                .unwrap(),
            Object::Bool(false)
        );
        assert_eq!(m.stack.len(), 0);
        assert_eq!(Object::cons_to_vec(m.env.clone()).unwrap().len(), 1);

        assert_eq!(
            m.eval(parse_program("(define (foo) #f) (foo)").unwrap())
                .unwrap(),
            Object::Bool(false)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(+ 1 2 3 4 5)").unwrap()).unwrap(),
            Object::make_int(15)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(quote a)").unwrap()).unwrap(),
            Object::Symbol(String::from("a"))
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("'a").unwrap()).unwrap(),
            Object::Symbol(String::from("a"))
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("((if #f + cons) 3 4)").unwrap())
                .unwrap(),
            Object::make_cons(Object::make_int(3), Object::make_int(4))
        );
        assert_eq!(m.stack.len(), 0);

        // Some examples from https://groups.csail.mit.edu/mac/ftpdir/scheme-reports/r5rs-html/r5rs_6.html
        assert_eq!(
            m.eval(parse_program("(quote (+ 1 2))").unwrap()).unwrap(),
            Object::make_cons(
                Object::Symbol(String::from("+")),
                Object::make_cons(
                    Object::make_int(1),
                    Object::make_cons(Object::make_int(2), Object::Nil)
                )
            )
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(let ((x 2) (y 3)) (* x y))").unwrap())
                .unwrap(),
            Object::make_int(6)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(let ((x 2) (y 3)) (let ((x 7) (z (+ x y))) (* z x)))").unwrap())
                .unwrap(),
            Object::make_int(35)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("((lambda x x) 1 2 3)").unwrap())
                .unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(2),
                    Object::make_cons(Object::make_int(3), Object::Nil)
                )
            )
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("((lambda (a . b) a) 1 2 3)").unwrap())
                .unwrap(),
            Object::make_int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("((lambda (a . b) b) 1 2 3)").unwrap())
                .unwrap(),
            Object::make_cons(
                Object::make_int(2),
                Object::make_cons(Object::make_int(3), Object::Nil)
            )
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("((lambda (a . b) b) 1)").unwrap())
                .unwrap(),
            Object::Nil,
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(
                parse_program("(define (fact n) (if (= n 1) 1 (* n (fact (- n 1))))) (fact 4)")
                    .unwrap()
            )
            .unwrap(),
            Object::make_int(24)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("`(+ 1 ,(+ 2 3))").unwrap()).unwrap(),
            Object::make_cons(
                Object::Symbol(String::from("+")),
                Object::make_cons(
                    Object::make_int(1),
                    Object::make_cons(Object::make_int(5), Object::Nil)
                )
            ),
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("``,,1").unwrap()).unwrap(),
            Object::make_quasiquote(Object::make_unquote(Object::make_int(1)))
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("`,`,1").unwrap()).unwrap(),
            Object::make_int(1)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("`(,@'(1 2 3))").unwrap()).unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(2),
                    Object::make_cons(Object::make_int(3), Object::Nil)
                )
            )
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(quasiquote (,@'(1 2 3)))").unwrap())
                .unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(2),
                    Object::make_cons(Object::make_int(3), Object::Nil)
                )
            )
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(quasiquote ((unquote-splicing '(1 2 3))))").unwrap())
                .unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(2),
                    Object::make_cons(Object::make_int(3), Object::Nil)
                )
            )
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(
                parse_program("(define x 3) (define (foo) (begin (define x 4) x)) (foo)").unwrap()
            )
            .unwrap(),
            Object::make_int(4)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("x").unwrap()).unwrap(),
            Object::make_int(3)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("(define (bar) (begin (set! x 4) x)) (bar)").unwrap())
                .unwrap(),
            Object::make_int(4)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("x").unwrap()).unwrap(),
            Object::make_int(4)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(parse_program("((lambda (x) (+ 1 x) (+ 1 x)) 1)").unwrap())
                .unwrap(),
            Object::make_int(2)
        );
        assert_eq!(m.stack.len(), 0);

        assert_eq!(
            m.eval(
                parse_program("(define x 1) (define (f x) (g 2)) (define (g y) (+ x y)) (f 5)")
                    .unwrap()
            )
            .unwrap(),
            Object::make_int(3)
        );
        assert_eq!(m.stack.len(), 0);
        assert_eq!(Object::cons_to_vec(m.env.clone()).unwrap().len(), 1);
    }
}
