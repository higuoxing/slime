use crate::error::Errors;
use crate::object::Object;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

pub type BuiltinFuncSig = fn(Rc<RefCell<Object>>) -> Result<Object, Errors>;

const BUILTIN_FUNCTIONS: &[(&str, BuiltinFuncSig)] = &[
    ("cons", builtin_cons as BuiltinFuncSig),
    ("=", builtin_numeric_eq as BuiltinFuncSig),
    ("+", builtin_numeric_plus as BuiltinFuncSig),
    ("-", builtin_numeric_minus as BuiltinFuncSig),
    ("*", builtin_numeric_times as BuiltinFuncSig),
];

pub fn make_prelude_env() -> HashMap<String, Rc<RefCell<Object>>> {
    let mut prelude_env: HashMap<String, Rc<RefCell<Object>>> = HashMap::new();

    // Initialize the builtin function table.
    for (fun_index, (fun_name, fun_impl)) in BUILTIN_FUNCTIONS.iter().enumerate() {
        prelude_env.insert(
            fun_name.to_string(),
            Rc::new(RefCell::new(Object::BuiltinFunc(
                Rc::new(*fun_impl),
                fun_index,
            ))),
        );
    }

    prelude_env
}

fn builtin_cons(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    if args.len() != 2 {
        return Err(Errors::RuntimeException(format!(
            "CONS expects 2 arguments"
        )));
    }
    Ok(Object::Cons {
        car: args[0].clone(),
        cdr: args[1].clone(),
    })
}

fn builtin_numeric_eq(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    if args.len() != 2 {
        return Err(Errors::RuntimeException(format!(
            "'=' expects 2 arguments, got {} arguments",
            args.len()
        )));
    }

    let mut use_float = false;

    for arg in args.iter() {
        match &*arg.clone().borrow() {
            Object::Real(_) => use_float = true,
            Object::Int(_) => continue,
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "'=' expectes 2 numeric typed objects"
                )))
            }
        }
    }

    if use_float {
        let arg1 = args[0].clone().borrow().get_as_float();
        let arg2 = args[1].clone().borrow().get_as_float();
        Ok(Object::Bool(arg1 == arg2))
    } else {
        let arg1 = args[0].clone().borrow().get_as_int();
        let arg2 = args[1].clone().borrow().get_as_int();
        Ok(Object::Bool(arg1 == arg2))
    }
}

fn builtin_numeric_plus(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    let mut use_float = false;

    for arg in args.iter() {
        match &*arg.borrow() {
            Object::Int(_) => {
                continue;
            }
            Object::Real(_) => {
                use_float = true;
            }
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "'+' can only be applied to numeric objects"
                )))
            }
        }
    }

    if use_float {
        let mut result = 0.0;
        for arg in args.iter() {
            result += arg.clone().borrow().get_as_float();
        }
        Ok(Object::Real(result))
    } else {
        let mut result = 0;
        for arg in args.iter() {
            result += arg.clone().borrow().get_as_int();
        }
        Ok(Object::Int(result))
    }
}

fn builtin_numeric_minus(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    let mut use_float = false;

    if args.len() < 1 {
        return Err(Errors::RuntimeException(String::from(
            "Unexpected number of arguments",
        )));
    }

    for arg in args.iter() {
        match &*arg.borrow() {
            Object::Int(_) => continue,
            Object::Real(_) => use_float = true,
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "'-' can only be applied to numeric objects"
                )))
            }
        }
    }

    if use_float {
        let mut result = 0.0;
        for (arg_index, arg) in args.iter().enumerate() {
            if arg_index == 0 {
                if args.len() == 1 {
                    result = 0.0 - arg.clone().borrow().get_as_float();
                } else {
                    result = arg.clone().borrow().get_as_float();
                }
            } else {
                result -= arg.clone().borrow().get_as_float();
            }
        }

        Ok(Object::Real(result))
    } else {
        let mut result = 0;
        for (arg_index, arg) in args.iter().enumerate() {
            if arg_index == 0 {
                if args.len() == 1 {
                    result -= arg.clone().borrow().get_as_int();
                } else {
                    result = arg.clone().borrow().get_as_int();
                }
            } else {
                result -= arg.clone().borrow().get_as_int();
            }
        }

        Ok(Object::Int(result))
    }
}

fn builtin_numeric_times(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    let mut use_float = false;

    for arg in args.iter() {
        match &*arg.borrow() {
            Object::Int(_) => {
                continue;
            }
            Object::Real(_) => {
                use_float = true;
            }
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "'*' can only be applied to numeric objects"
                )))
            }
        }
    }

    if use_float {
        let mut result = 1.0;
        for arg in args.iter() {
            result *= arg.clone().borrow().get_as_float();
        }
        Ok(Object::Real(result))
    } else {
        let mut result = 1;
        for arg in args.iter() {
            result *= arg.clone().borrow().get_as_int();
        }
        Ok(Object::Int(result))
    }
}
