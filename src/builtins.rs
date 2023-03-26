use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::error::Errors;
use crate::object::Object;

pub type BuiltinFuncSig = fn(Rc<RefCell<Object>>) -> Result<Object, Errors>;

const BUILTIN_FUNCTIONS: &[(&str, BuiltinFuncSig)] = &[
    ("cons", builtin_cons as BuiltinFuncSig),
    ("=", builtin_numeric_eq as BuiltinFuncSig),
    ("+", builtin_numeric_plus as BuiltinFuncSig),
    ("-", builtin_numeric_minus as BuiltinFuncSig),
    ("*", builtin_numeric_times as BuiltinFuncSig),
];

pub fn make_prelude_env() -> HashMap<String, (Rc<BuiltinFuncSig>, usize)> {
    let mut builtins: HashMap<String, (Rc<BuiltinFuncSig>, usize)> = HashMap::new();

    // Initialize the builtin function table.
    for (fun_index, (fun_name, fun_impl)) in BUILTIN_FUNCTIONS.iter().enumerate() {
        builtins.insert(fun_name.to_string(), (Rc::new(*fun_impl), fun_index));
    }

    builtins
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
            "'+' expects 2 arguments, got {} arguments",
            args.len()
        )));
    }

    let arg1 = match &*args[0].borrow() {
        Object::Int(n) => *n as f64,
        Object::Real(n) => *n,
        _ => {
            return Err(Errors::RuntimeException(String::from(
                "Unexpected object for argument 1",
            )))
        }
    };

    let arg2 = match &*args[1].borrow() {
        Object::Int(n) => *n as f64,
        Object::Real(n) => *n,
        _ => {
            return Err(Errors::RuntimeException(String::from(
                "Unexpected object for argument 2",
            )))
        }
    };

    return Ok(Object::Bool(arg1 == arg2));
}

fn builtin_numeric_plus(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    let mut return_float = false;
    let mut result: f64 = 0.0;

    for arg in args.iter() {
        match &*arg.borrow() {
            Object::Int(n) => {
                result += *n as f64;
            }
            Object::Real(n) => {
                result += *n;
                return_float = true;
            }
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "'+' can only be applied to numeric objects"
                )))
            }
        }
    }

    if return_float {
        Ok(Object::Real(result))
    } else {
        Ok(Object::Int(result as i64))
    }
}

fn builtin_numeric_minus(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    let mut return_float = false;
    let mut result: f64 = 0.0;

    if args.len() < 1 {
        return Err(Errors::RuntimeException(String::from(
            "Unexpected number of arguments",
        )));
    }

    for (arg_index, arg) in args.iter().enumerate() {
        match &*arg.borrow() {
            Object::Int(n) => {
                if arg_index == 0 && args.len() != 1 {
                    result = *n as f64;
                } else {
                    result -= *n as f64;
                }
            }
            Object::Real(n) => {
                if arg_index == 0 && args.len() != 1 {
                    result = *n;
                } else {
                    result -= *n;
                }
                return_float = true;
            }
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "'-' can only be applied to numeric objects"
                )))
            }
        }
    }

    if return_float {
        Ok(Object::Real(result))
    } else {
        Ok(Object::Int(result as i64))
    }
}

fn builtin_numeric_times(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
    let args = Object::cons_to_vec(expr)?;
    let mut return_float = false;
    let mut result: f64 = 1.0;

    for arg in args.iter() {
        match &*arg.borrow() {
            Object::Int(n) => {
                result *= *n as f64;
            }
            Object::Real(n) => {
                result *= *n;
                return_float = true;
            }
            _ => {
                return Err(Errors::RuntimeException(format!(
                    "'*' can only be applied to numeric objects"
                )))
            }
        }
    }

    if return_float {
        Ok(Object::Real(result))
    } else {
        Ok(Object::Int(result as i64))
    }
}
