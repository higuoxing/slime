use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::error::Errors;
use crate::object::Object;

pub type BuiltinFuncSig = fn(Rc<RefCell<Object>>) -> Result<Object, Errors>;

pub fn make_prelude_env() -> HashMap<String, Rc<BuiltinFuncSig>> {
    let mut builtins = HashMap::new();

    builtins.insert(
        String::from("cons"),
        Rc::new(builtin_cons as BuiltinFuncSig),
    );
    builtins.insert(String::from("+"), Rc::new(builtin_plus as BuiltinFuncSig));

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

fn builtin_plus(expr: Rc<RefCell<Object>>) -> Result<Object, Errors> {
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
