use crate::error::Errors;

use std::cell::RefCell;
use std::default::Default;
use std::rc::Rc;

#[derive(Clone, Debug, Default, PartialEq)]
pub enum Object {
    // Default is needed for taking ownership.
    #[default]
    Nil,
    Real(f64),
    Int(i64),
    Bool(bool),
    // An MIT Scheme character consists of a code part and a bucky bits part.
    // See: https://groups.csail.mit.edu/mac/ftpdir/scheme-7.4/doc-html/scheme_6.html
    Char(/* code part */ u32, /* bucky bits part */ u32),
    String(String),
    Symbol(String),
    Cons(
        /* car */ Rc<RefCell<Object>>,
        /* cdr */ Rc<RefCell<Object>>,
    ),
    // Some special builtin symbols for parsed AST.
    Begin(Rc<RefCell<Object>>),
    If(
        /* condition */ Rc<RefCell<Object>>,
        /* then */ Rc<RefCell<Object>>,
        /* else */ Rc<RefCell<Object>>,
    ),
    Define(String, Rc<RefCell<Object>>),
    Lambda(
        /* arguments */ Vec<String>,
        /* lambda body */ Rc<RefCell<Object>>,
    ),
}

impl Object {
    pub fn make_cons(car: Object, cdr: Object) -> Object {
        Object::Cons(Rc::new(RefCell::new(car)), Rc::new(RefCell::new(cdr)))
    }

    pub fn make_begin(object: Object) -> Object {
        Object::Begin(Rc::new(RefCell::new(object)))
    }

    pub fn is_cons(&self) -> bool {
        match self {
            Object::Cons(_, _) => true,
            _ => false,
        }
    }

    pub fn is_nil(&self) -> bool {
        match self {
            Object::Nil => true,
            _ => false,
        }
    }

    pub fn is_symbol(&self) -> bool {
        match self {
            Object::Symbol(_) => true,
            _ => false,
        }
    }

    pub fn symbol_name(&self) -> String {
        match self {
            Object::Symbol(sym) => sym.clone(),
            _ => format!(""),
        }
    }

    pub fn cons_to_vec(mut cons: Rc<RefCell<Object>>) -> Result<Vec<Rc<RefCell<Object>>>, Errors> {
        if !cons.borrow().is_cons() && !cons.borrow().is_nil() {
            Err(Errors::RuntimeException(format!(
                "Canont expand a non-Cons object to linked list."
            )))
        } else {
            let mut result = vec![];

            while let Object::Cons(ref car, ref cdr) = *cons.clone().borrow() {
                result.push(car.clone());
                cons = cdr.clone();
            }

            Ok(result)
        }
    }

    pub fn reverse_list_with_tail(mut list: Object, mut tail: Object) -> Object {
        while let Object::Cons(car, cdr) = list {
            tail = Object::make_cons(car.take(), tail);
            list = cdr.take();
        }
        tail
    }

    pub fn reverse_list(list: Object) -> Object {
        Self::reverse_list_with_tail(list, Object::Nil)
    }
}

#[cfg(test)]
mod tests {
    use crate::object::Object;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn test_cons_to_vec() {
        assert_eq!(
            Object::cons_to_vec(Rc::new(RefCell::new(Object::make_cons(
                Object::Int(1),
                Object::Nil
            ))))
            .unwrap(),
            vec![Rc::new(RefCell::new(Object::Int(1)))]
        )
    }
}
