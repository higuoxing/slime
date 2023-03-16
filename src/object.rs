use std::collections::LinkedList;

#[derive(Debug, PartialEq)]
pub enum Object {
    Nil,
    Real(f64),
    Int(i64),
    Bool(bool),
    Symbol(String),
    Cons(Box<Object>, Box<Object>),
}

impl Object {
    pub fn cons(car: Object, cdr: Object) -> Object {
        Object::Cons(Box::new(car), Box::new(cdr))
    }
}
