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
