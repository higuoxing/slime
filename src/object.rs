use crate::error::Errors;

#[derive(Debug, PartialEq)]
pub enum Object {
    Nil,
    Real(f64),
    Int(i64),
    Bool(bool),
    // An MIT Scheme character consists of a code part and a bucky bits part.
    // See: https://groups.csail.mit.edu/mac/ftpdir/scheme-7.4/doc-html/scheme_6.html
    Char(/* code part */ u32, /* bucky bits part */ u32),
    Symbol(String),
    Cons(/* car */ Box<Object>, /* cdr */ Box<Object>),
}

impl Object {
    pub fn cons(car: Object, cdr: Object) -> Object {
        Object::Cons(Box::new(car), Box::new(cdr))
    }
}
