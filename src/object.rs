use std::cell::RefCell;
use std::default::Default;
use std::rc::Rc;

#[derive(Debug, Default, PartialEq)]
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
    Symbol(String),
    Cons(
        /* car */ Rc<RefCell<Object>>,
        /* cdr */ Rc<RefCell<Object>>,
    ),
    // Some special symbols for parsed AST.
    Begin(Rc<RefCell<Object>>),
}

impl Object {
    pub fn cons(car: Object, cdr: Object) -> Object {
        Object::Cons(Rc::new(RefCell::new(car)), Rc::new(RefCell::new(cdr)))
    }

    pub fn begin(object: Object) -> Object {
        Object::Begin(Rc::new(RefCell::new(object)))
    }

    pub fn is_cons(&self) -> bool {
        match self {
            Object::Cons(_, _) => true,
            _ => false,
        }
    }
}
