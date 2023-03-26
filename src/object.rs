use crate::builtins::BuiltinFuncSig;
use crate::error::Errors;

use std::cell::RefCell;
use std::default::Default;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum LambdaFormal {
    // Any number of arguments.
    Any(String),
    // Fix number of arguments.
    Fixed(Vec<String>),
    // At least N arguments.
    AtLeastN(Vec<String>, /* The last symbol */ String),
}

#[derive(Clone, Debug, Default, PartialEq)]
pub enum Object {
    // Default is needed for taking ownership.
    #[default]
    Unspecified,
    Nil,
    Real(f64),
    Int(i64),
    Bool(bool),
    // An MIT Scheme character consists of a code part and a bucky bits part.
    // See: https://groups.csail.mit.edu/mac/ftpdir/scheme-7.4/doc-html/scheme_6.html
    Char {
        char_code: u32,
        bucky_bits: u32,
    },
    String(String),
    Symbol(String),
    Cons {
        car: Rc<RefCell<Object>>,
        cdr: Rc<RefCell<Object>>,
    },
    Quasiquote(Rc<RefCell<Object>>),
    Unquote(Rc<RefCell<Object>>),
    UnquoteSplice(Rc<RefCell<Object>>),
    Quote(Rc<RefCell<Object>>),
    // Some special builtin symbols for parsed AST.
    Begin(Rc<RefCell<Object>>),
    If {
        condition: Rc<RefCell<Object>>,
        then: Rc<RefCell<Object>>,
        otherwise: Rc<RefCell<Object>>,
    },
    Define(String, Rc<RefCell<Object>>),
    Set(String, Rc<RefCell<Object>>),
    Lambda {
        formals: Rc<RefCell<LambdaFormal>>,
        body: Rc<RefCell<Object>>,
    },
    Let {
        bindings: Vec<(String, Rc<RefCell<Object>>)>,
        body: Rc<RefCell<Object>>,
    },
    BuiltinFunc(
        /* Function prototype */ Rc<BuiltinFuncSig>,
        /* Index */ usize,
    ),
    // Partially evaluated UnquoteSplice node.
    // This node is expanded in eval_quasiquote_expr().
    EvaluatedUnquoteSplice(Rc<RefCell<Object>>),
}

impl Object {
    pub fn make_cons(car: Object, cdr: Object) -> Object {
        Object::Cons {
            car: Rc::new(RefCell::new(car)),
            cdr: Rc::new(RefCell::new(cdr)),
        }
    }

    pub fn make_begin(object: Object) -> Object {
        Object::Begin(Rc::new(RefCell::new(object)))
    }

    pub fn make_quote(object: Object) -> Object {
        Object::Quote(Rc::new(RefCell::new(object)))
    }

    pub fn make_quasiquote(object: Object) -> Object {
        Object::Quasiquote(Rc::new(RefCell::new(object)))
    }

    pub fn make_unquote(object: Object) -> Object {
        Object::Unquote(Rc::new(RefCell::new(object)))
    }

    pub fn make_unquotesplice(object: Object) -> Object {
        Object::UnquoteSplice(Rc::new(RefCell::new(object)))
    }

    pub fn make_evaluated_unquotesplice(object: Object) -> Object {
        Object::EvaluatedUnquoteSplice(Rc::new(RefCell::new(object)))
    }

    pub fn make_char(char_code: u32, bucky_bits: u32) -> Object {
        Object::Char {
            char_code,
            bucky_bits,
        }
    }

    pub fn is_cons(&self) -> bool {
        match self {
            Object::Cons { .. } => true,
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

            while let Object::Cons { ref car, ref cdr } = &*cons.clone().borrow() {
                result.push(car.clone());
                cons = cdr.clone();
            }

            Ok(result)
        }
    }

    pub fn reverse_list_with_tail(mut list: Object, mut tail: Object) -> Object {
        while let Object::Cons { car, cdr } = list {
            tail = Object::make_cons(car.take(), tail);
            list = cdr.take();
        }
        tail
    }

    pub fn reverse_list(list: Object) -> Object {
        Self::reverse_list_with_tail(list, Object::Nil)
    }

    pub fn to_string(&self) -> String {
        match self {
            Object::Bool(b) => {
                if *b {
                    String::from("#t")
                } else {
                    String::from("#f")
                }
            }
            Object::BuiltinFunc(_, index) => {
                format!("#[builtin-procedure #{}]", index)
            }
            Object::Char {
                char_code,
                bucky_bits,
            } => {
                format!("#\\{}-{}", char_code, bucky_bits)
            }
            Object::Cons { car, cdr } => {
                let mut result_str = String::from("(");
                let mut tail = Rc::new(RefCell::new(Object::Cons {
                    car: car.clone(),
                    cdr: cdr.clone(),
                }));

                while let Object::Cons { ref car, ref cdr } = &*tail.clone().borrow() {
                    result_str += car.borrow().to_string().as_str();

                    match &*cdr.clone().borrow() {
                        Object::Cons { .. } => result_str += " ",
                        o => {
                            if !o.is_nil() {
                                result_str += format!(" . {}", o.to_string()).as_str();
                            }
                        }
                    }

                    tail = cdr.clone();
                }

                result_str += ")";
                result_str
            }
            Object::Lambda { formals, .. } => match &*formals.clone().borrow() {
                LambdaFormal::Any(ref sym) => format!("lambda ({}..)", sym.as_str()),
                LambdaFormal::Fixed(ref symbols) => {
                    let mut result_str = String::from("lambda (");

                    for (sym_index, sym) in symbols.iter().enumerate() {
                        result_str += sym.to_string().as_str();
                        if sym_index != symbols.len() - 1 {
                            result_str += " ";
                        }
                    }

                    result_str += ")";
                    result_str
                }
                LambdaFormal::AtLeastN(ref symbols, ref last_sym) => {
                    let mut result_str = String::from("lambda (");

                    for (sym_index, sym) in symbols.iter().enumerate() {
                        result_str += sym.to_string().as_str();
                        if sym_index != symbols.len() - 1 {
                            result_str += " ";
                        }
                    }

                    result_str += format!(" {}..)", last_sym).as_str();
                    result_str
                }
            },
            Object::Nil => String::from("()"),
            Object::Int(n) => format!("{}", n),
            Object::Real(n) => format!("{}", n),
            Object::String(s) => format!("\"{}\"", s),
            Object::Symbol(_) => self.symbol_name(),
            Object::Quasiquote(ref q) => format!("(quasiquote {})", q.borrow().to_string()),
            Object::Unquote(ref unq) => format!("(unquote {})", unq.borrow().to_string()),
            Object::Quote(ref q) => format!("(quote {})", q.borrow().to_string()),
            Object::UnquoteSplice(ref unqspl) => {
                format!("(unquote-splicing {})", unqspl.borrow().to_string())
            }
            _ => todo!(),
        }
    }
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_string())
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
