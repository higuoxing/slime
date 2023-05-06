use std::collections::LinkedList;

use crate::error::Errors;
use crate::object::Object;
use crate::tokenizer::{Token, TokenKind, Tokenizer};
use pest::iterators::Pair;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "r5rs.pest"] // relative to src
struct R5RSParser;

pub fn parse_program(prog: &str) -> Result<Object, Errors> {
    let mut exprs = vec![];
    let pairs = R5RSParser::parse(Rule::program, prog).expect("todo");

    for pair in pairs {
        match pair.as_rule() {
            Rule::expression => exprs.push(build_ast_from_expression(
                pair.into_inner().next().expect("todo"),
            )),
            Rule::EOI => {
                // TODO?
            }
            unexpected => {
                panic!(
                    "Cannot process `{:?}` rule in top level! Pair: {:?}",
                    unexpected, pair
                )
            }
        }
    }

    // Insert a BEGIN symbol if we have multiple expressions.
    // See: 4.2.3  Sequencing
    // https://conservatory.scheme.org/schemers/Documents/Standards/R5RS/HTML/
    let result = if exprs.len() == 0 {
        Object::Nil
    } else if exprs.len() == 1 {
        exprs.into_iter().nth(0).expect("todo")
    } else {
        let mut tail = Object::Nil;
        for expr in exprs {
            tail = Object::make_cons(expr, tail);
        }
        Object::make_begin(Object::reverse_list(tail))
    };

    Ok(result)
}

fn build_ast_from_quotation(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::datum => Object::make_quote(build_ast_from_datum(
            pair.into_inner().next().expect("todo"),
        )),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `quotation`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_list(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::list1 => {
            let mut tail = Object::Nil;
            for datum in pair.into_inner() {
                tail = Object::make_cons(
                    build_ast_from_datum(datum.into_inner().next().expect("todo")),
                    tail,
                );
            }
            if !tail.is_nil() {
                tail = Object::reverse_list(tail);
            }
            tail
        }
        Rule::list2 => {
            let mut list = LinkedList::new();
            for datum in pair.into_inner() {
                list.push_back(build_ast_from_datum(
                    datum.into_inner().next().expect("todo"),
                ));
            }

            let last = list.pop_back().expect("todo");
            let mut tail = Object::Nil;
            for datum in list {
                tail = Object::make_cons(datum, tail);
            }

            Object::reverse_list_with_tail(tail, last)
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `compound_datum`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_compound_datum(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::list => build_ast_from_list(pair.into_inner().next().expect("todo")),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `compound_datum`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_symbol(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::symbol => Object::Symbol(pair.to_string()),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `symbol`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_simple_datum(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::boolean => build_ast_from_boolean(pair),
        Rule::number => build_ast_from_number(pair.into_inner().next().expect("todo")),
        Rule::character => build_ast_from_character(pair),
        Rule::string => build_ast_from_string(pair),
        Rule::symbol => build_ast_from_symbol(pair),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `simple_datum`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_datum(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::simple_datum => build_ast_from_simple_datum(pair.into_inner().next().expect("todo")),
        Rule::compound_datum => {
            build_ast_from_compound_datum(pair.into_inner().next().expect("todo"))
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `datum`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_expression(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::literal => build_ast_from_literal(pair.into_inner().next().expect("todo")),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `expression`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_number(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::num10 => {
            // FIXME: Support more numeric types!
            let num_str = pair.as_str();
            if num_str.contains(".") {
                Object::Real(num_str.parse::<f64>().expect("todo"))
            } else {
                Object::Int(num_str.parse::<i64>().expect("todo"))
            }
        }
        _ => todo!(),
    }
}

fn build_ast_from_boolean(pair: Pair<Rule>) -> Object {
    match pair.as_str() {
        "#t" | "#T" => Object::Bool(true),
        "#f" | "#F" => Object::Bool(false),
        _ => panic!("Cannot convert `{}` to boolean object!", pair),
    }
}

fn build_ast_from_character(pair: Pair<Rule>) -> Object {
    let inner = &pair.as_str()[2..];
    match inner {
        "space" => Object::make_char(' ' as u32, 0),
        "newline" => Object::make_char('\n' as u32, 0),
        _ => Object::make_char(inner.chars().nth(0).expect("todo") as u32, 0),
    }
}

fn build_ast_from_string(pair: Pair<Rule>) -> Object {
    let inner = pair.as_str();
    Object::String(inner[1..inner.len() - 1].to_string())
}

fn build_ast_from_self_evaluating(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::boolean => build_ast_from_boolean(pair),
        Rule::number => build_ast_from_number(pair.into_inner().next().expect("todo")),
        Rule::unit => Object::Nil,
        Rule::string => build_ast_from_string(pair),
        Rule::character => build_ast_from_character(pair),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `self_evaluating`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_literal(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::self_evaluating => {
            build_ast_from_self_evaluating(pair.into_inner().next().expect("todo"))
        }
        Rule::quotation => build_ast_from_quotation(pair.into_inner().next().expect("todo")),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `literal`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn parse_char_code(char_: &str, line: i64, column: i64) -> Result<u32, Errors> {
    if char_.len() == 1 {
        match char_.chars().nth(0) {
            Some(c) => Ok(c as u32),
            None => Err(Errors::UnexpectedToken(line, column)),
        }
    } else {
        // https://groups.csail.mit.edu/mac/ftpdir/scheme-7.4/doc-html/scheme_6.html
        // Character Name          ASCII Name
        // --------------          ----------
        //
        // altmode                 ESC
        // backnext                US
        // backspace               BS
        // call                    SUB
        // linefeed                LF
        // page                    FF
        // return                  CR
        // rubout                  DEL
        // space
        // tab                     HT
        match char_.to_uppercase().as_str() {
            "ALTMODE" | "ESC" => Ok(27 as u32),
            "BACKNEXT" | "US" => Ok(31 as u32),
            "BACKSPACE" | "BS" => Ok(8 as u32),
            "CALL" | "SUB" => Ok(26 as u32),
            "LINEFEED" | "LF" => Ok(10 as u32),
            "PAGE" | "FF" => Ok(12 as u32),
            "RETURN" | "CR" => Ok(13 as u32),
            "RUBOUT" | "DEL" => Ok(127 as u32),
            "SPACE" | "SPC" => Ok(32 as u32),
            "TAB" | "HT" => Ok(9 as u32),
            // FIXME: Let's add more???
            _ => Err(Errors::UnexpectedToken(line, column)),
        }
    }
}

fn parse_bucky_bits(bucky_bit: &str, line: i64, column: i64) -> Result<u32, Errors> {
    // https://groups.csail.mit.edu/mac/ftpdir/scheme-7.4/doc-html/scheme_6.html
    // Key             Bucky bit prefix        Bucky bit
    // ---             ----------------        ---------
    //
    // Meta            M- or Meta-                 1
    // Control         C- or Control-              2
    // Super           S- or Super-                4
    // Hyper           H- or Hyper-                8
    // Top             T- or Top-                 16
    match bucky_bit.to_uppercase().as_str() {
        "META" | "M" => Ok(1 as u32),
        "CONTROL" | "C" => Ok(2 as u32),
        "SUPER" | "S" => Ok(4 as u32),
        "HYPER" | "H" => Ok(8 as u32),
        "TOP" | "T" => Ok(16 as u32),
        _ => Err(Errors::UnexpectedToken(line, column)),
    }
}

#[cfg(test)]
mod tests {
    use super::R5RSParser;
    use super::Rule;
    use crate::object::Object;
    use crate::parser::parse_program;
    use pest::Parser;

    #[test]
    fn test_parse_list() {
        assert_eq!(
            parse_program("'(1 . 2)").unwrap(),
            Object::make_quote(Object::make_cons(Object::Int(1), Object::Int(2)))
        );
        assert_eq!(
            parse_program("'()").unwrap(),
            Object::make_quote(Object::Nil)
        );
        assert_eq!(
            parse_program("'(1 2 3)").unwrap(),
            Object::make_quote(Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(2),
                    Object::make_cons(Object::make_int(3), Object::Nil)
                )
            ))
        );

        assert_eq!(
            parse_program("'(1 '(2 3))").unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_cons(
                        Object::make_int(2),
                        Object::make_cons(Object::make_int(3), Object::Nil)
                    ),
                    Object::Nil
                )
            ),
        );

        assert_eq!(
            parse_program("(1 -2 -3) (+1 -2 -3)").unwrap(),
            Object::make_begin(Object::make_cons(
                Object::make_cons(
                    Object::make_int(1),
                    Object::make_cons(
                        Object::make_int(-2),
                        Object::make_cons(Object::make_int(-3), Object::Nil)
                    )
                ),
                Object::make_cons(
                    Object::make_cons(
                        Object::make_int(1),
                        Object::make_cons(
                            Object::make_int(-2),
                            Object::make_cons(Object::make_int(-3), Object::Nil)
                        )
                    ),
                    Object::Nil
                )
            ))
        );

        assert_eq!(
            parse_program("(1 (-2.5 3))").unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_cons(
                        Object::make_real(-2.5),
                        Object::make_cons(Object::make_int(3), Object::Nil)
                    ),
                    Object::Nil
                )
            )
        );

        assert_eq!(
            parse_program("(1 -2 #t)").unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(-2),
                    Object::make_cons(Object::Bool(true), Object::Nil)
                )
            )
        );

        assert_eq!(
            parse_program("(#f (-2.5 3))").unwrap(),
            Object::make_cons(
                Object::Bool(false),
                Object::make_cons(
                    Object::make_cons(
                        Object::make_real(-2.5),
                        Object::make_cons(Object::make_int(3), Object::Nil)
                    ),
                    Object::Nil
                )
            )
        );

        assert_eq!(
            parse_program("(#f . (-2.5 . 3))").unwrap(),
            Object::make_cons(
                Object::Bool(false),
                Object::make_cons(Object::make_real(-2.5), Object::make_int(3))
            )
        );

        assert_eq!(
            parse_program("(+ 1 3)").unwrap(),
            Object::make_cons(
                Object::Symbol(String::from("+")),
                Object::make_cons(
                    Object::make_int(1),
                    Object::make_cons(Object::make_int(3), Object::Nil)
                )
            )
        );

        assert_eq!(parse_program("()").unwrap(), Object::Nil);

        assert_eq!(
            parse_program(
                "(#\\a #\\b #\\c  #\\space #\\c-a #\\control-a #\\meta-b #\\0 #\\9 #\\liNeFeed)"
            )
            .unwrap(),
            Object::make_cons(
                Object::make_char(97, 0),
                Object::make_cons(
                    Object::make_char(98, 0),
                    Object::make_cons(
                        Object::make_char(99, 0),
                        Object::make_cons(
                            Object::make_char(32, 0),
                            Object::make_cons(
                                Object::make_char(97, 2),
                                Object::make_cons(
                                    Object::make_char(97, 2),
                                    Object::make_cons(
                                        Object::make_char(98, 1),
                                        Object::make_cons(
                                            Object::make_char(48, 0),
                                            Object::make_cons(
                                                Object::make_char(57, 0),
                                                Object::make_cons(
                                                    Object::make_char(10, 0),
                                                    Object::Nil
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        );

        assert_eq!(
            parse_program("()()").unwrap(),
            Object::make_begin(Object::make_cons(
                Object::Nil,
                Object::make_cons(Object::Nil, Object::Nil)
            ))
        );

        assert_eq!(parse_program("1").unwrap(), Object::make_int(1));
        assert_eq!(
            parse_program("(define foo 1) foo").unwrap(),
            Object::make_begin(Object::make_cons(
                Object::make_cons(
                    Object::Symbol(String::from("define")),
                    Object::make_cons(
                        Object::Symbol(String::from("foo")),
                        Object::make_cons(Object::make_int(1), Object::Nil)
                    )
                ),
                Object::make_cons(Object::Symbol(String::from("foo")), Object::Nil)
            ))
        );

        assert_eq!(
            parse_program("'(define foo 1)").unwrap(),
            Object::make_quote(Object::make_cons(
                Object::Symbol(String::from("define")),
                Object::make_cons(
                    Object::Symbol(String::from("foo")),
                    Object::make_cons(Object::make_int(1), Object::Nil)
                )
            ),)
        );
    }

    fn test_parse_atomic(rule: Rule, raw_identifier: &str, expected: &str) {
        assert_eq!(
            R5RSParser::parse(rule, raw_identifier)
                .unwrap()
                .next()
                .unwrap()
                .as_str(),
            expected
        );
    }

    fn test_parse_variable(raw_identifier: &str, expect_fail: bool) {
        if !expect_fail {
            assert_eq!(
                R5RSParser::parse(Rule::variable, raw_identifier)
                    .unwrap()
                    .next()
                    .unwrap()
                    .as_str(),
                raw_identifier
            );
        } else {
            assert!(R5RSParser::parse(Rule::variable, raw_identifier).is_err());
        }
    }

    fn test_parse_expression(rule: Rule, raw_expression: &str) {
        assert_eq!(
            R5RSParser::parse(Rule::expression, raw_expression)
                .unwrap()
                .next()
                .unwrap()
                .into_inner()
                .next()
                .unwrap()
                .as_rule(),
            rule
        );
    }

    #[test]
    fn test_pest_parser() {
        assert!(R5RSParser::parse(Rule::COMMENT, ";abc\n").is_ok());
        assert!(R5RSParser::parse(Rule::COMMENT, ";abc").is_ok());
        // Identifiers.
        test_parse_atomic(Rule::identifier, "foo", "foo");
        test_parse_atomic(Rule::identifier, "symbol->string\n", "symbol->string");
        test_parse_atomic(Rule::identifier, "let*   ", "let*");
        test_parse_atomic(Rule::identifier, "...", "...");
        test_parse_atomic(Rule::identifier, "+\n", "+");
        test_parse_atomic(Rule::identifier, "*\r", "*");

        // Variables.
        test_parse_variable("foo", /* expect_fail */ false);
        test_parse_variable("let*", /* expect_fail */ true);

        // Boolean.
        test_parse_atomic(Rule::boolean, "#f", "#f");
        test_parse_atomic(Rule::boolean, "#t  ", "#t");

        // Char.
        test_parse_atomic(Rule::character, "#\\a", "#\\a");
        test_parse_atomic(Rule::character, "#\\ ", "#\\ ");
        test_parse_atomic(Rule::character, "#\\space", "#\\space");

        // String.
        test_parse_atomic(Rule::string, r#""abc""#, r#""abc""#);
        test_parse_atomic(Rule::string, r#""abc\"""#, r#""abc\"""#);
        test_parse_atomic(Rule::string, r#""abc  \"\\""#, r#""abc  \"\\""#);

        // Number
        // Radix 2.
        test_parse_atomic(Rule::number, r#"#b01"#, r#"#b01"#);
        test_parse_atomic(Rule::number, r#"#b#i01"#, r#"#b#i01"#);
        test_parse_atomic(Rule::number, r#"#i#b01"#, r#"#i#b01"#);
        test_parse_atomic(Rule::number, r#"#i#b01+i"#, r#"#i#b01+i"#);
        test_parse_atomic(Rule::number, r#"#i#b01-1i"#, r#"#i#b01-1i"#);
        test_parse_atomic(Rule::number, r#"#b0/1"#, r#"#b0/1"#);
        // Radix 8.
        test_parse_atomic(Rule::number, r#"#o1"#, r#"#o1"#);
        test_parse_atomic(Rule::number, r#"#o1+2i"#, r#"#o1+2i"#);
        test_parse_atomic(Rule::number, r#"#o-1+2i"#, r#"#o-1+2i"#);
        test_parse_atomic(Rule::number, r#"#o-1-2i"#, r#"#o-1-2i"#);
        test_parse_atomic(Rule::number, r#"#o1/5"#, r#"#o1/5"#);
        // Radix 10.
        test_parse_atomic(Rule::number, r#"1"#, r#"1"#);
        test_parse_atomic(Rule::number, r#"1+2i"#, r#"1+2i"#);
        test_parse_atomic(Rule::number, r#"-1+2i"#, r#"-1+2i"#);
        test_parse_atomic(Rule::number, r#"-1-2i"#, r#"-1-2i"#);
        test_parse_atomic(Rule::number, r#"#d1/5"#, r#"#d1/5"#);
        // Radix 16.
        test_parse_atomic(Rule::number, r#"#x1"#, r#"#x1"#);
        test_parse_atomic(Rule::number, r#"#x1+ai"#, r#"#x1+ai"#);
        test_parse_atomic(Rule::number, r#"#x-a+2i"#, r#"#x-a+2i"#);
        test_parse_atomic(Rule::number, r#"#x-1-2i"#, r#"#x-1-2i"#);
        test_parse_atomic(Rule::number, r#"#xe/5"#, r#"#xe/5"#);

        // Expression.
        test_parse_expression(Rule::variable, "foo");
        test_parse_expression(Rule::literal, "1+2i");
        test_parse_expression(Rule::literal, "#t");
        test_parse_expression(Rule::literal, "#\\a");
        test_parse_expression(Rule::literal, r#""I like you.""#);
        test_parse_expression(Rule::literal, r#"'#(1 2 3)"#);
        test_parse_expression(Rule::literal, r#"'(1 2 3)"#);
        test_parse_expression(Rule::literal, r#"(quote #(1 2 3))"#);
        test_parse_expression(Rule::literal, r#"(quote ,(1 2 3))"#);
        test_parse_expression(Rule::procedure_call, r#"(dummy 1 2 3)"#);
        test_parse_expression(Rule::procedure_call, r#"(+ 1 2 3)"#);
        test_parse_expression(Rule::procedure_call, r#"(* 1 2 3)"#);
        test_parse_expression(Rule::procedure_call, r#"(bar 1 2 3)"#);
        test_parse_expression(Rule::procedure_call, r#"(+ x 1)"#);
        test_parse_expression(Rule::lambda_expression, r#"(lambda () 1)"#);
        test_parse_expression(Rule::lambda_expression, r#"(lambda (x) 1)"#);
        test_parse_expression(Rule::lambda_expression, r#"(lambda (x y z) 1)"#);
        test_parse_expression(Rule::lambda_expression, r#"(lambda (x y . z) 1)"#);
        test_parse_expression(Rule::lambda_expression, r#"(lambda (x y . z) (+ x y z))"#);
        test_parse_expression(
            Rule::lambda_expression,
            r#"(lambda (x y . z) (define x 1) (+ x y))"#,
        );
        test_parse_expression(
            Rule::lambda_expression,
            r#"(lambda (x y . z) (define (x) (+ x 1)) (+ x y))"#,
        );
        test_parse_expression(
            Rule::lambda_expression,
            r#"(lambda (x y . z) (begin (define x 1) (define y 2)) (+ x y))"#,
        );
        test_parse_expression(Rule::conditional, r#"(if #t 1)"#);
        test_parse_expression(Rule::conditional, r#"(if #t 1 2)"#);
        test_parse_expression(Rule::assignment, r#"(set! a 1)"#);

        assert_eq!(
            R5RSParser::parse(Rule::program, r#"(+ 1 2)"#)
                .unwrap()
                .next()
                .unwrap()
                .into_inner()
                .next()
                .unwrap()
                .as_rule(),
            Rule::procedure_call
        );

        assert_eq!(
            R5RSParser::parse(Rule::program, r#"(define x     1)"#)
                .unwrap()
                .next()
                .unwrap()
                .into_inner()
                .next()
                .unwrap()
                .as_rule(),
            Rule::definition1
        );

        // Parse program.
        assert_eq!(parse_program("#t").unwrap(), Object::Bool(true));
        assert_eq!(parse_program(" #f").unwrap(), Object::Bool(false));
        assert_eq!(
            parse_program(" 123456789  ").unwrap(),
            Object::Int(123456789)
        );

        assert_eq!(
            parse_program(" 123456789.12345  ").unwrap(),
            Object::Real(123456789.12345)
        );
        assert_eq!(parse_program("  (  )").unwrap(), Object::Nil);
        assert_eq!(
            parse_program(r#" "hello, world! \\  \" " "#).unwrap(),
            Object::String(String::from(r#"hello, world! \\  \" "#)),
        );
        assert_eq!(
            parse_program(r#" #\a "#).unwrap(),
            Object::make_char('a' as u32, 0)
        );
        assert_eq!(
            parse_program(r#" #\newline "#).unwrap(),
            Object::make_char('\n' as u32, 0),
        );
        assert_eq!(
            parse_program(r#" #\space "#).unwrap(),
            Object::make_char(' ' as u32, 0),
        );
        assert_eq!(
            parse_program(r#" a "#).unwrap(),
            Object::Symbol(String::from("a")),
        );
        assert_eq!(
            parse_program(
                r#"
;; comments
  ;; comments2

bbb
"#
            )
            .unwrap(),
            Object::Symbol(String::from("bbb")),
        );
    }
}
