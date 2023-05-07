use crate::{
    error::Errors,
    object::{LambdaFormal, Object},
    tokenizer::{Token, TokenKind, Tokenizer},
};
use pest::{iterators::Pair, Parser};
use pest_derive::Parser;
use std::{cell::RefCell, collections::LinkedList, fmt::format, rc::Rc};

#[derive(Parser)]
#[grammar = "r5rs.pest"] // relative to src
struct R5RSParser;

pub fn parse_program(prog: &str) -> Result<Object, Errors> {
    let mut exprs = vec![];
    let pairs = R5RSParser::parse(Rule::program, prog).expect("todo");

    for pair in pairs {
        match pair.as_rule() {
            Rule::expression => {
                exprs.push(build_expression(pair.into_inner().next().expect("todo")))
            }
            Rule::definition => {
                exprs.push(build_definition(pair.into_inner().next().expect("todo")))
            }
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

fn build_definition(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::definition1 => {
            let mut inner = pair.into_inner();
            let variable = inner.next().expect("todo");
            let expr = build_expression(
                inner
                    .next()
                    .expect("todo")
                    .into_inner()
                    .next()
                    .expect("todo"),
            );
            assert_eq!(variable.as_rule(), Rule::variable);
            Object::make_define(variable.as_str(), expr)
        }
        Rule::definition2 => {
            let mut inner = pair.into_inner();
            let variable = inner.next().expect("todo");
            assert_eq!(variable.as_rule(), Rule::variable);

            let def_formals = inner
                .next()
                .expect("todo")
                .into_inner()
                .next()
                .expect("todo");
            let def_formals = match def_formals.as_rule() {
                Rule::def_formals1 => todo!("{:?}", def_formals),
                Rule::def_formals2 => LambdaFormal::Fixed(
                    def_formals
                        .into_inner()
                        .into_iter()
                        .map(|variable| variable.as_str().to_string())
                        .collect(),
                ),
                unexpected => panic!(
                    "Cannot process `{:?}` rule in `definition`! Pair: {:?}",
                    unexpected, def_formals
                ),
            };

            let sequence = inner
                .next()
                .expect("todo")
                .into_inner()
                .next()
                .expect("todo");
            let mut body = Object::Nil;
            for expr in sequence.into_inner() {
                body = Object::make_cons(
                    build_expression(expr.into_inner().next().expect("todo")),
                    body,
                );
            }

            if !body.is_nil() {
                body = Object::reverse_list(body);
            }

            Object::make_define(
                variable.as_str(),
                Object::make_lambda_expression(def_formals, Object::make_begin(body)),
            )
        }
        Rule::definition3 => {
            todo!()
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `definition`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_quotation(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::datum => Object::make_quote(build_datum(pair.into_inner().next().expect("todo"))),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `quotation`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_list(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::list1 => {
            let mut tail = Object::Nil;
            for datum in pair.into_inner() {
                tail =
                    Object::make_cons(build_datum(datum.into_inner().next().expect("todo")), tail);
            }
            if !tail.is_nil() {
                tail = Object::reverse_list(tail);
            }
            tail
        }
        Rule::list2 => {
            let mut list = LinkedList::new();
            for datum in pair.into_inner() {
                list.push_back(build_datum(datum.into_inner().next().expect("todo")));
            }

            let last = list.pop_back().expect("todo");
            let mut tail = Object::Nil;
            for datum in list {
                tail = Object::make_cons(datum, tail);
            }

            Object::reverse_list_with_tail(tail, last)
        }
        Rule::abbreviation => {
            let mut prefix_datum = pair.into_inner();
            let prefix = prefix_datum.next().expect("todo");
            let datum = prefix_datum.next().expect("todo");
            match prefix.as_str() {
                "'" => Object::make_quote(build_datum(datum.into_inner().next().expect("todo"))),
                "`" => todo!("quasiquote"),
                "," => todo!("unquote"),
                ",@" => todo!("unquote-splice"),
                p => panic!("Unrecognized prefix: {}", p),
            }
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `list`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_compound_datum(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::list => build_list(pair.into_inner().next().expect("todo")),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `compound_datum`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_symbol_or_variable(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::symbol => Object::Symbol(pair.as_str().to_string()),
        Rule::variable => Object::Symbol(pair.as_str().to_string()),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `symbol`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_simple_datum(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::boolean => build_boolean(pair),
        Rule::number => build_number(pair.into_inner().next().expect("todo")),
        Rule::character => build_character(pair),
        Rule::string => build_string(pair),
        Rule::symbol => build_symbol_or_variable(pair),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `simple_datum`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_datum(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::simple_datum => build_simple_datum(pair.into_inner().next().expect("todo")),
        Rule::compound_datum => build_compound_datum(pair.into_inner().next().expect("todo")),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `datum`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_conditional(pair: Pair<Rule>) -> Object {
    let mut inner = pair.into_inner();
    let test = build_expression(
        inner
            .next()
            .expect("todo")
            .into_inner()
            .next()
            .expect("todo"),
    );
    let consequent = build_expression(
        inner
            .next()
            .expect("todo")
            .into_inner()
            .next()
            .expect("todo"),
    );
    let alternative = match inner.next() {
        None => Object::Unspecified,
        Some(alt) => build_expression(alt.into_inner().next().expect("todo")),
    };
    Object::make_conditional(test, consequent, alternative)
}

fn build_procedure_call(pair: Pair<Rule>) -> Object {
    let inner = pair.into_inner();
    let mut operator_operands = Object::Nil;

    for expr in inner {
        operator_operands = Object::make_cons(
            build_expression(
                expr.into_inner()
                    .next()
                    .expect("todo")
                    .into_inner()
                    .next()
                    .expect("todo"),
            ),
            operator_operands,
        );
    }

    Object::reverse_list(operator_operands)
}

fn build_body(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::body => {
            let mut body = Object::Nil;
            let inner = pair.into_inner();
            for definition_or_sequence in inner {
                match definition_or_sequence.as_rule() {
                    Rule::definition => {
                        body = Object::make_cons(
                            build_definition(
                                definition_or_sequence.into_inner().next().expect("todo"),
                            ),
                            body,
                        );
                    }
                    Rule::sequence => {
                        for seq in definition_or_sequence.into_inner() {
                            body = Object::make_cons(
                                build_expression(seq.into_inner().next().expect("todo")),
                                body,
                            );
                        }
                    }
                    unexpected => panic!(
                        "Cannot process `{:?}` rule in `body`! Pair: {:?}",
                        unexpected, definition_or_sequence
                    ),
                }
            }

            Object::make_begin(Object::reverse_list(body))
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `body`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_derived_expression(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::derived_begin => {
            let inner = pair.into_inner().next().expect("todo").into_inner();
            let mut sequence = Object::Nil;
            for expr in inner {
                sequence = Object::make_cons(
                    build_expression(expr.into_inner().next().expect("todo")),
                    sequence,
                );
            }
            Object::make_begin(Object::reverse_list(sequence))
        }
        Rule::derived_let1 => {
            let mut bindings = vec![];
            let inner = pair.into_inner();
            let mut body = Object::Nil;
            for binding_or_body in inner {
                match binding_or_body.as_rule() {
                    Rule::binding_spec => {
                        let mut inner = binding_or_body.into_inner();
                        let variable = inner.next().expect("todo");
                        let expression = inner.next().expect("todo");
                        bindings.push((
                            variable.as_str().to_string(),
                            Rc::new(RefCell::new(build_expression(
                                expression.into_inner().next().expect("todo"),
                            ))),
                        ));
                    }
                    Rule::body => {
                        body = build_body(binding_or_body);
                    }
                    unexpected => panic!(
                        "Cannot process `{:?}` rule in `derived_expression`! Pair: {:?}",
                        unexpected, binding_or_body
                    ),
                }
            }
            Object::make_let_expression(bindings, body)
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `derived_expression`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_lambda_expression(pair: Pair<Rule>) -> Object {
    let mut inner = pair.into_inner();
    let formals = inner
        .next()
        .expect("todo")
        .into_inner()
        .next()
        .expect("todo");

    let lambda_formals = match formals.as_rule() {
        Rule::lambda_formals1 => {
            let formals = formals.into_inner().next().expect("todo");
            assert_eq!(formals.as_rule(), Rule::variable);
            LambdaFormal::Any(formals.as_str().to_string())
        }
        Rule::lambda_formals2 => {
            let formals = formals.into_inner();
            let mut fixed = vec![];
            for expr in formals {
                fixed.push(expr.as_str().to_string());
            }
            LambdaFormal::Fixed(fixed)
        }
        Rule::lambda_formals3 => {
            let formals = formals.into_inner();
            let mut at_least_n = LinkedList::new();
            for expr in formals {
                at_least_n.push_back(expr.as_str().to_string());
            }
            let last = at_least_n.pop_back().expect("todo");
            LambdaFormal::AtLeastN(at_least_n.into_iter().collect(), last)
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `lambda_expression`! Pair: {:?}",
            unexpected, formals
        ),
    };

    let body = inner.next().expect("todo");
    Object::make_lambda_expression(lambda_formals, build_body(body))
}

fn build_expression(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::literal => build_literal(pair.into_inner().next().expect("todo")),
        Rule::conditional => build_conditional(pair),
        Rule::procedure_call => build_procedure_call(pair),
        Rule::variable => build_symbol_or_variable(pair),
        Rule::derived_expression => {
            build_derived_expression(pair.into_inner().next().expect("todo"))
        }
        Rule::lambda_expression => build_lambda_expression(pair),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `expression`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_number(pair: Pair<Rule>) -> Object {
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

fn build_boolean(pair: Pair<Rule>) -> Object {
    match pair.as_str() {
        "#t" | "#T" => Object::Bool(true),
        "#f" | "#F" => Object::Bool(false),
        _ => panic!("Cannot convert `{}` to boolean object!", pair),
    }
}

fn build_character(pair: Pair<Rule>) -> Object {
    let inner = &pair.as_str()[2..];
    match inner {
        "space" => Object::make_char(' ' as u32, 0),
        "newline" => Object::make_char('\n' as u32, 0),
        _ => Object::make_char(inner.chars().nth(0).expect("todo") as u32, 0),
    }
}

fn build_string(pair: Pair<Rule>) -> Object {
    let inner = pair.as_str();
    Object::String(inner[1..inner.len() - 1].to_string())
}

fn build_self_evaluating(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::boolean => build_boolean(pair),
        Rule::number => build_number(pair.into_inner().next().expect("todo")),
        Rule::unit => Object::Nil,
        Rule::string => build_string(pair),
        Rule::character => build_character(pair),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `self_evaluating`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_literal(pair: Pair<Rule>) -> Object {
    match pair.as_rule() {
        Rule::self_evaluating => build_self_evaluating(pair.into_inner().next().expect("todo")),
        Rule::quotation => build_quotation(pair.into_inner().next().expect("todo")),
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
    use super::{R5RSParser, Rule};
    use crate::{object::Object, parser::parse_program};
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
            parse_program("'(1 . '(2 3))").unwrap(),
            Object::make_quote(Object::make_cons(
                Object::Int(1),
                Object::make_quote(Object::make_cons(
                    Object::Int(2),
                    Object::make_cons(Object::Int(3), Object::Nil)
                ))
            ))
        );

        assert_eq!(
            parse_program("'(1 '(2 3))").unwrap(),
            Object::make_quote(Object::make_cons(
                Object::Int(1),
                Object::make_cons(
                    Object::make_quote(Object::make_cons(
                        Object::Int(2),
                        Object::make_cons(Object::Int(3), Object::Nil)
                    )),
                    Object::Nil
                )
            ))
        );

        assert_eq!(
            parse_program("'(1 -2 #t)").unwrap(),
            Object::make_quote(Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(-2),
                    Object::make_cons(Object::Bool(true), Object::Nil)
                )
            ))
        );

        assert_eq!(
            parse_program("'(#f (-2.5 3))").unwrap(),
            Object::make_quote(Object::make_cons(
                Object::Bool(false),
                Object::make_cons(
                    Object::make_cons(
                        Object::make_real(-2.5),
                        Object::make_cons(Object::make_int(3), Object::Nil)
                    ),
                    Object::Nil
                )
            ))
        );

        assert_eq!(
            parse_program("'(#f . (-2.5 . 3))").unwrap(),
            Object::make_quote(Object::make_cons(
                Object::Bool(false),
                Object::make_cons(Object::make_real(-2.5), Object::make_int(3))
            ))
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
                Object::make_define("foo", Object::Int(1)),
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
