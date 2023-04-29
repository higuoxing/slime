use crate::error::Errors;
use crate::object::Object;
use crate::tokenizer::{Token, TokenKind, Tokenizer};
use pest::iterators::Pair;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "r5rs.pest"] // relative to src
struct R5RSParser;

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    Nil,
    Boolean(bool),
    Integer(i64),
    Real(f64),
    String(String),
    Char(char),
    Variable(String),
}

pub fn parse(prog: &str) -> Vec<AstNode> {
    let mut ast = vec![];
    let pairs = R5RSParser::parse(Rule::program, prog).expect("todo");
    for pair in pairs {
        match pair.as_rule() {
            Rule::expression => {
                ast.push(build_ast_from_expr(pair.into_inner().next().expect("todo")));
            }
            unexpected => panic!(
                "Cannot process `{:?}` rule in top level! Pair: {:?}",
                unexpected, pair
            ),
        }
    }

    ast
}

fn build_ast_from_expr(pair: Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::literal => build_ast_from_literal(pair.into_inner().next().expect("todo")),
        Rule::variable => AstNode::Variable(pair.as_str().to_string()),
        unexpected => panic!(
            "Cannot process `{:?}` rule in `expression`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_literal(pair: Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::boolean => match pair.as_str() {
            "#t" | "#T" => AstNode::Boolean(true),
            "#f" | "#F" => AstNode::Boolean(false),
            _ => panic!("Cannot convert `{}` to boolean object!", pair),
        },
        Rule::number => build_ast_from_number(pair.into_inner().next().expect("todo")),
        Rule::unit => AstNode::Nil,
        Rule::string => {
            let inner = pair.as_str();
            AstNode::String(inner[1..inner.len() - 1].to_string())
        }
        Rule::character => {
            let inner = &pair.as_str()[2..];
            match inner {
                "space" => AstNode::Char(' '),
                "newline" => AstNode::Char('\n'),
                _ => AstNode::Char(inner.chars().nth(0).expect("todo")),
            }
        }
        unexpected => panic!(
            "Cannot process `{:?}` rule in `literal`! Pair: {:?}",
            unexpected, pair
        ),
    }
}

fn build_ast_from_number(pair: Pair<Rule>) -> AstNode {
    match pair.as_rule() {
        Rule::num10 => {
            // FIXME: Support more numeric types!
            let num_str = pair.as_str();
            if num_str.contains(".") {
                AstNode::Real(num_str.parse::<f64>().expect("todo"))
            } else {
                AstNode::Integer(num_str.parse::<i64>().expect("todo"))
            }
        }
        _ => todo!(),
    }
}

// See https://groups.csail.mit.edu/mac/ftpdir/scheme-reports/r5rs-html/r5rs_9.html
// for syntax and semantics of MIT Scheme.

fn parse_bool<'a>(tokens: &Vec<Token<'a>>, token_cursor: &mut usize) -> Result<Object, Errors> {
    let curr_token = tokens[*token_cursor];
    match curr_token.kind() {
        TokenKind::Bool => {
            // Advance the token cursor.
            *token_cursor += 1;
            if curr_token.literal() == "#t" {
                Ok(Object::Bool(true))
            } else if curr_token.literal() == "#f" {
                Ok(Object::Bool(false))
            } else {
                // Unlikely to happend.
                panic!("Cannot parse boolean value, expected '#t' or '#f'");
            }
        }
        _ => Err(Errors::UnexpectedToken(
            curr_token.line(),
            curr_token.column(),
        )),
    }
}

fn parse_number<'a>(tokens: &Vec<Token<'a>>, token_cursor: &mut usize) -> Result<Object, Errors> {
    let curr_token = tokens[*token_cursor];
    match curr_token.kind() {
        TokenKind::Int => match curr_token.literal().parse::<i64>() {
            Ok(n) => {
                *token_cursor += 1;
                Ok(Object::Int(n))
            }
            Err(_) => Err(Errors::UnexpectedToken(
                curr_token.line(),
                curr_token.column(),
            )),
        },
        TokenKind::Float => match curr_token.literal().parse::<f64>() {
            Ok(f) => {
                *token_cursor += 1;
                Ok(Object::Real(f))
            }
            Err(_) => Err(Errors::UnexpectedToken(
                curr_token.line(),
                curr_token.column(),
            )),
        },
        _ => Err(Errors::UnexpectedToken(
            curr_token.line(),
            curr_token.column(),
        )),
    }
}

fn parse_symbol<'a>(tokens: &Vec<Token<'a>>, token_cursor: &mut usize) -> Result<Object, Errors> {
    let curr_token = tokens[*token_cursor];
    match curr_token.kind() {
        TokenKind::Symbol => {
            let symbol = Object::Symbol(curr_token.literal().to_string());
            *token_cursor += 1;
            Ok(symbol)
        }
        _ => Err(Errors::UnexpectedToken(
            curr_token.line(),
            curr_token.column(),
        )),
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

fn parse_char<'a>(tokens: &Vec<Token<'a>>, token_cursor: &mut usize) -> Result<Object, Errors> {
    let curr_token = tokens[*token_cursor];
    match curr_token.kind() {
        TokenKind::Char => {
            // This may not be necessary, but we check it anyway.
            if curr_token.literal().len() <= 2 {
                return Err(Errors::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ));
            }

            // Remove the '#\' part.
            let char_part = &curr_token.literal()[2..];
            // Split it by '-'
            let char_tokens: Vec<_> = char_part.split("-").collect();
            let mut bucky_bits = 0;
            let mut char_code = 0;

            for (tok_idx, tok) in char_tokens.iter().enumerate() {
                if tok_idx != char_tokens.len() - 1 {
                    bucky_bits |= parse_bucky_bits(tok, curr_token.line(), curr_token.column())?;
                } else {
                    char_code = parse_char_code(tok, curr_token.line(), curr_token.column())?;
                }
            }

            *token_cursor += 1;
            return Ok(Object::make_char(char_code, bucky_bits));
        }
        _ => Err(Errors::UnexpectedToken(
            curr_token.line(),
            curr_token.column(),
        )),
    }
}

fn parse_string<'a>(tokens: &Vec<Token<'a>>, token_cursor: &mut usize) -> Result<Object, Errors> {
    let curr_token = tokens[*token_cursor];
    match curr_token.kind() {
        TokenKind::String => {
            *token_cursor += 1;
            let strlen = curr_token.literal().len();
            return Ok(Object::String(
                curr_token.literal()[1..strlen - 1].to_string(),
            ));
        }
        _ => Err(Errors::UnexpectedToken(
            curr_token.line(),
            curr_token.column(),
        )),
    }
}

fn parse_object_recursive<'a>(
    tokens: &Vec<Token<'a>>,
    token_cursor: &mut usize,
) -> Result<Object, Errors> {
    let token_len = tokens.len();

    if *token_cursor >= token_len {
        return Err(Errors::ExpectMoreToken);
    }

    let curr_token = tokens[*token_cursor];
    match curr_token.kind() {
        TokenKind::Dot => Err(Errors::UnexpectedToken(
            curr_token.line(),
            curr_token.column(),
        )),
        TokenKind::LeftParen => {
            let mut tail = Object::Nil;

            // Advance the cursor of token, eat '('.
            *token_cursor += 1;
            if *token_cursor >= token_len {
                return Err(Errors::ExpectMoreToken);
            }

            let mut curr_token = tokens[*token_cursor];
            while *token_cursor < token_len
                && curr_token.kind() != TokenKind::RightParen
                && curr_token.kind() != TokenKind::Dot
            {
                if let Ok(object) = parse_object_recursive(tokens, token_cursor) {
                    tail = Object::make_cons(object, tail);
                } else {
                    return Err(Errors::UnexpectedToken(
                        curr_token.line(),
                        curr_token.column(),
                    ));
                }

                if *token_cursor < token_len {
                    curr_token = tokens[*token_cursor];
                } else {
                    return Err(Errors::ExpectMoreToken);
                }
            }

            if curr_token.kind() == TokenKind::Dot {
                // Advance the cursor.
                *token_cursor += 1;
                if *token_cursor >= token_len {
                    return Err(Errors::ExpectMoreToken);
                }

                curr_token = tokens[*token_cursor];

                if curr_token.kind() != TokenKind::RightParen {
                    match parse_object_recursive(tokens, token_cursor) {
                        Ok(object) => {
                            tail = Object::reverse_list_with_tail(tail, object);

                            // The cursor is incremented in parse_object_recursive(), we should
                            // check the bound and update the curr_token.
                            if *token_cursor >= token_len {
                                return Err(Errors::ExpectMoreToken);
                            }
                            curr_token = tokens[*token_cursor];
                        }
                        Err(e) => return Err(e),
                    }
                }
            } else {
                tail = Object::reverse_list(tail);
            }

            if curr_token.kind() != TokenKind::RightParen {
                return Err(Errors::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ));
            }

            // Advance cursor, eat ')'.
            *token_cursor += 1;

            Ok(tail)
        }
        TokenKind::Float | TokenKind::Int => Ok(parse_number(tokens, token_cursor)?),
        TokenKind::Bool => Ok(parse_bool(tokens, token_cursor)?),
        TokenKind::Symbol => Ok(parse_symbol(tokens, token_cursor)?),
        TokenKind::Char => Ok(parse_char(tokens, token_cursor)?),
        TokenKind::String => Ok(parse_string(tokens, token_cursor)?),
        TokenKind::Quote => {
            *token_cursor += 1;
            Ok(Object::make_quote(parse_object_recursive(
                tokens,
                token_cursor,
            )?))
        }
        TokenKind::BackQuote => {
            *token_cursor += 1;
            Ok(Object::make_quasiquote(parse_object_recursive(
                tokens,
                token_cursor,
            )?))
        }
        TokenKind::Comma => {
            *token_cursor += 1;

            // Look one more token ahead.
            if *token_cursor >= token_len {
                return Err(Errors::ExpectMoreToken);
            }

            let curr_token = tokens[*token_cursor];
            match curr_token.kind() {
                TokenKind::At => {
                    *token_cursor += 1;
                    Ok(Object::make_unquotesplice(parse_object_recursive(
                        tokens,
                        token_cursor,
                    )?))
                }
                _ => Ok(Object::make_unquote(parse_object_recursive(
                    tokens,
                    token_cursor,
                )?)),
            }
        }
        _ => Err(Errors::UnexpectedToken(
            curr_token.line(),
            curr_token.column(),
        )),
    }
}

pub fn parse_program(program: &str) -> Result<Object, Errors> {
    let tokenizer = Tokenizer::new(program)?;
    let tokens = tokenizer.tokens();
    let token_len = tokens.len();
    let mut token_cursor = 0;
    let mut result = parse_object_recursive(tokens, &mut token_cursor)?;

    if token_cursor < token_len {
        result = Object::make_cons(result, Object::Nil);

        while token_cursor < token_len {
            match parse_object_recursive(tokens, &mut token_cursor) {
                Ok(object) => {
                    result = Object::make_cons(object, result);
                }
                Err(e) => {
                    return Err(e);
                }
            }
        }

        // Insert a BEGIN symbol if we have multiple expressions.
        // See: 4.2.3  Sequencing
        // https://conservatory.scheme.org/schemers/Documents/Standards/R5RS/HTML/
        result = Object::make_begin(Object::reverse_list(result));
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::R5RSParser;
    use super::Rule;
    use crate::object::Object;
    use crate::parser::parse;
    use crate::parser::parse_program;
    use crate::parser::AstNode;
    use pest::Parser;

    #[test]
    fn test_parse_list() {
        assert_eq!(
            parse_program("(1 2 3)").unwrap(),
            Object::make_cons(
                Object::make_int(1),
                Object::make_cons(
                    Object::make_int(2),
                    Object::make_cons(Object::make_int(3), Object::Nil)
                )
            )
        );

        assert_eq!(
            parse_program("(1 (2 3))").unwrap(),
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
        assert_eq!(parse("#t"), vec![AstNode::Boolean(true)]);
        assert_eq!(parse(" #f"), vec![AstNode::Boolean(false)]);
        assert_eq!(parse(" 123456789  "), vec![AstNode::Integer(123456789)]);

        assert_eq!(
            parse(" 123456789.12345  "),
            vec![AstNode::Real(123456789.12345)]
        );
        assert_eq!(parse("  (  )"), vec![AstNode::Nil]);
        assert_eq!(
            parse(r#" "hello, world! \\  \" " "#),
            vec![AstNode::String(String::from(r#"hello, world! \\  \" "#))]
        );
        assert_eq!(parse(r#" #\a "#), vec![AstNode::Char('a')]);
        assert_eq!(parse(r#" #\newline "#), vec![AstNode::Char('\n')]);
        assert_eq!(parse(r#" #\space "#), vec![AstNode::Char(' ')]);
        assert_eq!(parse(r#" a "#), vec![AstNode::Variable(String::from("a"))]);
    }
}
