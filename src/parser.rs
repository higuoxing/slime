use crate::error::Errors;
use crate::object::Object;
use crate::tokenizer::{Token, TokenKind, Tokenizer};
use std::collections::LinkedList;

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
        TokenKind::Int => {
            if let Ok(n) = curr_token.literal().parse::<i64>() {
                // Advance the cursor.
                *token_cursor += 1;
                Ok(Object::Int(n))
            } else {
                Err(Errors::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ))
            }
        }
        TokenKind::Float => {
            if let Ok(f) = curr_token.literal().parse::<f64>() {
                // Advance the cursor.
                *token_cursor += 1;
                Ok(Object::Real(f))
            } else {
                Err(Errors::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ))
            }
        }
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

fn parse_object_recursive<'a>(
    tokens: &Vec<Token<'a>>,
    token_cursor: &mut usize,
) -> Result<Object, Errors> {
    let token_len = tokens.len();
    let curr_token = tokens[*token_cursor];

    match curr_token.kind() {
        TokenKind::Dot => {
            return Err(Errors::UnexpectedToken(
                curr_token.line(),
                curr_token.column(),
            ))
        }
        TokenKind::LeftParen => {
            let mut list = LinkedList::new();

            // Advance the cursor of token, eat '('.
            *token_cursor += 1;
            if *token_cursor >= token_len {
                return Err(Errors::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ));
            }

            let mut curr_token = tokens[*token_cursor];
            while *token_cursor < token_len
                && curr_token.kind() != TokenKind::RightParen
                && curr_token.kind() != TokenKind::Dot
            {
                if let Ok(object) = parse_object_recursive(tokens, token_cursor) {
                    list.push_back(object);
                } else {
                    return Err(Errors::UnexpectedToken(
                        curr_token.line(),
                        curr_token.column(),
                    ));
                }
                curr_token = tokens[*token_cursor];
            }

            if curr_token.kind() == TokenKind::Dot {
                // Advance the cursor.
                *token_cursor += 1;
                if *token_cursor >= token_len {
                    return Err(Errors::UnexpectedToken(
                        curr_token.line(),
                        curr_token.column(),
                    ));
                }

                curr_token = tokens[*token_cursor];

                if curr_token.kind() != TokenKind::RightParen {
                    match parse_object_recursive(tokens, token_cursor) {
                        Ok(object) => {
                            list.push_back(object);

                            // The cursor is incremented in parse_object_recursive(), we should
                            // check the bound and update the curr_token.
                            if *token_cursor >= token_len {
                                return Err(Errors::UnexpectedToken(
                                    curr_token.line(),
                                    curr_token.column(),
                                ));
                            }
                            curr_token = tokens[*token_cursor];
                        }
                        Err(e) => return Err(e),
                    }
                }
            }

            if curr_token.kind() != TokenKind::RightParen {
                return Err(Errors::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ));
            }

            // Advance cursor, eat ')'.
            *token_cursor += 1;

            return Ok(Object::List(list));
        }
        TokenKind::Float | TokenKind::Int => {
            return Ok(parse_number(tokens, token_cursor)?);
        }
        TokenKind::Bool => {
            return Ok(parse_bool(tokens, token_cursor)?);
        }
        TokenKind::Symbol => {
            return Ok(parse_symbol(tokens, token_cursor)?);
        }
        _ => {
            panic!("Not implemented!");
        }
    }
}

pub fn parse_program(program: &str) -> Result<Object, Errors> {
    let tokenizer = Tokenizer::new(program)?;
    let tokens = tokenizer.tokens();
    let token_len = tokens.len();
    let mut token_cursor = 0;

    while token_cursor < token_len {
        let curr_token = tokens[token_cursor];

        match curr_token.kind() {
            TokenKind::LeftParen => match parse_object_recursive(tokens, &mut token_cursor) {
                Ok(object) => {
                    return Ok(object);
                }
                Err(e) => {
                    return Err(e);
                }
            },
            _ => {
                return Err(Errors::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ));
            }
        }
    }

    panic!("Unreachable!");
}

#[cfg(test)]
mod tests {
    use crate::object::Object;
    use crate::parser::parse_program;

    #[test]
    fn test_parse_list() {
        assert_eq!(
            parse_program("(1 2 3)").unwrap(),
            Object::List(
                vec![Object::Int(1), Object::Int(2), Object::Int(3)]
                    .into_iter()
                    .collect()
            )
        );

        assert_eq!(
            parse_program("(1 (2 3))").unwrap(),
            Object::List(
                vec![
                    Object::Int(1),
                    Object::List(vec![Object::Int(2), Object::Int(3)].into_iter().collect())
                ]
                .into_iter()
                .collect()
            )
        );

        assert_eq!(
            parse_program("(1 -2 -3)").unwrap(),
            Object::List(
                vec![Object::Int(1), Object::Int(-2), Object::Int(-3)]
                    .into_iter()
                    .collect()
            )
        );

        assert_eq!(
            parse_program("(1 (-2.5 3))").unwrap(),
            Object::List(
                vec![
                    Object::Int(1),
                    Object::List(
                        vec![Object::Real(-2.5), Object::Int(3)]
                            .into_iter()
                            .collect()
                    )
                ]
                .into_iter()
                .collect()
            )
        );

        assert_eq!(
            parse_program("(1 -2 #t)").unwrap(),
            Object::List(
                vec![Object::Int(1), Object::Int(-2), Object::Bool(true)]
                    .into_iter()
                    .collect()
            )
        );

        assert_eq!(
            parse_program("(#f (-2.5 3))").unwrap(),
            Object::List(
                vec![
                    Object::Bool(false),
                    Object::List(
                        vec![Object::Real(-2.5), Object::Int(3)]
                            .into_iter()
                            .collect()
                    )
                ]
                .into_iter()
                .collect()
            )
        );

        assert_eq!(
            parse_program("(#f . (-2.5 . 3))").unwrap(),
            Object::List(
                vec![
                    Object::Bool(false),
                    Object::List(
                        vec![Object::Real(-2.5), Object::Int(3)]
                            .into_iter()
                            .collect()
                    )
                ]
                .into_iter()
                .collect()
            )
        );

        assert_eq!(
            parse_program("(+ 1 3)").unwrap(),
            Object::List(
                vec![
                    Object::Symbol(String::from("+")),
                    Object::Int(1),
                    Object::Int(3)
                ]
                .into_iter()
                .collect()
            )
        );
    }
}
