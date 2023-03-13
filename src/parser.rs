use crate::tokenizer::{TokenKind, Tokenizer};

use std::collections::LinkedList;

use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum ParseError {
    #[error("Unexpected token at {0}:{1}")]
    UnexpectedToken(i64, i64),
    #[error("Unknown error")]
    Unknown,
}

#[derive(Debug, PartialEq)]
enum Object {
    Nil,
    Real(f64),
    Int(i64),
    Bool(bool),
    List(LinkedList<Object>),
}

#[derive(Debug)]
struct Parser<'a> {
    tokenizer: Tokenizer<'a>,
}

impl<'a> Parser<'a> {
    fn new(program: &'a str) -> Result<Self, ParseError> {
        Ok(Self {
            tokenizer: Tokenizer::new(program)?,
        })
    }

    fn parse_bool(&self, token_cursor: &mut usize) -> Result<Object, ParseError> {
        let curr_token = self.tokenizer.tokens()[*token_cursor];
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
            _ => Err(ParseError::UnexpectedToken(
                curr_token.line(),
                curr_token.column(),
            )),
        }
    }

    fn parse_number(&self, token_cursor: &mut usize) -> Result<Object, ParseError> {
        let curr_token = self.tokenizer.tokens()[*token_cursor];
        match curr_token.kind() {
            TokenKind::Int => {
                if let Ok(n) = curr_token.literal().parse::<i64>() {
                    // Advance the cursor.
                    *token_cursor += 1;
                    Ok(Object::Int(n))
                } else {
                    Err(ParseError::UnexpectedToken(
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
                    Err(ParseError::UnexpectedToken(
                        curr_token.line(),
                        curr_token.column(),
                    ))
                }
            }
            _ => Err(ParseError::UnexpectedToken(
                curr_token.line(),
                curr_token.column(),
            )),
        }
    }

    fn parse_object_recursive(&self, token_cursor: &mut usize) -> Result<Object, ParseError> {
        let token_len = self.tokenizer.tokens().len();
        let curr_token = self.tokenizer.tokens()[*token_cursor];

        match curr_token.kind() {
            TokenKind::Dot => {
                return Err(ParseError::UnexpectedToken(
                    curr_token.line(),
                    curr_token.column(),
                ))
            }
            TokenKind::LeftParen => {
                let mut list = LinkedList::new();

                // Advance the cursor of token, eat '('.
                *token_cursor += 1;
                if *token_cursor >= token_len {
                    return Err(ParseError::UnexpectedToken(
                        curr_token.line(),
                        curr_token.column(),
                    ));
                }

                let mut curr_token = self.tokenizer.tokens()[*token_cursor];
                while *token_cursor < token_len
                    && curr_token.kind() != TokenKind::RightParen
                    && curr_token.kind() != TokenKind::Dot
                {
                    if let Ok(object) = self.parse_object_recursive(token_cursor) {
                        list.push_back(object);
                    } else {
                        return Err(ParseError::UnexpectedToken(
                            curr_token.line(),
                            curr_token.column(),
                        ));
                    }
                    curr_token = self.tokenizer.tokens()[*token_cursor];
                }

                // TODO:
                // if curr_token.kind() == TokenKind::Dot {
                //     // Advance the cursor.
                //     *token_cursor += 1;
                //     if *token_cursor >= token_len {
                //         return Err(ParseError::UnexpectedToken(
                //             curr_token.line(),
                //             curr_token.column(),
                //         ));
                //     }
                //     curr_token = self.tokenizer.tokens()[*token_cursor];
                //
                //     if curr_token.kind() != TokenKind::RightParen {
                //         if let Ok(object) = self.parse_list(token_cursor) {
                //             list.push_back(object);
                //         } else {
                //             return Err(ParseError::UnexpectedToken(
                //                 curr_token.line(),
                //                 curr_token.column(),
                //             ));
                //         }
                //     }
                // }

                if curr_token.kind() != TokenKind::RightParen {
                    return Err(ParseError::UnexpectedToken(
                        curr_token.line(),
                        curr_token.column(),
                    ));
                }

                // Advance cursor, eat ')'.
                *token_cursor += 1;

                return Ok(Object::List(list));
            }
            TokenKind::Float | TokenKind::Int => {
                return Ok(self.parse_number(token_cursor)?);
            }
            TokenKind::Bool => {
                return Ok(self.parse_bool(token_cursor)?);
            }
            _ => {
                panic!("Not implemented!");
            }
        }
    }

    fn parse(&self) -> Result<Object, ParseError> {
        let token_len = self.tokenizer.tokens().len();
        let mut token_cursor = 0;

        while token_cursor < token_len {
            let curr_token = self.tokenizer.tokens()[token_cursor];

            match curr_token.kind() {
                TokenKind::LeftParen => match self.parse_object_recursive(&mut token_cursor) {
                    Ok(object) => {
                        return Ok(object);
                    }
                    Err(e) => {
                        return Err(e);
                    }
                },
                _ => {
                    return Err(ParseError::UnexpectedToken(
                        curr_token.line(),
                        curr_token.column(),
                    ));
                }
            }
        }

        panic!("Unreachable!");
    }
}

#[cfg(test)]
mod tests {
    use super::{Object, Parser};

    #[test]
    fn test_parse_list() {
        let parser = Parser::new("(1 2 3)").unwrap();
        assert_eq!(
            parser.parse().unwrap(),
            Object::List(
                vec![Object::Int(1), Object::Int(2), Object::Int(3)]
                    .into_iter()
                    .collect()
            )
        );

        let parser = Parser::new("(1 (2 3))").unwrap();
        assert_eq!(
            parser.parse().unwrap(),
            Object::List(
                vec![
                    Object::Int(1),
                    Object::List(vec![Object::Int(2), Object::Int(3)].into_iter().collect())
                ]
                .into_iter()
                .collect()
            )
        );

        let parser = Parser::new("(1 -2 -3)").unwrap();
        assert_eq!(
            parser.parse().unwrap(),
            Object::List(
                vec![Object::Int(1), Object::Int(-2), Object::Int(-3)]
                    .into_iter()
                    .collect()
            )
        );

        let parser = Parser::new("(1 (-2.5 3))").unwrap();
        assert_eq!(
            parser.parse().unwrap(),
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

        let parser = Parser::new("(1 -2 #t)").unwrap();
        assert_eq!(
            parser.parse().unwrap(),
            Object::List(
                vec![Object::Int(1), Object::Int(-2), Object::Bool(true)]
                    .into_iter()
                    .collect()
            )
        );

        let parser = Parser::new("(#f (-2.5 3))").unwrap();
        assert_eq!(
            parser.parse().unwrap(),
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
    }
}
