use crate::tokenizer::{Token, TokenKind, Tokenizer};

use std::str::CharIndices;

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

    fn parse_bool(curr_token: &Token) -> Result<Object, ParseError> {
        match curr_token.kind() {
            TokenKind::Bool => {
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
                curr_token.line_number(),
                curr_token.line_offset(),
            )),
        }
    }

    fn parse_number(curr_token: &Token) -> Result<Object, ParseError> {
        match curr_token.kind() {
            TokenKind::Int => {
                if let Ok(n) = curr_token.literal().parse::<i64>() {
                    Ok(Object::Int(n))
                } else {
                    Err(ParseError::UnexpectedToken(
                        curr_token.line_number(),
                        curr_token.line_offset(),
                    ))
                }
            }
            TokenKind::Float => {
                if let Ok(f) = curr_token.literal().parse::<f64>() {
                    Ok(Object::Real(f))
                } else {
                    Err(ParseError::UnexpectedToken(
                        curr_token.line_number(),
                        curr_token.line_offset(),
                    ))
                }
            }
            _ => Err(ParseError::UnexpectedToken(
                curr_token.line_number(),
                curr_token.line_offset(),
            )),
        }
    }

    fn parse(&self) -> Result<Object, ParseError> {
        if self.tokenizer.tokens().is_empty() {
            return Ok(Object::Nil);
        }

        let mut token_iter = self.tokenizer.tokens().iter();

        Err(ParseError::Unknown)
    }
}

#[cfg(test)]
mod tests {
    use super::{Object, Parser, Token, TokenKind};

    #[test]
    fn test_parser() {
        let token = Token::new("1.1", 1, 1, TokenKind::Float);
        assert_eq!(Parser::parse_number(&token), Ok(Object::Real(1.1)));

        let token = Token::new("-1.1", 1, 1, TokenKind::Float);
        assert_eq!(Parser::parse_number(&token), Ok(Object::Real(-1.1)));

        let token = Token::new("1", 1, 1, TokenKind::Int);
        assert_eq!(Parser::parse_number(&token), Ok(Object::Int(1)));

        let token = Token::new("-99999", 1, 1, TokenKind::Int);
        assert_eq!(Parser::parse_number(&token), Ok(Object::Int(-99999)));
    }
}
