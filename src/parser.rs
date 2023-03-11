use thiserror::Error;

#[derive(Debug, Error, PartialEq)]
pub enum ParseError {
    #[error("Unexpected token at {0}:{1}")]
    UnexpectedToken(i64, i64),
    #[error("Unknown error")]
    Unknown,
}

#[derive(Debug, PartialEq)]
enum TokenKind {
    None,       // None,
    LeftParen,  // '('
    RightParen, // ')'
    Dot,        // '.'
    Quote,      // '\''
    BackQuote,  // '`'
    Comma,      // ','
    At,         // '@'
    Symbol,
    String,
    Int,
    Float,
    Char,
    Bool,
    HashLeftParen, // '#('
}

#[derive(Debug, PartialEq)]
struct Token<'a> {
    literal: &'a str,
    line_number: i64,
    char_offset: i64,
    kind: TokenKind,
}

impl<'a> Token<'a> {
    fn new(literal: &'a str, line_number: i64, char_offset: i64, kind: TokenKind) -> Self {
        Self {
            literal,
            line_number,
            char_offset,
            kind,
        }
    }
}

#[derive(Debug, PartialEq)]
struct Lexer<'a> {
    program: &'a str,
    tokens: Vec<Token<'a>>,
}

impl<'a> Lexer<'a> {
    fn is_symbol(ch: char) -> bool {
        if ch < '!' || ch > 'z' {
            return false;
        }

        match ch {
            '(' | ')' | '#' | ';' => false,
            _ => true,
        }
    }

    fn tokenize(program: &'a str) -> Result<Vec<Token>, ParseError> {
        let mut tokens = vec![];
        let mut program_char_indices = program.char_indices();
        let mut line_number: i64 = 1;
        let mut line_offset: i64 = 1;

        while let Some((start, ch)) = program_char_indices.next() {
            // Skip whitespaces.
            if ch == '\n' {
                line_number += 1;
                line_offset = 1;
                continue;
            } else if ch == ' ' || ch == '\t' || ch == '\r' {
                line_offset += ch.len_utf8() as i64;
                continue;
            } else if ch == ';' {
                // Skip comments.
                while let Some((_, ch)) = program_char_indices.next() {
                    if ch == '\n' {
                        line_offset = 1;
                        line_number += 1;
                        break;
                    }
                }
                continue;
            }

            // Process tokens.
            match ch {
                '(' => {
                    tokens.push(Token::new(
                        &program[start..start + ch.len_utf8()],
                        line_number,
                        line_offset,
                        TokenKind::LeftParen,
                    ));
                    line_offset += ch.len_utf8() as i64;
                }
                ')' => {
                    tokens.push(Token::new(
                        &program[start..start + ch.len_utf8()],
                        line_number,
                        line_offset,
                        TokenKind::RightParen,
                    ));
                    line_offset += ch.len_utf8() as i64;
                }
                '.' => {
                    tokens.push(Token::new(
                        &program[start..start + ch.len_utf8()],
                        line_number,
                        line_offset,
                        TokenKind::Dot,
                    ));
                    line_offset += ch.len_utf8() as i64;
                }
                '\'' => {
                    tokens.push(Token::new(
                        &program[start..start + ch.len_utf8()],
                        line_number,
                        line_offset,
                        TokenKind::Quote,
                    ));
                    line_offset += ch.len_utf8() as i64;
                }
                '`' => {
                    tokens.push(Token::new(
                        &program[start..start + ch.len_utf8()],
                        line_number,
                        line_offset,
                        TokenKind::BackQuote,
                    ));
                    line_offset += ch.len_utf8() as i64;
                }
                ',' => {
                    tokens.push(Token::new(
                        &program[start..start + ch.len_utf8()],
                        line_number,
                        line_offset,
                        TokenKind::Comma,
                    ));
                    line_offset += ch.len_utf8() as i64;
                }
                '@' => {
                    tokens.push(Token::new(
                        &program[start..start + ch.len_utf8()],
                        line_number,
                        line_offset,
                        TokenKind::At,
                    ));
                    line_offset += ch.len_utf8() as i64;
                }
                '#' => {
                    // Look one token ahead.
                    if let Some((_, ch)) = program_char_indices.next() {
                        if ch == '(' {
                            tokens.push(Token::new(
                                &program[start..start + "#(".len()],
                                line_number,
                                line_offset,
                                TokenKind::HashLeftParen,
                            ));
                            line_offset += "#(".len() as i64;
                        } else if ch == 't' || ch == 'f' {
                            tokens.push(Token::new(
                                &program[start..start + "#t".len()],
                                line_number,
                                line_offset,
                                TokenKind::Bool,
                            ));
                            line_offset += "#t".len() as i64;
                        }
                    } else {
                        return Err(ParseError::UnexpectedToken(line_number, line_offset));
                    }
                }
                '"' => {
                    // Process string literal.
                    let mut strlen = "\"".len();
                    while let Some((_, ch)) = program_char_indices.next() {
                        strlen += ch.len_utf8();
                        if ch == '"' {
                            break;
                        }
                    }
                    tokens.push(Token::new(
                        &program[start..start + strlen],
                        line_number,
                        line_offset,
                        TokenKind::String,
                    ));
                    line_offset += strlen as i64;
                }
                _ => {
                    if ch.is_digit(10) {
                        // Try to parse it as number.
                        let mut digit_len = ch.len_utf8();
                        let mut is_float = false;
                        let mut prev_program_char_indices = program_char_indices.clone();
                        while let Some((_, ch)) = program_char_indices.next() {
                            if ch.is_digit(10) {
                                digit_len += ch.len_utf8();
                                prev_program_char_indices = program_char_indices.clone();
                                continue;
                            } else {
                                // Put back one character.
                                program_char_indices = prev_program_char_indices.clone();
                                break;
                            }
                        }

                        // Is this a float number?
                        prev_program_char_indices = program_char_indices.clone();
                        if let Some((_, ch)) = program_char_indices.next() {
                            if ch == '.' {
                                digit_len += ch.len_utf8();
                                is_float = true;

                                while let Some((_, ch)) = program_char_indices.next() {
                                    if ch.is_digit(10) {
                                        digit_len += ch.len_utf8();
                                        prev_program_char_indices = program_char_indices.clone();
                                        continue;
                                    } else {
                                        // Put back one character.
                                        program_char_indices = prev_program_char_indices.clone();
                                        break;
                                    }
                                }
                            } else {
                                // Put back one character.
                                program_char_indices = prev_program_char_indices.clone();
                            }
                        }

                        tokens.push(Token::new(
                            &program[start..start + digit_len],
                            line_number,
                            line_offset,
                            if is_float {
                                TokenKind::Float
                            } else {
                                TokenKind::Int
                            },
                        ));
                        line_offset += digit_len as i64;
                    } else {
                        // Try to parse it as a symbol.
                        let mut symbol_len = ch.len_utf8();
                        if !Self::is_symbol(ch) {
                            return Err(ParseError::UnexpectedToken(line_number, line_offset));
                        }

                        let mut prev_program_char_indices = program_char_indices.clone();
                        while let Some((_, ch)) = program_char_indices.next() {
                            if Self::is_symbol(ch) {
                                prev_program_char_indices = program_char_indices.clone();
                                symbol_len += ch.len_utf8();
                                continue;
                            } else {
                                program_char_indices = prev_program_char_indices.clone();
                                break;
                            }
                        }

                        tokens.push(Token::new(
                            &program[start..start + symbol_len],
                            line_number,
                            line_offset,
                            TokenKind::Symbol,
                        ));
                        line_offset += symbol_len as i64;
                    }
                }
            }
        }

        Ok(tokens)
    }

    fn new(program: &'a str) -> Result<Lexer<'a>, ParseError> {
        let tokens = Self::tokenize(program)?;
        Ok(Self { program, tokens })
    }
}

#[derive(Debug)]
struct Parser {}

impl Parser {}

#[cfg(test)]
mod test {
    use crate::parser::{Lexer, Token, TokenKind};

    #[test]
    fn test_tokenizer() {
        let program = String::from(
            "( (  ) ) . \n, @ #f #t #(\n\n  \" some string\" #(  3.1415926   (()) 3333  (()) some_symbol\nsome_symbol2  (())\n`",
        );
        assert_eq!(
            Lexer::tokenize(program.as_str()),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("(", 1, 3, TokenKind::LeftParen),
                Token::new(")", 1, 6, TokenKind::RightParen),
                Token::new(")", 1, 8, TokenKind::RightParen),
                Token::new(".", 1, 10, TokenKind::Dot),
                Token::new(",", 2, 1, TokenKind::Comma),
                Token::new("@", 2, 3, TokenKind::At),
                Token::new("#f", 2, 5, TokenKind::Bool),
                Token::new("#t", 2, 8, TokenKind::Bool),
                Token::new("#(", 2, 11, TokenKind::HashLeftParen),
                Token::new("\" some string\"", 4, 3, TokenKind::String),
                Token::new("#(", 4, 18, TokenKind::HashLeftParen),
                Token::new("3.1415926", 4, 22, TokenKind::Float),
                Token::new("(", 4, 34, TokenKind::LeftParen),
                Token::new("(", 4, 35, TokenKind::LeftParen),
                Token::new(")", 4, 36, TokenKind::RightParen),
                Token::new(")", 4, 37, TokenKind::RightParen),
                Token::new("3333", 4, 39, TokenKind::Int),
                Token::new("(", 4, 45, TokenKind::LeftParen),
                Token::new("(", 4, 46, TokenKind::LeftParen),
                Token::new(")", 4, 47, TokenKind::RightParen),
                Token::new(")", 4, 48, TokenKind::RightParen),
                Token::new("some_symbol", 4, 50, TokenKind::Symbol),
                Token::new("some_symbol2", 5, 1, TokenKind::Symbol),
                Token::new("(", 5, 15, TokenKind::LeftParen),
                Token::new("(", 5, 16, TokenKind::LeftParen),
                Token::new(")", 5, 17, TokenKind::RightParen),
                Token::new(")", 5, 18, TokenKind::RightParen),
                Token::new("`", 6, 1, TokenKind::BackQuote)
            ])
        );
    }
}
