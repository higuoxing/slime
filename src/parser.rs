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
enum TokenKind {
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
    line_offset: i64,
    kind: TokenKind,
}

impl<'a> Token<'a> {
    fn new(literal: &'a str, line_number: i64, line_offset: i64, kind: TokenKind) -> Self {
        Self {
            literal,
            line_number,
            line_offset,
            kind,
        }
    }
}

#[derive(Debug, PartialEq)]
struct Lexer<'a> {
    program: &'a str,
    tokens: Vec<Token<'a>>,
}

// FIXME: Try to make the lexer into an iterator.
impl<'a> Lexer<'a> {
    fn try_match_string_literal(
        program: &'a str,
        start: usize,
        line_number: i64,
        line_offset: i64,
        curr_char: char,
        program_char_indices: &mut CharIndices,
    ) -> Result<(Token<'a>, i64), ParseError> {
        let mut strlen = curr_char.len_utf8();
        while let Some((_, ch)) = program_char_indices.next() {
            strlen += ch.len_utf8();
            match ch {
                '\\' => {
                    // Look a character ahead.
                    if let Some((_, ch)) = program_char_indices.next() {
                        strlen += ch.len_utf8();
                        continue;
                    } else {
                        return Err(ParseError::UnexpectedToken(line_number, line_offset));
                    }
                }
                '"' => break,
                _ => continue,
            }
        }
        Ok((
            Token::new(
                &program[start..start + strlen],
                line_number,
                line_offset,
                TokenKind::String,
            ),
            strlen as i64,
        ))
    }

    fn try_match_number(
        program: &'a str,
        start: usize,
        line_number: i64,
        line_offset: i64,
        mut curr_char: char,
        program_char_indices: &mut CharIndices,
    ) -> Result<(Token<'a>, i64), ParseError> {
        let mut digit_len = 0;
        let mut is_float = false;
        let prev_program_char_indices = program_char_indices.clone();

        if curr_char == '+' || curr_char == '-' {
            digit_len += curr_char.len_utf8();

            // Look one character ahead.
            if let Some((_, ch)) = program_char_indices.next() {
                curr_char = ch;
            } else {
                // No more characters, put one character back.
                *program_char_indices = prev_program_char_indices.clone();
                return Err(ParseError::Unknown);
            }
        }

        if curr_char.is_digit(10) {
            // Try to parse it as number.
            digit_len += curr_char.len_utf8();
            let mut prev_program_char_indices = program_char_indices.clone();
            while let Some((_, ch)) = program_char_indices.next() {
                if ch.is_digit(10) {
                    digit_len += ch.len_utf8();
                    prev_program_char_indices = program_char_indices.clone();
                    continue;
                } else {
                    // Put back one character.
                    *program_char_indices = prev_program_char_indices.clone();
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
                            *program_char_indices = prev_program_char_indices.clone();
                            break;
                        }
                    }
                } else {
                    // Put back one character.
                    *program_char_indices = prev_program_char_indices.clone();
                }
            }

            Ok((
                Token::new(
                    &program[start..start + digit_len],
                    line_number,
                    line_offset,
                    if is_float {
                        TokenKind::Float
                    } else {
                        TokenKind::Int
                    },
                ),
                digit_len as i64,
            ))
        } else {
            // Put back one character.
            *program_char_indices = prev_program_char_indices.clone();
            Err(ParseError::Unknown)
        }
    }

    fn try_match_symbol(
        program: &'a str,
        start: usize,
        line_number: i64,
        line_offset: i64,
        curr_char: char,
        program_char_indices: &mut CharIndices,
    ) -> Result<(Token<'a>, i64), ParseError> {
        let mut symbol_len = curr_char.len_utf8();
        if !is_symbol(curr_char) {
            return Err(ParseError::UnexpectedToken(line_number, line_offset));
        }

        let mut prev_program_char_indices = program_char_indices.clone();
        while let Some((_, ch)) = program_char_indices.next() {
            if is_symbol(ch) {
                prev_program_char_indices = program_char_indices.clone();
                symbol_len += ch.len_utf8();
                continue;
            } else {
                *program_char_indices = prev_program_char_indices.clone();
                break;
            }
        }

        Ok((
            Token::new(
                &program[start..start + symbol_len],
                line_number,
                line_offset,
                TokenKind::Symbol,
            ),
            symbol_len as i64,
        ))
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
                        } else if ch == '\\' {
                            // Char type.
                            let mut charlen = "#\\".len();

                            if let Some((_, ch)) = program_char_indices.next() {
                                if ch.is_alphanumeric() {
                                    charlen += ch.len_utf8();

                                    let mut prev_program_char_indices =
                                        program_char_indices.clone();

                                    while let Some((_, ch)) = program_char_indices.next() {
                                        if ch.is_alphanumeric() {
                                            charlen += ch.len_utf8();
                                            prev_program_char_indices =
                                                program_char_indices.clone();
                                            continue;
                                        } else {
                                            // Put back one character.
                                            program_char_indices =
                                                prev_program_char_indices.clone();
                                            break;
                                        }
                                    }

                                    tokens.push(Token::new(
                                        &program[start..start + charlen],
                                        line_number,
                                        line_offset,
                                        TokenKind::Char,
                                    ));
                                    line_offset += charlen as i64;
                                } else if is_print(ch) {
                                    charlen += ch.len_utf8();
                                    tokens.push(Token::new(
                                        &program[start..start + charlen],
                                        line_number,
                                        line_offset,
                                        TokenKind::Char,
                                    ));
                                    line_offset += charlen as i64;
                                }
                            } else {
                                return Err(ParseError::UnexpectedToken(line_number, line_offset));
                            }
                        }
                    } else {
                        return Err(ParseError::UnexpectedToken(line_number, line_offset));
                    }
                }
                '"' => {
                    // Process string literal.
                    if let Ok((token, token_len)) = Self::try_match_string_literal(
                        program,
                        start,
                        line_number,
                        line_offset,
                        ch,
                        &mut program_char_indices,
                    ) {
                        tokens.push(token);
                        line_offset += token_len;
                        continue;
                    } else {
                        // Unlikely to happen.
                        return Err(ParseError::UnexpectedToken(line_number, line_offset));
                    }
                }
                _ => {
                    if let Ok((token, token_len)) = Self::try_match_number(
                        // Try to parse it as a number.
                        program,
                        start,
                        line_number,
                        line_offset,
                        ch,
                        &mut program_char_indices,
                    ) {
                        tokens.push(token);
                        line_offset += token_len;
                        continue;
                    } else if let Ok((token, token_len)) = Self::try_match_symbol(
                        // Try to parse it as a symbol.
                        program,
                        start,
                        line_number,
                        line_offset,
                        ch,
                        &mut program_char_indices,
                    ) {
                        tokens.push(token);
                        line_offset += token_len;
                        continue;
                    } else {
                        return Err(ParseError::UnexpectedToken(line_number, line_offset));
                    }
                }
            }
        }

        Ok(tokens)
    }

    fn tokens(&self) -> &Vec<Token> {
        self.tokens.as_ref()
    }

    fn new(program: &'a str) -> Result<Lexer<'a>, ParseError> {
        let tokens = Self::tokenize(program)?;
        Ok(Self { program, tokens })
    }
}

#[derive(Debug, PartialEq)]
enum Object {
    Nil,
    Real(f64),
    Int(i64),
}

#[derive(Debug)]
struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    fn new(program: &'a str) -> Result<Self, ParseError> {
        Ok(Self {
            lexer: Lexer::new(program)?,
        })
    }

    fn parse_number(curr_token: &Token) -> Result<Object, ParseError> {
        match curr_token.kind {
            TokenKind::Int => {
                if let Ok(n) = curr_token.literal.parse::<i64>() {
                    Ok(Object::Int(n))
                } else {
                    Err(ParseError::UnexpectedToken(
                        curr_token.line_number,
                        curr_token.line_offset,
                    ))
                }
            }
            TokenKind::Float => {
                if let Ok(f) = curr_token.literal.parse::<f64>() {
                    Ok(Object::Real(f))
                } else {
                    Err(ParseError::UnexpectedToken(
                        curr_token.line_number,
                        curr_token.line_offset,
                    ))
                }
            }
            _ => Err(ParseError::UnexpectedToken(
                curr_token.line_number,
                curr_token.line_offset,
            )),
        }
    }

    fn parse(&self) -> Result<Object, ParseError> {
        if self.lexer.tokens.is_empty() {
            return Ok(Object::Nil);
        }

        let mut token_iter = self.lexer.tokens.iter();

        Err(ParseError::Unknown)
    }
}

fn is_symbol(ch: char) -> bool {
    if ch < '!' || ch > 'z' {
        return false;
    }

    match ch {
        '(' | ')' | '#' | ';' => false,
        _ => true,
    }
}

// See the chapter of 'Character Sets' in
//   https://groups.csail.mit.edu/mac/ftpdir/scheme-7.4/doc-html/scheme_6.html
fn is_print(ch: char) -> bool {
    match ch {
        '!' | '"' | '#' | '$' | '%' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | '-' | '.'
        | '/' | '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' | ':' | ';' | '<'
        | '=' | '>' | '?' | '@' | 'A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J'
        | 'K' | 'L' | 'M' | 'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T' | 'U' | 'V' | 'W' | 'X'
        | 'Y' | 'Z' | '[' | '\\' | ']' | '^' | '_' | '`' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f'
        | 'g' | 'h' | 'i' | 'j' | 'k' | 'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't'
        | 'u' | 'v' | 'w' | 'x' | 'y' | 'z' | '{' | '|' | '}' | '~' => true,
        _ => false,
    }
}

#[cfg(test)]
mod test {
    use crate::parser::{Lexer, Object, Parser, Token, TokenKind};

    #[test]
    fn test_tokenizer() {
        // Test tokenize various symbols.
        let program = String::from(
            "( (  ) ) . \n, @ #f #t #(\n\n  \" some string\" #(  3.1415926   (()) 3333  (()) some_symbol\nsome_symbol2  (())\n`;; this is comment\nfoo\n#\\newline (())",
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
                Token::new("`", 6, 1, TokenKind::BackQuote),
                Token::new("foo", 7, 1, TokenKind::Symbol),
                Token::new("#\\newline", 8, 1, TokenKind::Char),
                Token::new("(", 8, 11, TokenKind::LeftParen),
                Token::new("(", 8, 12, TokenKind::LeftParen),
                Token::new(")", 8, 13, TokenKind::RightParen),
                Token::new(")", 8, 14, TokenKind::RightParen),
            ])
        );

        let program = String::from("(+  1 2)");
        assert_eq!(
            Lexer::tokenize(program.as_str()),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("+", 1, 2, TokenKind::Symbol),
                Token::new("1", 1, 5, TokenKind::Int),
                Token::new("2", 1, 7, TokenKind::Int),
                Token::new(")", 1, 8, TokenKind::RightParen)
            ])
        );

        let program = String::from("(- 1 -99999)");
        assert_eq!(
            Lexer::tokenize(program.as_str()),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("-", 1, 2, TokenKind::Symbol),
                Token::new("1", 1, 4, TokenKind::Int),
                Token::new("-99999", 1, 6, TokenKind::Int),
                Token::new(")", 1, 12, TokenKind::RightParen)
            ])
        );

        let program = String::from("(- 1 -999.99)");
        assert_eq!(
            Lexer::tokenize(program.as_str()),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("-", 1, 2, TokenKind::Symbol),
                Token::new("1", 1, 4, TokenKind::Int),
                Token::new("-999.99", 1, 6, TokenKind::Float),
                Token::new(")", 1, 13, TokenKind::RightParen)
            ])
        );

        let program = String::from("(- 1 \"string with escape character\\n\")");
        assert_eq!(
            Lexer::tokenize(program.as_str()),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("-", 1, 2, TokenKind::Symbol),
                Token::new("1", 1, 4, TokenKind::Int),
                Token::new(
                    "\"string with escape character\\n\"",
                    1,
                    6,
                    TokenKind::String
                ),
                Token::new(")", 1, 38, TokenKind::RightParen)
            ])
        );
    }

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
