use crate::error::Errors;

use std::str::CharIndices;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum TokenKind {
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

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Token<'a> {
    literal: &'a str,
    line: i64,
    column: i64,
    kind: TokenKind,
}

impl<'a> Token<'a> {
    pub fn new(literal: &'a str, line_number: i64, line_offset: i64, kind: TokenKind) -> Self {
        Self {
            literal,
            line: line_number,
            column: line_offset,
            kind,
        }
    }

    pub fn line(&self) -> i64 {
        self.line
    }

    pub fn column(&self) -> i64 {
        self.column
    }

    pub fn kind(&self) -> TokenKind {
        self.kind
    }

    pub fn literal(&self) -> &'a str {
        self.literal
    }
}

#[derive(Debug, PartialEq)]
pub struct Tokenizer<'a> {
    program: &'a str,
    tokens: Vec<Token<'a>>,
}

// FIXME: Try to make the lexer into an iterator.
impl<'a> Tokenizer<'a> {
    fn try_match_string_literal(
        program: &'a str,
        start: usize,
        line_number: i64,
        line_offset: i64,
        curr_char: char,
        program_char_indices: &mut CharIndices,
    ) -> Result<(Token<'a>, i64), Errors> {
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
                        return Err(Errors::UnexpectedToken(line_number, line_offset));
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
    ) -> Result<(Token<'a>, i64), Errors> {
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
                return Err(Errors::Unknown);
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
            Err(Errors::Unknown)
        }
    }

    fn try_match_symbol(
        program: &'a str,
        start: usize,
        line_number: i64,
        line_offset: i64,
        curr_char: char,
        program_char_indices: &mut CharIndices,
    ) -> Result<(Token<'a>, i64), Errors> {
        let mut symbol_len = curr_char.len_utf8();
        if !is_symbol(curr_char) {
            return Err(Errors::UnexpectedToken(line_number, line_offset));
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

    pub fn tokenize(program: &'a str) -> Result<Vec<Token>, Errors> {
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
                                        if ch.is_alphanumeric() || ch == '-' {
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
                                return Err(Errors::UnexpectedToken(line_number, line_offset));
                            }
                        }
                    } else {
                        return Err(Errors::UnexpectedToken(line_number, line_offset));
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
                        panic!("Cannot parse string literal");
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
                        return Err(Errors::UnexpectedToken(line_number, line_offset));
                    }
                }
            }
        }

        Ok(tokens)
    }

    pub fn tokens(&self) -> &Vec<Token> {
        self.tokens.as_ref()
    }

    pub fn new(program: &'a str) -> Result<Tokenizer<'a>, Errors> {
        let tokens = Self::tokenize(program)?;
        Ok(Self { program, tokens })
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
mod tests {
    use super::{Token, TokenKind, Tokenizer};

    #[test]
    fn test_tokenizer() {
        // Test tokenize various symbols.
        assert_eq!(
            Tokenizer::tokenize(
                "( (  ) ) . \n, @ #f #t #(

  \" some string\" #(  3.1415926   (()) 3333  (()) some_symbol
some_symbol2  (())
`;; this is comment
foo
#\\newline (())"
            ),
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

        assert_eq!(
            Tokenizer::tokenize("(+  1 2)"),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("+", 1, 2, TokenKind::Symbol),
                Token::new("1", 1, 5, TokenKind::Int),
                Token::new("2", 1, 7, TokenKind::Int),
                Token::new(")", 1, 8, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            Tokenizer::tokenize("(- 1 -99999)"),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("-", 1, 2, TokenKind::Symbol),
                Token::new("1", 1, 4, TokenKind::Int),
                Token::new("-99999", 1, 6, TokenKind::Int),
                Token::new(")", 1, 12, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            Tokenizer::tokenize("(- 1 -999.99)"),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("-", 1, 2, TokenKind::Symbol),
                Token::new("1", 1, 4, TokenKind::Int),
                Token::new("-999.99", 1, 6, TokenKind::Float),
                Token::new(")", 1, 13, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            Tokenizer::tokenize("(- 1 \"string with escape character\\n\")"),
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

        assert_eq!(
            Tokenizer::tokenize("(symbol->string 'flying-fish)"),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("symbol->string", 1, 2, TokenKind::Symbol),
                Token::new("'", 1, 17, TokenKind::Quote),
                Token::new("flying-fish", 1, 18, TokenKind::Symbol),
                Token::new(")", 1, 29, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            Tokenizer::tokenize(
                "(define counter
    ((lambda (val)
       (lambda () (setq val (+ val 1)) val))
     0))
  (counter)

  (counter)"
            ),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("define", 1, 2, TokenKind::Symbol),
                Token::new("counter", 1, 9, TokenKind::Symbol),
                Token::new("(", 2, 5, TokenKind::LeftParen),
                Token::new("(", 2, 6, TokenKind::LeftParen),
                Token::new("lambda", 2, 7, TokenKind::Symbol),
                Token::new("(", 2, 14, TokenKind::LeftParen),
                Token::new("val", 2, 15, TokenKind::Symbol),
                Token::new(")", 2, 18, TokenKind::RightParen),
                Token::new("(", 3, 8, TokenKind::LeftParen),
                Token::new("lambda", 3, 9, TokenKind::Symbol),
                Token::new("(", 3, 16, TokenKind::LeftParen),
                Token::new(")", 3, 17, TokenKind::RightParen),
                Token::new("(", 3, 19, TokenKind::LeftParen),
                Token::new("setq", 3, 20, TokenKind::Symbol),
                Token::new("val", 3, 25, TokenKind::Symbol),
                Token::new("(", 3, 29, TokenKind::LeftParen),
                Token::new("+", 3, 30, TokenKind::Symbol),
                Token::new("val", 3, 32, TokenKind::Symbol),
                Token::new("1", 3, 36, TokenKind::Int),
                Token::new(")", 3, 37, TokenKind::RightParen),
                Token::new(")", 3, 38, TokenKind::RightParen),
                Token::new("val", 3, 40, TokenKind::Symbol),
                Token::new(")", 3, 43, TokenKind::RightParen),
                Token::new(")", 3, 44, TokenKind::RightParen),
                Token::new("0", 4, 6, TokenKind::Int),
                Token::new(")", 4, 7, TokenKind::RightParen),
                Token::new(")", 4, 8, TokenKind::RightParen),
                Token::new("(", 5, 3, TokenKind::LeftParen),
                Token::new("counter", 5, 4, TokenKind::Symbol),
                Token::new(")", 5, 11, TokenKind::RightParen),
                Token::new("(", 7, 3, TokenKind::LeftParen),
                Token::new("counter", 7, 4, TokenKind::Symbol),
                Token::new(")", 7, 11, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            Tokenizer::tokenize(
                "(#\\a #\\b #\\c  #\\space #\\c-a #\\control-a #\\meta-b #\\c-m-a  #\\C-M-a #\\0 #\\9)"
            ),
            Ok(vec![
                Token::new("(", 1, 1, TokenKind::LeftParen),
                Token::new("#\\a", 1, 2, TokenKind::Char),
                Token::new("#\\b", 1, 6, TokenKind::Char),
                Token::new("#\\c", 1, 10, TokenKind::Char),
                Token::new("#\\space", 1, 15, TokenKind::Char),
                Token::new("#\\c-a", 1, 23, TokenKind::Char),
                Token::new("#\\control-a", 1, 29, TokenKind::Char),
                Token::new("#\\meta-b", 1, 41, TokenKind::Char),
                Token::new("#\\c-m-a", 1, 50, TokenKind::Char),
                Token::new("#\\C-M-a", 1, 59, TokenKind::Char),
                Token::new("#\\0", 1, 67, TokenKind::Char),
                Token::new("#\\9", 1, 71, TokenKind::Char),
                Token::new(")", 1, 74, TokenKind::RightParen)
            ])
        );
    }
}
