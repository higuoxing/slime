use lazy_static::lazy_static;
use regex::Regex;

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
    pub fn from(literal: &'a str, line_number: i64, line_offset: i64, kind: TokenKind) -> Self {
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

lazy_static! {
    static ref TOKEN_MATCHERS: Vec<(Regex, TokenKind)> = vec![
        (Regex::new("^#[t|f]$").unwrap(), TokenKind::Bool),
        (Regex::new("^([+|-]?)([[:digit:]]+)$").unwrap(), TokenKind::Int),
        (Regex::new("^([+|-]?)([[:digit:]]+)(\\.[[:digit:]]+)?$").unwrap(), TokenKind::Float),
        (/* Identifier.
          * https://www.gnu.org/software/mit-scheme/documentation/stable/mit-scheme-ref/Identifiers.html
          */
         Regex::new("^[^#,][^\\(\\);\"`\\|\\[\\]\\{\\}\\t\\ \\n\\r]*$").unwrap(), TokenKind::Symbol)
    ];
}

// Definition for delimiters:
//   https://www.gnu.org/software/mit-scheme/documentation/stable/mit-scheme-ref/Delimiters.html
fn is_delimiter(ch: char) -> bool {
    match ch {
        '(' | ')' | ';' | '"' | '\'' | '`' | '|' | '[' | ']' | '{' | '}' | '\t' | ' ' | '\r'
        | '\n' => true,
        _ => false,
    }
}

// FIXME: Try to make the lexer into an iterator.
fn try_match_string_literal<'a>(
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
        Token::from(
            &program[start..start + strlen],
            line_number,
            line_offset,
            TokenKind::String,
        ),
        strlen as i64,
    ))
}

pub fn tokenize(prog: &str) -> Result<Vec<Token>, Errors> {
    let mut tokens = vec![];
    let mut program_char_indices = prog.char_indices();
    let mut line: i64 = 1;
    let mut column: i64 = 1;

    while let Some((start, ch)) = program_char_indices.next() {
        // Firstly, match delimiters.
        if ch == '\n' {
            line += 1;
            column = 1;
            continue;
        } else if ch == ' ' || ch == '\t' || ch == '\r' {
            column += ch.len_utf8() as i64;
            continue;
        } else if ch == ';' {
            // Skip comments.
            while let Some((_, ch)) = program_char_indices.next() {
                if ch == '\n' {
                    column = 1;
                    line += 1;
                    break;
                }
            }
            continue;
        } else if ch == '(' {
            tokens.push(Token::from(
                &prog[start..start + ch.len_utf8()],
                line,
                column,
                TokenKind::LeftParen,
            ));
            column += ch.len_utf8() as i64;
            continue;
        } else if ch == ')' {
            tokens.push(Token::from(
                &prog[start..start + ch.len_utf8()],
                line,
                column,
                TokenKind::RightParen,
            ));
            column += ch.len_utf8() as i64;
            continue;
        } else if ch == '.' {
            tokens.push(Token::from(
                &prog[start..start + ch.len_utf8()],
                line,
                column,
                TokenKind::Dot,
            ));
            column += ch.len_utf8() as i64;
            continue;
        } else if ch == '\'' {
            tokens.push(Token::from(
                &prog[start..start + ch.len_utf8()],
                line,
                column,
                TokenKind::Quote,
            ));
            column += ch.len_utf8() as i64;
            continue;
        } else if ch == '`' {
            tokens.push(Token::from(
                &prog[start..start + ch.len_utf8()],
                line,
                column,
                TokenKind::BackQuote,
            ));
            column += ch.len_utf8() as i64;
            continue;
        } else if ch == ',' {
            tokens.push(Token::from(
                &prog[start..start + ch.len_utf8()],
                line,
                column,
                TokenKind::Comma,
            ));
            column += ch.len_utf8() as i64;
            continue;
        } else if ch == '@' {
            tokens.push(Token::from(
                &prog[start..start + ch.len_utf8()],
                line,
                column,
                TokenKind::At,
            ));
            column += ch.len_utf8() as i64;
            continue;
        }
        if ch == '"' {
            // Process string literal.
            if let Ok((token, token_len)) =
                try_match_string_literal(prog, start, line, column, ch, &mut program_char_indices)
            {
                tokens.push(token);
                column += token_len;
                continue;
            } else {
                // Unlikely to happen.
                panic!("Cannot parse string literal");
            }
        } else {
            // Process tokens.
            let save_program_char_indices1 = program_char_indices.clone();
            let mut save_program_char_indices2 = program_char_indices.clone();
            let mut end_ind = start;
            let mut break_by_delimiter = false;

            while let Some((ind, ch)) = program_char_indices.next() {
                end_ind = ind;
                if is_delimiter(ch) {
                    break_by_delimiter = true;
                    break;
                }
                save_program_char_indices2 = program_char_indices.clone();
            }

            if !break_by_delimiter {
                end_ind += 1;
            }

            let mut matched = false;
            for tok_matcher in TOKEN_MATCHERS.iter() {
                if tok_matcher.0.is_match(&prog[start..end_ind]) {
                    tokens.push(Token::from(
                        &prog[start..end_ind],
                        line,
                        column,
                        tok_matcher.1,
                    ));
                    column += (end_ind - start) as i64;
                    //                    println!("{} - {:?}", prog, &prog[start..end_ind]);
                    matched = true;
                    break;
                }
            }

            if matched {
                program_char_indices = save_program_char_indices2;
                continue;
            }
            program_char_indices = save_program_char_indices1;

            match ch {
                '#' => {
                    // Look one token ahead.
                    if let Some((_, ch)) = program_char_indices.next() {
                        if ch == '(' {
                            tokens.push(Token::from(
                                &prog[start..start + "#(".len()],
                                line,
                                column,
                                TokenKind::HashLeftParen,
                            ));
                            column += "#(".len() as i64;
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

                                    tokens.push(Token::from(
                                        &prog[start..start + charlen],
                                        line,
                                        column,
                                        TokenKind::Char,
                                    ));
                                    column += charlen as i64;
                                } else if is_print(ch) {
                                    charlen += ch.len_utf8();
                                    tokens.push(Token::from(
                                        &prog[start..start + charlen],
                                        line,
                                        column,
                                        TokenKind::Char,
                                    ));
                                    column += charlen as i64;
                                }
                            } else {
                                return Err(Errors::UnexpectedToken(line, column));
                            }
                        }
                    } else {
                        return Err(Errors::UnexpectedToken(line, column));
                    }
                }
                _ => {
                    return Err(Errors::UnexpectedToken(line, column));
                }
            }
        }
    }

    Ok(tokens)
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
    use super::{tokenize, Token, TokenKind};

    #[test]
    fn test_tokenizer() {
        // Test tokenize various symbols.
        assert_eq!(
            tokenize(
                "( (  ) ) . \n, @ #f #t #(

  \" some string\" #(  3.1415926   (()) 3333  (()) some_symbol
some_symbol2  (())
`;; this is comment
foo
#\\newline (())"
            ),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("(", 1, 3, TokenKind::LeftParen),
                Token::from(")", 1, 6, TokenKind::RightParen),
                Token::from(")", 1, 8, TokenKind::RightParen),
                Token::from(".", 1, 10, TokenKind::Dot),
                Token::from(",", 2, 1, TokenKind::Comma),
                Token::from("@", 2, 3, TokenKind::At),
                Token::from("#f", 2, 5, TokenKind::Bool),
                Token::from("#t", 2, 8, TokenKind::Bool),
                Token::from("#(", 2, 11, TokenKind::HashLeftParen),
                Token::from("\" some string\"", 4, 3, TokenKind::String),
                Token::from("#(", 4, 18, TokenKind::HashLeftParen),
                Token::from("3.1415926", 4, 22, TokenKind::Float),
                Token::from("(", 4, 34, TokenKind::LeftParen),
                Token::from("(", 4, 35, TokenKind::LeftParen),
                Token::from(")", 4, 36, TokenKind::RightParen),
                Token::from(")", 4, 37, TokenKind::RightParen),
                Token::from("3333", 4, 39, TokenKind::Int),
                Token::from("(", 4, 45, TokenKind::LeftParen),
                Token::from("(", 4, 46, TokenKind::LeftParen),
                Token::from(")", 4, 47, TokenKind::RightParen),
                Token::from(")", 4, 48, TokenKind::RightParen),
                Token::from("some_symbol", 4, 50, TokenKind::Symbol),
                Token::from("some_symbol2", 5, 1, TokenKind::Symbol),
                Token::from("(", 5, 15, TokenKind::LeftParen),
                Token::from("(", 5, 16, TokenKind::LeftParen),
                Token::from(")", 5, 17, TokenKind::RightParen),
                Token::from(")", 5, 18, TokenKind::RightParen),
                Token::from("`", 6, 1, TokenKind::BackQuote),
                Token::from("foo", 7, 1, TokenKind::Symbol),
                Token::from("#\\newline", 8, 1, TokenKind::Char),
                Token::from("(", 8, 11, TokenKind::LeftParen),
                Token::from("(", 8, 12, TokenKind::LeftParen),
                Token::from(")", 8, 13, TokenKind::RightParen),
                Token::from(")", 8, 14, TokenKind::RightParen),
            ])
        );

        assert_eq!(
            tokenize("lambda\nq\nlist->vector\nsoup\n+\nV17a\n<=?\na34kTMNs\nthe-word-recursion-has-many-meanings"),
            Ok(vec![Token::from("lambda", 1, 1, TokenKind::Symbol),
                    Token::from("q", 2, 1, TokenKind::Symbol),
                    Token::from("list->vector", 3, 1, TokenKind::Symbol),
                    Token::from("soup", 4, 1, TokenKind::Symbol),
                    Token::from("+", 5, 1, TokenKind::Symbol),
                    Token::from("V17a", 6, 1, TokenKind::Symbol),
                    Token::from("<=?", 7, 1, TokenKind::Symbol),
                    Token::from("a34kTMNs", 8, 1, TokenKind::Symbol),
                    Token::from("the-word-recursion-has-many-meanings", 9, 1, TokenKind::Symbol)
	    ])
        );

        assert_eq!(
            tokenize("(+  1 2)"),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("+", 1, 2, TokenKind::Symbol),
                Token::from("1", 1, 5, TokenKind::Int),
                Token::from("2", 1, 7, TokenKind::Int),
                Token::from(")", 1, 8, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            tokenize("(- 1 -99999)"),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("-", 1, 2, TokenKind::Symbol),
                Token::from("1", 1, 4, TokenKind::Int),
                Token::from("-99999", 1, 6, TokenKind::Int),
                Token::from(")", 1, 12, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            tokenize("(- 1 -999.99)"),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("-", 1, 2, TokenKind::Symbol),
                Token::from("1", 1, 4, TokenKind::Int),
                Token::from("-999.99", 1, 6, TokenKind::Float),
                Token::from(")", 1, 13, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            tokenize("(- 1 \"string with escape character\\n\")"),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("-", 1, 2, TokenKind::Symbol),
                Token::from("1", 1, 4, TokenKind::Int),
                Token::from(
                    "\"string with escape character\\n\"",
                    1,
                    6,
                    TokenKind::String
                ),
                Token::from(")", 1, 38, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            tokenize("(symbol->string 'flying-fish)"),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("symbol->string", 1, 2, TokenKind::Symbol),
                Token::from("'", 1, 17, TokenKind::Quote),
                Token::from("flying-fish", 1, 18, TokenKind::Symbol),
                Token::from(")", 1, 29, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            tokenize(
                "(define counter
    ((lambda (val)
       (lambda () (setq val (+ val 1)) val))
     0))
  (counter)

  (counter)"
            ),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("define", 1, 2, TokenKind::Symbol),
                Token::from("counter", 1, 9, TokenKind::Symbol),
                Token::from("(", 2, 5, TokenKind::LeftParen),
                Token::from("(", 2, 6, TokenKind::LeftParen),
                Token::from("lambda", 2, 7, TokenKind::Symbol),
                Token::from("(", 2, 14, TokenKind::LeftParen),
                Token::from("val", 2, 15, TokenKind::Symbol),
                Token::from(")", 2, 18, TokenKind::RightParen),
                Token::from("(", 3, 8, TokenKind::LeftParen),
                Token::from("lambda", 3, 9, TokenKind::Symbol),
                Token::from("(", 3, 16, TokenKind::LeftParen),
                Token::from(")", 3, 17, TokenKind::RightParen),
                Token::from("(", 3, 19, TokenKind::LeftParen),
                Token::from("setq", 3, 20, TokenKind::Symbol),
                Token::from("val", 3, 25, TokenKind::Symbol),
                Token::from("(", 3, 29, TokenKind::LeftParen),
                Token::from("+", 3, 30, TokenKind::Symbol),
                Token::from("val", 3, 32, TokenKind::Symbol),
                Token::from("1", 3, 36, TokenKind::Int),
                Token::from(")", 3, 37, TokenKind::RightParen),
                Token::from(")", 3, 38, TokenKind::RightParen),
                Token::from("val", 3, 40, TokenKind::Symbol),
                Token::from(")", 3, 43, TokenKind::RightParen),
                Token::from(")", 3, 44, TokenKind::RightParen),
                Token::from("0", 4, 6, TokenKind::Int),
                Token::from(")", 4, 7, TokenKind::RightParen),
                Token::from(")", 4, 8, TokenKind::RightParen),
                Token::from("(", 5, 3, TokenKind::LeftParen),
                Token::from("counter", 5, 4, TokenKind::Symbol),
                Token::from(")", 5, 11, TokenKind::RightParen),
                Token::from("(", 7, 3, TokenKind::LeftParen),
                Token::from("counter", 7, 4, TokenKind::Symbol),
                Token::from(")", 7, 11, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            tokenize(
                "(#\\a #\\b #\\c  #\\space #\\c-a #\\control-a #\\meta-b #\\c-m-a  #\\C-M-a #\\0 #\\9)"
            ),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("#\\a", 1, 2, TokenKind::Char),
                Token::from("#\\b", 1, 6, TokenKind::Char),
                Token::from("#\\c", 1, 10, TokenKind::Char),
                Token::from("#\\space", 1, 15, TokenKind::Char),
                Token::from("#\\c-a", 1, 23, TokenKind::Char),
                Token::from("#\\control-a", 1, 29, TokenKind::Char),
                Token::from("#\\meta-b", 1, 41, TokenKind::Char),
                Token::from("#\\c-m-a", 1, 50, TokenKind::Char),
                Token::from("#\\C-M-a", 1, 59, TokenKind::Char),
                Token::from("#\\0", 1, 67, TokenKind::Char),
                Token::from("#\\9", 1, 71, TokenKind::Char),
                Token::from(")", 1, 74, TokenKind::RightParen)
            ])
        );

        assert_eq!(
            tokenize("(define foo 1) foo"),
            Ok(vec![
                Token::from("(", 1, 1, TokenKind::LeftParen),
                Token::from("define", 1, 2, TokenKind::Symbol),
                Token::from("foo", 1, 9, TokenKind::Symbol),
                Token::from("1", 1, 13, TokenKind::Int),
                Token::from(")", 1, 14, TokenKind::RightParen),
                Token::from("foo", 1, 16, TokenKind::Symbol),
            ])
        );
    }
}
