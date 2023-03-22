use crate::error::Errors;
use crate::object::Object;
use crate::tokenizer::{Token, TokenKind, Tokenizer};

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
            return Ok(Object::Char {
                char_code,
                bucky_bits,
            });
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
                    tail = Object::make_cons(object, tail);
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
                            tail = Object::reverse_list_with_tail(tail, object);

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
    use crate::object::Object;
    use crate::parser::parse_program;

    #[test]
    fn test_parse_list() {
        assert_eq!(
            parse_program("(1 2 3)").unwrap(),
            Object::make_cons(
                Object::Int(1),
                Object::make_cons(
                    Object::Int(2),
                    Object::make_cons(Object::Int(3), Object::Nil)
                )
            )
        );

        assert_eq!(
            parse_program("(1 (2 3))").unwrap(),
            Object::make_cons(
                Object::Int(1),
                Object::make_cons(
                    Object::make_cons(
                        Object::Int(2),
                        Object::make_cons(Object::Int(3), Object::Nil)
                    ),
                    Object::Nil
                )
            ),
        );

        assert_eq!(
            parse_program("(1 -2 -3) (+1 -2 -3)").unwrap(),
            Object::make_begin(Object::make_cons(
                Object::make_cons(
                    Object::Int(1),
                    Object::make_cons(
                        Object::Int(-2),
                        Object::make_cons(Object::Int(-3), Object::Nil)
                    )
                ),
                Object::make_cons(
                    Object::make_cons(
                        Object::Int(1),
                        Object::make_cons(
                            Object::Int(-2),
                            Object::make_cons(Object::Int(-3), Object::Nil)
                        )
                    ),
                    Object::Nil
                )
            ))
        );

        assert_eq!(
            parse_program("(1 (-2.5 3))").unwrap(),
            Object::make_cons(
                Object::Int(1),
                Object::make_cons(
                    Object::make_cons(
                        Object::Real(-2.5),
                        Object::make_cons(Object::Int(3), Object::Nil)
                    ),
                    Object::Nil
                )
            )
        );

        assert_eq!(
            parse_program("(1 -2 #t)").unwrap(),
            Object::make_cons(
                Object::Int(1),
                Object::make_cons(
                    Object::Int(-2),
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
                        Object::Real(-2.5),
                        Object::make_cons(Object::Int(3), Object::Nil)
                    ),
                    Object::Nil
                )
            )
        );

        assert_eq!(
            parse_program("(#f . (-2.5 . 3))").unwrap(),
            Object::make_cons(
                Object::Bool(false),
                Object::make_cons(Object::Real(-2.5), Object::Int(3))
            )
        );

        assert_eq!(
            parse_program("(+ 1 3)").unwrap(),
            Object::make_cons(
                Object::Symbol(String::from("+")),
                Object::make_cons(
                    Object::Int(1),
                    Object::make_cons(Object::Int(3), Object::Nil)
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

        assert_eq!(parse_program("1").unwrap(), Object::Int(1));
        assert_eq!(
            parse_program("(define foo 1) foo").unwrap(),
            Object::make_begin(Object::make_cons(
                Object::make_cons(
                    Object::Symbol(String::from("define")),
                    Object::make_cons(
                        Object::Symbol(String::from("foo")),
                        Object::make_cons(Object::Int(1), Object::Nil)
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
                    Object::make_cons(Object::Int(1), Object::Nil)
                )
            ),)
        );
    }
}
