// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: lexer.rs
// Creator: Jonas Forsman

//! Lexical analysis for Prolog source code
//! 
//! This module provides tokenization of Prolog text into a stream of tokens
//! that can be consumed by the parser. It handles all Prolog syntax including
//! operators, delimiters, comments, and provides detailed error reporting
//! with position information.

use crate::error::{ParseError, ParseResult, Position};

/// Token types representing all lexical elements in Prolog
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// Atom: lowercase identifier or quoted string
    Atom(String),
    /// Variable: uppercase identifier or underscore
    Variable(String),
    /// Integer number
    Number(i64),
    /// Left parenthesis '('
    LeftParen,
    /// Right parenthesis ')'
    RightParen,
    /// Left bracket '['
    LeftBracket,
    /// Right bracket ']'
    RightBracket,
    /// Comma ','
    Comma,
    /// Dot '.'
    Dot,
    /// Rule operator ':-'
    Rule,
    /// Pipe '|' (for list tails)
    Pipe,
    /// Question mark '?' (for queries)
    Question,
    /// Cut '!'
    Cut,
    
    // Arithmetic operators
    /// Addition '+'
    Plus,
    /// Subtraction '-'
    Minus,
    /// Multiplication '*'
    Multiply,
    /// Integer division '//'
    Divide,
    /// Greater than '>'
    Greater,
    /// Less than '<'
    Less,
    /// Greater than or equal '>='
    GreaterEq,
    /// Less than or equal '=<'
    LessEq,
    /// Arithmetic equality '=:='
    ArithEq,
    /// Arithmetic inequality '=\\='
    ArithNeq,
    /// Unification '='
    Unify,
    /// Non-unification '\\='
    NotUnify,
    /// Arithmetic evaluation 'is'
    Is,
    /// Modulo 'mod'
    Mod,
    /// End of file
    Eof,
}

impl Token {
    /// Get a human-readable description of the token type
    pub fn description(&self) -> &'static str {
        match self {
            Token::Atom(_) => "atom",
            Token::Variable(_) => "variable",
            Token::Number(_) => "number",
            Token::LeftParen => "'('",
            Token::RightParen => "')'",
            Token::LeftBracket => "'['",
            Token::RightBracket => "']'",
            Token::Comma => "','",
            Token::Dot => "'.'",
            Token::Rule => "':-'",
            Token::Pipe => "'|'",
            Token::Question => "'?'",
            Token::Cut => "'!'",
            Token::Plus => "'+'",
            Token::Minus => "'-'",
            Token::Multiply => "'*'",
            Token::Divide => "'//'",
            Token::Greater => "'>'",
            Token::Less => "'<'",
            Token::GreaterEq => "'>='",
            Token::LessEq => "'=<'",
            Token::ArithEq => "'=:='",
            Token::ArithNeq => "'=\\='",
            Token::Unify => "'='",
            Token::NotUnify => "'\\='",
            Token::Is => "'is'",
            Token::Mod => "'mod'",
            Token::Eof => "end of file",
        }
    }
    
    /// Check if this token can start an expression
    pub fn can_start_expression(&self) -> bool {
        matches!(self, 
            Token::Atom(_) | Token::Variable(_) | Token::Number(_) | 
            Token::LeftParen | Token::LeftBracket | Token::Cut
        )
    }
}

/// Tokenizer for Prolog source code with position tracking
pub struct Tokenizer {
    input: Vec<char>,
    position: usize,
    current_line: usize,
    current_column: usize,
    paren_stack: Vec<(char, Position)>, // Track open delimiters for better error reporting
}

impl Tokenizer {
    /// Create a new tokenizer for the given input string
    pub fn new(input: &str) -> Self {
        Tokenizer {
            input: input.chars().collect(),
            position: 0,
            current_line: 1,
            current_column: 1,
            paren_stack: Vec::new(),
        }
    }
    
    /// Get the current position in the input
    fn current_position(&self) -> Position {
        Position::new(self.current_line, self.current_column, self.position)
    }
    
    /// Tokenize the entire input into a vector of tokens
    pub fn tokenize(&mut self) -> ParseResult<Vec<Token>> {
        let mut tokens = Vec::new();
        
        while self.position < self.input.len() {
            self.skip_whitespace();
            
            if self.position >= self.input.len() {
                break;
            }
            
            let ch = self.current_char();
            let pos = self.current_position();
            
            match ch {
                '(' => {
                    self.paren_stack.push(('(', pos));
                    tokens.push(Token::LeftParen);
                    self.advance();
                }
                ')' => {
                    self.check_matching_delimiter(')')?;
                    tokens.push(Token::RightParen);
                    self.advance();
                }
                '[' => {
                    self.paren_stack.push(('[', pos));
                    tokens.push(Token::LeftBracket);
                    self.advance();
                }
                ']' => {
                    self.check_matching_delimiter(']')?;
                    tokens.push(Token::RightBracket);
                    self.advance();
                }
                ',' => {
                    tokens.push(Token::Comma);
                    self.advance();
                }
                '.' => {
                    tokens.push(Token::Dot);
                    self.advance();
                }
                '|' => {
                    tokens.push(Token::Pipe);
                    self.advance();
                }
                '?' => {
                    tokens.push(Token::Question);
                    self.advance();
                }
                '!' => {
                    tokens.push(Token::Cut);
                    self.advance();
                }
                '+' => {
                    tokens.push(Token::Plus);
                    self.advance();
                }
                '-' => {
                    if self.peek_ahead_for_digit() {
                        tokens.push(self.read_negative_number()?);
                    } else {
                        tokens.push(Token::Minus);
                        self.advance();
                    }
                }
                '*' => {
                    tokens.push(Token::Multiply);
                    self.advance();
                }
                '/' => {
                    let pos = self.current_position();
                    self.advance();
                    if self.current_char() == '/' {
                        tokens.push(Token::Divide);
                        self.advance();
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            token: "/".to_string(),
                            position: pos,
                            expected: Some(vec!["//".to_string()]),
                        });
                    }
                }
                '>' => {
                    self.advance();
                    if self.current_char() == '=' {
                        tokens.push(Token::GreaterEq);
                        self.advance();
                    } else {
                        tokens.push(Token::Greater);
                    }
                }
                '<' => {
                    tokens.push(Token::Less);
                    self.advance();
                }
                '=' => {
                    let pos = self.current_position();
                    self.advance();
                    if self.current_char() == ':' {
                        self.advance();
                        if self.current_char() == '=' {
                            tokens.push(Token::ArithEq);
                            self.advance();
                        } else {
                            return Err(ParseError::UnexpectedToken {
                                token: "=:".to_string(),
                                position: pos,
                                expected: Some(vec!["=:=".to_string()]),
                            });
                        }
                    } else if self.current_char() == '<' {
                        tokens.push(Token::LessEq);
                        self.advance();
                    } else if self.current_char() == '\\' {
                        self.advance();
                        if self.current_char() == '=' {
                            tokens.push(Token::ArithNeq);
                            self.advance();
                        } else {
                            return Err(ParseError::UnexpectedToken {
                                token: "=\\".to_string(),
                                position: pos,
                                expected: Some(vec!["=\\=".to_string()]),
                            });
                        }
                    } else {
                        tokens.push(Token::Unify);
                    }
                }
                '\\' => {
                    let pos = self.current_position();
                    self.advance();
                    if self.current_char() == '=' {
                        tokens.push(Token::NotUnify);
                        self.advance();
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            token: "\\".to_string(),
                            position: pos,
                            expected: Some(vec!["\\=".to_string()]),
                        });
                    }
                }
                ':' => {
                    let pos = self.current_position();
                    self.advance();
                    if self.current_char() == '-' {
                        tokens.push(Token::Rule);
                        self.advance();
                    } else {
                        return Err(ParseError::UnexpectedToken {
                            token: ":".to_string(),
                            position: pos,
                            expected: Some(vec![":-".to_string()]),
                        });
                    }
                }
                '%' => {
                    // Skip comments
                    while self.position < self.input.len() && self.current_char() != '\n' {
                        self.advance();
                    }
                }
                _ if ch.is_ascii_digit() => {
                    tokens.push(self.read_number()?);
                }
                _ if ch.is_ascii_uppercase() || ch == '_' => {
                    tokens.push(Token::Variable(self.read_identifier()?));
                }
                _ if ch.is_ascii_lowercase() => {
                    let identifier = self.read_identifier()?;
                    match identifier.as_str() {
                        "is" => tokens.push(Token::Is),
                        "mod" => tokens.push(Token::Mod),
                        _ => tokens.push(Token::Atom(identifier)),
                    }
                }
                '\'' => {
                    // Quoted atom
                    tokens.push(Token::Atom(self.read_quoted_atom()?));
                }
                _ => {
                    return Err(ParseError::UnexpectedToken {
                        token: ch.to_string(),
                        position: self.current_position(),
                        expected: None,
                    });
                }
            }
        }
        
        // Check for unclosed delimiters
        if let Some((delimiter, open_pos)) = self.paren_stack.pop() {
            return Err(ParseError::UnclosedDelimiter {
                delimiter,
                open_position: open_pos,
                current_position: self.current_position(),
            });
        }
        
        tokens.push(Token::Eof);
        Ok(tokens)
    }
    
    /// Check if a closing delimiter matches the most recent opening delimiter
    fn check_matching_delimiter(&mut self, closing: char) -> ParseResult<()> {
        if let Some((opening, _)) = self.paren_stack.pop() {
            let expected_closing = match opening {
                '(' => ')',
                '[' => ']',
                _ => unreachable!(),
            };
            
            if closing != expected_closing {
                return Err(ParseError::InvalidSyntax {
                    message: format!("Mismatched delimiter: expected '{}', found '{}'", 
                                   expected_closing, closing),
                    position: self.current_position(),
                    suggestion: Some(format!("Check that '{}' has a matching '{}'", 
                                           opening, expected_closing)),
                });
            }
        } else {
            return Err(ParseError::InvalidSyntax {
                message: format!("Unexpected closing delimiter '{}'", closing),
                position: self.current_position(),
                suggestion: Some("Check for extra closing delimiters".to_string()),
            });
        }
        Ok(())
    }
    
    /// Get the current character, or '\0' if at end of input
    fn current_char(&self) -> char {
        if self.position < self.input.len() {
            self.input[self.position]
        } else {
            '\0'
        }
    }
    
    /// Check if the next character after current position is a digit
    fn peek_ahead_for_digit(&self) -> bool {
        if self.position + 1 < self.input.len() {
            self.input[self.position + 1].is_ascii_digit()
        } else {
            false
        }
    }
    
    /// Read a negative number (starts with minus sign)
    fn read_negative_number(&mut self) -> ParseResult<Token> {
        let start_pos = self.current_position();
        self.advance(); // consume '-'
        let start = self.position;
        
        if !self.current_char().is_ascii_digit() {
            return Err(ParseError::InvalidNumber {
                value: "-".to_string(),
                position: start_pos,
                reason: "Expected digit after minus sign".to_string(),
            });
        }
        
        while self.position < self.input.len() && self.current_char().is_ascii_digit() {
            self.advance();
        }
        
        let number_str: String = self.input[start..self.position].iter().collect();
        let number = number_str.parse::<i64>()
            .map_err(|_| ParseError::InvalidNumber {
                value: format!("-{}", number_str),
                position: start_pos,
                reason: "Number too large for 64-bit integer".to_string(),
            })?;
        
        Ok(Token::Number(-number))
    }
    
    /// Advance the position by one character, updating line and column
    fn advance(&mut self) {
        if self.position < self.input.len() {
            if self.input[self.position] == '\n' {
                self.current_line += 1;
                self.current_column = 1;
            } else {
                self.current_column += 1;
            }
            self.position += 1;
        }
    }
    
    /// Skip whitespace characters
    fn skip_whitespace(&mut self) {
        while self.position < self.input.len() && self.current_char().is_whitespace() {
            self.advance();
        }
    }
    
    /// Read an identifier (atom or variable name)
    fn read_identifier(&mut self) -> ParseResult<String> {
        let start = self.position;
        let start_pos = self.current_position();
        
        while self.position < self.input.len() {
            let ch = self.current_char();
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;
            }
        }
        
        let identifier: String = self.input[start..self.position].iter().collect();
        
        if identifier.is_empty() {
            return Err(ParseError::InvalidSyntax {
                message: "Empty identifier".to_string(),
                position: start_pos,
                suggestion: None,
            });
        }
        
        // Validate identifier rules
        if identifier.len() > 1024 {
            return Err(ParseError::InvalidVariable {
                name: identifier,
                position: start_pos,
                reason: "Identifier too long (max 1024 characters)".to_string(),
            });
        }
        
        Ok(identifier)
    }
    
    /// Read a quoted atom (enclosed in single quotes)
    fn read_quoted_atom(&mut self) -> ParseResult<String> {
        let start_pos = self.current_position();
        self.advance(); // consume opening quote
        let mut atom = String::new();
        
        while self.position < self.input.len() && self.current_char() != '\'' {
            let ch = self.current_char();
            
            if ch == '\\' {
                // Handle escape sequences
                self.advance();
                if self.position >= self.input.len() {
                    return Err(ParseError::InvalidSyntax {
                        message: "Unterminated escape sequence in quoted atom".to_string(),
                        position: self.current_position(),
                        suggestion: Some("Add the escaped character or closing quote".to_string()),
                    });
                }
                
                let escaped_char = match self.current_char() {
                    'n' => '\n',
                    't' => '\t',
                    'r' => '\r',
                    '\\' => '\\',
                    '\'' => '\'',
                    ch => ch, // For other characters, include as-is
                };
                
                atom.push(escaped_char);
                self.advance();
            } else {
                atom.push(ch);
                self.advance();
            }
        }
        
        if self.position >= self.input.len() {
            return Err(ParseError::InvalidSyntax {
                message: "Unterminated quoted atom".to_string(),
                position: start_pos,
                suggestion: Some("Add closing single quote".to_string()),
            });
        }
        
        self.advance(); // consume closing quote
        Ok(atom)
    }
    
    /// Read a positive number
    fn read_number(&mut self) -> ParseResult<Token> {
        let start = self.position;
        let start_pos = self.current_position();
        
        while self.position < self.input.len() && self.current_char().is_ascii_digit() {
            self.advance();
        }
        
        let number_str: String = self.input[start..self.position].iter().collect();
        let number = number_str.parse::<i64>()
            .map_err(|_| ParseError::InvalidNumber {
                value: number_str.clone(),
                position: start_pos,
                reason: "Number too large for 64-bit integer".to_string(),
            })?;
        
        Ok(Token::Number(number))
    }
    
    /// Get statistics about the tokenization process
    pub fn get_position_info(&self) -> (usize, usize, usize) {
        (self.current_line, self.current_column, self.position)
    }
    
    /// Check if there are any unclosed delimiters
    pub fn has_unclosed_delimiters(&self) -> bool {
        !self.paren_stack.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_tokens() {
        let mut tokenizer = Tokenizer::new("hello world 123");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 4); // hello, world, 123, EOF
        assert_eq!(tokens[0], Token::Atom("hello".to_string()));
        assert_eq!(tokens[1], Token::Atom("world".to_string()));
        assert_eq!(tokens[2], Token::Number(123));
        assert_eq!(tokens[3], Token::Eof);
    }

    #[test]
    fn test_variables() {
        let mut tokenizer = Tokenizer::new("X Y _var Variable123");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert!(matches!(tokens[0], Token::Variable(_)));
        assert!(matches!(tokens[1], Token::Variable(_)));
        assert!(matches!(tokens[2], Token::Variable(_)));
        assert!(matches!(tokens[3], Token::Variable(_)));
    }

    #[test]
    fn test_operators() {
        let mut tokenizer = Tokenizer::new(":- =:= =\\= >= =< \\= is mod");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert_eq!(tokens[0], Token::Rule);
        assert_eq!(tokens[1], Token::ArithEq);
        assert_eq!(tokens[2], Token::ArithNeq);
        assert_eq!(tokens[3], Token::GreaterEq);
        assert_eq!(tokens[4], Token::LessEq);
        assert_eq!(tokens[5], Token::NotUnify);
        assert_eq!(tokens[6], Token::Is);
        assert_eq!(tokens[7], Token::Mod);
    }

    #[test]
    fn test_delimiters() {
        let mut tokenizer = Tokenizer::new("( ) [ ] , . | ? !");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert_eq!(tokens[0], Token::LeftParen);
        assert_eq!(tokens[1], Token::RightParen);
        assert_eq!(tokens[2], Token::LeftBracket);
        assert_eq!(tokens[3], Token::RightBracket);
        assert_eq!(tokens[4], Token::Comma);
        assert_eq!(tokens[5], Token::Dot);
        assert_eq!(tokens[6], Token::Pipe);
        assert_eq!(tokens[7], Token::Question);
        assert_eq!(tokens[8], Token::Cut);
    }

    #[test]
    fn test_arithmetic() {
        let mut tokenizer = Tokenizer::new("+ - * // > < = -42");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert_eq!(tokens[0], Token::Plus);
        assert_eq!(tokens[1], Token::Minus);
        assert_eq!(tokens[2], Token::Multiply);
        assert_eq!(tokens[3], Token::Divide);
        assert_eq!(tokens[4], Token::Greater);
        assert_eq!(tokens[5], Token::Less);
        assert_eq!(tokens[6], Token::Unify);
        assert_eq!(tokens[7], Token::Number(-42));
    }

    #[test]
    fn test_quoted_atoms() {
        let mut tokenizer = Tokenizer::new("'hello world' 'with\\nnewline'");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert_eq!(tokens[0], Token::Atom("hello world".to_string()));
        assert_eq!(tokens[1], Token::Atom("with\nnewline".to_string()));
    }

    #[test]
    fn test_comments() {
        let mut tokenizer = Tokenizer::new("hello % this is a comment\nworld");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert_eq!(tokens.len(), 3); // hello, world, EOF
        assert_eq!(tokens[0], Token::Atom("hello".to_string()));
        assert_eq!(tokens[1], Token::Atom("world".to_string()));
    }

    #[test]
    fn test_error_unclosed_paren() {
        let mut tokenizer = Tokenizer::new("hello(world");
        let result = tokenizer.tokenize();
        
        assert!(result.is_err());
        if let Err(ParseError::UnclosedDelimiter { delimiter, .. }) = result {
            assert_eq!(delimiter, '(');
        } else {
            panic!("Expected UnclosedDelimiter error");
        }
    }

    #[test]
    fn test_error_mismatched_delimiters() {
        let mut tokenizer = Tokenizer::new("hello(world]");
        let result = tokenizer.tokenize();
        
        assert!(result.is_err());
        if let Err(ParseError::InvalidSyntax { message, .. }) = result {
            assert!(message.contains("Mismatched delimiter"));
        } else {
            panic!("Expected InvalidSyntax error");
        }
    }

    #[test]
    fn test_position_tracking() {
        let mut tokenizer = Tokenizer::new("hello\nworld");
        let tokens = tokenizer.tokenize().unwrap();
        
        // Position tracking is internal, but we can verify it doesn't crash
        assert_eq!(tokens.len(), 3); // hello, world, EOF
    }

    #[test]
    fn test_complex_expression() {
        let mut tokenizer = Tokenizer::new("parent(X, Y) :- father(X, Y), male(X).");
        let tokens = tokenizer.tokenize().unwrap();
        
        // Should tokenize without errors
        assert!(tokens.len() > 10);
        assert_eq!(tokens[0], Token::Atom("parent".to_string()));
        assert_eq!(tokens[1], Token::LeftParen);
        // ... and so on
    }

    #[test]
    fn test_negative_numbers() {
        let mut tokenizer = Tokenizer::new("X is -42 + -1");
        let tokens = tokenizer.tokenize().unwrap();
        
        assert_eq!(tokens[2], Token::Number(-42));
        assert_eq!(tokens[4], Token::Number(-1));
    }
}