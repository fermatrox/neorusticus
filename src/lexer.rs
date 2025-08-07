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
    /// 
    /// This is primarily used for error messages to provide clear feedback
    /// about what token was expected. For example, when a parser expects
    /// a closing parenthesis, it can say "Expected ')'" rather than
    /// "Expected RightParen".
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
    /// 
    /// In Prolog, only certain tokens can begin an expression. This method
    /// helps the parser validate syntax by checking if a token is valid
    /// at the beginning of an expression context. For example, a closing
    /// parenthesis ')' cannot start an expression, but an atom or number can.
    pub fn can_start_expression(&self) -> bool {
        matches!(self, 
            Token::Atom(_) | Token::Variable(_) | Token::Number(_) | 
            Token::LeftParen | Token::LeftBracket | Token::Cut
        )
    }
}

/// Tokenizer for Prolog source code with position tracking
/// 
/// The tokenizer maintains state about the current position in the input,
/// tracks line and column numbers for error reporting, and keeps a stack
/// of open delimiters to detect mismatched parentheses and brackets.
pub struct Tokenizer {
    /// The input string converted to a vector of characters for easy indexing
    input: Vec<char>,
    /// Current position in the input vector (0-based index)
    position: usize,
    /// Current line number (1-based, following text editor conventions)
    current_line: usize,
    /// Current column within the line (1-based)
    current_column: usize,
    /// Stack tracking open delimiters for matching validation
    /// Each entry contains the delimiter character and its position for error reporting
    paren_stack: Vec<(char, Position)>,
}

impl Tokenizer {
    /// Create a new tokenizer for the given input string
    /// 
    /// Initializes the tokenizer with the input converted to a character vector
    /// for efficient random access. Position tracking starts at line 1, column 1,
    /// which matches how most text editors display positions.
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
    /// 
    /// Creates a Position struct that captures the current line, column,
    /// and absolute offset. This is used for error reporting to show
    /// exactly where in the source code an error occurred.
    fn current_position(&self) -> Position {
        Position::new(self.current_line, self.current_column, self.position)
    }
    
    /// Tokenize the entire input into a vector of tokens
    /// 
    /// This is the main entry point for tokenization. It processes the input
    /// character by character, recognizing different token types and handling
    /// special cases like multi-character operators, quoted atoms, and comments.
    /// 
    /// The tokenization process:
    /// 1. Skip any leading whitespace
    /// 2. Examine the current character to determine token type
    /// 3. Consume the appropriate characters for that token type
    /// 4. Add the token to the result vector
    /// 5. Repeat until end of input
    /// 6. Verify all delimiters are properly closed
    /// 7. Add EOF token to mark the end
    pub fn tokenize(&mut self) -> ParseResult<Vec<Token>> {
        let mut tokens = Vec::new();
        
        // Main tokenization loop - process until we've consumed all input
        while self.position < self.input.len() {
            // Skip any whitespace (spaces, tabs, newlines) between tokens
            self.skip_whitespace();
            
            // Check if we've reached the end after skipping whitespace
            if self.position >= self.input.len() {
                break;
            }
            
            // Get the current character and save position for error reporting
            let ch = self.current_char();
            let pos = self.current_position();
            
            // Large match statement to handle each possible character
            // Characters are grouped by type (delimiters, operators, etc.)
            match ch {
                // === Delimiter tokens (single character) ===
                '(' => {
                    // Track opening parenthesis for matching validation
                    self.paren_stack.push(('(', pos));
                    tokens.push(Token::LeftParen);
                    self.advance();
                }
                ')' => {
                    // Verify this closing paren matches an opening one
                    self.check_matching_delimiter(')')?;
                    tokens.push(Token::RightParen);
                    self.advance();
                }
                '[' => {
                    // Track opening bracket for list syntax
                    self.paren_stack.push(('[', pos));
                    tokens.push(Token::LeftBracket);
                    self.advance();
                }
                ']' => {
                    // Verify this closing bracket matches an opening one
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
                    // Pipe is used in list tail syntax: [Head|Tail]
                    tokens.push(Token::Pipe);
                    self.advance();
                }
                '?' => {
                    // Question mark can end queries in some Prolog systems
                    tokens.push(Token::Question);
                    self.advance();
                }
                '!' => {
                    // Cut operator - prevents backtracking
                    tokens.push(Token::Cut);
                    self.advance();
                }
                
                // === Arithmetic operators ===
                '+' => {
                    tokens.push(Token::Plus);
                    self.advance();
                }
                '-' => {
                    // Minus is special: could be subtraction operator or negative number
                    // Check if the next character is a digit to determine which
                    if self.peek_ahead_for_digit() {
                        // It's a negative number like -42
                        tokens.push(self.read_negative_number()?);
                    } else {
                        // It's the subtraction operator
                        tokens.push(Token::Minus);
                        self.advance();
                    }
                }
                '*' => {
                    tokens.push(Token::Multiply);
                    self.advance();
                }
                '/' => {
                    // Division in Prolog is '//' (integer division)
                    // A single '/' is invalid, so we need to check for the second '/'
                    let pos = self.current_position();
                    self.advance();
                    if self.current_char() == '/' {
                        tokens.push(Token::Divide);
                        self.advance();
                    } else {
                        // Single '/' is not valid in Prolog
                        return Err(ParseError::UnexpectedToken {
                            token: "/".to_string(),
                            position: pos,
                            expected: Some(vec!["//".to_string()]),
                        });
                    }
                }
                
                // === Comparison operators ===
                '>' => {
                    // Could be '>' or '>='
                    self.advance();
                    if self.current_char() == '=' {
                        tokens.push(Token::GreaterEq);
                        self.advance();
                    } else {
                        tokens.push(Token::Greater);
                    }
                }
                '<' => {
                    // Less than (note: '<=' is handled under '=' for Prolog's '=<')
                    tokens.push(Token::Less);
                    self.advance();
                }
                
                // === Complex operators starting with '=' ===
                '=' => {
                    // '=' can start multiple operators:
                    // '=' (unification), '=:=' (arithmetic equal), 
                    // '=<' (less than or equal), '=\=' (arithmetic not equal)
                    let pos = self.current_position();
                    self.advance();
                    
                    if self.current_char() == ':' {
                        // Could be '=:=' (arithmetic equality)
                        self.advance();
                        if self.current_char() == '=' {
                            tokens.push(Token::ArithEq);
                            self.advance();
                        } else {
                            // '=:' without final '=' is invalid
                            return Err(ParseError::UnexpectedToken {
                                token: "=:".to_string(),
                                position: pos,
                                expected: Some(vec!["=:=".to_string()]),
                            });
                        }
                    } else if self.current_char() == '<' {
                        // '=<' is Prolog's less than or equal (not '<=')
                        tokens.push(Token::LessEq);
                        self.advance();
                    } else if self.current_char() == '\\' {
                        // Could be '=\=' (arithmetic not equal)
                        self.advance();
                        if self.current_char() == '=' {
                            tokens.push(Token::ArithNeq);
                            self.advance();
                        } else {
                            // '=\' without final '=' is invalid
                            return Err(ParseError::UnexpectedToken {
                                token: "=\\".to_string(),
                                position: pos,
                                expected: Some(vec!["=\\=".to_string()]),
                            });
                        }
                    } else {
                        // Just '=' by itself is unification
                        tokens.push(Token::Unify);
                    }
                }
                
                // === Operators starting with '\' ===
                '\\' => {
                    // '\=' is not-unifiable operator
                    let pos = self.current_position();
                    self.advance();
                    if self.current_char() == '=' {
                        tokens.push(Token::NotUnify);
                        self.advance();
                    } else {
                        // '\' by itself is invalid
                        return Err(ParseError::UnexpectedToken {
                            token: "\\".to_string(),
                            position: pos,
                            expected: Some(vec!["\\=".to_string()]),
                        });
                    }
                }
                
                // === Rule operator ':-' ===
                ':' => {
                    // ':' must be followed by '-' to form ':-' (rule operator)
                    let pos = self.current_position();
                    self.advance();
                    if self.current_char() == '-' {
                        tokens.push(Token::Rule);
                        self.advance();
                    } else {
                        // ':' by itself is invalid
                        return Err(ParseError::UnexpectedToken {
                            token: ":".to_string(),
                            position: pos,
                            expected: Some(vec![":-".to_string()]),
                        });
                    }
                }
                
                // === Comments ===
                '%' => {
                    // '%' starts a single-line comment in Prolog
                    // Skip everything until the end of the line
                    while self.position < self.input.len() && self.current_char() != '\n' {
                        self.advance();
                    }
                    // The newline will be consumed as whitespace in the next iteration
                }
                
                // === Numbers, identifiers, and quoted atoms ===
                _ if ch.is_ascii_digit() => {
                    // Positive number literal
                    tokens.push(self.read_number()?);
                }
                _ if ch.is_ascii_uppercase() || ch == '_' => {
                    // Variable (starts with uppercase or underscore)
                    tokens.push(Token::Variable(self.read_identifier()?));
                }
                _ if ch.is_ascii_lowercase() => {
                    // Could be an atom or a keyword (is, mod)
                    let identifier = self.read_identifier()?;
                    match identifier.as_str() {
                        "is" => tokens.push(Token::Is),
                        "mod" => tokens.push(Token::Mod),
                        _ => tokens.push(Token::Atom(identifier)),
                    }
                }
                '\'' => {
                    // Quoted atom - can contain spaces and special characters
                    tokens.push(Token::Atom(self.read_quoted_atom()?));
                }
                
                // === Invalid character ===
                _ => {
                    // Character not recognized as part of Prolog syntax
                    return Err(ParseError::UnexpectedToken {
                        token: ch.to_string(),
                        position: self.current_position(),
                        expected: None,
                    });
                }
            }
        }
        
        // After processing all input, check for unclosed delimiters
        // If the stack isn't empty, we have unmatched opening delimiters
        if let Some((delimiter, open_pos)) = self.paren_stack.pop() {
            return Err(ParseError::UnclosedDelimiter {
                delimiter,
                open_position: open_pos,
                current_position: self.current_position(),
            });
        }
        
        // Add EOF token to mark the end of the token stream
        tokens.push(Token::Eof);
        Ok(tokens)
    }
    
    /// Check if a closing delimiter matches the most recent opening delimiter
    /// 
    /// This function maintains the delimiter stack to ensure that parentheses
    /// and brackets are properly nested. For example, "(]" is invalid because
    /// the closing bracket doesn't match the opening parenthesis.
    /// 
    /// The algorithm:
    /// 1. Pop the most recent opening delimiter from the stack
    /// 2. Check if it matches the closing delimiter we found
    /// 3. If not, report a mismatch error
    /// 4. If the stack is empty, report an unexpected closing delimiter
    fn check_matching_delimiter(&mut self, closing: char) -> ParseResult<()> {
        if let Some((opening, _)) = self.paren_stack.pop() {
            // Determine what the closing delimiter should be based on the opening
            let expected_closing = match opening {
                '(' => ')',
                '[' => ']',
                _ => unreachable!(),  // We only push '(' and '[' to the stack
            };
            
            // Check if the actual closing delimiter matches the expected one
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
            // No opening delimiter on the stack - this closing delimiter is unexpected
            return Err(ParseError::InvalidSyntax {
                message: format!("Unexpected closing delimiter '{}'", closing),
                position: self.current_position(),
                suggestion: Some("Check for extra closing delimiters".to_string()),
            });
        }
        Ok(())
    }
    
    /// Get the current character, or '\0' if at end of input
    /// 
    /// Returns the character at the current position in the input.
    /// Returns null character '\0' as a sentinel value when we've
    /// reached the end of the input to avoid index out of bounds.
    fn current_char(&self) -> char {
        if self.position < self.input.len() {
            self.input[self.position]
        } else {
            '\0'
        }
    }
    
    /// Check if the next character after current position is a digit
    /// 
    /// This is used to disambiguate the minus sign: "-5" is a negative
    /// number, but "- 5" or "-X" has minus as an operator. We look ahead
    /// one character without consuming it to make this determination.
    fn peek_ahead_for_digit(&self) -> bool {
        if self.position + 1 < self.input.len() {
            self.input[self.position + 1].is_ascii_digit()
        } else {
            false
        }
    }
    
    /// Read a negative number (starts with minus sign)
    /// 
    /// Called when we encounter a minus sign followed immediately by a digit.
    /// This function:
    /// 1. Consumes the minus sign
    /// 2. Reads all following digits
    /// 3. Parses the complete string (including minus) as an i64
    /// 
    /// Special handling for i64::MIN (-9223372036854775808):
    /// The positive part (9223372036854775808) would overflow i64::MAX,
    /// so we parse the entire negative string directly rather than
    /// parsing positive and negating.
    fn read_negative_number(&mut self) -> ParseResult<Token> {
        let start_pos = self.current_position();
        self.advance(); // consume '-'
        let start = self.position;
        
        // Verify there's actually a digit after the minus
        if !self.current_char().is_ascii_digit() {
            return Err(ParseError::InvalidNumber {
                value: "-".to_string(),
                position: start_pos,
                reason: "Expected digit after minus sign".to_string(),
            });
        }
        
        // Consume all consecutive digits
        while self.position < self.input.len() && self.current_char().is_ascii_digit() {
            self.advance();
        }
        
        // Extract the digit portion and create the full negative number string
        let number_str: String = self.input[start..self.position].iter().collect();
        
        // Parse the complete negative number string
        // This handles i64::MIN correctly since we're parsing "-9223372036854775808"
        // directly rather than parsing "9223372036854775808" and negating
        let full_str = format!("-{}", number_str);
        let number = full_str.parse::<i64>()
            .map_err(|_| ParseError::InvalidNumber {
                value: full_str.clone(),
                position: start_pos,
                reason: "Number too large for 64-bit integer".to_string(),
            })?;
        
        Ok(Token::Number(number))
    }
    
    /// Advance the position by one character, updating line and column
    /// 
    /// Moves forward in the input by one character and updates position tracking.
    /// When we encounter a newline, we increment the line number and reset
    /// the column to 1. This maintains accurate position information for
    /// error reporting.
    fn advance(&mut self) {
        if self.position < self.input.len() {
            if self.input[self.position] == '\n' {
                // Moving to a new line
                self.current_line += 1;
                self.current_column = 1;
            } else {
                // Moving to next column on same line
                self.current_column += 1;
            }
            self.position += 1;
        }
    }
    
    /// Skip whitespace characters
    /// 
    /// Consumes consecutive whitespace characters (spaces, tabs, newlines, etc.)
    /// until we reach a non-whitespace character or the end of input.
    /// This is called between tokens to ignore formatting whitespace.
    fn skip_whitespace(&mut self) {
        while self.position < self.input.len() && self.current_char().is_whitespace() {
            self.advance();
        }
    }
    
    /// Read an identifier (atom or variable name)
    /// 
    /// Identifiers in Prolog consist of alphanumeric characters and underscores.
    /// This function reads consecutive valid identifier characters and returns
    /// them as a string. The caller determines whether it's an atom or variable
    /// based on the first character (lowercase = atom, uppercase/underscore = variable).
    /// 
    /// Also enforces a maximum identifier length of 1024 characters to prevent
    /// excessive memory usage from malformed input.
    fn read_identifier(&mut self) -> ParseResult<String> {
        let start = self.position;
        let start_pos = self.current_position();
        
        // Consume all valid identifier characters
        while self.position < self.input.len() {
            let ch = self.current_char();
            if ch.is_alphanumeric() || ch == '_' {
                self.advance();
            } else {
                break;  // Found a non-identifier character
            }
        }
        
        // Extract the identifier string from the input
        let identifier: String = self.input[start..self.position].iter().collect();
        
        // Validate the identifier
        if identifier.is_empty() {
            return Err(ParseError::InvalidSyntax {
                message: "Empty identifier".to_string(),
                position: start_pos,
                suggestion: None,
            });
        }
        
        // Check for excessively long identifiers (potential DoS or memory issue)
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
    /// 
    /// Quoted atoms in Prolog allow for atoms that contain spaces, special
    /// characters, or start with uppercase letters. They're enclosed in
    /// single quotes and support escape sequences.
    /// 
    /// Escape sequences supported:
    /// - \n -> newline
    /// - \t -> tab
    /// - \r -> carriage return
    /// - \\ -> backslash
    /// - \' -> single quote
    /// - \x -> x (any other character is treated literally)
    /// 
    /// The function reads until it finds the closing quote or end of input.
    fn read_quoted_atom(&mut self) -> ParseResult<String> {
        let start_pos = self.current_position();
        self.advance(); // consume opening quote
        let mut atom = String::new();
        
        // Read characters until we find the closing quote
        while self.position < self.input.len() && self.current_char() != '\'' {
            let ch = self.current_char();
            
            if ch == '\\' {
                // Handle escape sequences
                self.advance();
                
                // Check that there's a character after the backslash
                if self.position >= self.input.len() {
                    return Err(ParseError::InvalidSyntax {
                        message: "Unterminated escape sequence in quoted atom".to_string(),
                        position: self.current_position(),
                        suggestion: Some("Add the escaped character or closing quote".to_string()),
                    });
                }
                
                // Process the escape sequence
                let escaped_char = match self.current_char() {
                    'n' => '\n',    // Newline
                    't' => '\t',    // Tab
                    'r' => '\r',    // Carriage return
                    '\\' => '\\',   // Literal backslash
                    '\'' => '\'',   // Literal single quote
                    ch => ch,       // Any other character is taken literally
                };
                
                atom.push(escaped_char);
                self.advance();
            } else {
                // Regular character - add it to the atom
                atom.push(ch);
                self.advance();
            }
        }
        
        // Check that we found the closing quote
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
    /// 
    /// Reads consecutive digits and parses them as a 64-bit signed integer.
    /// This is simpler than read_negative_number since we don't need special
    /// handling for overflow cases - positive overflow is straightforward to detect.
    fn read_number(&mut self) -> ParseResult<Token> {
        let start = self.position;
        let start_pos = self.current_position();
        
        // Consume all consecutive digits
        while self.position < self.input.len() && self.current_char().is_ascii_digit() {
            self.advance();
        }
        
        // Extract and parse the number string
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
    /// 
    /// Returns the current position information as a tuple of
    /// (line number, column number, absolute position).
    /// Useful for debugging and for providing context in error messages.
    pub fn get_position_info(&self) -> (usize, usize, usize) {
        (self.current_line, self.current_column, self.position)
    }
    
    /// Check if there are any unclosed delimiters
    /// 
    /// Returns true if the delimiter stack is not empty, indicating that
    /// some opening parentheses or brackets haven't been closed.
    /// This is useful for providing early error detection in interactive
    /// environments where input might be incomplete.
    pub fn has_unclosed_delimiters(&self) -> bool {
        !self.paren_stack.is_empty()
    }
}

// Link to the test module
#[cfg(test)]
#[path = "lexer_tests.rs"]
mod tests;