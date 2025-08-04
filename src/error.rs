// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: error.rs
// Creator: Jonas Forsman

//! Error types and position tracking for the Prolog parser and runtime
//! 
//! This module contains all error types used throughout the Neorusticus library,
//! including detailed position information for better error reporting.

use std::fmt;

/// Position information for better error reporting
#[derive(Debug, Clone, PartialEq)]
pub struct Position {
    pub line: usize,
    pub column: usize,
    pub offset: usize,
}

impl Position {
    pub fn new(line: usize, column: usize, offset: usize) -> Self {
        Position { line, column, offset }
    }
    
    pub fn start() -> Self {
        Position { line: 1, column: 1, offset: 0 }
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {}, column {}", self.line, self.column)
    }
}

/// Enhanced error types with position information and suggestions
#[derive(Debug)]
pub enum ParseError {
    UnexpectedToken {
        token: String,
        position: Position,
        expected: Option<Vec<String>>,
    },
    UnexpectedEof {
        position: Position,
        expected: Option<Vec<String>>,
    },
    InvalidNumber {
        value: String,
        position: Position,
        reason: String,
    },
    InvalidSyntax {
        message: String,
        position: Position,
        suggestion: Option<String>,
    },
    UnclosedDelimiter {
        delimiter: char,
        open_position: Position,
        current_position: Position,
    },
    InvalidVariable {
        name: String,
        position: Position,
        reason: String,
    },
    InvalidAtom {
        name: String,
        position: Position,
        reason: String,
    },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::UnexpectedToken { token, position, expected } => {
                write!(f, "Unexpected token '{}' at {}", token, position)?;
                if let Some(expected_tokens) = expected {
                    write!(f, ". Expected one of: {}", expected_tokens.join(", "))?;
                }
                Ok(())
            }
            ParseError::UnexpectedEof { position, expected } => {
                write!(f, "Unexpected end of input at {}", position)?;
                if let Some(expected_tokens) = expected {
                    write!(f, ". Expected one of: {}", expected_tokens.join(", "))?;
                }
                Ok(())
            }
            ParseError::InvalidNumber { value, position, reason } => {
                write!(f, "Invalid number '{}' at {}: {}", value, position, reason)
            }
            ParseError::InvalidSyntax { message, position, suggestion } => {
                write!(f, "Invalid syntax at {}: {}", position, message)?;
                if let Some(hint) = suggestion {
                    write!(f, ". Suggestion: {}", hint)?;
                }
                Ok(())
            }
            ParseError::UnclosedDelimiter { delimiter, open_position, current_position } => {
                write!(f, "Unclosed '{}' opened at {} (reached {})", 
                       delimiter, open_position, current_position)
            }
            ParseError::InvalidVariable { name, position, reason } => {
                write!(f, "Invalid variable '{}' at {}: {}", name, position, reason)
            }
            ParseError::InvalidAtom { name, position, reason } => {
                write!(f, "Invalid atom '{}' at {}: {}", name, position, reason)
            }
        }
    }
}

impl std::error::Error for ParseError {}

/// Runtime errors for execution
#[derive(Debug)]
pub enum RuntimeError {
    ArithmeticError {
        operation: String,
        operands: Vec<crate::ast::Term>,
        reason: String,
    },
    DivisionByZero {
        expression: crate::ast::Term,
    },
    TypeMismatch {
        expected: String,
        found: crate::ast::Term,
        context: String,
    },
    UninstantiatedVariable {
        variable: String,
        context: String,
    },
    PredicateNotFound {
        functor: String,
        arity: usize,
        suggestion: Option<String>,
    },
    StackOverflow {
        depth: usize,
        predicate: String,
    },
    CutOutsideRule,
    InvalidListStructure {
        term: crate::ast::Term,
        expected: String,
    },
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RuntimeError::ArithmeticError { operation, operands, reason } => {
                write!(f, "Arithmetic error in '{}' with operands {:?}: {}", 
                       operation, operands, reason)
            }
            RuntimeError::DivisionByZero { expression } => {
                write!(f, "Division by zero in expression: {}", expression)
            }
            RuntimeError::TypeMismatch { expected, found, context } => {
                write!(f, "Type mismatch in {}: expected {}, found {}", 
                       context, expected, found)
            }
            RuntimeError::UninstantiatedVariable { variable, context } => {
                write!(f, "Variable '{}' is not sufficiently instantiated in {}", 
                       variable, context)
            }
            RuntimeError::PredicateNotFound { functor, arity, suggestion } => {
                write!(f, "Undefined predicate: {}/{}", functor, arity)?;
                if let Some(hint) = suggestion {
                    write!(f, ". Did you mean: {}", hint)?;
                }
                Ok(())
            }
            RuntimeError::StackOverflow { depth, predicate } => {
                write!(f, "Stack overflow (depth {}) in predicate: {}", depth, predicate)
            }
            RuntimeError::CutOutsideRule => {
                write!(f, "Cut (!) can only be used inside rule bodies")
            }
            RuntimeError::InvalidListStructure { term, expected } => {
                write!(f, "Invalid list structure: expected {}, found {}", expected, term)
            }
        }
    }
}

impl std::error::Error for RuntimeError {}

/// Result types for better error handling
pub type ParseResult<T> = Result<T, ParseError>;
pub type RuntimeResult<T> = Result<T, RuntimeError>;

/// Calculate Levenshtein distance for predicate suggestions
pub fn levenshtein_distance(s1: &str, s2: &str) -> usize {
    let len1 = s1.len();
    let len2 = s2.len();
    let mut matrix = vec![vec![0; len2 + 1]; len1 + 1];
    
    for i in 0..=len1 {
        matrix[i][0] = i;
    }
    for j in 0..=len2 {
        matrix[0][j] = j;
    }
    
    for (i, c1) in s1.chars().enumerate() {
        for (j, c2) in s2.chars().enumerate() {
            let cost = if c1 == c2 { 0 } else { 1 };
            matrix[i + 1][j + 1] = std::cmp::min(
                std::cmp::min(
                    matrix[i][j + 1] + 1,     // deletion
                    matrix[i + 1][j] + 1,     // insertion
                ),
                matrix[i][j] + cost,          // substitution
            );
        }
    }
    
    matrix[len1][len2]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_position_display() {
        let pos = Position::new(5, 10, 42);
        assert_eq!(format!("{}", pos), "line 5, column 10");
    }

    #[test]
    fn test_levenshtein_distance() {
        assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
        assert_eq!(levenshtein_distance("append", "appendd"), 1);  
        assert_eq!(levenshtein_distance("length", "lentgh"), 2);
        assert_eq!(levenshtein_distance("same", "same"), 0);
    }

    #[test]
    fn test_parse_error_display() {
        let pos = Position::new(1, 5, 4);
        let error = ParseError::UnexpectedToken {
            token: "(".to_string(),
            position: pos,
            expected: Some(vec!["atom".to_string(), "variable".to_string()]),
        };
        
        let display = format!("{}", error);
        assert!(display.contains("Unexpected token '('"));
        assert!(display.contains("line 1, column 5"));
        assert!(display.contains("Expected one of: atom, variable"));
    }
}