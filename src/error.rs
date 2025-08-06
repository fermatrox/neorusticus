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
/// 
/// Tracks the exact location in source code where tokens or errors occur.
/// This is essential for providing helpful error messages to users.
#[derive(Debug, Clone, PartialEq)]
pub struct Position {
    /// Line number (1-indexed, following standard text editor conventions)
    pub line: usize,
    /// Column number within the line (1-indexed)
    pub column: usize,
    /// Absolute character offset from the start of the input (0-indexed)
    pub offset: usize,
}

impl Position {
    /// Create a new position with specific coordinates
    /// 
    /// # Arguments
    /// * `line` - The line number (typically starts at 1)
    /// * `column` - The column number within the line (typically starts at 1)
    /// * `offset` - The absolute character offset from input start (starts at 0)
    pub fn new(line: usize, column: usize, offset: usize) -> Self {
        Position { line, column, offset }
    }
    
    /// Create a position representing the start of input
    /// 
    /// Returns a position at line 1, column 1, offset 0, which is the
    /// conventional starting position for text files and source code.
    pub fn start() -> Self {
        Position { line: 1, column: 1, offset: 0 }
    }
}

impl fmt::Display for Position {
    /// Format the position for human-readable error messages
    /// 
    /// Displays as "line X, column Y" format, which is familiar to users
    /// from compiler and editor error messages. The offset is not shown
    /// as it's less meaningful to users than line/column coordinates.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {}, column {}", self.line, self.column)
    }
}

/// Enhanced error types with position information and suggestions
/// 
/// ParseError represents all possible parsing failures that can occur when
/// tokenizing or parsing Prolog source code. Each variant includes position
/// information for precise error reporting and optional suggestions for fixes.
#[derive(Debug)]
pub enum ParseError {
    /// An unexpected token was encountered during parsing
    UnexpectedToken {
        /// The actual token that was found
        token: String,
        /// Where in the source the unexpected token appeared
        position: Position,
        /// Optional list of tokens that were expected instead
        expected: Option<Vec<String>>,
    },
    /// The input ended unexpectedly while parsing was incomplete
    UnexpectedEof {
        /// Where the input ended
        position: Position,
        /// What tokens would have been valid to continue parsing
        expected: Option<Vec<String>>,
    },
    /// A number literal could not be parsed correctly
    InvalidNumber {
        /// The string that was supposed to be a number
        value: String,
        /// Where the invalid number appeared
        position: Position,
        /// Explanation of why the number is invalid (e.g., "too large", "invalid format")
        reason: String,
    },
    /// General syntax error for complex parsing failures
    InvalidSyntax {
        /// Description of what went wrong
        message: String,
        /// Where the syntax error was detected
        position: Position,
        /// Optional hint for how to fix the error
        suggestion: Option<String>,
    },
    /// A delimiter (parenthesis, bracket) was opened but never closed
    UnclosedDelimiter {
        /// The opening delimiter character ('(', '[', etc.)
        delimiter: char,
        /// Where the delimiter was opened
        open_position: Position,
        /// Where parsing ended without finding the closing delimiter
        current_position: Position,
    },
    /// A variable name violates Prolog naming rules
    InvalidVariable {
        /// The problematic variable name
        name: String,
        /// Where the invalid variable appeared
        position: Position,
        /// Explanation of the naming rule violation
        reason: String,
    },
    /// An atom name violates Prolog naming rules
    InvalidAtom {
        /// The problematic atom name
        name: String,
        /// Where the invalid atom appeared
        position: Position,
        /// Explanation of the naming rule violation
        reason: String,
    },
}

impl fmt::Display for ParseError {
    /// Format parse errors into human-readable messages
    /// 
    /// Each error type is formatted with:
    /// 1. A clear description of what went wrong
    /// 2. The position where the error occurred
    /// 3. Optional context like expected tokens or suggestions
    /// 
    /// The messages are designed to be helpful for users debugging their Prolog code.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ParseError::UnexpectedToken { token, position, expected } => {
                // Basic error: "Unexpected token 'X' at line Y, column Z"
                write!(f, "Unexpected token '{}' at {}", token, position)?;
                // Add expected tokens if provided: ". Expected one of: A, B, C"
                if let Some(expected_tokens) = expected {
                    write!(f, ". Expected one of: {}", expected_tokens.join(", "))?;
                }
                Ok(())
            }
            ParseError::UnexpectedEof { position, expected } => {
                // EOF is special - users need to know input ended prematurely
                write!(f, "Unexpected end of input at {}", position)?;
                if let Some(expected_tokens) = expected {
                    write!(f, ". Expected one of: {}", expected_tokens.join(", "))?;
                }
                Ok(())
            }
            ParseError::InvalidNumber { value, position, reason } => {
                // Numbers can fail for various reasons (overflow, invalid format, etc.)
                write!(f, "Invalid number '{}' at {}: {}", value, position, reason)
            }
            ParseError::InvalidSyntax { message, position, suggestion } => {
                // Generic syntax errors with optional fix suggestions
                write!(f, "Invalid syntax at {}: {}", position, message)?;
                if let Some(hint) = suggestion {
                    // Suggestions help users fix their code
                    write!(f, ". Suggestion: {}", hint)?;
                }
                Ok(())
            }
            ParseError::UnclosedDelimiter { delimiter, open_position, current_position } => {
                // Shows both where delimiter was opened and where parsing ended
                // This helps users find the missing closing delimiter
                write!(f, "Unclosed '{}' opened at {} (reached {})", 
                       delimiter, open_position, current_position)
            }
            ParseError::InvalidVariable { name, position, reason } => {
                // Variable naming rules are strict in Prolog (uppercase/underscore start)
                write!(f, "Invalid variable '{}' at {}: {}", name, position, reason)
            }
            ParseError::InvalidAtom { name, position, reason } => {
                // Atom naming rules (lowercase start, or quoted)
                write!(f, "Invalid atom '{}' at {}: {}", name, position, reason)
            }
        }
    }
}

impl std::error::Error for ParseError {}

/// Runtime errors for execution
/// 
/// RuntimeError represents failures that occur during query execution,
/// after successful parsing. These include type errors, arithmetic failures,
/// undefined predicates, and resource exhaustion (stack overflow).
#[derive(Debug)]
pub enum RuntimeError {
    /// An arithmetic operation failed (overflow, invalid operands, etc.)
    ArithmeticError {
        /// The operation that failed ("+", "-", "*", etc.)
        operation: String,
        /// The operands that caused the failure
        operands: Vec<crate::ast::Term>,
        /// Explanation of why the operation failed
        reason: String,
    },
    /// Attempted division by zero
    DivisionByZero {
        /// The complete expression that contained the division by zero
        expression: crate::ast::Term,
    },
    /// A term has the wrong type for an operation
    TypeMismatch {
        /// What type was expected (e.g., "number", "atom", "list")
        expected: String,
        /// The actual term that was found
        found: crate::ast::Term,
        /// Where the type check occurred (e.g., "arithmetic evaluation")
        context: String,
    },
    /// A variable needs a value but doesn't have one
    UninstantiatedVariable {
        /// Name of the unbound variable
        variable: String,
        /// Where the variable needed to be instantiated
        context: String,
    },
    /// Attempted to call a predicate that doesn't exist
    PredicateNotFound {
        /// The predicate name (functor)
        functor: String,
        /// The number of arguments (arity)
        arity: usize,
        /// Optional suggestion for a similar predicate (using Levenshtein distance)
        suggestion: Option<String>,
    },
    /// Recursion depth exceeded the safety limit
    StackOverflow {
        /// How deep the stack was when overflow occurred
        depth: usize,
        /// Which predicate was being called when overflow happened
        predicate: String,
    },
    /// Cut (!) operator used outside of a rule body
    CutOutsideRule,
    /// A term was expected to be a list but wasn't
    InvalidListStructure {
        /// The term that should have been a list
        term: crate::ast::Term,
        /// What kind of list was expected (e.g., "proper list", "list or variable")
        expected: String,
    },
}

impl fmt::Display for RuntimeError {
    /// Format runtime errors into human-readable messages
    /// 
    /// Runtime errors often need more context than parse errors because
    /// they occur during complex query evaluation. Messages include the
    /// operation that failed and relevant context to help debugging.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RuntimeError::ArithmeticError { operation, operands, reason } => {
                // Show the operation, what values caused the problem, and why
                write!(f, "Arithmetic error in '{}' with operands {:?}: {}", 
                       operation, operands, reason)
            }
            RuntimeError::DivisionByZero { expression } => {
                // Division by zero is common enough to warrant its own error type
                write!(f, "Division by zero in expression: {}", expression)
            }
            RuntimeError::TypeMismatch { expected, found, context } => {
                // Help users understand what type was needed and what they provided
                write!(f, "Type mismatch in {}: expected {}, found {}", 
                       context, expected, found)
            }
            RuntimeError::UninstantiatedVariable { variable, context } => {
                // Variables must be bound before use in certain contexts (like arithmetic)
                write!(f, "Variable '{}' is not sufficiently instantiated in {}", 
                       variable, context)
            }
            RuntimeError::PredicateNotFound { functor, arity, suggestion } => {
                // Show predicate in standard Prolog notation: name/arity
                write!(f, "Undefined predicate: {}/{}", functor, arity)?;
                if let Some(hint) = suggestion {
                    // If we found a similar predicate name, suggest it (helps with typos)
                    write!(f, ". Did you mean: {}", hint)?;
                }
                Ok(())
            }
            RuntimeError::StackOverflow { depth, predicate } => {
                // Stack overflow usually indicates infinite recursion
                write!(f, "Stack overflow (depth {}) in predicate: {}", depth, predicate)
            }
            RuntimeError::CutOutsideRule => {
                // Cut is a special operator that only makes sense in rule bodies
                write!(f, "Cut (!) can only be used inside rule bodies")
            }
            RuntimeError::InvalidListStructure { term, expected } => {
                // List operations require proper list structure
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
/// 
/// The Levenshtein distance (edit distance) counts the minimum number of
/// single-character edits (insertions, deletions, substitutions) needed
/// to change one string into another.
/// 
/// # Algorithm
/// Uses dynamic programming with a 2D matrix where matrix[i][j] represents
/// the distance between the first i characters of s1 and first j characters of s2.
/// 
/// # Use Case
/// When a user calls an undefined predicate, we use this to find similar
/// predicate names and suggest them. For example, if user types "appned",
/// we can suggest "append" since the distance is only 1.
/// 
/// # Complexity
/// Time: O(m*n) where m and n are the lengths of the strings
/// Space: O(m*n) for the matrix
pub fn levenshtein_distance(s1: &str, s2: &str) -> usize {
    let len1 = s1.len();
    let len2 = s2.len();
    
    // Create matrix with dimensions (len1+1) x (len2+1)
    // The +1 accounts for the empty string base case
    let mut matrix = vec![vec![0; len2 + 1]; len1 + 1];
    
    // Initialize first column: distance from s1 prefixes to empty string
    // This represents deleting all characters from s1
    for i in 0..=len1 {
        matrix[i][0] = i;
    }
    
    // Initialize first row: distance from empty string to s2 prefixes  
    // This represents inserting all characters of s2
    for j in 0..=len2 {
        matrix[0][j] = j;
    }
    
    // Fill the matrix using dynamic programming
    for (i, c1) in s1.chars().enumerate() {
        for (j, c2) in s2.chars().enumerate() {
            // If characters match, no edit needed (cost = 0)
            // If they don't match, substitution needed (cost = 1)
            let cost = if c1 == c2 { 0 } else { 1 };
            
            // Calculate minimum of three possible operations:
            matrix[i + 1][j + 1] = std::cmp::min(
                std::cmp::min(
                    matrix[i][j + 1] + 1,     // deletion: remove c1 from s1
                    matrix[i + 1][j] + 1,     // insertion: add c2 to s1
                ),
                matrix[i][j] + cost,          // substitution: replace c1 with c2
            );
        }
    }
    
    // The bottom-right cell contains the final distance
    matrix[len1][len2]
}

// Link to the test module
#[cfg(test)]
#[path = "error_tests.rs"]
mod tests;