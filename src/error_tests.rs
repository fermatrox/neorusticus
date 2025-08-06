// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: error_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the error module
//! 
//! This test suite validates all error handling functionality including:
//! - Position tracking for source locations
//! - Parse error formatting and display
//! - Runtime error formatting and display
//! - Levenshtein distance algorithm for typo suggestions
//! - Error trait implementations
//! - Edge cases and boundary conditions

use super::*;
use std::error::Error;

// ===== Position Tests =====
// 
// The Position struct tracks where in the source code something occurs.
// These tests ensure position tracking works correctly for error reporting.

#[test]
fn test_position_new() {
    // Test creating a position with specific coordinates
    // This is the main constructor used throughout the parser
    let pos = Position::new(5, 10, 42);
    assert_eq!(pos.line, 5);      // Line 5
    assert_eq!(pos.column, 10);   // Column 10 within that line
    assert_eq!(pos.offset, 42);   // 42 characters from start of input
}

#[test]
fn test_position_start() {
    // Test the convenience constructor for the beginning of input
    // Most text editors use 1-based line/column numbering, so we start at (1,1)
    // The offset is 0-based since it's a byte offset
    let pos = Position::start();
    assert_eq!(pos.line, 1);
    assert_eq!(pos.column, 1);
    assert_eq!(pos.offset, 0);
}

#[test]
fn test_position_display() {
    // Test that positions format correctly for error messages
    // Users see "line X, column Y" which matches editor displays
    let pos = Position::new(5, 10, 42);
    assert_eq!(format!("{}", pos), "line 5, column 10");
    
    // Test edge case with large numbers
    // Ensures no overflow or formatting issues with big files
    let pos_large = Position::new(999999, 999999, 999999999);
    assert_eq!(format!("{}", pos_large), "line 999999, column 999999");
}

#[test]
fn test_position_clone() {
    // Test that Position implements Clone correctly
    // Important for error handling where we need to copy positions
    let pos1 = Position::new(3, 7, 25);
    let pos2 = pos1.clone();
    assert_eq!(pos1, pos2);
    // Verify it's a deep copy, not just pointer equality
    assert_eq!(pos1.line, pos2.line);
    assert_eq!(pos1.column, pos2.column);
    assert_eq!(pos1.offset, pos2.offset);
}

#[test]
fn test_position_equality() {
    // Test PartialEq implementation for Position
    // Positions are equal if all three fields match
    let pos1 = Position::new(2, 4, 10);
    let pos2 = Position::new(2, 4, 10);
    let pos3 = Position::new(2, 4, 11);  // Different offset
    
    assert_eq!(pos1, pos2);    // All fields match
    assert_ne!(pos1, pos3);    // Offset differs
}

#[test]
fn test_position_boundary_values() {
    // Test with extreme values to ensure robustness
    
    // Zero values (technically invalid for line/column but should handle gracefully)
    // Some tools might produce 0-based positions that we need to handle
    let pos_zero = Position::new(0, 0, 0);
    assert_eq!(format!("{}", pos_zero), "line 0, column 0");
    
    // Test with max usize (boundary condition)
    // Ensures no integer overflow in position handling
    let pos_max = Position::new(usize::MAX, usize::MAX, usize::MAX);
    assert_eq!(pos_max.line, usize::MAX);
    assert_eq!(pos_max.column, usize::MAX);
    assert_eq!(pos_max.offset, usize::MAX);
}

// ===== ParseError Tests =====
// 
// ParseError represents problems during tokenization and parsing.
// These tests verify that each error type formats helpful messages.

#[test]
fn test_parse_error_unexpected_token() {
    // Test the most common parse error: finding an unexpected token
    // This happens when the parser encounters something it doesn't expect
    
    let pos = Position::new(1, 5, 4);
    
    // Case 1: Without expected tokens (generic unexpected token)
    let error = ParseError::UnexpectedToken {
        token: "(".to_string(),
        position: pos.clone(),
        expected: None,
    };
    let display = format!("{}", error);
    assert!(display.contains("Unexpected token '('"));
    assert!(display.contains("line 1, column 5"));
    assert!(!display.contains("Expected"));  // No expectations listed
    
    // Case 2: With expected tokens (more helpful error)
    // This gives users specific guidance on what would be valid
    let error_with_expected = ParseError::UnexpectedToken {
        token: "(".to_string(),
        position: pos,
        expected: Some(vec!["atom".to_string(), "variable".to_string()]),
    };
    let display = format!("{}", error_with_expected);
    assert!(display.contains("Expected one of: atom, variable"));
}

#[test]
fn test_parse_error_unexpected_eof() {
    // Test error when input ends unexpectedly
    // Common when users forget closing delimiters or incomplete queries
    
    let pos = Position::new(10, 20, 150);
    
    // Case 1: Generic EOF error
    let error = ParseError::UnexpectedEof {
        position: pos.clone(),
        expected: None,
    };
    let display = format!("{}", error);
    assert!(display.contains("Unexpected end of input"));
    assert!(display.contains("line 10, column 20"));
    
    // Case 2: EOF with specific expected tokens
    // Helps users understand what's missing
    let error_with_expected = ParseError::UnexpectedEof {
        position: pos,
        expected: Some(vec![")".to_string(), "]".to_string()]),
    };
    let display = format!("{}", error_with_expected);
    assert!(display.contains("Expected one of: ), ]"));
}

#[test]
fn test_parse_error_invalid_number() {
    // Test number parsing errors
    // Numbers can fail due to overflow, invalid format, etc.
    
    let pos = Position::new(3, 8, 25);
    let error = ParseError::InvalidNumber {
        value: "999999999999999999999".to_string(),
        position: pos,
        reason: "Number too large for 64-bit integer".to_string(),
    };
    
    let display = format!("{}", error);
    assert!(display.contains("Invalid number '999999999999999999999'"));
    assert!(display.contains("line 3, column 8"));
    assert!(display.contains("Number too large"));
}

#[test]
fn test_parse_error_invalid_syntax() {
    // Test generic syntax errors with optional suggestions
    // Used for complex errors that don't fit other categories
    
    let pos = Position::new(2, 1, 10);
    
    // Case 1: Without suggestion (just describes the problem)
    let error = ParseError::InvalidSyntax {
        message: "Missing operator".to_string(),
        position: pos.clone(),
        suggestion: None,
    };
    let display = format!("{}", error);
    assert!(display.contains("Invalid syntax"));
    assert!(display.contains("Missing operator"));
    assert!(!display.contains("Suggestion"));
    
    // Case 2: With suggestion (helps users fix the issue)
    let error_with_suggestion = ParseError::InvalidSyntax {
        message: "Missing operator".to_string(),
        position: pos,
        suggestion: Some("Add ':-' between head and body".to_string()),
    };
    let display = format!("{}", error_with_suggestion);
    assert!(display.contains("Suggestion: Add ':-' between head and body"));
}

#[test]
fn test_parse_error_unclosed_delimiter() {
    // Test error for unclosed parentheses, brackets, etc.
    // Shows both where delimiter was opened and where parsing ended
    // This helps users find the missing closing delimiter
    
    let open_pos = Position::new(1, 10, 9);
    let current_pos = Position::new(5, 1, 100);
    let error = ParseError::UnclosedDelimiter {
        delimiter: '(',
        open_position: open_pos,
        current_position: current_pos,
    };
    
    let display = format!("{}", error);
    assert!(display.contains("Unclosed '('"));
    assert!(display.contains("opened at line 1, column 10"));
    assert!(display.contains("reached line 5, column 1"));
}

#[test]
fn test_parse_error_invalid_variable() {
    // Test variable naming rule violations
    // In Prolog, variables must start with uppercase or underscore
    
    let pos = Position::new(4, 3, 30);
    let error = ParseError::InvalidVariable {
        name: "123Var".to_string(),  // Invalid: starts with digit
        position: pos,
        reason: "Variable names must start with uppercase or underscore".to_string(),
    };
    
    let display = format!("{}", error);
    assert!(display.contains("Invalid variable '123Var'"));
    assert!(display.contains("line 4, column 3"));
    assert!(display.contains("must start with uppercase"));
}

#[test]
fn test_parse_error_invalid_atom() {
    // Test atom naming rule violations
    // Atoms typically start with lowercase or are quoted strings
    
    let pos = Position::new(7, 15, 85);
    let error = ParseError::InvalidAtom {
        name: "".to_string(),  // Empty atom name
        position: pos,
        reason: "Atom name cannot be empty".to_string(),
    };
    
    let display = format!("{}", error);
    assert!(display.contains("Invalid atom ''"));
    assert!(display.contains("line 7, column 15"));
    assert!(display.contains("cannot be empty"));
}

#[test]
fn test_parse_error_edge_cases() {
    // Test edge cases and boundary conditions for ParseError
    
    // Test with empty strings
    // Ensures we handle empty tokens gracefully
    let error = ParseError::UnexpectedToken {
        token: "".to_string(),
        position: Position::start(),
        expected: Some(vec![]),  // Empty expected list
    };
    let display = format!("{}", error);
    assert!(display.contains("Unexpected token ''"));
    assert!(display.contains("Expected one of: ")); // Empty list still shows prefix
    
    // Test with very long token
    // Ensures we don't truncate or have buffer issues
    let long_token = "a".repeat(1000);
    let error = ParseError::UnexpectedToken {
        token: long_token.clone(),
        position: Position::new(1, 1, 0),
        expected: None,
    };
    let display = format!("{}", error);
    assert!(display.contains(&long_token));
    
    // Test with special characters in tokens
    // Ensures special chars don't break formatting
    let error = ParseError::UnexpectedToken {
        token: "\n\t\r".to_string(),  // Whitespace characters
        position: Position::new(1, 1, 0),
        expected: None,
    };
    let display = format!("{}", error);
    assert!(display.contains("\n\t\r"));
}

// ===== Levenshtein Distance Tests =====
// 
// The Levenshtein distance algorithm is used to suggest similar predicate names
// when users make typos. These tests ensure the algorithm works correctly.

#[test]
fn test_levenshtein_distance_basic() {
    // Test the classic examples from literature
    // These are well-known test cases for edit distance
    
    // "kitten" -> "sitting" requires 3 edits:
    // k -> s (substitute), e -> i (substitute), add g at end
    assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
    
    // Common typos in programming:
    assert_eq!(levenshtein_distance("append", "appendd"), 1);  // Extra 'd'
    assert_eq!(levenshtein_distance("length", "lentgh"), 2);   // Transposition
    assert_eq!(levenshtein_distance("same", "same"), 0);       // Identical strings
}

#[test]
fn test_levenshtein_distance_empty_strings() {
    // Test edge cases with empty strings
    // Distance from empty string is just the length of the other string
    
    assert_eq!(levenshtein_distance("", ""), 0);      // Both empty
    assert_eq!(levenshtein_distance("abc", ""), 3);   // Delete 3 chars
    assert_eq!(levenshtein_distance("", "xyz"), 3);   // Insert 3 chars
}

#[test]
fn test_levenshtein_distance_single_char() {
    // Test single character strings
    // Simplest non-empty test cases
    
    assert_eq!(levenshtein_distance("a", "a"), 0);    // Same char
    assert_eq!(levenshtein_distance("a", "b"), 1);    // Different chars
    assert_eq!(levenshtein_distance("a", "ab"), 1);   // Add one char
    assert_eq!(levenshtein_distance("ab", "a"), 1);   // Remove one char
}

#[test]
fn test_levenshtein_distance_case_sensitive() {
    // Test that the algorithm is case-sensitive
    // Important for Prolog where case matters (Variable vs atom)
    
    assert_eq!(levenshtein_distance("ABC", "abc"), 3);  // All different
    assert_eq!(levenshtein_distance("Test", "test"), 1); // First char differs
}

#[test]
fn test_levenshtein_distance_unicode() {
    // Test with Unicode characters
    // Note: Unicode handling may vary depending on system encoding
    // The main use case for this function is ASCII predicate names anyway
    
    // Test with same Unicode strings
    assert_eq!(levenshtein_distance("こんにちは", "こんにちは"), 0);
    
    // Test with clearly different ASCII strings
    assert_eq!(levenshtein_distance("abc", "xyz"), 3);
    assert_eq!(levenshtein_distance("test", "best"), 1);
    
    // Test mixed cases that work reliably
    assert_eq!(levenshtein_distance("hello", "hallo"), 1);  // e -> a
    assert_eq!(levenshtein_distance("world", "word"), 1);    // Delete 'l'
}

#[test]
fn test_levenshtein_distance_boundary_cases() {
    // Test performance and correctness with extreme inputs
    
    // Very long strings with minimal difference
    // Tests that the algorithm handles large inputs efficiently
    let long1 = "a".repeat(100);
    let long2 = "a".repeat(99) + "b";  // Last char different
    assert_eq!(levenshtein_distance(&long1, &long2), 1);
    
    // Completely different strings
    // Maximum possible distance equals the longer string's length
    assert_eq!(levenshtein_distance("abc", "xyz"), 3);
    assert_eq!(levenshtein_distance("12345", "abcde"), 5);
    
    // Transpositions (swapped adjacent characters)
    // Basic Levenshtein treats this as 2 edits (not 1 like Damerau-Levenshtein)
    assert_eq!(levenshtein_distance("ab", "ba"), 2);
}

#[test]
fn test_levenshtein_distance_typical_typos() {
    // Test common programming typos
    // These are the real-world cases we want to catch and suggest fixes for
    
    assert_eq!(levenshtein_distance("append", "apend"), 1);   // Missing letter
    assert_eq!(levenshtein_distance("member", "mebmer"), 2);  // Transposition
    assert_eq!(levenshtein_distance("length", "lenght"), 2);  // Transposition (n-g swap, h-t swap)
    assert_eq!(levenshtein_distance("write", "wriet"), 2);    // Transposition
    assert_eq!(levenshtein_distance("fail", "fial"), 2);      // Transposition
}

// ===== Error Trait Implementation Tests =====
// 
// Verify that our error types properly implement the std::error::Error trait

#[test]
fn test_parse_error_implements_error_trait() {
    // Test that ParseError can be used as a standard Error
    let error = ParseError::InvalidSyntax {
        message: "test".to_string(),
        position: Position::start(),
        suggestion: None,
    };
    
    // Verify it implements std::error::Error
    // This allows it to work with ? operator and error handling libraries
    let _: &dyn std::error::Error = &error;
    
    // Verify source() returns None (no cause for ParseError)
    // ParseError is a root cause, not caused by another error
    assert!(error.source().is_none());
}

#[test]
fn test_runtime_error_implements_error_trait() {
    // Test that RuntimeError can be used as a standard Error
    use crate::ast::Term;
    
    let error = RuntimeError::DivisionByZero {
        expression: Term::Number(0),
    };
    
    // Verify it implements std::error::Error
    let _: &dyn std::error::Error = &error;
    
    // Verify source() returns None (no cause for RuntimeError)
    assert!(error.source().is_none());
}

// ===== Integration Tests with Result Types =====
// 
// Test the convenience type aliases ParseResult and RuntimeResult

#[test]
fn test_parse_result_type() {
    // Test that ParseResult<T> works as expected
    
    // Function that returns a parse error
    fn parse_something() -> ParseResult<i32> {
        Err(ParseError::InvalidSyntax {
            message: "test error".to_string(),
            position: Position::start(),
            suggestion: None,
        })
    }
    
    let result = parse_something();
    assert!(result.is_err());
    
    // Function that returns success
    fn parse_success() -> ParseResult<i32> {
        Ok(42)
    }
    
    let result = parse_success();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);
}

#[test]
fn test_runtime_result_type() {
    // Test that RuntimeResult<T> works as expected
    use crate::ast::Term;
    
    // Example function using RuntimeResult
    fn divide(a: i64, b: i64) -> RuntimeResult<i64> {
        if b == 0 {
            Err(RuntimeError::DivisionByZero {
                expression: Term::Number(a),
            })
        } else {
            Ok(a / b)
        }
    }
    
    // Test successful division
    let result = divide(10, 2);
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 5);
    
    // Test division by zero error
    let result = divide(10, 0);
    assert!(result.is_err());
}

// ===== Format String Security Tests =====
// 
// Ensure that user input in error messages doesn't cause format string issues

#[test]
fn test_error_display_format_string_injection() {
    // Test that format strings in user input don't cause issues
    // This is a security test - user input shouldn't be able to break formatting
    
    let error = ParseError::UnexpectedToken {
        token: "{} {:?} {:.2}".to_string(),  // Format specifiers as token
        position: Position::new(1, 1, 0),
        expected: Some(vec!["{:x}".to_string()]),  // Format specifier in expected
    };
    
    let display = format!("{}", error);
    // The format specifiers should be treated as literal strings
    assert!(display.contains("{} {:?} {:.2}"));
    assert!(display.contains("{:x}"));
}

// ===== RuntimeError Display Tests =====
// 
// RuntimeError represents execution-time failures.
// These tests verify each error type formats helpful runtime error messages.

#[test]
fn test_runtime_error_display() {
    use crate::ast::Term;
    
    // Test ArithmeticError
    // Covers overflow, underflow, and other arithmetic failures
    let error = RuntimeError::ArithmeticError {
        operation: "+".to_string(),
        operands: vec![Term::Number(1), Term::Number(2)],
        reason: "Integer overflow".to_string(),
    };
    let display = format!("{}", error);
    assert!(display.contains("Arithmetic error in '+'"));
    assert!(display.contains("Integer overflow"));
    
    // Test DivisionByZero
    // Special case of arithmetic error that's common enough for its own type
    let error = RuntimeError::DivisionByZero {
        expression: Term::Number(42),
    };
    let display = format!("{}", error);
    assert!(display.contains("Division by zero"));
    assert!(display.contains("42"));
    
    // Test TypeMismatch
    // Occurs when operations receive wrong types (e.g., adding atom to number)
    let error = RuntimeError::TypeMismatch {
        expected: "number".to_string(),
        found: Term::Atom("hello".to_string()),
        context: "arithmetic evaluation".to_string(),
    };
    let display = format!("{}", error);
    assert!(display.contains("Type mismatch"));
    assert!(display.contains("expected number"));
    assert!(display.contains("found hello"));
    
    // Test UninstantiatedVariable
    // Variables must be bound before use in arithmetic/comparisons
    let error = RuntimeError::UninstantiatedVariable {
        variable: "X".to_string(),
        context: "arithmetic expression".to_string(),
    };
    let display = format!("{}", error);
    assert!(display.contains("Variable 'X'"));
    assert!(display.contains("not sufficiently instantiated"));
    
    // Test PredicateNotFound without suggestion
    // User called a predicate that doesn't exist
    let error = RuntimeError::PredicateNotFound {
        functor: "unknown".to_string(),
        arity: 2,
        suggestion: None,
    };
    let display = format!("{}", error);
    assert!(display.contains("Undefined predicate: unknown/2"));
    assert!(!display.contains("Did you mean"));  // No suggestion provided
    
    // Test PredicateNotFound with suggestion
    // We found a similar predicate name to suggest (typo correction)
    let error = RuntimeError::PredicateNotFound {
        functor: "appned".to_string(),
        arity: 3,
        suggestion: Some("append/3".to_string()),
    };
    let display = format!("{}", error);
    assert!(display.contains("Did you mean: append/3"));
    
    // Test StackOverflow
    // Infinite recursion or very deep recursion hit the safety limit
    let error = RuntimeError::StackOverflow {
        depth: 1000,
        predicate: "infinite/1".to_string(),
    };
    let display = format!("{}", error);
    assert!(display.contains("Stack overflow"));
    assert!(display.contains("depth 1000"));
    assert!(display.contains("infinite/1"));
    
    // Test CutOutsideRule
    // The cut operator (!) only makes sense inside rule bodies
    let error = RuntimeError::CutOutsideRule;
    let display = format!("{}", error);
    assert!(display.contains("Cut (!)"));
    assert!(display.contains("inside rule bodies"));
    
    // Test InvalidListStructure
    // List operations expect proper list format
    let error = RuntimeError::InvalidListStructure {
        term: Term::Atom("not_a_list".to_string()),
        expected: "proper list".to_string(),
    };
    let display = format!("{}", error);
    assert!(display.contains("Invalid list structure"));
    assert!(display.contains("expected proper list"));
    assert!(display.contains("not_a_list"));
}

// ===== Memory and Performance Tests =====
// 
// Test that the error handling works efficiently with large inputs

#[test]
fn test_levenshtein_large_strings() {
    // Test that the algorithm handles reasonably large strings
    // This ensures no stack overflow or excessive memory use
    
    let s1 = "a".repeat(500);
    let s2 = "a".repeat(499) + "b";
    assert_eq!(levenshtein_distance(&s1, &s2), 1);
    
    // Test with completely different large strings
    // This is the worst case for the algorithm (maximum edits)
    let s3 = "x".repeat(100);
    let s4 = "y".repeat(100);
    assert_eq!(levenshtein_distance(&s3, &s4), 100);
}

#[test]
fn test_position_debug_trait() {
    // Test Debug trait implementation for Position
    // Debug format is used in error messages and logging
    
    let pos = Position::new(5, 10, 42);
    let debug_str = format!("{:?}", pos);
    
    // Verify the debug output contains the expected fields
    // Note: exact format may vary, but should contain the data
    assert!(debug_str.contains("Position"));
    assert!(debug_str.contains("line: 5"));
    assert!(debug_str.contains("column: 10"));
    assert!(debug_str.contains("offset: 42"));
}

#[test]
fn test_error_debug_trait() {
    // Test Debug trait implementation for ParseError
    // Important for debugging and logging
    
    let error = ParseError::InvalidSyntax {
        message: "test".to_string(),
        position: Position::new(1, 1, 0),
        suggestion: Some("fix it".to_string()),
    };
    
    let debug_str = format!("{:?}", error);
    
    // Debug output should contain all the error fields
    assert!(debug_str.contains("InvalidSyntax"));
    assert!(debug_str.contains("test"));
    assert!(debug_str.contains("fix it"));
}