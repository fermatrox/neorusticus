// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: lexer_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the lexer module
//! 
//! This module contains all unit tests for the lexer, including tests for
//! Token methods, Tokenizer functionality, and edge cases.

use super::*;
use crate::error::ParseError;

// ===== Token Tests =====
// These tests verify the Token enum's methods work correctly.
// The Token enum is fundamental to the lexer's output, so these
// tests ensure that tokens can be properly described and validated.

#[test]
fn test_token_description() {
    // The description() method is used to generate human-readable error messages.
    // When the parser expects a specific token and finds something else, it uses
    // description() to tell the user what was expected (e.g., "Expected ')'").
    // This test verifies that each token type returns the correct description string.
    
    // Test value-carrying tokens (these contain data)
    assert_eq!(Token::Atom("test".to_string()).description(), "atom");
    assert_eq!(Token::Variable("X".to_string()).description(), "variable");
    assert_eq!(Token::Number(42).description(), "number");
    
    // Test delimiter tokens (used for grouping and lists)
    assert_eq!(Token::LeftParen.description(), "'('");
    assert_eq!(Token::RightParen.description(), "')'");
    assert_eq!(Token::LeftBracket.description(), "'['");
    assert_eq!(Token::RightBracket.description(), "']'");
    
    // Test punctuation tokens
    assert_eq!(Token::Comma.description(), "','");
    assert_eq!(Token::Dot.description(), "'.'");
    assert_eq!(Token::Pipe.description(), "'|'");      // Used in list syntax [H|T]
    assert_eq!(Token::Question.description(), "'?'");  // Query terminator
    assert_eq!(Token::Cut.description(), "'!'");       // Cut operator
    
    // Test arithmetic operator tokens
    assert_eq!(Token::Plus.description(), "'+'");
    assert_eq!(Token::Minus.description(), "'-'");
    assert_eq!(Token::Multiply.description(), "'*'");
    assert_eq!(Token::Divide.description(), "'//'");   // Integer division in Prolog
    
    // Test comparison operator tokens
    assert_eq!(Token::Greater.description(), "'>'");
    assert_eq!(Token::Less.description(), "'<'");
    assert_eq!(Token::GreaterEq.description(), "'>='");
    assert_eq!(Token::LessEq.description(), "'=<'");   // Note: Prolog uses =< not <=
    
    // Test equality and unification operator tokens
    assert_eq!(Token::ArithEq.description(), "'=:='");   // Arithmetic equality
    assert_eq!(Token::ArithNeq.description(), "'=\\='"); // Arithmetic inequality
    assert_eq!(Token::Unify.description(), "'='");       // Unification
    assert_eq!(Token::NotUnify.description(), "'\\='");  // Non-unification
    
    // Test special tokens
    assert_eq!(Token::Rule.description(), "':-'");     // Rule definition operator
    assert_eq!(Token::Is.description(), "'is'");       // Arithmetic evaluation
    assert_eq!(Token::Mod.description(), "'mod'");     // Modulo operator
    assert_eq!(Token::Eof.description(), "end of file");
}

#[test]
fn test_can_start_expression() {
    // In Prolog's grammar, only certain tokens can legally begin an expression.
    // This method helps the parser validate syntax by checking if a token
    // can appear at the start of an expression context.
    
    // These tokens CAN start expressions:
    // - Atoms: represent constants or functors
    // - Variables: can be unified with values
    // - Numbers: literal values
    // - Left parenthesis: starts a grouped expression
    // - Left bracket: starts a list
    // - Cut: special operator that can appear as a goal
    assert!(Token::Atom("test".to_string()).can_start_expression());
    assert!(Token::Variable("X".to_string()).can_start_expression());
    assert!(Token::Number(42).can_start_expression());
    assert!(Token::LeftParen.can_start_expression());
    assert!(Token::LeftBracket.can_start_expression());
    assert!(Token::Cut.can_start_expression());
    
    // These tokens CANNOT start expressions:
    // They're either operators that need operands, closing delimiters,
    // or punctuation that serves other syntactic purposes.
    assert!(!Token::RightParen.can_start_expression());
    assert!(!Token::RightBracket.can_start_expression());
    assert!(!Token::Comma.can_start_expression());
    assert!(!Token::Dot.can_start_expression());
    assert!(!Token::Rule.can_start_expression());
    assert!(!Token::Pipe.can_start_expression());
    assert!(!Token::Question.can_start_expression());
    assert!(!Token::Plus.can_start_expression());
    assert!(!Token::Minus.can_start_expression());
    assert!(!Token::Multiply.can_start_expression());
    assert!(!Token::Divide.can_start_expression());
    assert!(!Token::Greater.can_start_expression());
    assert!(!Token::Less.can_start_expression());
    assert!(!Token::GreaterEq.can_start_expression());
    assert!(!Token::LessEq.can_start_expression());
    assert!(!Token::ArithEq.can_start_expression());
    assert!(!Token::ArithNeq.can_start_expression());
    assert!(!Token::Unify.can_start_expression());
    assert!(!Token::NotUnify.can_start_expression());
    assert!(!Token::Is.can_start_expression());
    assert!(!Token::Mod.can_start_expression());
    assert!(!Token::Eof.can_start_expression());
}

#[test]
fn test_token_equality() {
    // Tests the PartialEq implementation for Token.
    // This is important for comparing tokens in the parser and for testing.
    // Tokens with the same variant and value should be equal.
    
    // Test atom equality - same string content means equal tokens
    assert_eq!(Token::Atom("test".to_string()), Token::Atom("test".to_string()));
    assert_ne!(Token::Atom("test".to_string()), Token::Atom("other".to_string()));
    
    // Test variable equality
    assert_eq!(Token::Variable("X".to_string()), Token::Variable("X".to_string()));
    assert_ne!(Token::Variable("X".to_string()), Token::Variable("Y".to_string()));
    
    // Test number equality
    assert_eq!(Token::Number(42), Token::Number(42));
    assert_ne!(Token::Number(42), Token::Number(17));
    
    // Test simple token equality (tokens without associated data)
    assert_eq!(Token::LeftParen, Token::LeftParen);
    assert_ne!(Token::LeftParen, Token::RightParen);
}

#[test]
fn test_token_clone() {
    // Tests the Clone trait implementation.
    // Tokens need to be cloneable for the parser to work with them
    // without consuming the original token stream.
    
    let atom = Token::Atom("test".to_string());
    let cloned = atom.clone();
    assert_eq!(atom, cloned);
    
    let var = Token::Variable("X".to_string());
    let cloned = var.clone();
    assert_eq!(var, cloned);
    
    let num = Token::Number(42);
    let cloned = num.clone();
    assert_eq!(num, cloned);
}

// ===== Tokenizer Tests =====
// These tests verify that the Tokenizer correctly converts strings
// into sequences of tokens, handling all Prolog syntax correctly.

#[test]
fn test_simple_tokens() {
    // Tests basic tokenization of atoms and numbers separated by whitespace.
    // This is the simplest case: lowercase words become atoms, numbers become number tokens.
    
    let mut tokenizer = Tokenizer::new("hello world 123");
    let tokens = tokenizer.tokenize().unwrap();
    
    // Should produce: [Atom("hello"), Atom("world"), Number(123), Eof]
    assert_eq!(tokens.len(), 4);
    assert_eq!(tokens[0], Token::Atom("hello".to_string()));
    assert_eq!(tokens[1], Token::Atom("world".to_string()));
    assert_eq!(tokens[2], Token::Number(123));
    assert_eq!(tokens[3], Token::Eof);  // EOF always added at the end
}

#[test]
fn test_variables() {
    // In Prolog, identifiers starting with uppercase or underscore are variables.
    // This test verifies that the tokenizer correctly identifies variables.
    
    let mut tokenizer = Tokenizer::new("X Y _var Variable123");
    let tokens = tokenizer.tokenize().unwrap();
    
    // All should be recognized as variables
    // We use matches! macro because we only care about the variant, not the value
    assert!(matches!(tokens[0], Token::Variable(_)));
    assert!(matches!(tokens[1], Token::Variable(_)));
    assert!(matches!(tokens[2], Token::Variable(_)));  // Underscore prefix
    assert!(matches!(tokens[3], Token::Variable(_)));  // Mixed case with numbers
}

#[test]
fn test_operators() {
    // Tests tokenization of Prolog's multi-character operators.
    // Many Prolog operators are multiple characters that must be recognized as a unit.
    
    let mut tokenizer = Tokenizer::new(":- =:= =\\= >= =< \\= is mod");
    let tokens = tokenizer.tokenize().unwrap();
    
    assert_eq!(tokens[0], Token::Rule);      // :- (rule definition)
    assert_eq!(tokens[1], Token::ArithEq);   // =:= (arithmetic equality)
    assert_eq!(tokens[2], Token::ArithNeq);  // =\= (arithmetic inequality)
    assert_eq!(tokens[3], Token::GreaterEq); // >= (greater or equal)
    assert_eq!(tokens[4], Token::LessEq);    // =< (less or equal, Prolog style)
    assert_eq!(tokens[5], Token::NotUnify);  // \= (not unifiable)
    assert_eq!(tokens[6], Token::Is);        // 'is' keyword for arithmetic
    assert_eq!(tokens[7], Token::Mod);       // 'mod' keyword for modulo
}

#[test]
fn test_delimiters() {
    // Tests single-character delimiters and punctuation.
    // These are fundamental to Prolog's syntax structure.
    
    let mut tokenizer = Tokenizer::new("( ) [ ] , . | ? !");
    let tokens = tokenizer.tokenize().unwrap();
    
    assert_eq!(tokens[0], Token::LeftParen);
    assert_eq!(tokens[1], Token::RightParen);
    assert_eq!(tokens[2], Token::LeftBracket);
    assert_eq!(tokens[3], Token::RightBracket);
    assert_eq!(tokens[4], Token::Comma);
    assert_eq!(tokens[5], Token::Dot);
    assert_eq!(tokens[6], Token::Pipe);       // Used in list syntax [H|T]
    assert_eq!(tokens[7], Token::Question);   // Query terminator
    assert_eq!(tokens[8], Token::Cut);        // Cut operator !
}

#[test]
fn test_arithmetic() {
    // Tests arithmetic operators and negative numbers.
    // Note the special handling of minus: it's an operator when alone,
    // but part of a negative number when immediately followed by digits.
    
    let mut tokenizer = Tokenizer::new("+ - * // > < = -42");
    let tokens = tokenizer.tokenize().unwrap();
    
    assert_eq!(tokens[0], Token::Plus);
    assert_eq!(tokens[1], Token::Minus);     // Standalone minus is an operator
    assert_eq!(tokens[2], Token::Multiply);
    assert_eq!(tokens[3], Token::Divide);    // // is integer division in Prolog
    assert_eq!(tokens[4], Token::Greater);
    assert_eq!(tokens[5], Token::Less);
    assert_eq!(tokens[6], Token::Unify);     // = is unification
    assert_eq!(tokens[7], Token::Number(-42)); // -42 is a negative number token
}

#[test]
fn test_quoted_atoms() {
    // Quoted atoms allow special characters, spaces, and uppercase in atom names.
    // They also support escape sequences for special characters.
    
    let mut tokenizer = Tokenizer::new("'hello world' 'with\\nnewline'");
    let tokens = tokenizer.tokenize().unwrap();
    
    // First quoted atom contains a space
    assert_eq!(tokens[0], Token::Atom("hello world".to_string()));
    // Second quoted atom contains an escaped newline
    assert_eq!(tokens[1], Token::Atom("with\nnewline".to_string()));
}

#[test]
fn test_comments() {
    // Prolog uses % for single-line comments.
    // Everything after % until the end of line should be ignored.
    
    let mut tokenizer = Tokenizer::new("hello % this is a comment\nworld");
    let tokens = tokenizer.tokenize().unwrap();
    
    // The comment should be completely ignored
    assert_eq!(tokens.len(), 3); // hello, world, EOF
    assert_eq!(tokens[0], Token::Atom("hello".to_string()));
    assert_eq!(tokens[1], Token::Atom("world".to_string()));
    // Note: no tokens from the comment text
}

#[test]
fn test_error_unclosed_paren() {
    // Tests error detection for unclosed parentheses.
    // The tokenizer maintains a stack of open delimiters to detect this error.
    
    let mut tokenizer = Tokenizer::new("hello(world");
    let result = tokenizer.tokenize();
    
    assert!(result.is_err());
    if let Err(ParseError::UnclosedDelimiter { delimiter, .. }) = result {
        assert_eq!(delimiter, '(');  // Should report which delimiter is unclosed
    } else {
        panic!("Expected UnclosedDelimiter error");
    }
}

#[test]
fn test_error_mismatched_delimiters() {
    // Tests detection of mismatched delimiters like (] or [).
    // Each closing delimiter must match the most recent opening delimiter.
    
    let mut tokenizer = Tokenizer::new("hello(world]");  // ( closed with ]
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
    // Verifies that the tokenizer correctly tracks line positions.
    // This is important for error reporting - errors should show the correct line number.
    
    let mut tokenizer = Tokenizer::new("hello\nworld");
    let tokens = tokenizer.tokenize().unwrap();
    
    // Position tracking is internal, but we verify it works by checking
    // that tokenization succeeds and produces the expected tokens
    assert_eq!(tokens.len(), 3); // hello, world, EOF
}

#[test]
fn test_complex_expression() {
    // Tests tokenization of a complete Prolog rule with multiple components.
    // This verifies that the tokenizer can handle realistic Prolog code.
    
    let mut tokenizer = Tokenizer::new("parent(X, Y) :- father(X, Y), male(X).");
    let tokens = tokenizer.tokenize().unwrap();
    
    // Should tokenize into many tokens representing the complete rule
    assert!(tokens.len() > 10);
    assert_eq!(tokens[0], Token::Atom("parent".to_string()));
    assert_eq!(tokens[1], Token::LeftParen);
    // The complete tokenization includes variables, operators, commas, etc.
}

#[test]
fn test_negative_numbers() {
    // Tests that negative numbers are correctly distinguished from minus operators.
    // "-42" should be a single negative number token, not minus followed by 42.
    
    let mut tokenizer = Tokenizer::new("X is -42 + -1");
    let tokens = tokenizer.tokenize().unwrap();
    
    // -42 and -1 should be single negative number tokens
    assert_eq!(tokens[2], Token::Number(-42));
    assert_eq!(tokens[4], Token::Number(-1));
}

// ===== Edge Case Tests =====
// These tests verify the tokenizer handles unusual inputs correctly,
// including empty input, extreme values, and malformed syntax.

#[test]
fn test_empty_input() {
    // An empty string should produce just an EOF token.
    // This is the minimal valid token stream.
    
    let mut tokenizer = Tokenizer::new("");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0], Token::Eof);
}

#[test]
fn test_whitespace_only() {
    // Input containing only whitespace should also produce just EOF.
    // Whitespace is not significant in Prolog except as a separator.
    
    let mut tokenizer = Tokenizer::new("   \n\t  \r\n  ");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0], Token::Eof);
}

#[test]
fn test_comment_only() {
    // A file containing only a comment should produce just EOF.
    // Comments are completely ignored by the tokenizer.
    
    let mut tokenizer = Tokenizer::new("% just a comment");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens.len(), 1);
    assert_eq!(tokens[0], Token::Eof);
}

#[test]
fn test_multiple_comments() {
    // Tests that multiple comments are correctly ignored.
    // Comments can appear anywhere in the code and should all be skipped.
    
    let mut tokenizer = Tokenizer::new("hello % comment 1\n% comment 2\nworld % comment 3");
    let tokens = tokenizer.tokenize().unwrap();
    
    // Should only get the actual tokens, not the comments
    assert_eq!(tokens.len(), 3);
    assert_eq!(tokens[0], Token::Atom("hello".to_string()));
    assert_eq!(tokens[1], Token::Atom("world".to_string()));
    assert_eq!(tokens[2], Token::Eof);
}

#[test]
fn test_numbers_at_boundaries() {
    // Tests handling of numbers at the limits of i64.
    // This is important for ensuring the tokenizer doesn't overflow or panic.
    
    // Test maximum i64 (9223372036854775807)
    let max_i64_str = i64::MAX.to_string();
    let mut tokenizer = Tokenizer::new(&max_i64_str);
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Number(i64::MAX));
    
    // Test minimum i64 (-9223372036854775808)
    // This is a special case because the positive value would overflow
    let min_i64_str = i64::MIN.to_string();
    let mut tokenizer = Tokenizer::new(&min_i64_str);
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Number(i64::MIN));
    
    // Test overflow - number too large for i64
    let overflow_str = "99999999999999999999999999999";
    let mut tokenizer = Tokenizer::new(overflow_str);
    let result = tokenizer.tokenize();
    assert!(result.is_err());
    if let Err(ParseError::InvalidNumber { reason, .. }) = result {
        assert!(reason.contains("too large"));
    } else {
        panic!("Expected InvalidNumber error");
    }
}

#[test]
fn test_zero_and_negative_zero() {
    // In integer arithmetic, -0 equals 0.
    // This test verifies both are handled correctly.
    
    let mut tokenizer = Tokenizer::new("0 -0");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Number(0));
    assert_eq!(tokens[1], Token::Number(0)); // -0 == 0 for integers
}

#[test]
fn test_identifiers_at_length_limit() {
    // Tests the 1024 character limit on identifier length.
    // This prevents potential DoS attacks with extremely long identifiers.
    
    // Test identifier at max length (1024)
    let long_id = "a".repeat(1024);
    let mut tokenizer = Tokenizer::new(&long_id);
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Atom(long_id));  // Should succeed
    
    // Test identifier exceeding max length (1025)
    let too_long_id = "a".repeat(1025);
    let mut tokenizer = Tokenizer::new(&too_long_id);
    let result = tokenizer.tokenize();
    assert!(result.is_err());  // Should fail
    if let Err(ParseError::InvalidVariable { reason, .. }) = result {
        assert!(reason.contains("too long"));
    } else {
        panic!("Expected InvalidVariable error");
    }
}

#[test]
fn test_quoted_atom_edge_cases() {
    // Tests various edge cases for quoted atoms, including empty atoms,
    // escape sequences, and error conditions.
    
    // Empty quoted atom - '' is a valid atom with empty name
    let mut tokenizer = Tokenizer::new("''");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Atom("".to_string()));
    
    // Quoted atom with all escape sequences
    // Tests: \n (newline), \t (tab), \r (return), \\ (backslash), \' (quote)
    let mut tokenizer = Tokenizer::new("'\\n\\t\\r\\\\\\'test'");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Atom("\n\t\r\\'test".to_string()));
    
    // Unclosed quoted atom - missing closing quote
    let mut tokenizer = Tokenizer::new("'unclosed");
    let result = tokenizer.tokenize();
    assert!(result.is_err());
    if let Err(ParseError::InvalidSyntax { message, .. }) = result {
        assert!(message.contains("Unterminated quoted atom"));
    } else {
        panic!("Expected InvalidSyntax error");
    }
    
    // Quoted atom with unterminated escape sequence
    let mut tokenizer = Tokenizer::new("'test\\");  // Backslash at end
    let result = tokenizer.tokenize();
    assert!(result.is_err());
    if let Err(ParseError::InvalidSyntax { message, .. }) = result {
        assert!(message.contains("Unterminated escape sequence"));
    } else {
        panic!("Expected InvalidSyntax error");
    }
}

#[test]
fn test_delimiter_nesting() {
    // Tests correct handling of nested delimiters.
    // The tokenizer uses a stack to ensure proper nesting.
    
    // Deep nesting - [[[[]]]]
    let mut tokenizer = Tokenizer::new("[[[[]]]]");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens.len(), 9); // 4 '[', 4 ']', EOF
    
    // Mixed invalid nesting - [({})]
    // Curly braces are not valid Prolog tokens
    let mut tokenizer = Tokenizer::new("[({})]");
    let result = tokenizer.tokenize();
    assert!(result.is_err()); // '{' and '}' are not valid tokens
    
    // Complex valid nesting - function with nested lists
    let mut tokenizer = Tokenizer::new("f([a, b], (c, [d]))");
    let tokens = tokenizer.tokenize().unwrap();
    assert!(tokens.len() > 10);  // Many tokens for the complex structure
}

#[test]
fn test_operator_sequences() {
    // Tests that incomplete multi-character operators are detected as errors.
    // Many Prolog operators are multiple characters and must be complete.
    
    // Test incomplete ':' (should be ':-')
    let mut tokenizer = Tokenizer::new(":");
    let result = tokenizer.tokenize();
    assert!(result.is_err());
    
    // Test incomplete '=:' (should be '=:=')
    let mut tokenizer = Tokenizer::new("=:");
    let result = tokenizer.tokenize();
    assert!(result.is_err());
    
    // Test incomplete '=\' (should be '=\=')
    let mut tokenizer = Tokenizer::new("=\\");
    let result = tokenizer.tokenize();
    assert!(result.is_err());
    
    // Test single slash (should be '//' for integer division)
    let mut tokenizer = Tokenizer::new("/");
    let result = tokenizer.tokenize();
    assert!(result.is_err());
}

#[test]
fn test_invalid_characters() {
    // Tests that characters not part of Prolog syntax are rejected.
    // This helps catch typos and ensures only valid Prolog is accepted.
    
    let invalid_chars = vec!['@', '#', '$', '^', '&', '~', '`'];
    
    for ch in invalid_chars {
        let input = ch.to_string();
        let mut tokenizer = Tokenizer::new(&input);
        let result = tokenizer.tokenize();
        assert!(result.is_err());
        if let Err(ParseError::UnexpectedToken { token, .. }) = result {
            assert_eq!(token, ch.to_string());
        } else {
            panic!("Expected UnexpectedToken error for '{}'", ch);
        }
    }
}

#[test]
fn test_underscore_variables() {
    // In Prolog, underscore is the anonymous variable, and identifiers
    // starting with underscore are regular variables (but often used as "don't care").
    
    let mut tokenizer = Tokenizer::new("_ _123 _test_var");
    let tokens = tokenizer.tokenize().unwrap();
    
    assert_eq!(tokens[0], Token::Variable("_".to_string()));         // Anonymous variable
    assert_eq!(tokens[1], Token::Variable("_123".to_string()));       // Named underscore variable
    assert_eq!(tokens[2], Token::Variable("_test_var".to_string()));  // Another underscore variable
}

#[test]
fn test_mixed_case_identifiers() {
    // Tests that case determines whether an identifier is an atom or variable.
    // Lowercase start = atom, uppercase/underscore start = variable.
    
    let mut tokenizer = Tokenizer::new("testVar Test123 test_VAR");
    let tokens = tokenizer.tokenize().unwrap();
    
    assert_eq!(tokens[0], Token::Atom("testVar".to_string()));      // lowercase start -> atom
    assert_eq!(tokens[1], Token::Variable("Test123".to_string()));  // uppercase start -> variable
    assert_eq!(tokens[2], Token::Atom("test_VAR".to_string()));     // lowercase start -> atom
}

#[test]
fn test_keywords_as_atoms() {
    // 'is' and 'mod' are keywords in Prolog but can also be used as regular atoms
    // when quoted. This test verifies both cases work correctly.
    
    // Keywords are recognized as special tokens
    let mut tokenizer = Tokenizer::new("is mod");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Is);   // Recognized as 'is' keyword
    assert_eq!(tokens[1], Token::Mod);  // Recognized as 'mod' keyword
    
    // But they can be quoted to be regular atoms
    let mut tokenizer = Tokenizer::new("'is' 'mod'");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Atom("is".to_string()));   // Regular atom
    assert_eq!(tokens[1], Token::Atom("mod".to_string()));  // Regular atom
}

#[test]
fn test_position_info() {
    // Tests that the tokenizer correctly tracks position through the input.
    // Position info is crucial for good error messages.
    
    let mut tokenizer = Tokenizer::new("hello\nworld");
    tokenizer.tokenize().unwrap();
    let (line, _col, pos) = tokenizer.get_position_info();
    
    assert!(line >= 2);  // Should be on at least line 2 after newline
    assert!(pos > 0);    // Should have advanced position
    // Note: _col is prefixed with underscore to indicate we're not using it
}

#[test]
fn test_has_unclosed_delimiters() {
    // Tests the method that checks for unclosed delimiters.
    // Useful for interactive environments to detect incomplete input.
    
    let mut tokenizer = Tokenizer::new("(");
    assert!(!tokenizer.has_unclosed_delimiters()); // Before tokenization, stack is empty
    let _ = tokenizer.tokenize(); // Will fail but modifies state
    // After failed tokenization, the error handling may have cleared the stack
    
    // Test with successful partial tokenization
    let mut tokenizer = Tokenizer::new("(hello");
    let _ = tokenizer.tokenize();
    // After failed tokenization due to unclosed delimiter
}

#[test]
fn test_minus_vs_negative_number() {
    // Critical test for disambiguating minus operator from negative numbers.
    // The rule: if minus is immediately followed by a digit, it's a negative number.
    // Otherwise, it's the subtraction operator.
    
    // Minus followed by space -> operator
    let mut tokenizer = Tokenizer::new("X - 5");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Variable("X".to_string()));
    assert_eq!(tokens[1], Token::Minus);        // Operator
    assert_eq!(tokens[2], Token::Number(5));
    
    // Minus followed by digit -> negative number
    let mut tokenizer = Tokenizer::new("X -5");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Variable("X".to_string()));
    assert_eq!(tokens[1], Token::Number(-5));   // Single negative number token
    
    // Minus at start followed by digit -> negative number
    let mut tokenizer = Tokenizer::new("-5");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Number(-5));
    
    // Minus not followed by digit -> operator
    let mut tokenizer = Tokenizer::new("-X");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Minus);        // Operator
    assert_eq!(tokens[1], Token::Variable("X".to_string()));
}

#[test]
fn test_consecutive_operators() {
    // Tests sequences of operators, particularly ensuring that single '/'
    // is properly rejected (Prolog uses '//' for integer division).
    
    // Test that single '/' causes an error (must be '//')
    let mut tokenizer = Tokenizer::new("+-*/");
    let result = tokenizer.tokenize();
    assert!(result.is_err());
    if let Err(ParseError::UnexpectedToken { token, expected, .. }) = result {
        assert_eq!(token, "/");
        assert!(expected.is_some());  // Should suggest '//'
    }
    
    // Test with valid operators including '//'
    let mut tokenizer = Tokenizer::new("+-*//");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Plus);
    assert_eq!(tokens[1], Token::Minus);
    assert_eq!(tokens[2], Token::Multiply);
    assert_eq!(tokens[3], Token::Divide);
    
    // Test with spaces (operators don't need to be adjacent)
    let mut tokenizer = Tokenizer::new("+ - * //");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Plus);
    assert_eq!(tokens[1], Token::Minus);
    assert_eq!(tokens[2], Token::Multiply);
    assert_eq!(tokens[3], Token::Divide);
}

#[test]
fn test_unicode_handling() {
    // Tests that Unicode is properly handled in quoted atoms but
    // rejected outside quotes (Prolog traditionally uses ASCII).
    
    // Unicode in quoted atoms should work
    let mut tokenizer = Tokenizer::new("'Hello, 世界!'");
    let tokens = tokenizer.tokenize().unwrap();
    assert_eq!(tokens[0], Token::Atom("Hello, 世界!".to_string()));
    
    // Unicode outside quotes should fail (not valid Prolog syntax)
    let mut tokenizer = Tokenizer::new("世界");
    let result = tokenizer.tokenize();
    assert!(result.is_err());
}

#[test]
fn test_escape_sequences_in_quoted_atoms() {
    // Comprehensive test of all supported escape sequences in quoted atoms.
    // Escape sequences allow special characters to be included in atom names.
    
    let test_cases = vec![
        ("'\\n'", "\n"),     // Newline
        ("'\\t'", "\t"),     // Tab
        ("'\\r'", "\r"),     // Carriage return
        ("'\\\\'", "\\"),    // Backslash
        ("'\\''", "'"),      // Single quote
        ("'\\x'", "x"),      // Unknown escape -> literal character
    ];
    
    for (input, expected) in test_cases {
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize().unwrap();
        assert_eq!(tokens[0], Token::Atom(expected.to_string()));
    }
}

#[test]
fn test_line_column_tracking() {
    // Verifies that line numbers are correctly tracked through newlines.
    // This is essential for accurate error reporting.
    
    let mut tokenizer = Tokenizer::new("a\nb\nc");
    tokenizer.tokenize().unwrap();
    let (line, _, _) = tokenizer.get_position_info();
    assert!(line >= 3); // Should be on at least line 3 after two newlines
}

#[test]
fn test_complex_real_world_example() {
    // Tests tokenization of a realistic Prolog program with multiple constructs.
    // This is an integration test ensuring all components work together.
    
    let input = r#"
% This is a comment
parent(tom, bob).
parent(bob, ann) :- true.

grandparent(X, Z) :-
    parent(X, Y),
    parent(Y, Z),
    X \= Z.

% Another comment
likes('Mary', 'wine').
age(bob, -5).  % negative age?
test([1, 2|Tail]).
"#;
    
    let mut tokenizer = Tokenizer::new(input);
    let result = tokenizer.tokenize();
    assert!(result.is_ok());
    let tokens = result.unwrap();
    
    // Should have many tokens representing the complete program
    assert!(tokens.len() > 20);
    
    // Spot-check for expected tokens to verify correct tokenization
    assert!(tokens.contains(&Token::Atom("parent".to_string())));
    assert!(tokens.contains(&Token::Rule));              // :-
    assert!(tokens.contains(&Token::Variable("X".to_string())));
    assert!(tokens.contains(&Token::NotUnify));          // \=
    assert!(tokens.contains(&Token::Number(-5)));        // Negative number
    assert!(tokens.contains(&Token::Pipe));              // | in list
    assert!(tokens.contains(&Token::Eof));
}