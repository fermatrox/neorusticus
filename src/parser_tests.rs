// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: parser_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the parser module
//! 
//! This test suite validates all aspects of the Prolog parser including:
//! - Basic term parsing (atoms, variables, numbers)
//! - Compound terms and function calls
//! - List syntax and structures
//! - Operator precedence and associativity
//! - Error handling and recovery
//! - Edge cases and boundary conditions

use super::*;
use crate::lexer::Tokenizer;

/// Helper function to parse a term from a string
/// 
/// This simplifies testing by handling the full pipeline:
/// 1. Create a tokenizer with the input string
/// 2. Tokenize to get a vector of tokens
/// 3. Parse the tokens into a Term
/// 
/// The ? operator propagates any errors up to the test
fn parse_term_string(input: &str) -> ParseResult<Term> {
    let mut tokenizer = Tokenizer::new(input);
    let tokens = tokenizer.tokenize()?;
    Parser::parse_term_from_tokens(tokens)
}

/// Helper function to parse a clause from a string
/// 
/// Similar to parse_term_string but expects a complete clause
/// ending with a dot. Used for testing fact and rule parsing.
fn parse_clause_string(input: &str) -> ParseResult<Clause> {
    let mut tokenizer = Tokenizer::new(input);
    let tokens = tokenizer.tokenize()?;
    Parser::parse_clause_from_tokens(tokens)
}

#[test]
fn test_parse_atoms() {
    // Tests parsing of simple atoms (constants)
    // 
    // Atoms are the basic constants in Prolog, like 'hello' or 'foo'.
    // They start with lowercase letters and can contain letters, digits, and underscores.
    // This test verifies that a simple atom is correctly parsed into an Atom term.
    
    let term = parse_term_string("hello").unwrap();
    assert_eq!(term, Term::Atom("hello".to_string()));
}

#[test]
fn test_parse_variables() {
    // Tests parsing of Prolog variables
    // 
    // Variables in Prolog start with uppercase letters or underscore.
    // - X, Y, Z are typical variables
    // - _var is a named underscore variable
    // - _ alone is the anonymous variable
    // 
    // This test verifies both standard and underscore variables are parsed correctly.
    
    // Standard variable starting with uppercase
    let term = parse_term_string("X").unwrap();
    assert_eq!(term, Term::Variable("X".to_string()));
    
    // Underscore variable (often used for "don't care" values)
    let term = parse_term_string("_var").unwrap();
    assert_eq!(term, Term::Variable("_var".to_string()));
}

#[test]
fn test_parse_numbers() {
    // Tests parsing of integer literals
    // 
    // Prolog supports integer numbers (currently no floating point in our implementation).
    // This includes positive and negative integers.
    // The lexer handles negative numbers as single tokens (e.g., -17).
    
    // Positive number
    let term = parse_term_string("42").unwrap();
    assert_eq!(term, Term::Number(42));
    
    // Negative number (handled by lexer as a single token)
    let term = parse_term_string("-17").unwrap();
    assert_eq!(term, Term::Number(-17));
}

#[test]
fn test_parse_compound_terms() {
    // Tests parsing of compound terms (functors with arguments)
    // 
    // Compound terms are the primary structure in Prolog: functor(arg1, arg2, ...).
    // Examples: parent(tom, bob), likes(mary, X), foo(bar, baz(qux)).
    // 
    // This test verifies:
    // 1. The functor name is correctly identified
    // 2. Arguments are parsed in order
    // 3. Different argument types (atoms, variables) work correctly
    
    let term = parse_term_string("foo(bar, X)").unwrap();
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "foo");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], Term::Atom("bar".to_string()));  // First arg is an atom
            assert_eq!(args[1], Term::Variable("X".to_string())); // Second arg is a variable
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_parse_lists() {
    // Tests parsing of Prolog list syntax
    // 
    // Lists in Prolog have special syntax but are actually compound terms:
    // - [] is the empty list (an atom)
    // - [1, 2, 3] is syntactic sugar for .(1, .(2, .(3, [])))
    // - [H|T] is the list with head H and tail T
    // 
    // This test covers all three list forms.
    
    // Empty list - special atom
    let term = parse_term_string("[]").unwrap();
    assert_eq!(term, Term::Atom("[]".to_string()));
    
    // Simple list with elements
    // Should be parsed into nested dot structures
    let term = parse_term_string("[1, 2, 3]").unwrap();
    assert!(term.is_proper_list());
    let elements = term.to_list().unwrap();
    assert_eq!(elements.len(), 3);
    
    // List with tail notation [H|T]
    // Used for pattern matching and list decomposition
    let term = parse_term_string("[H|T]").unwrap();
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, ".");  // The dot functor represents cons
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], Term::Variable("H".to_string())); // Head
            assert_eq!(args[1], Term::Variable("T".to_string())); // Tail
        }
        _ => panic!("Expected compound term for list"),
    }
}

#[test]
fn test_parse_arithmetic() {
    // Tests operator precedence in arithmetic expressions
    // 
    // Prolog follows standard mathematical precedence:
    // - Multiplication (*) binds tighter than addition (+)
    // - So "2 + 3 * 4" should parse as "2 + (3 * 4)" = 14, not "(2 + 3) * 4" = 20
    // 
    // This test verifies the parser builds the correct AST structure
    // respecting operator precedence.
    
    let term = parse_term_string("2 + 3 * 4").unwrap();
    // Should parse as: 2 + (3 * 4) due to precedence
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "+");  // Top level is addition
            assert_eq!(args[0], Term::Number(2));  // Left operand is 2
            
            // Right operand should be the multiplication
            match &args[1] {
                Term::Compound(inner_op, inner_args) => {
                    assert_eq!(inner_op, "*");
                    assert_eq!(inner_args[0], Term::Number(3));
                    assert_eq!(inner_args[1], Term::Number(4));
                }
                _ => panic!("Expected multiplication term"),
            }
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_parse_comparison() {
    // Tests parsing of comparison operators
    // 
    // Comparison operators (>, <, >=, =<, =:=, =\=) have lower precedence
    // than arithmetic but higher than unification.
    // 
    // This test verifies a simple comparison is parsed correctly.
    
    let term = parse_term_string("X > 5").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, ">");
            assert_eq!(args[0], Term::Variable("X".to_string()));
            assert_eq!(args[1], Term::Number(5));
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_parse_unification() {
    // Tests parsing of unification operators
    // 
    // Unification operators (=, \=, is) have the lowest precedence.
    // - = is unification (structural equality)
    // - \= is non-unification
    // - is evaluates arithmetic on the right and unifies with left
    // 
    // This test verifies these operators are parsed correctly and
    // that 'is' properly captures arithmetic expressions on its right.
    
    // Simple unification
    let term = parse_term_string("X = hello").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "=");
            assert_eq!(args[0], Term::Variable("X".to_string()));
            assert_eq!(args[1], Term::Atom("hello".to_string()));
        }
        _ => panic!("Expected compound term"),
    }
    
    // Arithmetic evaluation with 'is'
    let term = parse_term_string("Y is 2 + 3").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "is");
            assert_eq!(args[0], Term::Variable("Y".to_string()));
            // args[1] should be the parsed arithmetic expression (2 + 3)
            // We don't check its structure here, but it should be a compound term
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_parse_facts() {
    // Tests parsing of facts (clauses with no body)
    // 
    // Facts are assertions that are always true, like parent(tom, bob).
    // They consist of just a head term followed by a dot.
    // 
    // This test verifies facts are correctly identified and parsed.
    
    let clause = parse_clause_string("parent(tom, bob).").unwrap();
    assert!(clause.is_fact());  // Should be recognized as a fact
    
    // Verify the head structure
    match clause.head {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "parent");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected compound head"),
    }
}

#[test]
fn test_parse_rules() {
    // Tests parsing of rules (clauses with body)
    // 
    // Rules define relationships: head :- body.
    // The body is a comma-separated list of goals that must be satisfied.
    // Example: grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
    // 
    // This test verifies:
    // 1. Rules are distinguished from facts
    // 2. The head is parsed correctly
    // 3. Body goals are parsed as a list
    
    let clause = parse_clause_string("grandparent(X, Z) :- parent(X, Y), parent(Y, Z).").unwrap();
    assert!(clause.is_rule());  // Should be recognized as a rule
    assert_eq!(clause.body.len(), 2);  // Should have 2 goals in body
    
    // Check head structure
    if let Some(("grandparent", 2)) = clause.head.functor_arity() {
        // Head is grandparent/2 as expected
    } else {
        panic!("Expected grandparent/2 head");
    }
}

#[test]
fn test_parse_cut() {
    // Tests parsing of the cut operator (!)
    // 
    // The cut operator prevents backtracking in Prolog.
    // It's represented as a special atom "!".
    // 
    // This test verifies the cut is recognized and parsed correctly.
    
    let term = parse_term_string("!").unwrap();
    assert_eq!(term, Term::Atom("!".to_string()));
}

#[test]
fn test_parse_parentheses() {
    // Tests that parentheses correctly override operator precedence
    // 
    // Parentheses allow overriding the default precedence rules.
    // "(2 + 3) * 4" should parse differently from "2 + 3 * 4".
    // 
    // This test verifies parentheses create the expected AST structure.
    
    let term = parse_term_string("(2 + 3) * 4").unwrap();
    // Should parse as: (2 + 3) * 4, not 2 + (3 * 4)
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "*");  // Multiplication is at top level
            
            // Left operand should be the addition
            match &args[0] {
                Term::Compound(inner_op, inner_args) => {
                    assert_eq!(inner_op, "+");
                    assert_eq!(inner_args[0], Term::Number(2));
                    assert_eq!(inner_args[1], Term::Number(3));
                }
                _ => panic!("Expected addition term"),
            }
            assert_eq!(args[1], Term::Number(4));  // Right operand is 4
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_operator_precedence() {
    // Tests that operator precedence is correctly implemented
    // 
    // This is a critical test ensuring mathematical expressions are
    // parsed according to standard precedence rules.
    // Without parentheses, * should bind tighter than +.
    // 
    // 1 + 2 * 3 should equal 1 + 6 = 7, not 3 * 3 = 9
    
    let term = parse_term_string("1 + 2 * 3").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "+");  // Addition at top level
            assert_eq!(args[0], Term::Number(1));
            
            // Multiplication should be nested on the right
            match &args[1] {
                Term::Compound(mult_op, mult_args) => {
                    assert_eq!(mult_op, "*");
                    assert_eq!(mult_args[0], Term::Number(2));
                    assert_eq!(mult_args[1], Term::Number(3));
                }
                _ => panic!("Expected multiplication"),
            }
        }
        _ => panic!("Expected addition at top level"),
    }
}

#[test]
fn test_error_handling() {
    // Tests various error conditions and proper error reporting
    // 
    // The parser should gracefully handle various error conditions:
    // 1. Unclosed parentheses (caught by lexer)
    // 2. Incomplete expressions (operator without operand)
    // 3. Invalid token positions (operator in primary position)
    // 4. Mismatched delimiters
    // 5. Unclosed function calls
    // 
    // This test verifies errors are detected and reported correctly.
    
    // Test unclosed parenthesis - this should be caught by the lexer first
    let mut tokenizer = Tokenizer::new("foo(bar");
    let result = tokenizer.tokenize();
    assert!(result.is_err(), "Lexer should catch unclosed parenthesis");
    
    // Test incomplete expression - operator without right operand
    let tokens = vec![Token::Variable("X".to_string()), Token::Plus, Token::Eof];
    let mut parser = Parser::new(tokens);
    let result = parser.parse_expression();
    assert!(result.is_err(), "Parser should reject incomplete expressions");
    
    // Test unexpected token in primary position
    // Plus operator can't start an expression
    let tokens = vec![Token::Plus, Token::Eof];
    let mut parser = Parser::new(tokens);
    let result = parser.parse_expression();
    assert!(result.is_err(), "Parser should reject expression starting with operator");
    
    // Test mismatched parentheses (caught by lexer)
    let result = parse_term_string("foo)");
    assert!(result.is_err(), "Should reject unexpected closing parenthesis");
    
    // Test incomplete compound term
    let result = parse_term_string("foo(");
    assert!(result.is_err(), "Should reject unclosed function call");
}

#[test]
fn test_complex_expressions() {
    // Tests parsing of complex clauses with multiple goals
    // 
    // Real Prolog programs have rules with multiple conditions.
    // This test verifies that a rule with multiple different types
    // of goals (comparison, arithmetic, etc.) is parsed correctly.
    // 
    // The rule: test(X, Y) :- X > 0, Y is X * 2, Y < 20.
    // Has three different goal types that should all parse correctly.
    
    let clause = parse_clause_string("test(X, Y) :- X > 0, Y is X * 2, Y < 20.").unwrap();
    assert!(clause.is_rule());
    assert_eq!(clause.body.len(), 3);  // Three goals in the body
    
    // Verify the goals are parsed correctly
    let goals = &clause.body;
    
    // First goal: X > 0 (comparison)
    if let Term::Compound(op, args) = &goals[0] {
        assert_eq!(op, ">");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected comparison in first goal");
    }
    
    // Second goal: Y is X * 2 (arithmetic evaluation)
    if let Term::Compound(op, args) = &goals[1] {
        assert_eq!(op, "is");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected 'is' in second goal");
    }
    
    // Third goal: Y < 20 (comparison)
    if let Term::Compound(op, args) = &goals[2] {
        assert_eq!(op, "<");
        assert_eq!(args.len(), 2);
    } else {
        panic!("Expected comparison in third goal");
    }
}

// Additional comprehensive tests

#[test]
fn test_empty_input() {
    // Tests parsing an empty program
    // 
    // An empty token stream (just EOF) should produce an empty program.
    // This is a valid edge case - a Prolog file can be empty.
    
    let tokens = vec![Token::Eof];
    let mut parser = Parser::new(tokens);
    let result = parser.parse_program();
    assert!(result.is_ok());
    assert_eq!(result.unwrap().len(), 0);
}

#[test]
fn test_empty_argument_list() {
    // Tests parsing compound terms with no arguments
    // 
    // In Prolog, foo() is different from the atom foo.
    // foo() is a compound term with 0 arguments.
    // 
    // This distinction is important for predicate matching.
    
    let term = parse_term_string("foo()").unwrap();
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "foo");
            assert_eq!(args.len(), 0);  // Empty argument list
        }
        _ => panic!("Expected compound term with no arguments"),
    }
}

#[test]
fn test_nested_lists() {
    // Tests parsing of nested list structures
    // 
    // Lists can contain other lists: [[1, 2], [3, 4]].
    // This creates nested dot structures.
    // 
    // This test verifies the parser correctly handles
    // multiple levels of list nesting.
    
    let term = parse_term_string("[[1, 2], [3, 4]]").unwrap();
    assert!(term.is_proper_list());
    let elements = term.to_list().unwrap();
    assert_eq!(elements.len(), 2);
    assert!(elements[0].is_proper_list());  // First element is also a list
    assert!(elements[1].is_proper_list());  // Second element is also a list
}

#[test]
fn test_list_with_tail_variable() {
    // Tests parsing lists with tail variables
    // 
    // [1, 2|X] represents a list starting with 1 and 2,
    // with X as the remaining tail (which could be any list).
    // 
    // This is not a "proper list" because it doesn't end with [].
    
    let term = parse_term_string("[1, 2|X]").unwrap();
    assert!(!term.is_proper_list()); // Not a proper list due to variable tail
}

#[test]
fn test_complex_list_patterns() {
    // Tests parsing of complex list patterns used in pattern matching
    // 
    // [H1, H2|T] is a common pattern for matching lists with at least
    // two elements, where H1 is the first, H2 is the second, and T is the rest.
    // 
    // This should create: .(H1, .(H2, T))
    
    let term = parse_term_string("[H1, H2|T]").unwrap();
    match term {
        Term::Compound(functor, args) if functor == "." => {
            assert_eq!(args[0], Term::Variable("H1".to_string()));
            
            // The tail should be another dot structure
            match &args[1] {
                Term::Compound(f2, args2) if f2 == "." => {
                    assert_eq!(args2[0], Term::Variable("H2".to_string()));
                    assert_eq!(args2[1], Term::Variable("T".to_string()));
                }
                _ => panic!("Expected nested list structure"),
            }
        }
        _ => panic!("Expected list structure"),
    }
}

#[test]
fn test_parse_with_recovery() {
    // Tests the error recovery mechanism
    // 
    // The parser should be able to recover from errors and continue
    // parsing subsequent clauses. This is important for IDEs and tools
    // that want to show multiple errors at once.
    // 
    // We create a token stream with:
    // 1. A valid clause
    // 2. An invalid clause (dot inside parentheses)
    // 3. Another valid clause
    // 
    // The parser should parse clauses 1 and 3, reporting an error for 2.
    
    let tokens = vec![
        Token::Atom("valid".to_string()),
        Token::LeftParen,
        Token::Atom("a".to_string()),
        Token::RightParen,
        Token::Dot,
        Token::Atom("invalid".to_string()),
        Token::LeftParen,
        Token::Dot,  // Invalid: dot inside parentheses
        Token::RightParen,
        Token::Dot,
        Token::Atom("another".to_string()),
        Token::LeftParen,
        Token::Atom("b".to_string()),
        Token::RightParen,
        Token::Dot,
        Token::Eof,
    ];
    let mut parser = Parser::new(tokens);
    let (clauses, errors) = parser.parse_with_recovery();
    
    // Should parse at least first and last clause
    assert!(clauses.len() >= 2, "Should parse at least first and last clause");
    assert!(!errors.is_empty(), "Should have errors for invalid clause");
    
    // Verify the valid clauses
    if let Term::Compound(name, _) = &clauses[0].head {
        assert_eq!(name, "valid");
    }
    
    // The last successfully parsed clause should be "another"
    if let Some(last_clause) = clauses.last() {
        if let Term::Compound(name, _) = &last_clause.head {
            assert_eq!(name, "another");
        }
    }
}

#[test]
fn test_validate_clause_head() {
    // Tests validation of clause heads
    // 
    // Not all terms can be clause heads in Prolog:
    // - Valid: atoms (foo) and compound terms (foo(X))
    // - Invalid: variables (X) and numbers (42)
    // 
    // This ensures semantic correctness of Prolog programs.
    
    // Valid heads
    assert!(Parser::validate_clause_head(&Term::Atom("foo".to_string())).is_ok());
    assert!(Parser::validate_clause_head(&Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string())
    ])).is_ok());
    
    // Invalid heads
    assert!(Parser::validate_clause_head(&Term::Variable("X".to_string())).is_err());
    assert!(Parser::validate_clause_head(&Term::Number(42)).is_err());
}

#[test]
fn test_all_operators() {
    // Tests that all Prolog operators are parsed correctly
    // 
    // This comprehensive test ensures every operator token is
    // correctly converted to its string representation in the AST.
    // 
    // It's important that operators maintain their exact string form
    // for proper evaluation later (e.g., "=<" not "<=" for Prolog).
    
    let tests = vec![
        ("X = Y", "="),          // Unification
        ("X \\= Y", "\\="),      // Non-unification
        ("X is Y", "is"),        // Arithmetic evaluation
        ("X > Y", ">"),          // Greater than
        ("X < Y", "<"),          // Less than
        ("X >= Y", ">="),        // Greater or equal
        ("X =< Y", "=<"),        // Less or equal (Prolog style)
        ("X =:= Y", "=:="),      // Arithmetic equality
        ("X =\\= Y", "=\\="),    // Arithmetic inequality
        ("X + Y", "+"),          // Addition
        ("X - Y", "-"),          // Subtraction
        ("X * Y", "*"),          // Multiplication
        ("X // Y", "//"),        // Integer division
        ("X mod Y", "mod"),      // Modulo
    ];
    
    for (input, expected_op) in tests {
        let term = parse_term_string(input).unwrap();
        if let Term::Compound(op, args) = term {
            assert_eq!(op, expected_op, "Failed for input: {}", input);
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected compound term for: {}", input);
        }
    }
}

#[test]
fn test_operator_associativity() {
    // Tests left associativity of operators
    // 
    // Binary operators in Prolog are left-associative:
    // 1 + 2 + 3 parses as (1 + 2) + 3, not 1 + (2 + 3).
    // 
    // While mathematically equivalent for addition, this matters
    // for non-associative operations and for AST structure.
    
    let term = parse_term_string("1 + 2 + 3").unwrap();
    // Should parse as (1 + 2) + 3 due to left associativity
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "+");
            assert_eq!(args[1], Term::Number(3));  // Right operand is 3
            
            // Left operand should be (1 + 2)
            match &args[0] {
                Term::Compound(inner_op, inner_args) => {
                    assert_eq!(inner_op, "+");
                    assert_eq!(inner_args[0], Term::Number(1));
                    assert_eq!(inner_args[1], Term::Number(2));
                }
                _ => panic!("Expected nested addition"),
            }
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_mixed_operators() {
    // Tests complex expressions with multiple operator types
    // 
    // This verifies that operators at different precedence levels
    // interact correctly. The expression X = Y + 2 * 3 should parse as:
    // X = (Y + (2 * 3))
    // 
    // Precedence order: * > + > =
    
    let term = parse_term_string("X = Y + 2 * 3").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "=");  // Unification at top level
            assert_eq!(args[0], Term::Variable("X".to_string()));
            
            // Right side: Y + (2 * 3)
            match &args[1] {
                Term::Compound(plus_op, plus_args) => {
                    assert_eq!(plus_op, "+");
                    assert_eq!(plus_args[0], Term::Variable("Y".to_string()));
                    
                    // Multiplication nested deeper
                    match &plus_args[1] {
                        Term::Compound(mult_op, mult_args) => {
                            assert_eq!(mult_op, "*");
                            assert_eq!(mult_args[0], Term::Number(2));
                            assert_eq!(mult_args[1], Term::Number(3));
                        }
                        _ => panic!("Expected multiplication"),
                    }
                }
                _ => panic!("Expected addition"),
            }
        }
        _ => panic!("Expected unification"),
    }
}

#[test]
fn test_query_parsing() {
    // Tests parsing of queries with multiple goals
    // 
    // Queries are comma-separated lists of goals ending with ? or .
    // Example: parent(X, Y), ancestor(Y, Z)?
    // 
    // This should parse into a vector of two goal terms.
    
    let mut tokenizer = Tokenizer::new("parent(X, Y), ancestor(Y, Z)?");
    let tokens = tokenizer.tokenize().unwrap();
    let query = Parser::parse_query_from_tokens(tokens).unwrap();
    assert_eq!(query.len(), 2);  // Two goals in the query
}

#[test]
fn test_multiple_clauses() {
    // Tests parsing a program with multiple clauses
    // 
    // A Prolog program consists of multiple clauses separated by dots.
    // This test verifies:
    // 1. Multiple clauses are parsed in order
    // 2. Facts and rules are correctly distinguished
    // 3. Dots properly separate clauses
    
    let mut tokenizer = Tokenizer::new("fact1. fact2. rule :- body.");
    let tokens = tokenizer.tokenize().unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();
    
    assert_eq!(program.len(), 3);
    assert!(program[0].is_fact());  // fact1
    assert!(program[1].is_fact());  // fact2
    assert!(program[2].is_rule());  // rule :- body
}

#[test]
fn test_skip_extra_dots() {
    // Tests tolerance for extra dots between clauses
    // 
    // Users might accidentally type extra dots.
    // The parser should skip these gracefully rather than failing.
    // 
    // "fact1.. fact2..." should still parse as two facts.
    
    let mut tokenizer = Tokenizer::new("fact1.. fact2...");
    let tokens = tokenizer.tokenize().unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap();
    assert_eq!(program.len(), 2);  // Should still get two clauses
}

#[test]
fn test_unary_minus() {
    // Tests parsing of unary minus operator
    // 
    // While the lexer handles negative number literals (-5),
    // the parser needs to handle unary minus as an operator
    // in cases where it's not part of a number literal.
    // 
    // This creates: -(5) as a compound term.
    
    let tokens = vec![Token::Minus, Token::Number(5), Token::Eof];
    let mut parser = Parser::new(tokens);
    let result = parser.parse_primary();
    assert!(result.is_ok());
    
    if let Ok(Term::Compound(op, args)) = result {
        assert_eq!(op, "-");
        assert_eq!(args.len(), 1);
        assert_eq!(args[0], Term::Number(5));
    } else {
        panic!("Expected unary minus compound");
    }
}

#[test]
fn test_boundary_conditions() {
    // Tests parser behavior at token stream boundaries
    // 
    // This verifies:
    // 1. Position tracking works correctly
    // 2. EOF detection works
    // 3. Advancing past EOF is safe
    // 4. Multiple tokens are handled correctly
    // 
    // These boundary conditions are important for parser robustness.
    
    let tokens = vec![Token::Atom("test".to_string()), Token::Eof];
    let mut parser = Parser::new(tokens.clone());
    
    assert_eq!(parser.position(), 0);
    assert!(!parser.is_at_end());
    
    parser.advance();
    assert_eq!(parser.position(), 1);
    assert!(parser.is_at_end()); // At EOF token, so we're at end
    
    // Advancing past EOF should be safe
    parser.advance();
    assert_eq!(parser.position(), 2);
    assert!(parser.is_at_end());
    
    // Test with more tokens
    let tokens2 = vec![
        Token::Atom("a".to_string()),
        Token::Atom("b".to_string()),
        Token::Eof,
    ];
    let mut parser2 = Parser::new(tokens2);
    
    assert!(!parser2.is_at_end());
    parser2.advance(); // to "b"
    assert!(!parser2.is_at_end());
    parser2.advance(); // to EOF
    assert!(parser2.is_at_end());
}

#[test]
fn test_peek_token_at_end() {
    // Tests token peeking behavior at stream boundaries
    // 
    // peek_token() should safely return EOF when peeking
    // past the end of the token stream. This is important
    // for lookahead parsing decisions.
    
    let tokens = vec![Token::Atom("test".to_string()), Token::Eof];
    let parser = Parser::new(tokens);
    
    assert_eq!(*parser.peek_token(), Token::Eof);
    
    // Even when already at EOF, peeking should return EOF
    let tokens2 = vec![Token::Eof];
    let mut parser2 = Parser::new(tokens2);
    parser2.advance();
    assert_eq!(*parser2.peek_token(), Token::Eof);
}

#[test]
fn test_remaining_tokens() {
    // Tests the remaining_tokens debug helper
    // 
    // This function is useful for debugging parser state
    // by showing what tokens are left to process.
    // 
    // Verifies the count decreases as tokens are consumed.
    
    let tokens = vec![
        Token::Atom("a".to_string()),
        Token::Atom("b".to_string()),
        Token::Atom("c".to_string()),
        Token::Eof,
    ];
    let mut parser = Parser::new(tokens);
    
    assert_eq!(parser.remaining_tokens().len(), 4);  // All tokens
    parser.advance();
    assert_eq!(parser.remaining_tokens().len(), 3);  // b, c, EOF
    parser.advance();
    assert_eq!(parser.remaining_tokens().len(), 2);  // c, EOF
}

#[test]
fn test_check_method() {
    // Tests the check() method for token type matching
    // 
    // check() uses discriminant comparison to match token types
    // without comparing the associated data. This means
    // Token::Atom("test") matches Token::Atom("any").
    // 
    // This is crucial for the parser's conditional logic.
    
    let tokens = vec![Token::Atom("test".to_string()), Token::Eof];
    let parser = Parser::new(tokens);
    
    assert!(parser.check(&Token::Atom("any".to_string()))); // Checks type only
    assert!(!parser.check(&Token::Variable("X".to_string())));
    assert!(!parser.check(&Token::Eof));
}

#[test]
fn test_error_position() {
    // Tests that parse errors include correct position information
    // 
    // When parsing fails, the error should indicate where
    // in the token stream the problem occurred.
    // 
    // This is essential for good error messages.
    
    let tokens = vec![Token::Plus, Token::Eof];
    let mut parser = Parser::new(tokens);
    let result = parser.parse_primary();
    
    assert!(result.is_err());
    if let Err(ParseError::UnexpectedToken { position, .. }) = result {
        assert_eq!(position.offset, 0); // Error at the Plus token
    }
}

#[test]
fn test_circular_reference_prevention() {
    // Tests that the parser handles deeply nested structures safely
    // 
    // The parser should handle recursive structures without
    // stack overflow or infinite loops. This tests:
    // 1. Deep nesting (many levels of function calls)
    // 2. Long argument lists
    // 3. Recursive-looking structures
    // 
    // The parser is naturally protected because it consumes
    // tokens linearly - no actual circular references are possible.
    
    // Deeply nested structures
    let deep_nest = "f(g(h(i(j(k(l(m(n(o(p(q(atom))))))))))))";
    let result = parse_term_string(deep_nest);
    assert!(result.is_ok());
    
    // Long argument lists
    let many_args = "pred(a1, a2, a3, a4, a5, a6, a7, a8, a9, a10)";
    let result = parse_term_string(many_args);
    assert!(result.is_ok());
    
    // Recursive-looking structures (same functor nested)
    let tokens = vec![
        Token::Atom("recursive".to_string()),
        Token::LeftParen,
        Token::Atom("recursive".to_string()),
        Token::LeftParen,
        Token::Atom("base".to_string()),
        Token::RightParen,
        Token::RightParen,
        Token::Eof,
    ];
    let mut parser = Parser::new(tokens);
    let result = parser.parse_term();
    assert!(result.is_ok());
}

#[test]
fn test_expect_method_error() {
    // Tests the expect() method's error reporting
    // 
    // When expect() fails (token doesn't match), it should:
    // 1. Return an error
    // 2. Include what was expected in the error message
    // 3. Not advance the parser position
    // 
    // This test verifies proper error construction.
    
    let tokens = vec![Token::Atom("test".to_string()), Token::Eof];
    let mut parser = Parser::new(tokens);
    
    let result = parser.expect(Token::Variable("X".to_string()));
    assert!(result.is_err());
    
    if let Err(ParseError::UnexpectedToken { expected, .. }) = result {
        assert!(expected.is_some());
        // Check if any string in the vector contains "variable"
        let expected_vec = expected.unwrap();
        assert!(expected_vec.iter().any(|s| s.contains("variable")));
    }
}