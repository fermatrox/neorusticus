// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: ast_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the ast module
//! 
//! This test suite covers all functionality of the Term and Clause types,
//! including edge cases, boundary conditions, and error scenarios.

use super::*;

// ===== TERM CREATION AND DISPLAY TESTS =====
// These tests verify that terms can be created and displayed correctly

#[test]
fn test_term_creation_and_display() {
    // Test basic term creation and their string representation
    // This verifies that the Display trait is implemented correctly for all term types
    
    // Atom: constant in Prolog like 'hello' or 'foo'
    let atom = Term::Atom("hello".to_string());
    assert_eq!(format!("{}", atom), "hello");
    
    // Variable: starts with uppercase or underscore in Prolog
    let var = Term::Variable("X".to_string());
    assert_eq!(format!("{}", var), "X");
    
    // Number: integer literal
    let num = Term::Number(42);
    assert_eq!(format!("{}", num), "42");
    
    // Compound: functor with arguments, like foo(bar, X)
    let compound = Term::Compound("foo".to_string(), vec![
        Term::Atom("bar".to_string()),
        Term::Variable("X".to_string())
    ]);
    assert_eq!(format!("{}", compound), "foo(bar, X)");
}

#[test]
fn test_empty_atom() {
    // Edge case: empty string as an atom
    // While unusual, empty atoms are valid in some Prolog implementations
    let atom = Term::Atom("".to_string());
    assert_eq!(format!("{}", atom), "");
    assert!(atom.is_atom());
    // Empty atom still has functor/arity (with arity 0)
    assert_eq!(atom.functor_arity(), Some(("", 0)));
}

#[test]
fn test_negative_numbers() {
    // Test negative numbers and boundary values
    // Important for arithmetic operations and ensuring no overflow issues
    
    let neg = Term::Number(-42);
    assert_eq!(format!("{}", neg), "-42");
    assert!(neg.is_number());
    assert_eq!(neg.as_number(), Some(-42));
    
    // Test extreme values - minimum i64
    let min_int = Term::Number(i64::MIN);
    assert_eq!(min_int.as_number(), Some(i64::MIN));
    
    // Test extreme values - maximum i64
    let max_int = Term::Number(i64::MAX);
    assert_eq!(max_int.as_number(), Some(i64::MAX));
}

#[test]
fn test_compound_with_no_args() {
    // Edge case: compound term with zero arguments
    // In Prolog, foo() is different from the atom foo
    let compound = Term::Compound("foo".to_string(), vec![]);
    assert_eq!(format!("{}", compound), "foo()");
    assert_eq!(compound.functor_arity(), Some(("foo", 0)));
    assert!(compound.is_compound());
}

#[test]
fn test_deeply_nested_compound() {
    // Test deeply nested structure: f(g(h(1)))
    // Verifies that recursive structures are handled correctly
    // Also tests the size() function with nested terms
    let nested = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![
            Term::Compound("h".to_string(), vec![
                Term::Number(1)
            ])
        ])
    ]);
    assert_eq!(format!("{}", nested), "f(g(h(1)))");
    // Size should count all subterms: f + g + h + 1 = 4
    assert_eq!(nested.size(), 4);
}

// ===== FUNCTOR ARITY TESTS =====
// Tests for getting the functor name and arity of terms

#[test]
fn test_functor_arity() {
    // Test that functor_arity returns correct values for different term types
    // In Prolog, predicates are identified by functor/arity (e.g., append/3)
    
    // Atom has functor with arity 0
    let atom = Term::Atom("hello".to_string());
    assert_eq!(atom.functor_arity(), Some(("hello", 0)));
    
    // Compound has functor with arity equal to number of arguments
    let compound = Term::Compound("foo".to_string(), vec![
        Term::Atom("bar".to_string()),
        Term::Variable("X".to_string())
    ]);
    assert_eq!(compound.functor_arity(), Some(("foo", 2)));
    
    // Variables don't have functors
    let var = Term::Variable("X".to_string());
    assert_eq!(var.functor_arity(), None);
    
    // Numbers don't have functors
    let num = Term::Number(42);
    assert_eq!(num.functor_arity(), None);
}

// ===== TYPE CHECK TESTS =====
// Tests for the is_* predicate functions

#[test]
fn test_type_checks() {
    // Test all type checking predicates
    // These are used throughout the codebase to determine term types
    // Each term type should return true for its own check and false for others
    
    let atom = Term::Atom("hello".to_string());
    assert!(atom.is_atom());
    assert!(!atom.is_variable());
    assert!(!atom.is_compound());
    assert!(!atom.is_number());
    
    let var = Term::Variable("X".to_string());
    assert!(var.is_variable());
    assert!(!var.is_atom());
    assert!(!var.is_compound());
    assert!(!var.is_number());
    
    let num = Term::Number(42);
    assert!(num.is_number());
    assert!(!num.is_compound());
    assert!(!num.is_atom());
    assert!(!num.is_variable());
    
    // Even empty compound is still a compound
    let compound = Term::Compound("foo".to_string(), vec![]);
    assert!(compound.is_compound());
    assert!(!compound.is_atom());
    assert!(!compound.is_variable());
    assert!(!compound.is_number());
}

// ===== LIST OPERATION TESTS =====
// Tests for Prolog list handling

#[test]
fn test_list_operations() {
    // Test proper list creation, detection, and conversion
    // In Prolog, [1, 2, 3] is syntactic sugar for .(1, .(2, .(3, [])))
    
    // Create a list [1, 2, 3] using from_list
    let list = Term::from_list(vec![
        Term::Number(1),
        Term::Number(2),
        Term::Number(3)
    ]);
    
    // Verify it's recognized as a proper list
    assert!(list.is_proper_list());
    
    // Convert back to Vec and verify elements
    let elements = list.to_list().unwrap();
    assert_eq!(elements.len(), 3);
    assert_eq!(elements[0], Term::Number(1));
    assert_eq!(elements[1], Term::Number(2));
    assert_eq!(elements[2], Term::Number(3));
    
    // Test display format uses square bracket notation
    assert_eq!(format!("{}", list), "[1, 2, 3]");
    
    // Test empty list (special atom "[]")
    let empty = Term::Atom("[]".to_string());
    assert!(empty.is_proper_list());
    assert_eq!(empty.to_list().unwrap().len(), 0);
}

#[test]
fn test_improper_list() {
    // Test improper list: [1|X]
    // This is a list that doesn't end with [], but with a variable
    // Common in Prolog for pattern matching like [H|T]
    
    let improper = Term::Compound(".".to_string(), vec![
        Term::Number(1),
        Term::Variable("X".to_string())
    ]);
    
    // Should not be recognized as a proper list
    assert!(!improper.is_proper_list());
    // to_list should return None for improper lists
    assert!(improper.to_list().is_none());
    // Display should use pipe notation for improper lists
    assert_eq!(format!("{}", improper), "[1|X]");
}

#[test]
fn test_list_with_compound_elements() {
    // Test list containing different types of elements
    // Lists can contain any terms: atoms, compounds, variables, even other lists
    
    let list = Term::from_list(vec![
        Term::Compound("foo".to_string(), vec![Term::Number(1)]),
        Term::Atom("bar".to_string()),
        Term::Variable("X".to_string())
    ]);
    
    assert!(list.is_proper_list());
    let elements = list.to_list().unwrap();
    assert_eq!(elements.len(), 3);
    // Display should handle complex elements correctly
    assert_eq!(format!("{}", list), "[foo(1), bar, X]");
}

#[test]
fn test_empty_list_conversion() {
    // Test converting empty Vec to Prolog list
    // Should produce the special empty list atom "[]"
    
    let empty_vec: Vec<Term> = vec![];
    let empty_list = Term::from_list(empty_vec);
    assert_eq!(empty_list, Term::Atom("[]".to_string()));
    assert!(empty_list.is_proper_list());
}

#[test]
fn test_single_element_list() {
    // Edge case: list with single element [42]
    // Should be .(42, [])
    
    let list = Term::from_list(vec![Term::Number(42)]);
    assert!(list.is_proper_list());
    let elements = list.to_list().unwrap();
    assert_eq!(elements.len(), 1);
    assert_eq!(elements[0], Term::Number(42));
    assert_eq!(format!("{}", list), "[42]");
}

// ===== VARIABLE COLLECTION TESTS =====
// Tests for extracting variables from terms

#[test]
fn test_variable_collection() {
    // Test that variables() correctly collects all unique variables
    // Variables can appear multiple times but should only be listed once
    
    let term = Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Compound("bar".to_string(), vec![
            Term::Variable("Y".to_string()),
            Term::Variable("X".to_string()), // Duplicate X
        ])
    ]);
    
    let vars = term.variables();
    // Should have exactly 2 unique variables
    assert_eq!(vars.len(), 2);
    assert!(vars.contains(&&"X".to_string()));
    assert!(vars.contains(&&"Y".to_string()));
}

#[test]
fn test_no_variables() {
    // Test term with no variables (ground term)
    // Ground terms are fully instantiated with no unbound variables
    
    let term = Term::Compound("foo".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Number(42)
    ]);
    
    let vars = term.variables();
    assert_eq!(vars.len(), 0);
}

#[test]
fn test_underscore_variable() {
    // Test underscore variables (anonymous variables in Prolog)
    // Each underscore is treated as a different variable
    
    let term = Term::Compound("foo".to_string(), vec![
        Term::Variable("_".to_string()),
        Term::Variable("_123".to_string())
    ]);
    
    let vars = term.variables();
    // Both underscore variables should be collected
    assert_eq!(vars.len(), 2);
}

// ===== GROUND TERM TESTS =====
// Tests for checking if terms contain variables

#[test]
fn test_ground_terms() {
    // Test is_ground() predicate
    // Ground terms have no variables and are fully instantiated
    
    // Term with only atoms and numbers is ground
    let ground_term = Term::Compound("foo".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Number(42)
    ]);
    assert!(ground_term.is_ground());
    
    // Term with at least one variable is not ground
    let non_ground_term = Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Number(42)
    ]);
    assert!(!non_ground_term.is_ground());
}

#[test]
fn test_ground_deeply_nested() {
    // Test is_ground() with deeply nested structures
    // All nested terms must be ground for the whole term to be ground
    
    // Nested term with no variables
    let ground = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![
            Term::Compound("h".to_string(), vec![
                Term::Atom("a".to_string())
            ])
        ])
    ]);
    assert!(ground.is_ground());
    
    // Same structure but with one variable deep inside
    let non_ground = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![
            Term::Compound("h".to_string(), vec![
                Term::Variable("X".to_string())
            ])
        ])
    ]);
    assert!(!non_ground.is_ground());
}

// ===== ACCESSOR METHOD TESTS =====
// Tests for safe accessor methods that return Option

#[test]
fn test_accessor_methods() {
    // Test as_* methods that safely extract values from specific term types
    // These return Some(value) for the correct type, None for others
    
    // Variable accessor
    let var = Term::Variable("X".to_string());
    assert_eq!(var.as_variable(), Some(&"X".to_string()));
    assert_eq!(var.as_atom(), None);
    assert_eq!(var.as_number(), None);
    assert_eq!(var.as_compound(), None);
    
    // Atom accessor
    let atom = Term::Atom("hello".to_string());
    assert_eq!(atom.as_atom(), Some(&"hello".to_string()));
    assert_eq!(atom.as_variable(), None);
    assert_eq!(atom.as_number(), None);
    assert_eq!(atom.as_compound(), None);
    
    // Number accessor (returns value, not reference)
    let num = Term::Number(42);
    assert_eq!(num.as_number(), Some(42));
    assert_eq!(num.as_atom(), None);
    assert_eq!(num.as_variable(), None);
    assert_eq!(num.as_compound(), None);
    
    // Compound accessor returns both functor and args
    let compound = Term::Compound("foo".to_string(), vec![Term::Atom("bar".to_string())]);
    if let Some((functor, args)) = compound.as_compound() {
        assert_eq!(functor, "foo");
        assert_eq!(args.len(), 1);
    } else {
        panic!("Expected compound term");
    }
    assert_eq!(compound.as_atom(), None);
    assert_eq!(compound.as_variable(), None);
    assert_eq!(compound.as_number(), None);
}

// ===== TERM SIZE TESTS =====
// Tests for counting subterms

#[test]
fn test_term_size() {
    // Test size() function that counts all subterms
    // Useful for term complexity analysis
    
    // Atomic terms have size 1
    let atom = Term::Atom("hello".to_string());
    assert_eq!(atom.size(), 1);
    
    // Compound counts itself plus all nested terms
    // foo(bar, baz(42)) = foo + bar + baz + 42 = 4
    let compound = Term::Compound("foo".to_string(), vec![
        Term::Atom("bar".to_string()),
        Term::Compound("baz".to_string(), vec![Term::Number(42)])
    ]);
    assert_eq!(compound.size(), 4);
}

#[test]
fn test_size_empty_compound() {
    // Edge case: compound with no arguments still has size 1
    let compound = Term::Compound("foo".to_string(), vec![]);
    assert_eq!(compound.size(), 1);
}

#[test]
fn test_size_large_list() {
    // Test size with a large list structure
    // Lists are represented as nested compound terms
    // [1,2,...,100] has 100 numbers + 100 cons cells + 1 nil = 201
    
    let list = Term::from_list((0..100).map(Term::Number).collect());
    assert_eq!(list.size(), 201);
}

// ===== CLAUSE TESTS =====
// Tests for Prolog clauses (facts and rules)

#[test]
fn test_clause_creation() {
    // Test creating facts (clauses with no body) and rules (clauses with body)
    
    // Fact: statement that is always true
    let fact = Clause::fact(Term::Atom("parent(tom, bob)".to_string()));
    assert!(fact.is_fact());
    assert!(!fact.is_rule());
    
    // Rule: head is true if body conditions are met
    let rule = Clause::rule(
        Term::Atom("grandparent(X, Z)".to_string()),
        vec![
            Term::Atom("parent(X, Y)".to_string()),
            Term::Atom("parent(Y, Z)".to_string()),
        ]
    );
    assert!(rule.is_rule());
    assert!(!rule.is_fact());
}

#[test]
fn test_clause_display() {
    // Test Display formatting for clauses
    // Facts show as "head"
    // Rules show as "head :- body1, body2, ..."
    
    let fact = Clause::fact(Term::Atom("likes(mary, wine)".to_string()));
    assert_eq!(format!("{}", fact), "likes(mary, wine)");
    
    let rule = Clause::rule(
        Term::Atom("happy(X)".to_string()),
        vec![Term::Atom("likes(X, wine)".to_string())]
    );
    assert_eq!(format!("{}", rule), "happy(X) :- likes(X, wine)");
}

#[test]
fn test_clause_with_multiple_goals() {
    // Test rule with multiple goals in the body
    // Goals are separated by commas in the display
    
    let rule = Clause::rule(
        Term::Compound("ancestor".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Variable("Z".to_string())
        ]),
        vec![
            Term::Compound("parent".to_string(), vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string())
            ]),
            Term::Compound("parent".to_string(), vec![
                Term::Variable("Y".to_string()),
                Term::Variable("Z".to_string())
            ])
        ]
    );
    
    assert_eq!(rule.body.len(), 2);
    assert!(rule.is_rule());
    let display = format!("{}", rule);
    // Check for rule operator and comma separator
    assert!(display.contains(" :- "));
    assert!(display.contains(", "));
}

#[test]
fn test_clause_functor_arity() {
    // Test extracting functor and arity from clause head
    // This identifies what predicate the clause defines
    
    let clause = Clause::fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("tom".to_string()),
        Term::Atom("bob".to_string())
    ]));
    
    assert_eq!(clause.head_functor_arity(), Some(("parent", 2)));
    assert_eq!(clause.arity(), 2);
    assert_eq!(clause.functor(), Some("parent"));
}

#[test]
fn test_clause_with_atom_head() {
    // Test clause where head is just an atom (0-arity predicate)
    // Common for predicates like 'true' or 'fail'
    
    let clause = Clause::fact(Term::Atom("true".to_string()));
    assert_eq!(clause.head_functor_arity(), Some(("true", 0)));
    assert_eq!(clause.arity(), 0);
    assert_eq!(clause.functor(), Some("true"));
}

#[test]
fn test_clause_variables() {
    // Test collecting all variables from a clause (head and body)
    // Each variable should appear only once in the result
    
    let clause = Clause::rule(
        Term::Compound("foo".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Variable("Y".to_string())
        ]),
        vec![
            Term::Compound("bar".to_string(), vec![
                Term::Variable("X".to_string()), // X appears again
                Term::Variable("Z".to_string())  // New variable Z
            ])
        ]
    );
    
    let vars = clause.variables();
    // Should have X, Y, Z (each once)
    assert_eq!(vars.len(), 3);
    assert!(vars.contains(&&"X".to_string()));
    assert!(vars.contains(&&"Y".to_string()));
    assert!(vars.contains(&&"Z".to_string()));
}

#[test]
fn test_clause_no_variables() {
    // Test clause with no variables (ground clause)
    
    let clause = Clause::fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("tom".to_string()),
        Term::Atom("bob".to_string())
    ]));
    
    let vars = clause.variables();
    assert_eq!(vars.len(), 0);
}

#[test]
fn test_clause_is_ground() {
    // Test is_ground() for clauses
    // A clause is ground if it contains no variables anywhere
    
    // Ground clause: all terms are atoms or numbers
    let ground_clause = Clause::fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("tom".to_string()),
        Term::Atom("bob".to_string())
    ]));
    assert!(ground_clause.is_ground());
    
    // Non-ground clause: contains at least one variable
    let non_ground_clause = Clause::rule(
        Term::Compound("parent".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Atom("bob".to_string())
        ]),
        vec![Term::Atom("true".to_string())]
    );
    assert!(!non_ground_clause.is_ground());
}

// ===== EDGE CASE TESTS =====
// Tests for unusual but valid inputs and boundary conditions

#[test]
fn test_special_characters_in_atoms() {
    // Test atoms with special characters
    // Prolog allows various characters in atoms when quoted
    
    let atom = Term::Atom("foo_bar-123".to_string());
    assert_eq!(format!("{}", atom), "foo_bar-123");
    assert_eq!(atom.functor_arity(), Some(("foo_bar-123", 0)));
}

#[test]
fn test_unicode_in_atoms() {
    // Test Unicode support in atom names
    // Modern Prolog implementations support Unicode
    
    let atom = Term::Atom("こんにちは".to_string());
    assert_eq!(format!("{}", atom), "こんにちは");
    assert!(atom.is_atom());
}

#[test]
fn test_very_long_names() {
    // Test handling of very long names (1000 characters)
    // Ensures no stack overflow or performance issues
    
    let long_name = "a".repeat(1000);
    let atom = Term::Atom(long_name.clone());
    assert_eq!(atom.as_atom(), Some(&long_name));
    
    let var = Term::Variable(long_name.clone());
    assert_eq!(var.as_variable(), Some(&long_name));
}

#[test]
fn test_deeply_nested_list() {
    // Test extremely nested list structure: [[[[1]]]]
    // Verifies recursive algorithms handle deep nesting
    
    let inner = Term::from_list(vec![Term::Number(1)]);
    let level2 = Term::from_list(vec![inner]);
    let level3 = Term::from_list(vec![level2]);
    let level4 = Term::from_list(vec![level3]);
    
    assert!(level4.is_proper_list());
    assert_eq!(format!("{}", level4), "[[[[1]]]]");
}

#[test]
fn test_mixed_list_structures() {
    // Test list containing another list as element: [1, [2, 3], 4]
    // Lists can contain any terms, including other lists
    
    let inner_list = Term::from_list(vec![Term::Number(2), Term::Number(3)]);
    let outer_list = Term::from_list(vec![
        Term::Number(1),
        inner_list,
        Term::Number(4)
    ]);
    
    assert!(outer_list.is_proper_list());
    let elements = outer_list.to_list().unwrap();
    assert_eq!(elements.len(), 3);
    assert_eq!(format!("{}", outer_list), "[1, [2, 3], 4]");
}

#[test]
fn test_compound_with_many_arguments() {
    // Test compound term with 100 arguments
    // Ensures no issues with large argument lists
    
    let args: Vec<Term> = (0..100).map(Term::Number).collect();
    let compound = Term::Compound("big".to_string(), args);
    
    assert_eq!(compound.functor_arity(), Some(("big", 100)));
    // Size is 1 (compound) + 100 (numbers) = 101
    assert_eq!(compound.size(), 101);
}

#[test]
fn test_empty_body_clause() {
    // Edge case: rule with empty body is actually a fact
    // This is a quirk of the representation
    
    let clause = Clause::rule(
        Term::Atom("foo".to_string()),
        vec![]
    );
    
    // Empty body means it's a fact, not a rule
    assert!(clause.is_fact());
    assert!(!clause.is_rule());
}

#[test]
fn test_clause_with_variable_head() {
    // Invalid in real Prolog but our AST allows it
    // Tests robustness of the implementation
    
    let clause = Clause::fact(Term::Variable("X".to_string()));
    // Variable heads don't have functors
    assert_eq!(clause.functor(), None);
    assert_eq!(clause.arity(), 0);
    assert_eq!(clause.head_functor_arity(), None);
}

#[test]
fn test_clause_with_number_head() {
    // Also invalid in real Prolog but allowed by our AST
    // Tests edge case handling
    
    let clause = Clause::fact(Term::Number(42));
    // Number heads don't have functors
    assert_eq!(clause.functor(), None);
    assert_eq!(clause.arity(), 0);
    assert_eq!(clause.head_functor_arity(), None);
}

#[test]
fn test_display_list_with_non_list_tail() {
    // Test improper list with non-variable tail: [1, 2 | foo]
    // The tail is an atom instead of [] or a variable
    
    let improper = Term::Compound(".".to_string(), vec![
        Term::Number(1),
        Term::Compound(".".to_string(), vec![
            Term::Number(2),
            Term::Atom("foo".to_string()) // Non-list tail
        ])
    ]);
    
    assert!(!improper.is_proper_list());
    let display = format!("{}", improper);
    // Should contain pipe or dot to show it's not a proper list
    assert!(display.contains("|") || display.contains("."));
}

#[test]
fn test_variables_ordering_preserved() {
    // Test that variable collection preserves first-occurrence order
    // Important for consistent variable ordering in operations
    
    let term = Term::Compound("foo".to_string(), vec![
        Term::Variable("Z".to_string()),
        Term::Variable("A".to_string()),
        Term::Variable("Z".to_string()), // Duplicate - should not be collected again
        Term::Variable("M".to_string()),
    ]);
    
    let vars = term.variables();
    assert_eq!(vars.len(), 3);
    // Order should be Z, A, M (order of first occurrence)
    assert_eq!(vars[0], &"Z".to_string());
    assert_eq!(vars[1], &"A".to_string());
    assert_eq!(vars[2], &"M".to_string());
}

#[test]
fn test_compound_equality() {
    // Test PartialEq implementation for compound terms
    // Terms should be equal if they have same structure and values
    
    let term1 = Term::Compound("foo".to_string(), vec![
        Term::Number(1),
        Term::Atom("bar".to_string())
    ]);
    
    let term2 = Term::Compound("foo".to_string(), vec![
        Term::Number(1),
        Term::Atom("bar".to_string())
    ]);
    
    let term3 = Term::Compound("foo".to_string(), vec![
        Term::Number(2), // Different number
        Term::Atom("bar".to_string())
    ]);
    
    assert_eq!(term1, term2);
    assert_ne!(term1, term3);
}

#[test]
fn test_clone_terms() {
    // Test that Clone trait creates deep copies
    // Important for term manipulation without affecting originals
    
    let original = Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Number(42)
    ]);
    
    let cloned = original.clone();
    assert_eq!(original, cloned);
    
    // Verify it's a deep clone by checking the structure
    if let Term::Compound(_, args) = cloned {
        assert_eq!(args.len(), 2);
    }
}

#[test]
fn test_debug_format() {
    // Test Debug trait implementation
    // Debug format should show the internal structure
    
    let term = Term::Atom("test".to_string());
    let debug_str = format!("{:?}", term);
    // Debug format should indicate it's an Atom variant
    assert!(debug_str.contains("Atom"));
    assert!(debug_str.contains("test"));
}