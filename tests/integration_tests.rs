// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: integration_tests.rs
// Creator: Jonas Forsman

//! Integration tests for the Neorusticus Prolog engine
//! 
//! These tests exercise the public API as end users would use it.

use neorusticus::{PrologEngine, quick_query};

#[test]
fn test_basic_facts_and_queries() {
    let mut engine = PrologEngine::new();
    
    // Add some facts
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    engine.parse_and_add("parent(ann, sue).").unwrap();
    
    // Query for direct parents
    let solutions = engine.parse_query("parent(tom, X)?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Query for all children
    let solutions = engine.parse_query("parent(X, ann)?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Query that should fail
    let solutions = engine.parse_query("parent(sue, X)?").unwrap();
    assert_eq!(solutions.len(), 0);
}

#[test]
fn test_rules_and_recursion() {
    let mut engine = PrologEngine::new();
    
    // Add facts and rules
    engine.parse_and_add("parent(alice, bob).").unwrap();
    engine.parse_and_add("parent(bob, charlie).").unwrap();
    engine.parse_and_add("parent(charlie, diana).").unwrap();
    
    engine.parse_and_add("ancestor(X, Y) :- parent(X, Y).").unwrap();
    engine.parse_and_add("ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).").unwrap();
    
    // Test direct ancestry
    let solutions = engine.parse_query("ancestor(alice, bob)?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test transitive ancestry
    let solutions = engine.parse_query("ancestor(alice, diana)?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test finding all descendants
    let solutions = engine.parse_query("ancestor(alice, X)?").unwrap();
    assert_eq!(solutions.len(), 3); // bob, charlie, diana
}

#[test]
fn test_arithmetic_operations() {
    let mut engine = PrologEngine::new();
    
    // Test basic arithmetic
    let solutions = engine.parse_query("X is 2 + 3 * 4?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test comparison
    let solutions = engine.parse_query("5 > 3?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    let solutions = engine.parse_query("3 > 5?").unwrap();
    assert_eq!(solutions.len(), 0);
    
    // Test arithmetic equality
    let solutions = engine.parse_query("6 =:= 2 * 3?").unwrap();
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_list_operations() {
    let mut engine = PrologEngine::new();
    
    // Test append
    let solutions = engine.parse_query("append([1, 2], [3, 4], X)?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test member
    let solutions = engine.parse_query("member(2, [1, 2, 3])?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    let solutions = engine.parse_query("member(4, [1, 2, 3])?").unwrap();
    assert_eq!(solutions.len(), 0);
    
    // Test length
    let solutions = engine.parse_query("length([a, b, c], X)?").unwrap();
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_cut_operation() {
    let mut engine = PrologEngine::new();
    
    // Define max with cut
    engine.parse_and_add("max(X, Y, X) :- X >= Y, !.").unwrap();
    engine.parse_and_add("max(X, Y, Y).").unwrap();
    
    // Test that cut prevents backtracking
    let solutions = engine.parse_query("max(5, 3, Z)?").unwrap();
    assert_eq!(solutions.len(), 1); // Should only find one solution due to cut
    
    let solutions = engine.parse_query("max(2, 7, Z)?").unwrap();
    assert_eq!(solutions.len(), 1); // Should find the second clause
}

#[test]
fn test_error_handling() {
    let mut engine = PrologEngine::new();
    
    // Test parse errors
    assert!(engine.parse_and_add("invalid syntax").is_err());
    assert!(engine.parse_and_add("foo(bar").is_err()); // Unclosed paren
    
    // Test runtime errors
    assert!(engine.parse_query("X is 5 // 0?").is_err()); // Division by zero
    assert!(engine.parse_query("X is Y + 1?").is_err()); // Uninstantiated variable
}

#[test]
fn test_quick_query_convenience_function() {
    let clauses = &[
        "likes(mary, food).",
        "likes(mary, wine).",
        "likes(john, wine).",
        "likes(john, mary).",
    ];
    
    // Test finding what mary likes
    let solutions = quick_query(clauses, "likes(mary, X)?").unwrap();
    assert_eq!(solutions.len(), 2);
    
    // Test finding who likes wine
    let solutions = quick_query(clauses, "likes(X, wine)?").unwrap();
    assert_eq!(solutions.len(), 2);
    
    // Test query that should fail
    let solutions = quick_query(clauses, "likes(bob, X)?").unwrap();
    assert_eq!(solutions.len(), 0);
}

#[test]
fn test_variable_scoping() {
    let mut engine = PrologEngine::new();
    
    engine.parse_and_add("test(X, Y) :- X = 1, Y = 2.").unwrap();
    engine.parse_and_add("test(A, B) :- A = 3, B = 4.").unwrap();
    
    // Should find both solutions with proper variable renaming
    let solutions = engine.parse_query("test(P, Q)?").unwrap();
    assert_eq!(solutions.len(), 2);
}

#[test]
fn test_complex_unification() {
    let mut engine = PrologEngine::new();
    
    engine.parse_and_add("complex(f(X, Y), f(a, b)) :- X = a, Y = b.").unwrap();
    
    let solutions = engine.parse_query("complex(f(a, b), Z)?").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test that non-unifiable terms fail
    let solutions = engine.parse_query("complex(f(c, d), f(a, b))?").unwrap();
    assert_eq!(solutions.len(), 0);
}