// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: lib_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the lib module's public API functions

use super::*;

// ===== Basic Functionality Tests =====

#[test]
fn test_parse_term_basic() {
    // This test verifies that parse_term correctly handles all basic term types
    // that form the foundation of Prolog syntax
    
    // Test parsing simple atom
    // Atoms are constants in Prolog - they start with lowercase letters
    // The parse_term function should recognize "foo" as an atom
    let term = parse_term("foo").unwrap();
    assert_eq!(term, Term::Atom("foo".to_string()));
    
    // Test parsing variable
    // Variables in Prolog start with uppercase letters or underscore
    // "X" is a standard variable name
    let term = parse_term("X").unwrap();
    assert_eq!(term, Term::Variable("X".to_string()));
    
    // Test parsing number
    // Prolog supports integer literals
    // The parser should recognize "42" as a number
    let term = parse_term("42").unwrap();
    assert_eq!(term, Term::Number(42));
    
    // Test parsing negative number
    // Negative numbers are handled by the lexer as single tokens
    // "-17" should be parsed as a single negative number, not minus operator followed by 17
    let term = parse_term("-17").unwrap();
    assert_eq!(term, Term::Number(-17));
}

#[test]
fn test_parse_term_compound() {
    // This test verifies parsing of compound terms (functors with arguments)
    // Compound terms are the primary structure in Prolog
    
    // Test parsing compound term with no arguments
    // foo() is different from the atom foo in Prolog
    // The empty parentheses indicate a compound term with 0 arity
    let term = parse_term("foo()").unwrap();
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "foo");
            assert_eq!(args.len(), 0);
        }
        _ => panic!("Expected compound term"),
    }
    
    // Test parsing compound term with arguments
    // foo(bar, X) represents a relationship or structure
    // with an atom argument and a variable argument
    let term = parse_term("foo(bar, X)").unwrap();
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "foo");
            assert_eq!(args.len(), 2);
            // Verify the first argument is the atom 'bar'
            assert_eq!(args[0], Term::Atom("bar".to_string()));
            // Verify the second argument is the variable 'X'
            assert_eq!(args[1], Term::Variable("X".to_string()));
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_parse_term_lists() {
    // This test verifies parsing of Prolog list syntax
    // Lists are special syntax sugar for nested compound terms
    
    // Test parsing empty list
    // [] is a special atom representing the empty list
    let term = parse_term("[]").unwrap();
    assert_eq!(term, Term::Atom("[]".to_string()));
    
    // Test parsing simple list
    // [1, 2, 3] is syntactic sugar for .(1, .(2, .(3, [])))
    // The parser should build this nested structure
    let term = parse_term("[1, 2, 3]").unwrap();
    // is_proper_list checks if the term is a well-formed list ending in []
    assert!(term.is_proper_list());
    // to_list extracts the elements from the nested structure
    let elements = term.to_list().unwrap();
    assert_eq!(elements.len(), 3);
    assert_eq!(elements[0], Term::Number(1));
    assert_eq!(elements[1], Term::Number(2));
    assert_eq!(elements[2], Term::Number(3));
    
    // Test parsing list with tail
    // [H|T] is the list pattern matching syntax
    // H is the head (first element), T is the tail (rest of the list)
    // This is actually .(H, T) in the internal representation
    let term = parse_term("[H|T]").unwrap();
    match term {
        Term::Compound(functor, args) => {
            // The dot functor represents the list constructor
            assert_eq!(functor, ".");
            assert_eq!(args[0], Term::Variable("H".to_string()));
            assert_eq!(args[1], Term::Variable("T".to_string()));
        }
        _ => panic!("Expected compound term for list"),
    }
}

#[test]
fn test_parse_term_operators() {
    // This test verifies parsing of operators and their precedence
    // Operators in Prolog are actually compound terms with special syntax
    
    // Test parsing arithmetic expression
    // 2 + 3 is syntactic sugar for +(2, 3)
    let term = parse_term("2 + 3").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "+");
            assert_eq!(args[0], Term::Number(2));
            assert_eq!(args[1], Term::Number(3));
        }
        _ => panic!("Expected compound term"),
    }
    
    // Test parsing comparison
    // X > 5 becomes >(X, 5) internally
    let term = parse_term("X > 5").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, ">");
            assert_eq!(args[0], Term::Variable("X".to_string()));
            assert_eq!(args[1], Term::Number(5));
        }
        _ => panic!("Expected compound term"),
    }
    
    // Test parsing unification
    // X = hello is the unification operator, becomes =(X, hello)
    let term = parse_term("X = hello").unwrap();
    match term {
        Term::Compound(op, args) => {
            assert_eq!(op, "=");
            assert_eq!(args[0], Term::Variable("X".to_string()));
            assert_eq!(args[1], Term::Atom("hello".to_string()));
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_quick_query_basic() {
    // This test verifies the quick_query convenience function
    // which combines engine creation, clause loading, and query execution
    
    // Test simple fact query
    // Create a small database with parent facts
    let clauses = &["parent(tom, bob).", "parent(bob, ann)."];
    // Query: "Who is tom's child?" (find X where parent(tom, X))
    let solutions = quick_query(clauses, "parent(tom, X).").unwrap();
    // Should find exactly one solution: X = bob
    assert_eq!(solutions.len(), 1);
    // Verify the variable binding in the solution
    assert_eq!(solutions[0].get("X"), Some(&Term::Atom("bob".to_string())));
    
    // Test query with no solutions
    // Query: "Who is mary's child?" (mary is not in the database)
    let solutions = quick_query(clauses, "parent(mary, X).").unwrap();
    // Should find no solutions since mary is not a parent in our database
    assert_eq!(solutions.len(), 0);
    
    // Test ground query (no variables)
    // Query: "Is tom the parent of bob?" (yes/no question)
    let solutions = quick_query(clauses, "parent(tom, bob).").unwrap();
    // Should succeed with one solution (true)
    // Even though there are no variables to bind, we get one empty substitution
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_quick_query_with_rules() {
    // This test verifies that quick_query properly handles rules (not just facts)
    // Rules allow deriving new information from existing facts
    
    // Create a database with facts and a rule
    let clauses = &[
        "parent(tom, bob).",      // Fact: tom is parent of bob
        "parent(bob, ann).",      // Fact: bob is parent of ann
        "grandparent(X, Z) :- parent(X, Y), parent(Y, Z)."  // Rule: X is grandparent of Z if...
    ];
    
    // Query: "Who is tom's grandchild?"
    let solutions = quick_query(clauses, "grandparent(tom, X).").unwrap();
    // Should find one solution through the rule: X = ann
    assert_eq!(solutions.len(), 1);
    
    // Apply substitution to resolve the variable fully
    // The solution might have X bound to another variable that's bound to 'ann'
    // so we need to follow the chain of substitutions
    let x_binding = solutions[0].get("X").unwrap();
    let resolved = Unifier::apply_substitution(x_binding, &solutions[0]);
    assert_eq!(resolved, Term::Atom("ann".to_string()));
    
    // Test finding all grandparent relationships
    // Query: "Find all grandparent-grandchild pairs"
    let solutions = quick_query(clauses, "grandparent(X, Y).").unwrap();
    // Should find only tom -> ann relationship
    assert_eq!(solutions.len(), 1);
}

// ===== Edge Case Tests =====

#[test]
fn test_parse_term_empty_input() {
    // Test error handling for invalid inputs
    
    // Test completely empty input
    // An empty string cannot be parsed as a term
    let result = parse_term("");
    assert!(result.is_err());
    
    // Test whitespace-only input
    // Whitespace alone doesn't constitute a valid term
    let result = parse_term("   \n\t  ");
    assert!(result.is_err());
}

#[test]
fn test_parse_term_invalid_syntax() {
    // Test various syntax errors to ensure proper error detection
    
    // Test incomplete compound term
    // Opening parenthesis without closing
    let result = parse_term("foo(");
    assert!(result.is_err());
    
    // Test mismatched parentheses
    // Extra closing parenthesis
    let result = parse_term("foo(bar))");
    assert!(result.is_err());
    
    // Test invalid characters
    // @ # $ are not valid in Prolog syntax
    let result = parse_term("@#$");
    assert!(result.is_err());
    
    // Test incomplete operator
    // Colon alone is not valid (should be :- for rules)
    let result = parse_term("X :");
    assert!(result.is_err());
    
    // Test operator without operands
    // Plus operator needs operands on both sides
    let result = parse_term("+");
    assert!(result.is_err());
}

#[test]
fn test_parse_term_boundary_values() {
    // Test parsing of extreme numeric values
    
    // Test maximum i64 value
    // Should handle the largest possible 64-bit integer
    let term = parse_term(&i64::MAX.to_string()).unwrap();
    assert_eq!(term, Term::Number(i64::MAX));
    
    // Test minimum i64 value
    // Should handle the most negative 64-bit integer
    // This is a special case because abs(i64::MIN) > i64::MAX
    let term = parse_term(&i64::MIN.to_string()).unwrap();
    assert_eq!(term, Term::Number(i64::MIN));
    
    // Test number overflow (should fail)
    // A number too large to fit in i64 should cause an error
    let result = parse_term("99999999999999999999999999999");
    assert!(result.is_err());
}

#[test]
fn test_parse_term_deeply_nested() {
    // Test parsing of deeply nested structures
    // This verifies the parser can handle recursive structures without stack overflow
    
    // Test deeply nested compound terms
    // Create f(g(h(i(j(k(l(m(n(o(p(q(r(s(t(u(v(w(x(y(z(atom)))))))))))))))))))))
    let nested = "f(g(h(i(j(k(l(m(n(o(p(q(r(s(t(u(v(w(x(y(z(atom)))))))))))))))))))))";
    let term = parse_term(nested).unwrap();
    
    // Verify it's a compound term with deep nesting
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "f");
            assert_eq!(args.len(), 1);
            // The parser should handle arbitrary nesting depth
        }
        _ => panic!("Expected compound term"),
    }
    
    // Test deeply nested lists
    // [[[[[[[[[[1]]]]]]]]]]
    let nested_list = "[[[[[[[[[[1]]]]]]]]]]";
    let term = parse_term(nested_list).unwrap();
    // Should parse as a proper list despite deep nesting
    assert!(term.is_proper_list());
}

#[test]
fn test_parse_term_complex_expressions() {
    // Test parsing of complex expressions with multiple operators
    // This verifies correct operator precedence handling
    
    // Test complex arithmetic with precedence
    // Should parse according to standard mathematical precedence
    let term = parse_term("(2 + 3) * 4 - 5 // 2").unwrap();
    match term {
        Term::Compound(op, _args) => {
            // Subtraction should be at top level (lowest precedence here)
            assert_eq!(op, "-");
        }
        _ => panic!("Expected compound term"),
    }
    
    // Test mixed operators
    // Unification (=) has lower precedence than arithmetic
    let term = parse_term("X = Y + 2 * 3").unwrap();
    match term {
        Term::Compound(op, _args) => {
            // Unification should be at the top level
            assert_eq!(op, "=");
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_parse_term_special_cases() {
    // Test parsing of special Prolog constructs
    
    // Test cut operator
    // ! is the cut operator that prevents backtracking
    let term = parse_term("!").unwrap();
    assert_eq!(term, Term::Atom("!".to_string()));
    
    // Test underscore variable
    // _ is the anonymous variable (don't care about its value)
    let term = parse_term("_").unwrap();
    assert_eq!(term, Term::Variable("_".to_string()));
    
    // Test underscore-prefixed variable
    // _temp is a named variable that follows underscore convention
    // (often used for variables we don't care much about)
    let term = parse_term("_temp").unwrap();
    assert_eq!(term, Term::Variable("_temp".to_string()));
    
    // Test quoted atoms (if supported by lexer)
    // Quoted atoms allow spaces and special characters
    let result = parse_term("'quoted atom'");
    if result.is_ok() {
        let term = result.unwrap();
        assert_eq!(term, Term::Atom("quoted atom".to_string()));
    }
}

#[test]
fn test_quick_query_empty_inputs() {
    // Test edge cases with empty or minimal inputs
    
    // Test with empty clause list
    // An empty database should still work but find no solutions
    let clauses = &[];
    let solutions = quick_query(clauses, "foo(X).").unwrap();
    assert_eq!(solutions.len(), 0); // No clauses, no solutions
    
    // Test with empty query (should fail)
    // An empty string is not a valid query
    let clauses = &["foo(bar)."];
    let result = quick_query(clauses, "");
    assert!(result.is_err());
}

#[test]
fn test_quick_query_invalid_inputs() {
    // Test error handling for various invalid inputs
    
    // Test with invalid clause syntax
    // Missing closing parenthesis should cause parse error
    let clauses = &["invalid syntax here"];
    let result = quick_query(clauses, "foo(X).");
    assert!(result.is_err());
    
    // Test with invalid query syntax
    let clauses = &["foo(bar)."];
    let result = quick_query(clauses, "invalid query");
    assert!(result.is_err());
    
    // Test with missing dots in clauses
    // Prolog clauses must end with periods
    let clauses = &["foo(bar)", "baz(qux)"];
    let result = quick_query(clauses, "foo(X).");
    assert!(result.is_err());
}

#[test]
fn test_quick_query_circular_references() {
    // Test handling of circular definitions
    // This creates an infinite loop if not handled properly
    
    let clauses = &[
        "loop(X) :- loop(X)."  // Infinitely recursive rule
    ];
    
    // Should handle gracefully (either timeout or stack limit)
    // The engine should detect stack overflow and return an error
    let result = quick_query(clauses, "loop(test).");
    assert!(result.is_err());
}

#[test]
fn test_quick_query_mutual_recursion() {
    // Test mutually recursive predicates
    // Two predicates that call each other indefinitely
    
    let clauses = &[
        "ping(X) :- pong(X).",  // ping calls pong
        "pong(X) :- ping(X)."   // pong calls ping
    ];
    
    // Should handle infinite mutual recursion gracefully
    let result = quick_query(clauses, "ping(test).");
    assert!(result.is_err()); // Should detect stack overflow
}

#[test]
fn test_quick_query_complex_programs() {
    // Test a more realistic Prolog program with multiple predicates
    
    let clauses = &[
        // Facts about family relationships
        "parent(tom, bob).",
        "parent(tom, liz).",
        "parent(bob, ann).",
        "parent(bob, pat).",
        "parent(pat, jim).",
        // Facts about gender
        "male(tom).",
        "male(bob).",
        "male(jim).",
        "female(liz).",
        "female(ann).",
        "female(pat).",
        // Derived rules
        "father(X, Y) :- parent(X, Y), male(X).",      // Father is male parent
        "mother(X, Y) :- parent(X, Y), female(X).",    // Mother is female parent
        "ancestor(X, Y) :- parent(X, Y).",             // Direct parent is ancestor
        "ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z)."  // Transitive ancestor
    ];
    
    // Test finding all fathers
    let solutions = quick_query(clauses, "father(X, Y).").unwrap();
    assert!(solutions.len() > 0);
    
    // Test finding ancestors
    // Tom should be ancestor of bob, liz, ann, pat, jim
    let solutions = quick_query(clauses, "ancestor(tom, X).").unwrap();
    assert!(solutions.len() >= 4);
    
    // Test specific query
    // Tom should be ancestor of jim (through bob and pat)
    let solutions = quick_query(clauses, "ancestor(tom, jim).").unwrap();
    assert_eq!(solutions.len(), 1); // Should find the path
}

#[test]
fn test_quick_query_with_arithmetic() {
    // Test queries with arithmetic evaluation
    // Arithmetic in Prolog uses the 'is' operator for evaluation
    
    let clauses = &[
        "number(1).",
        "number(2).",
        "number(3).",
        "sum(X, Y, Z) :- Z is X + Y.",    // Z is the sum of X and Y
        "greater(X, Y) :- X > Y."         // X is greater than Y
    ];
    
    // Test arithmetic evaluation
    // Query: what is 2 + 3?
    let solutions = quick_query(clauses, "sum(2, 3, Z).").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Apply substitution to resolve the variable fully
    let z_binding = solutions[0].get("Z").unwrap();
    let resolved = Unifier::apply_substitution(z_binding, &solutions[0]);
    assert_eq!(resolved, Term::Number(5));
    
    // Test comparison
    // 5 > 3 should succeed
    let solutions = quick_query(clauses, "greater(5, 3).").unwrap();
    assert_eq!(solutions.len(), 1); // Should succeed
    
    // 3 > 5 should fail
    let solutions = quick_query(clauses, "greater(3, 5).").unwrap();
    assert_eq!(solutions.len(), 0); // Should fail
}

#[test]
fn test_quick_query_with_lists() {
    // Test queries with list operations
    // Lists are fundamental data structures in Prolog
    
    let clauses = &[
        "list([1, 2, 3]).",
        "list([a, b, c]).",
        "first([H|_], H).",              // H is first element of list
        "last([X], X).",                  // Single element is the last
        "last([_|T], X) :- last(T, X)."  // Recursively find last in tail
    ];
    
    // Test finding first element
    let solutions = quick_query(clauses, "first([1, 2, 3], X).").unwrap();
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get("X"), Some(&Term::Number(1)));
    
    // Test finding last element (recursive)
    let solutions = quick_query(clauses, "last([1, 2, 3], X).").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Apply substitution to resolve the variable fully
    let x_binding = solutions[0].get("X").unwrap();
    let resolved = Unifier::apply_substitution(x_binding, &solutions[0]);
    assert_eq!(resolved, Term::Number(3));
}

#[test]
fn test_quick_query_with_cut() {
    // Test cut operator behavior
    // Cut (!) prevents backtracking to find alternative solutions
    
    let clauses = &[
        "max(X, Y, X) :- X >= Y, !.",  // If X >= Y, X is max, don't try other clause
        "max(X, Y, Y)."                 // Otherwise Y is max
    ];
    
    // Cut should prevent backtracking to second clause
    let solutions = quick_query(clauses, "max(5, 3, Z).").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Apply substitution to resolve the variable fully
    let z_binding = solutions[0].get("Z").unwrap();
    let resolved = Unifier::apply_substitution(z_binding, &solutions[0]);
    assert_eq!(resolved, Term::Number(5));
    
    // Test when first clause fails
    let solutions = quick_query(clauses, "max(3, 5, Z).").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Apply substitution to resolve the variable fully
    let z_binding = solutions[0].get("Z").unwrap();
    let resolved = Unifier::apply_substitution(z_binding, &solutions[0]);
    assert_eq!(resolved, Term::Number(5));
}

#[test]
fn test_quick_query_builtin_predicates() {
    // Test that built-in predicates work through quick_query
    // Built-ins are implemented in Rust, not defined as Prolog clauses
    
    let clauses = &[];  // No user-defined clauses needed
    
    // Test append
    // append/3 concatenates two lists
    let solutions = quick_query(clauses, "append([1, 2], [3, 4], X).").unwrap();
    assert_eq!(solutions.len(), 1);
    // X should be [1, 2, 3, 4]
    
    // Test member
    // member/2 checks list membership
    let solutions = quick_query(clauses, "member(2, [1, 2, 3]).").unwrap();
    assert_eq!(solutions.len(), 1); // 2 is a member
    
    // Test length
    // length/2 computes list length
    let solutions = quick_query(clauses, "length([a, b, c], X).").unwrap();
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get("X"), Some(&Term::Number(3)));
    
    // Test type checking
    // atom/1 checks if term is an atom
    let solutions = quick_query(clauses, "atom(hello).").unwrap();
    assert_eq!(solutions.len(), 1); // Should succeed
    
    // number/1 checks if term is a number
    let solutions = quick_query(clauses, "number(hello).").unwrap();
    assert_eq!(solutions.len(), 0); // Should fail
}

#[test]
fn test_parse_term_all_operators() {
    // Test parsing all supported operators
    // Each operator has specific syntax and precedence
    
    let operators = vec![
        ("X = Y", "="),        // Unification
        ("X \\= Y", "\\="),    // Non-unification
        ("X is Y", "is"),      // Arithmetic evaluation
        ("X > Y", ">"),        // Greater than
        ("X < Y", "<"),        // Less than
        ("X >= Y", ">="),      // Greater or equal
        ("X =< Y", "=<"),      // Less or equal (Prolog style, not <=)
        ("X =:= Y", "=:="),    // Arithmetic equality
        ("X =\\= Y", "=\\="),  // Arithmetic inequality
        ("X + Y", "+"),        // Addition
        ("X - Y", "-"),        // Subtraction
        ("X * Y", "*"),        // Multiplication
        ("X // Y", "//"),      // Integer division
        ("X mod Y", "mod"),    // Modulo
    ];
    
    for (input, expected_op) in operators {
        let term = parse_term(input).unwrap();
        match term {
            Term::Compound(op, args) => {
                assert_eq!(op, expected_op, "Failed for input: {}", input);
                assert_eq!(args.len(), 2);  // All are binary operators
            }
            _ => panic!("Expected compound term for: {}", input),
        }
    }
}

#[test]
fn test_quick_query_multiple_solutions() {
    // Test queries that produce multiple solutions
    // Prolog's backtracking finds all possible solutions
    
    let clauses = &[
        "color(red).",
        "color(green).",
        "color(blue).",
        "primary(red).",
        "primary(blue).",
        "primary(yellow)."
    ];
    
    // Find all colors
    let solutions = quick_query(clauses, "color(X).").unwrap();
    assert_eq!(solutions.len(), 3);  // red, green, blue
    
    // Find all primary colors (including one not in color/1)
    let solutions = quick_query(clauses, "primary(X).").unwrap();
    assert_eq!(solutions.len(), 3);  // red, blue, yellow
    
    // Combined query - find colors that are also primary
    // This uses conjunction (comma means AND)
    let solutions = quick_query(clauses, "color(X), primary(X).").unwrap();
    assert_eq!(solutions.len(), 2); // red and blue
}

#[test]
fn test_parse_term_stress_test() {
    // Test parsing with very long identifiers and many arguments
    // This tests memory handling and performance
    
    // Test parsing with very long identifiers
    let long_atom = "a".repeat(1000);  // 1000-character atom name
    let term = parse_term(&long_atom).unwrap();
    assert_eq!(term, Term::Atom(long_atom));
    
    // Test parsing with many arguments
    // Create pred(0, 1, 2, ..., 99) with 100 arguments
    let many_args = (0..100)
        .map(|i| i.to_string())
        .collect::<Vec<_>>()
        .join(", ");
    let input = format!("pred({})", many_args);
    let term = parse_term(&input).unwrap();
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "pred");
            assert_eq!(args.len(), 100);
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_quick_query_error_propagation() {
    // Test that errors are properly propagated through quick_query
    
    // Syntax error in clause
    // Missing closing parenthesis should be caught
    let clauses = &["foo(bar"];
    let result = quick_query(clauses, "foo(X).");
    assert!(result.is_err());
    
    // Syntax error in query
    // Missing closing parenthesis in query
    let clauses = &["foo(bar)."];
    let result = quick_query(clauses, "foo(X");
    assert!(result.is_err());
    
    // Runtime error (division by zero in arithmetic)
    // Division by zero should be caught during execution
    let clauses = &["divide_by_zero(X) :- X is 5 // 0."];
    let result = quick_query(clauses, "divide_by_zero(X).");
    assert!(result.is_err());
}

#[test]
fn test_integration_parse_and_query() {
    // Test that parse_term and quick_query work well together
    // This verifies the integration between different components
    
    // Parse a term
    let term = parse_term("parent(tom, bob)").unwrap();
    
    // Use the same structure in a query
    let clauses = &["parent(tom, bob).", "parent(bob, ann)."];
    
    // Query for the parsed term structure
    let solutions = quick_query(clauses, "parent(tom, bob).").unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Verify term structure matches what we'd get in the engine
    match term {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "parent");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("Expected compound term"),
    }
}