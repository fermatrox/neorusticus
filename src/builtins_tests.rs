// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: builtins_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the builtins module
//! 
//! This test suite validates all built-in predicates including:
//! - Arithmetic operations and evaluation
//! - Unification and type checking
//! - List operations (append, member, length)
//! - Control flow (true, fail, cut)
//! - I/O operations (write, nl)
//! - Error handling and edge cases

use super::*;
use crate::ast::Term;
use crate::engine::ExecutionContext;
use crate::error::RuntimeError;
use crate::unification::Unifier;
use std::collections::HashMap;

/// Helper function to create a fresh execution context for testing
/// 
/// Many builtin predicates need an ExecutionContext to track cut operations
/// and stack depth. This helper creates a clean context for each test.
fn create_test_context() -> ExecutionContext {
    ExecutionContext::new()
}

// ===== BASIC FUNCTIONALITY TESTS =====

#[test]
fn test_is_builtin() {
    // This test verifies that the is_builtin() function correctly identifies
    // which predicates are built into the system vs user-defined.
    // 
    // The is_builtin() function is crucial because the engine needs to know
    // whether to look up a predicate in the user-defined clauses or handle
    // it with the builtin system.
    
    // Test that known builtins are recognized with correct arity
    // The /2 notation means the predicate takes 2 arguments
    assert!(BuiltinPredicates::is_builtin("is", 2));      // X is Expression
    assert!(BuiltinPredicates::is_builtin("append", 3));  // append(L1, L2, Result)
    assert!(BuiltinPredicates::is_builtin("!", 0));       // Cut has no arguments
    
    // Test that unknown predicates are not recognized as builtins
    // This should return false so the engine looks for user-defined clauses
    assert!(!BuiltinPredicates::is_builtin("unknown", 1));
}

#[test]
fn test_arithmetic_is() {
    // Tests the 'is' predicate which evaluates arithmetic expressions
    // In Prolog: X is 2 + 3 means "evaluate 2+3 and unify the result with X"
    
    // Create empty substitution (no variables bound yet)
    let mut subst = HashMap::new();
    // Vector to collect solutions (successful substitutions)
    let mut solutions = Vec::new();
    
    // Create the terms: X (variable) and 2 + 3 (arithmetic expression)
    let left = Term::Variable("X".to_string());
    let right = Term::Compound("+".to_string(), vec![
        Term::Number(2),
        Term::Number(3)
    ]);
    
    // Execute: X is 2 + 3
    // This should evaluate 2+3=5 and bind X to 5
    BuiltinPredicates::handle_is(&left, &right, &mut subst, &mut solutions).unwrap();
    
    // Verify we got exactly one solution
    assert_eq!(solutions.len(), 1);
    // Verify that X was bound to 5 in that solution
    assert_eq!(solutions[0].get("X"), Some(&Term::Number(5)));
}

#[test]
fn test_arithmetic_comparison() {
    // Tests the comparison operators (>, <, etc.)
    // These evaluate both sides as arithmetic and compare the results
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    let left = Term::Number(5);
    let right = Term::Number(3);
    
    // Test 5 > 3 (should succeed)
    BuiltinPredicates::handle_greater(&left, &right, &mut subst, &mut solutions).unwrap();
    // Should have one solution (indicating success)
    assert_eq!(solutions.len(), 1);
    
    // Clear solutions and test 5 < 3 (should fail)
    solutions.clear();
    BuiltinPredicates::handle_less(&left, &right, &mut subst, &mut solutions).unwrap();
    // Should have no solutions (indicating failure)
    assert_eq!(solutions.len(), 0);
}

#[test]
fn test_unification() {
    // Tests the unification operator (=)
    // Unification makes two terms identical by binding variables
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create terms: X (variable) and 'hello' (atom)
    let term1 = Term::Variable("X".to_string());
    let term2 = Term::Atom("hello".to_string());
    
    // Execute: X = hello
    // This should bind X to 'hello'
    BuiltinPredicates::handle_unify(&term1, &term2, &mut subst, &mut solutions);
    
    // Verify we got a solution with X bound to 'hello'
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get("X"), Some(&Term::Atom("hello".to_string())));
}

#[test]
fn test_type_checking() {
    // Tests the type-checking predicates (var/1, atom/1, etc.)
    // These check the type of a term and succeed/fail accordingly
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create test terms
    let var = Term::Variable("X".to_string());
    let atom = Term::Atom("hello".to_string());
    
    // Test var/1 - checks if term is an unbound variable
    // var(X) should succeed because X is unbound
    BuiltinPredicates::handle_var(&var, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);  // Success
    
    // var(hello) should fail because 'hello' is an atom, not a variable
    solutions.clear();
    BuiltinPredicates::handle_var(&atom, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 0);  // Failure
    
    // Test atom/1 - checks if term is an atom
    // atom(hello) should succeed
    solutions.clear();
    BuiltinPredicates::handle_atom(&atom, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);  // Success
}

#[test]
fn test_list_append() {
    // Tests the append/3 predicate for list concatenation
    // append([1,2], [3], X) should bind X to [1,2,3]
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create list terms using the from_list helper
    // This creates the internal Prolog list structure: .(1, .(2, []))
    let list1 = Term::from_list(vec![Term::Number(1), Term::Number(2)]);
    let list2 = Term::from_list(vec![Term::Number(3)]);
    let result = Term::Variable("X".to_string());
    
    // Execute: append([1,2], [3], X)
    BuiltinPredicates::handle_append(&list1, &list2, &result, &mut subst, &mut solutions).unwrap();
    
    // Should find at least one solution
    assert!(solutions.len() > 0, "Should find at least one solution");
    
    // Check that we found the correct appended result [1,2,3]
    // We need to search through solutions because append might generate
    // multiple solutions in different modes
    let mut found_correct_result = false;
    for solution in &solutions {
        if let Some(x_binding) = solution.get("X") {
            // Apply substitution to resolve the binding fully
            let resolved = Unifier::apply_substitution(x_binding, solution);
            // Check if it's a proper list
            if let Some(elements) = resolved.to_list() {
                // Verify it's [1,2,3]
                if elements.len() == 3 &&
                   elements[0] == Term::Number(1) &&
                   elements[1] == Term::Number(2) &&
                   elements[2] == Term::Number(3) {
                    found_correct_result = true;
                    break;
                }
            }
        }
    }
    
    assert!(found_correct_result, "Should find the correct append result [1,2,3]");
}

#[test]
fn test_list_member() {
    // Tests the member/2 predicate for list membership
    // member(Element, List) checks if Element is in List
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create test data
    let element = Term::Number(2);
    let list = Term::from_list(vec![Term::Number(1), Term::Number(2), Term::Number(3)]);
    
    // Test: member(2, [1,2,3]) - should succeed
    BuiltinPredicates::handle_member(&element, &list, &mut subst, &mut solutions).unwrap();
    assert!(solutions.len() > 0); // Should find the element
    
    // Test non-member: member(4, [1,2,3]) - should fail
    solutions.clear();
    let non_element = Term::Number(4);
    BuiltinPredicates::handle_member(&non_element, &list, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 0); // Should not find the element
}

#[test]
fn test_list_length() {
    // Tests the length/2 predicate
    // length(List, Length) computes or checks the length of a list
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create a list [1,2,3]
    let list = Term::from_list(vec![Term::Number(1), Term::Number(2), Term::Number(3)]);
    let length = Term::Variable("L".to_string());
    
    // Execute: length([1,2,3], L)
    // Should bind L to 3
    BuiltinPredicates::handle_length(&list, &length, &mut subst, &mut solutions).unwrap();
    
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get("L"), Some(&Term::Number(3)));
}

#[test]
fn test_control_predicates() {
    // Tests control flow predicates: true, fail, and cut (!)
    // These control the success/failure and backtracking behavior
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    let mut context = create_test_context();
    
    // Test true/0 - always succeeds
    let true_goal = Term::Atom("true".to_string());
    BuiltinPredicates::execute(&true_goal, &mut subst, &mut solutions, &mut context).unwrap();
    assert_eq!(solutions.len(), 1);  // Should succeed with one solution
    
    // Test fail/0 - always fails
    solutions.clear();
    let fail_goal = Term::Atom("fail".to_string());
    BuiltinPredicates::execute(&fail_goal, &mut subst, &mut solutions, &mut context).unwrap();
    assert_eq!(solutions.len(), 0);  // Should fail with no solutions
    
    // Test cut/0 (!) - succeeds and prevents backtracking
    solutions.clear();
    context.reset_cut();  // Reset cut flag from previous tests
    let cut_goal = Term::Atom("!".to_string());
    BuiltinPredicates::execute(&cut_goal, &mut subst, &mut solutions, &mut context).unwrap();
    assert_eq!(solutions.len(), 1);  // Should succeed
    assert!(context.is_cut_called());  // Should set the cut flag
}

#[test]
fn test_arithmetic_evaluation() {
    // Tests the evaluate_arithmetic function with complex expressions
    // This is the core arithmetic evaluator used by 'is' and comparison operators
    
    // Create expression: (2 * 3) + 4
    let expr = Term::Compound("+".to_string(), vec![
        Term::Compound("*".to_string(), vec![Term::Number(2), Term::Number(3)]),
        Term::Number(4)
    ]);
    
    let subst = HashMap::new();
    // Evaluate the expression
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap();
    // (2 * 3) + 4 = 6 + 4 = 10
    assert_eq!(result, 10);
}

// ===== ERROR HANDLING TESTS =====

#[test]
fn test_division_by_zero() {
    // Tests that division by zero is properly detected and reported
    
    // Create expression: 5 // 0 (integer division by zero)
    let expr = Term::Compound("//".to_string(), vec![
        Term::Number(5),
        Term::Number(0)
    ]);
    
    let subst = HashMap::new();
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    
    // Should return an error
    assert!(result.is_err());
    
    // Verify it's specifically a DivisionByZero error
    if let Err(RuntimeError::DivisionByZero { .. }) = result {
        // Expected error type
    } else {
        panic!("Expected DivisionByZero error");
    }
}

#[test]
fn test_uninstantiated_variable_error() {
    // Tests that using unbound variables in arithmetic causes an error
    // In Prolog, you can't do arithmetic with unbound variables
    
    // Create expression: X + 1 where X is unbound
    let expr = Term::Compound("+".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Number(1)
    ]);
    
    let subst = HashMap::new();  // X is not in the substitution, so it's unbound
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    
    // Should return an error
    assert!(result.is_err());
    
    // Verify it's an UninstantiatedVariable error
    if let Err(RuntimeError::UninstantiatedVariable { .. }) = result {
        // Expected error type
    } else {
        panic!("Expected UninstantiatedVariable error");
    }
}

#[test]
fn test_predicate_suggestions() {
    // Tests the typo suggestion system
    // When users mistype a predicate name, we suggest similar ones
    
    // Test typo: "lentgh" instead of "length"
    // Levenshtein distance = 2 (swap n-g and h-t)
    let suggestion = BuiltinPredicates::suggest_predicate("lentgh", 2);
    assert!(suggestion.is_some());
    assert!(suggestion.unwrap().contains("length"));
    
    // Test typo: "appendd" instead of "append"
    // Levenshtein distance = 1 (extra 'd')
    let suggestion = BuiltinPredicates::suggest_predicate("appendd", 3);
    assert!(suggestion.is_some());
    assert!(suggestion.unwrap().contains("append"));
    
    // Test completely wrong predicate - too different to suggest
    let suggestion = BuiltinPredicates::suggest_predicate("totally_wrong", 5);
    assert!(suggestion.is_none());
}

#[test]
fn test_arithmetic_operators() {
    // Tests individual arithmetic operators
    // Each operator is tested separately to ensure correct evaluation
    
    let subst = HashMap::new();
    
    // Test subtraction: 10 - 3 = 7
    let expr = Term::Compound("-".to_string(), vec![Term::Number(10), Term::Number(3)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 7);
    
    // Test multiplication: 4 * 5 = 20
    let expr = Term::Compound("*".to_string(), vec![Term::Number(4), Term::Number(5)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 20);
    
    // Test modulo: 17 mod 5 = 2 (remainder of 17/5)
    let expr = Term::Compound("mod".to_string(), vec![Term::Number(17), Term::Number(5)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 2);
    
    // Test unary minus: -42
    let expr = Term::Compound("-".to_string(), vec![Term::Number(42)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), -42);
}

#[test]
fn test_extended_arithmetic() {
    // Tests additional arithmetic functions: abs, max, min
    
    let subst = HashMap::new();
    
    // Test abs with negative number: abs(-5) = 5
    let expr = Term::Compound("abs".to_string(), vec![Term::Number(-5)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 5);
    
    // Test abs with zero: abs(0) = 0
    let expr = Term::Compound("abs".to_string(), vec![Term::Number(0)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 0);
    
    // Test abs with i64::MIN - special case that would overflow
    // abs(i64::MIN) would be i64::MAX + 1, which doesn't fit in i64
    let expr = Term::Compound("abs".to_string(), vec![Term::Number(i64::MIN)]);
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    assert!(result.is_err());
    
    // Test max: max(3, 7) = 7
    let expr = Term::Compound("max".to_string(), vec![Term::Number(3), Term::Number(7)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 7);
    
    // Test min: min(3, 7) = 3
    let expr = Term::Compound("min".to_string(), vec![Term::Number(3), Term::Number(7)]);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 3);
}

// ===== EDGE CASE TESTS =====

#[test]
fn test_empty_list_operations() {
    // Tests list operations with empty lists - important edge cases
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    let empty = Term::Atom("[]".to_string());
    let list = Term::from_list(vec![Term::Number(1)]);
    
    // Test append([], [1], X) - appending empty list to [1]
    // Should bind X to [1]
    solutions.clear();
    let result = Term::Variable("X".to_string());
    BuiltinPredicates::handle_append(&empty, &list, &result, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test member(X, []) - finding members of empty list
    // Should fail (no members in empty list)
    solutions.clear();
    let element = Term::Variable("Y".to_string());
    BuiltinPredicates::handle_member(&element, &empty, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 0);
    
    // Test length([], X) - length of empty list
    // Should bind X to 0
    solutions.clear();
    let len_var = Term::Variable("L".to_string());
    BuiltinPredicates::handle_length(&empty, &len_var, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get("L"), Some(&Term::Number(0)));
}

#[test]
fn test_arithmetic_overflow() {
    // Tests that arithmetic overflow is properly detected
    // Important for preventing undefined behavior in Rust
    
    let subst = HashMap::new();
    
    // Test addition overflow: i64::MAX + 1
    let expr = Term::Compound("+".to_string(), vec![
        Term::Number(i64::MAX),
        Term::Number(1)
    ]);
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    assert!(result.is_err());
    if let Err(RuntimeError::ArithmeticError { reason, .. }) = result {
        assert!(reason.contains("overflow"));
    }
    
    // Test multiplication overflow: (i64::MAX / 2) * 3
    let expr = Term::Compound("*".to_string(), vec![
        Term::Number(i64::MAX / 2),
        Term::Number(3)
    ]);
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    assert!(result.is_err());
    
    // Test unary minus overflow on i64::MIN
    // -i64::MIN would be i64::MAX + 1, which overflows
    let expr = Term::Compound("-".to_string(), vec![Term::Number(i64::MIN)]);
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    assert!(result.is_err());
}

#[test]
fn test_invalid_list_structures() {
    // Tests error handling for malformed list structures
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test member with non-list (should error)
    let element = Term::Number(1);
    let not_a_list = Term::Atom("not_a_list".to_string());
    let result = BuiltinPredicates::handle_member(&element, &not_a_list, &mut subst, &mut solutions);
    assert!(result.is_err());
    
    // Test length with non-list (should error)
    let len_var = Term::Variable("L".to_string());
    let result = BuiltinPredicates::handle_length(&not_a_list, &len_var, &mut subst, &mut solutions);
    assert!(result.is_err());
    
    // Test with uninstantiated variable as list (should error)
    let var_list = Term::Variable("UnboundList".to_string());
    let result = BuiltinPredicates::handle_member(&element, &var_list, &mut subst, &mut solutions);
    assert!(result.is_err());
    if let Err(RuntimeError::UninstantiatedVariable { variable, .. }) = result {
        assert!(variable.contains("UnboundList"));
    }
}

#[test]
fn test_complex_list_operations() {
    // Tests append with variables in multiple positions
    // append can be used in multiple "modes" for different purposes
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test append(X, Y, [1,2,3]) - find all ways to split [1,2,3]
    // This is the "reverse" mode of append, very powerful in Prolog
    let x = Term::Variable("X".to_string());
    let y = Term::Variable("Y".to_string());
    let result = Term::from_list(vec![Term::Number(1), Term::Number(2), Term::Number(3)]);
    
    BuiltinPredicates::handle_append(&x, &y, &result, &mut subst, &mut solutions).unwrap();
    
    // Should find multiple solutions:
    // X=[], Y=[1,2,3]
    // X=[1], Y=[2,3]
    // X=[1,2], Y=[3]
    // X=[1,2,3], Y=[]
    assert!(solutions.len() > 1);
}

#[test]
fn test_nested_arithmetic() {
    // Tests deeply nested arithmetic expressions
    // Ensures the recursive evaluator handles complex expressions
    
    let subst = HashMap::new();
    
    // Test: ((2 + 3) * (4 - 1)) // 5 = (5 * 3) // 5 = 15 // 5 = 3
    let expr = Term::Compound("//".to_string(), vec![
        Term::Compound("*".to_string(), vec![
            Term::Compound("+".to_string(), vec![Term::Number(2), Term::Number(3)]),
            Term::Compound("-".to_string(), vec![Term::Number(4), Term::Number(1)])
        ]),
        Term::Number(5)
    ]);
    
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap();
    assert_eq!(result, 3);
}

#[test]
fn test_boundary_values() {
    // Tests with extreme integer values (i64 boundaries)
    
    let subst = HashMap::new();
    
    // Test with i64::MAX - should evaluate correctly
    let expr = Term::Number(i64::MAX);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), i64::MAX);
    
    // Test with i64::MIN - should evaluate correctly
    let expr = Term::Number(i64::MIN);
    assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), i64::MIN);
    
    // Test abs with i64::MIN - special overflow case
    // abs(i64::MIN) = i64::MAX + 1, which doesn't fit in i64
    let expr = Term::Compound("abs".to_string(), vec![Term::Number(i64::MIN)]);
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    assert!(result.is_err());
    if let Err(RuntimeError::ArithmeticError { reason, .. }) = result {
        assert!(reason.contains("overflow"));
    } else {
        panic!("Expected ArithmeticError for abs(i64::MIN)");
    }
}

#[test]
fn test_type_check_with_substitution() {
    // Tests type checking when variables are bound
    // Important: var/1 checks if a variable is UNBOUND
    // If X is bound to an atom, var(X) should fail
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Bind X to an atom
    subst.insert("X".to_string(), Term::Atom("bound".to_string()));
    
    let x_var = Term::Variable("X".to_string());
    
    // var(X) should fail since X is bound
    BuiltinPredicates::handle_var(&x_var, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 0);
    
    // nonvar(X) should succeed since X is bound
    solutions.clear();
    BuiltinPredicates::handle_nonvar(&x_var, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);
    
    // atom(X) should succeed since X is bound to an atom
    solutions.clear();
    BuiltinPredicates::handle_atom(&x_var, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_unify_complex_terms() {
    // Tests unification of compound terms with variables
    // Unification should bind variables to make terms identical
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test unifying: f(X, Y) = f(1, 2)
    // Should bind X->1 and Y->2
    let term1 = Term::Compound("f".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Variable("Y".to_string())
    ]);
    let term2 = Term::Compound("f".to_string(), vec![
        Term::Number(1),
        Term::Number(2)
    ]);
    
    BuiltinPredicates::handle_unify(&term1, &term2, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get("X"), Some(&Term::Number(1)));
    assert_eq!(solutions[0].get("Y"), Some(&Term::Number(2)));
}

#[test]
fn test_not_unify() {
    // Tests the \= operator (not unifiable)
    // Succeeds if terms CANNOT be unified
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test: a \= b (different atoms)
    // Should succeed because 'a' and 'b' cannot be unified
    let term1 = Term::Atom("a".to_string());
    let term2 = Term::Atom("b".to_string());
    
    BuiltinPredicates::handle_not_unify(&term1, &term2, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1); // Should succeed
    
    // Test: a \= a (same atom)
    // Should fail because 'a' can be unified with 'a'
    solutions.clear();
    BuiltinPredicates::handle_not_unify(&term1, &term1, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 0); // Should fail
}

#[test]
fn test_modulo_by_zero() {
    // Tests that modulo by zero is properly detected
    // Like division by zero, this is an error condition
    
    let expr = Term::Compound("mod".to_string(), vec![
        Term::Number(10),
        Term::Number(0)
    ]);
    
    let subst = HashMap::new();
    let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
    assert!(result.is_err());
    
    if let Err(RuntimeError::DivisionByZero { .. }) = result {
        // Expected error
    } else {
        panic!("Expected DivisionByZero error for mod by 0");
    }
}

#[test]
fn test_list_builtin_info() {
    // Tests the list_builtins function that returns information
    // about all available built-in predicates
    
    let builtins = BuiltinPredicates::list_builtins();
    assert!(!builtins.is_empty());
    
    // Check that some expected predicates are listed
    let names: Vec<&String> = builtins.iter().map(|(name, _, _)| name).collect();
    assert!(names.contains(&&"is".to_string()));
    assert!(names.contains(&&"append".to_string()));
    assert!(names.contains(&&"member".to_string()));
    assert!(names.contains(&&"true".to_string()));
}

#[test]
fn test_error_handling_in_execute() {
    // Tests the main execute function's error handling
    // This is the entry point for all builtin predicates
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    let mut context = create_test_context();
    
    // Test unknown predicate - should return PredicateNotFound error
    let unknown_goal = Term::Compound("unknown_predicate".to_string(), vec![Term::Number(1)]);
    let result = BuiltinPredicates::execute(&unknown_goal, &mut subst, &mut solutions, &mut context);
    
    assert!(result.is_err());
    if let Err(RuntimeError::PredicateNotFound { functor, arity, .. }) = result {
        assert_eq!(functor, "unknown_predicate");
        assert_eq!(arity, 1);
    } else {
        panic!("Expected PredicateNotFound error");
    }
}

#[test]
fn test_write_predicate() {
    // Tests the write/1 predicate for output
    // write(Term) outputs the term and always succeeds
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test writing different term types
    let atom = Term::Atom("test".to_string());
    BuiltinPredicates::handle_write(&atom, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);  // Should succeed
    
    solutions.clear();
    let number = Term::Number(42);
    BuiltinPredicates::handle_write(&number, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);  // Should succeed
    
    // Test writing with substitution applied
    // If X is bound to 'substituted', write(X) should output 'substituted'
    solutions.clear();
    subst.insert("X".to_string(), Term::Atom("substituted".to_string()));
    let var = Term::Variable("X".to_string());
    BuiltinPredicates::handle_write(&var, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);  // Should succeed
}

#[test]
fn test_nl_predicate() {
    // Tests the nl/0 predicate (newline output)
    // nl outputs a newline and always succeeds
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    let mut context = create_test_context();
    
    let nl_goal = Term::Atom("nl".to_string());
    BuiltinPredicates::execute(&nl_goal, &mut subst, &mut solutions, &mut context).unwrap();
    assert_eq!(solutions.len(), 1);  // Should succeed
}

#[test]
fn test_arithmetic_equality_operators() {
    // Tests =:= (arithmetic equality) and =\= (arithmetic inequality)
    // These evaluate both sides arithmetically before comparing
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test =:= with expression that equals 5
    // (2 + 3) =:= 5 should succeed
    let left = Term::Compound("+".to_string(), vec![Term::Number(2), Term::Number(3)]);
    let right = Term::Number(5);
    BuiltinPredicates::handle_arithmetic_equal(&left, &right, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);  // Should succeed
    
    // Test =\= with different values
    // (2 + 3) =\= 6 should succeed
    solutions.clear();
    let right2 = Term::Number(6);
    BuiltinPredicates::handle_arithmetic_not_equal(&left, &right2, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);  // Should succeed
    
    // Test =\= with equal values (should fail)
    // (2 + 3) =\= 5 should fail
    solutions.clear();
    BuiltinPredicates::handle_arithmetic_not_equal(&left, &right, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 0);  // Should fail
}

#[test]
fn test_all_comparison_operators() {
    // Tests >= and =< operators
    // Note: Prolog uses =< not <= for less-than-or-equal
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    let five = Term::Number(5);
    let three = Term::Number(3);
    
    // Test >= with 5 >= 3 (should succeed)
    BuiltinPredicates::handle_greater_equal(&five, &three, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test >= with equal values: 5 >= 5 (should succeed)
    solutions.clear();
    BuiltinPredicates::handle_greater_equal(&five, &five, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test =< with 3 =< 5 (should succeed)
    solutions.clear();
    BuiltinPredicates::handle_less_equal(&three, &five, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);
    
    // Test =< with equal values: 3 =< 3 (should succeed)
    solutions.clear();
    BuiltinPredicates::handle_less_equal(&three, &three, &mut subst, &mut solutions).unwrap();
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_type_check_compound() {
    // Tests the compound/1 predicate
    // Checks if a term is a compound structure (has functor and arguments)
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test with actual compound term: f(1)
    let compound = Term::Compound("f".to_string(), vec![Term::Number(1)]);
    BuiltinPredicates::handle_compound(&compound, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);  // Should succeed
    
    // Test with atom (should fail - atoms are not compound)
    solutions.clear();
    let atom = Term::Atom("not_compound".to_string());
    BuiltinPredicates::handle_compound(&atom, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 0);  // Should fail
    
    // Test with number (should fail)
    solutions.clear();
    let number = Term::Number(42);
    BuiltinPredicates::handle_compound(&number, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 0);  // Should fail
}

#[test]
fn test_number_type_check() {
    // Tests the number/1 predicate
    // Checks if a term is a number
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Test with actual number
    let number = Term::Number(42);
    BuiltinPredicates::handle_number(&number, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 1);  // Should succeed
    
    // Test with variable (should fail - unbound variables are not numbers)
    solutions.clear();
    let var = Term::Variable("X".to_string());
    BuiltinPredicates::handle_number(&var, &mut subst, &mut solutions);
    assert_eq!(solutions.len(), 0);  // Should fail
}

#[test]
fn test_invalid_goal_type() {
    // Tests that execute() properly rejects invalid goal types
    // Goals must be atoms or compound terms, not numbers or variables
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    let mut context = create_test_context();
    
    // Test executing a number as a goal (invalid)
    let number_goal = Term::Number(42);
    let result = BuiltinPredicates::execute(&number_goal, &mut subst, &mut solutions, &mut context);
    
    assert!(result.is_err());
    if let Err(RuntimeError::TypeMismatch { expected, .. }) = result {
        assert!(expected.contains("compound term or atom"));
    }
}

#[test]
fn test_append_with_large_lists() {
    // Tests recursion depth limits in append
    // append is recursive, so we need limits to prevent stack overflow
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create large lists to test recursion depth limits
    let large_list1: Vec<Term> = (0..50).map(Term::Number).collect();
    let large_list2: Vec<Term> = (50..100).map(Term::Number).collect();
    
    let list1 = Term::from_list(large_list1);
    let list2 = Term::from_list(large_list2);
    let result = Term::Variable("Result".to_string());
    
    // This should complete without stack overflow due to depth limit (100)
    let result = BuiltinPredicates::handle_append(&list1, &list2, &result, &mut subst, &mut solutions);
    
    // Should either succeed or hit the safety limit gracefully
    assert!(result.is_ok() || solutions.len() > 0);
}

#[test]
fn test_member_with_nested_lists() {
    // Tests member with lists containing other lists
    // member should find exact matches, including nested structures
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create a list containing another list: [1, [2, 3], 4]
    let inner_list = Term::from_list(vec![Term::Number(2), Term::Number(3)]);
    let outer_list = Term::from_list(vec![
        Term::Number(1),
        inner_list.clone(),
        Term::Number(4)
    ]);
    
    // Should find the inner list [2, 3] as a member
    BuiltinPredicates::handle_member(&inner_list, &outer_list, &mut subst, &mut solutions).unwrap();
    assert!(solutions.len() > 0);
}

#[test]
fn test_length_with_improper_list() {
    // Tests error handling for improper lists
    // An improper list doesn't end with [] (e.g., [1, 2 | 3])
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create an improper list [1, 2 | 3]
    // This is .(1, .(2, 3)) instead of .(1, .(2, []))
    let improper_list = Term::Compound(".".to_string(), vec![
        Term::Number(1),
        Term::Compound(".".to_string(), vec![
            Term::Number(2),
            Term::Number(3)  // Should be [] for a proper list
        ])
    ]);
    
    let len_var = Term::Variable("L".to_string());
    let result = BuiltinPredicates::handle_length(&improper_list, &len_var, &mut subst, &mut solutions);
    
    // Should error on improper list
    assert!(result.is_err());
    if let Err(RuntimeError::InvalidListStructure { .. }) = result {
        // Expected error
    }
}

#[test]
fn test_circular_reference_prevention() {
    // Tests that append has a depth check to prevent infinite recursion
    // Without this check, very long lists could cause stack overflow
    
    let mut subst = HashMap::new();
    let mut solutions = Vec::new();
    
    // Create a very long list that would cause issues without depth check
    let long_list: Vec<Term> = (0..200).map(Term::Number).collect();
    let list = Term::from_list(long_list);
    
    let empty = Term::Atom("[]".to_string());
    let result = Term::Variable("R".to_string());
    
    // This should be handled safely with the depth check
    // The implementation limits recursion to 100 levels
    let res = BuiltinPredicates::handle_append(&list, &empty, &result, &mut subst, &mut solutions);
    
    // Should complete without stack overflow
    assert!(res.is_ok());
}