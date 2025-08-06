// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: unification_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the unification module

use super::*;
use crate::ast::Term;
use std::collections::HashMap;

// ===== Basic Unification Tests =====
// These tests verify the fundamental unification rules for different term types

#[test]
fn test_unify_atoms() {
    // Atoms are constants in Prolog - they only unify if they're identical
    let mut subst = HashMap::new();
    
    // Same atoms should unify
    // This is the basic rule: atom 'hello' unifies with atom 'hello'
    let atom1 = Term::Atom("hello".to_string());
    let atom2 = Term::Atom("hello".to_string());
    assert!(Unifier::unify(&atom1, &atom2, &mut subst));
    // Important: unifying identical atoms doesn't create any bindings
    assert!(subst.is_empty());
    
    // Different atoms should not unify
    // 'hello' and 'world' are different constants, so they can't be made equal
    let atom3 = Term::Atom("world".to_string());
    assert!(!Unifier::unify(&atom1, &atom3, &mut subst));
}

#[test]
fn test_unify_numbers() {
    let mut subst = HashMap::new();
    
    // Same numbers should unify
    // Like atoms, numbers are constants and only unify if equal
    let num1 = Term::Number(42);
    let num2 = Term::Number(42);
    assert!(Unifier::unify(&num1, &num2, &mut subst));
    
    // Different numbers should not unify
    // 42 and 17 are different values, so they can't unify
    let num3 = Term::Number(17);
    assert!(!Unifier::unify(&num1, &num3, &mut subst));
    
    // Test negative numbers
    // Ensuring the algorithm handles negative values properly
    let neg1 = Term::Number(-5);
    let neg2 = Term::Number(-5);
    assert!(Unifier::unify(&neg1, &neg2, &mut subst));
}

#[test]
fn test_unify_variables() {
    let mut subst = HashMap::new();
    
    // Variable with atom
    // This creates a binding: X -> hello
    let var = Term::Variable("X".to_string());
    let atom = Term::Atom("hello".to_string());
    assert!(Unifier::unify(&var, &atom, &mut subst));
    assert_eq!(subst.get("X"), Some(&atom));
    
    // Same variable again should unify with existing binding
    // X is already bound to 'hello', so it can unify with 'hello' again
    let atom2 = Term::Atom("hello".to_string());
    assert!(Unifier::unify(&var, &atom2, &mut subst));
    
    // Different atom should not unify
    // X is bound to 'hello', so it can't unify with 'world'
    // This ensures logical consistency
    let atom3 = Term::Atom("world".to_string());
    assert!(!Unifier::unify(&var, &atom3, &mut subst));
}

#[test]
fn test_unify_two_unbound_variables() {
    // Test unifying two variables that aren't bound to anything
    let mut subst = HashMap::new();
    
    let var1 = Term::Variable("X".to_string());
    let var2 = Term::Variable("Y".to_string());
    
    assert!(Unifier::unify(&var1, &var2, &mut subst));
    
    // One should be bound to the other
    // When two unbound variables unify, one gets bound to the other
    // The algorithm can choose either X -> Y or Y -> X
    assert!(subst.contains_key("X") || subst.contains_key("Y"));
}

#[test]
fn test_unify_same_variable() {
    // Test the trivial case: X unifies with X
    let mut subst = HashMap::new();
    
    let var = Term::Variable("X".to_string());
    assert!(Unifier::unify(&var, &var, &mut subst));
    
    // Should not create unnecessary binding
    // Important: X = X should NOT create a binding X -> X
    // That would be redundant and could cause issues
    assert!(!subst.contains_key("X"));
}

#[test]
fn test_unify_compound_terms() {
    let mut subst = HashMap::new();
    
    // f(a, b) with f(a, b)
    // Identical compound terms should unify
    let term1 = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Atom("b".to_string())
    ]);
    let term2 = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Atom("b".to_string())
    ]);
    assert!(Unifier::unify(&term1, &term2, &mut subst));
    
    // f(X, b) with f(a, b)
    // Compound with variable unifies and binds the variable
    let term3 = Term::Compound("f".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Atom("b".to_string())
    ]);
    assert!(Unifier::unify(&term3, &term2, &mut subst));
    // Verify that X was correctly bound to 'a'
    assert_eq!(subst.get("X"), Some(&Term::Atom("a".to_string())));
}

#[test]
fn test_unify_different_functors() {
    // Compound terms with different functors can't unify
    // This is like trying to unify f(a) with g(a) - different function names
    let mut subst = HashMap::new();
    
    let term1 = Term::Compound("f".to_string(), vec![Term::Atom("a".to_string())]);
    let term2 = Term::Compound("g".to_string(), vec![Term::Atom("a".to_string())]);
    
    // Even though the arguments are the same, different functors mean no unification
    assert!(!Unifier::unify(&term1, &term2, &mut subst));
}

#[test]
fn test_unify_different_arities() {
    // Compound terms with same functor but different number of arguments can't unify
    // f(a) vs f(a, b) - same name but different arity
    let mut subst = HashMap::new();
    
    let term1 = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string())
    ]);
    let term2 = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Atom("b".to_string())
    ]);
    
    // f/1 and f/2 are considered different predicates in Prolog
    assert!(!Unifier::unify(&term1, &term2, &mut subst));
}

#[test]
fn test_unify_nested_compounds() {
    // Test unification with nested compound terms
    // This tests that the algorithm correctly recurses through structures
    let mut subst = HashMap::new();
    
    // f(g(X), h(a)) with f(g(b), h(Y))
    // Create f(g(X), h(a)) - a compound with nested compounds
    let term1 = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![Term::Variable("X".to_string())]),
        Term::Compound("h".to_string(), vec![Term::Atom("a".to_string())])
    ]);
    // Create f(g(b), h(Y)) - another nested structure
    let term2 = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![Term::Atom("b".to_string())]),
        Term::Compound("h".to_string(), vec![Term::Variable("Y".to_string())])
    ]);
    
    assert!(Unifier::unify(&term1, &term2, &mut subst));
    // The unification should bind X -> b and Y -> a
    assert_eq!(subst.get("X"), Some(&Term::Atom("b".to_string())));
    assert_eq!(subst.get("Y"), Some(&Term::Atom("a".to_string())));
}

// ===== Occurs Check Tests =====
// The occurs check prevents creating infinite recursive structures

#[test]
fn test_occurs_check() {
    // Classic occurs check test: X = f(X)
    // This would create an infinite structure: X = f(f(f(...)))
    let mut subst = HashMap::new();
    
    // X = f(X) should fail occurs check
    let var = Term::Variable("X".to_string());
    let recursive = Term::Compound("f".to_string(), vec![var.clone()]);
    assert!(!Unifier::unify(&var, &recursive, &mut subst));
    // No binding should be created when occurs check fails
    assert!(subst.is_empty());
}

#[test]
fn test_occurs_check_nested() {
    // More complex occurs check: X = f(g(X))
    // The variable X appears deeper in the structure
    let mut subst = HashMap::new();
    
    // X = f(g(X)) should also fail
    let var = Term::Variable("X".to_string());
    let nested = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![var.clone()])
    ]);
    // Should still detect the cycle even when nested
    assert!(!Unifier::unify(&var, &nested, &mut subst));
}

#[test]
fn test_occurs_check_through_substitution() {
    // Test occurs check with existing substitutions
    // This tests a subtle case where cycles can form through bindings
    let mut subst = HashMap::new();
    
    // First bind Y to X
    subst.insert("Y".to_string(), Term::Variable("X".to_string()));
    
    // Now try X = f(Y), which is really X = f(X)
    let var_x = Term::Variable("X".to_string());
    let term = Term::Compound("f".to_string(), vec![Term::Variable("Y".to_string())]);
    
    // The occurs check should detect this indirect cycle
    assert!(!Unifier::unify(&var_x, &term, &mut subst));
}

// ===== Substitution Application Tests =====
// These tests verify that substitutions are correctly applied to terms

#[test]
fn test_apply_substitution() {
    // Test applying a substitution to various term types
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Atom("hello".to_string()));
    subst.insert("Y".to_string(), Term::Number(42));
    
    // Apply to variable
    // X should be replaced with 'hello'
    let var = Term::Variable("X".to_string());
    let result = Unifier::apply_substitution(&var, &subst);
    assert_eq!(result, Term::Atom("hello".to_string()));
    
    // Apply to compound term
    // f(X, Y) should become f(hello, 42)
    let compound = Term::Compound("f".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Variable("Y".to_string())
    ]);
    let result = Unifier::apply_substitution(&compound, &subst);
    match result {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "f");
            assert_eq!(args[0], Term::Atom("hello".to_string()));
            assert_eq!(args[1], Term::Number(42));
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_apply_substitution_unbound_variable() {
    // Test that unbound variables remain unchanged
    let subst = HashMap::new();
    
    let var = Term::Variable("X".to_string());
    let result = Unifier::apply_substitution(&var, &subst);
    // X should remain X since it's not bound
    assert_eq!(result, var);
}

#[test]
fn test_apply_substitution_to_atom() {
    // Test that atoms are not affected by substitutions
    // (atoms are constants, not variables)
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Atom("test".to_string()));
    
    let atom = Term::Atom("hello".to_string());
    let result = Unifier::apply_substitution(&atom, &subst);
    // The atom should remain unchanged
    assert_eq!(result, atom);
}

#[test]
fn test_apply_substitution_to_terms() {
    // Test batch application to multiple terms
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Number(1));
    subst.insert("Y".to_string(), Term::Number(2));
    
    let terms = vec![
        Term::Variable("X".to_string()),
        Term::Variable("Y".to_string()),
        Term::Atom("a".to_string())
    ];
    
    let results = Unifier::apply_substitution_to_terms(&terms, &subst);
    assert_eq!(results[0], Term::Number(1));
    assert_eq!(results[1], Term::Number(2));
    assert_eq!(results[2], Term::Atom("a".to_string()));
}

#[test]
fn test_variable_chains() {
    // Test that substitution follows chains of variable bindings
    // This is crucial for correctness
    let mut subst = HashMap::new();
    
    // X = Y, Y = Z, Z = hello
    // Create a chain: X -> Y -> Z -> hello
    subst.insert("X".to_string(), Term::Variable("Y".to_string()));
    subst.insert("Y".to_string(), Term::Variable("Z".to_string()));
    subst.insert("Z".to_string(), Term::Atom("hello".to_string()));
    
    let var_x = Term::Variable("X".to_string());
    let result = Unifier::apply_substitution(&var_x, &subst);
    // X should resolve all the way to 'hello'
    assert_eq!(result, Term::Atom("hello".to_string()));
}

// ===== Can Unify Tests =====
// Tests for checking unifiability without modifying state

#[test]
fn test_can_unify() {
    // Test the can_unify predicate function
    // This checks if terms CAN unify without actually doing it
    let term1 = Term::Variable("X".to_string());
    let term2 = Term::Atom("hello".to_string());
    assert!(Unifier::can_unify(&term1, &term2));
    
    let term3 = Term::Atom("hello".to_string());
    let term4 = Term::Atom("world".to_string());
    assert!(!Unifier::can_unify(&term3, &term4));
}

#[test]
fn test_can_unify_doesnt_modify_state() {
    // Verify that can_unify is truly side-effect free
    // It should not retain any state between calls
    let term1 = Term::Variable("X".to_string());
    let term2 = Term::Atom("test".to_string());
    
    // Test multiple times to ensure no state is retained
    assert!(Unifier::can_unify(&term1, &term2));
    assert!(Unifier::can_unify(&term1, &term2));
    assert!(Unifier::can_unify(&term1, &Term::Atom("other".to_string())));
}

// ===== Variable Renaming Tests =====
// Tests for creating fresh variable names to avoid conflicts

#[test]
fn test_rename_variables() {
    // Test renaming variables in a compound term
    // This is used when instantiating clauses to avoid variable conflicts
    let term = Term::Compound("f".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Atom("a".to_string()),
        Term::Variable("Y".to_string())
    ]);
    
    let renamed = Unifier::rename_variables(&term, "_1");
    match renamed {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "f");
            // X becomes X_1
            assert_eq!(args[0], Term::Variable("X_1".to_string()));
            // Atom remains unchanged
            assert_eq!(args[1], Term::Atom("a".to_string()));
            // Y becomes Y_1
            assert_eq!(args[2], Term::Variable("Y_1".to_string()));
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_rename_variables_nested() {
    // Test that renaming works recursively through nested structures
    let term = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![
            Term::Variable("X".to_string())
        ])
    ]);
    
    let renamed = Unifier::rename_variables(&term, "_new");
    match renamed {
        Term::Compound(_, args) => {
            match &args[0] {
                Term::Compound(_, inner_args) => {
                    // Variable in nested compound should also be renamed
                    assert_eq!(inner_args[0], Term::Variable("X_new".to_string()));
                }
                _ => panic!("Expected nested compound"),
            }
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_rename_variables_preserves_non_variables() {
    // Test that renaming only affects variables, not atoms or numbers
    let term = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Number(42)
    ]);
    
    let renamed = Unifier::rename_variables(&term, "_suffix");
    assert_eq!(renamed, term); // Should be unchanged
}

// ===== Get All Variables Tests =====
// Tests for extracting all variables from a substitution

#[test]
fn test_get_all_variables_empty() {
    // Empty substitution should return empty list
    let subst = HashMap::new();
    let vars = Unifier::get_all_variables(&subst);
    assert!(vars.is_empty());
}

#[test]
fn test_get_all_variables() {
    // Test extracting variables from both keys and values
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Variable("Y".to_string()));
    subst.insert("Y".to_string(), Term::Atom("hello".to_string()));
    subst.insert("Z".to_string(), Term::Compound("f".to_string(), vec![
        Term::Variable("W".to_string())
    ]));
    
    let vars = Unifier::get_all_variables(&subst);
    // Should find all four variables: X, Y, Z (from keys) and W (from value)
    assert!(vars.contains(&"X".to_string()));
    assert!(vars.contains(&"Y".to_string()));
    assert!(vars.contains(&"Z".to_string()));
    assert!(vars.contains(&"W".to_string()));
}

#[test]
fn test_get_all_variables_sorted() {
    // Test that variables are returned in sorted order
    let mut subst = HashMap::new();
    subst.insert("Z".to_string(), Term::Atom("z".to_string()));
    subst.insert("A".to_string(), Term::Atom("a".to_string()));
    subst.insert("M".to_string(), Term::Atom("m".to_string()));
    
    let vars = Unifier::get_all_variables(&subst);
    // Should be alphabetically sorted
    assert_eq!(vars, vec!["A", "M", "Z"]);
}

// ===== Compose Substitutions Tests =====
// Tests for combining multiple substitutions

#[test]
fn test_compose_substitutions() {
    // Test basic composition: first apply subst1, then subst2
    let mut subst1 = HashMap::new();
    subst1.insert("X".to_string(), Term::Variable("Y".to_string()));
    
    let mut subst2 = HashMap::new();
    subst2.insert("Y".to_string(), Term::Atom("hello".to_string()));
    
    let composed = Unifier::compose_substitutions(&subst1, &subst2);
    
    // X should map to hello (through Y)
    // This tests that composition correctly follows chains
    let x_result = Unifier::apply_substitution(&Term::Variable("X".to_string()), &composed);
    assert_eq!(x_result, Term::Atom("hello".to_string()));
}

#[test]
fn test_compose_substitutions_overlap() {
    // Test composition when substitutions have overlapping variables
    let mut subst1 = HashMap::new();
    subst1.insert("X".to_string(), Term::Atom("first".to_string()));
    
    let mut subst2 = HashMap::new();
    subst2.insert("X".to_string(), Term::Atom("second".to_string()));
    subst2.insert("Y".to_string(), Term::Atom("new".to_string()));
    
    let composed = Unifier::compose_substitutions(&subst1, &subst2);
    
    // X from subst1 should be preserved (applied through subst2)
    // This is because composition applies subst2 to the VALUES of subst1, not the keys
    assert_eq!(composed.get("X"), Some(&Term::Atom("first".to_string())));
    // Y from subst2 should be added
    assert_eq!(composed.get("Y"), Some(&Term::Atom("new".to_string())));
}

#[test]
fn test_compose_substitutions_complex() {
    // Test composition with compound terms
    let mut subst1 = HashMap::new();
    subst1.insert("X".to_string(), Term::Compound("f".to_string(), vec![
        Term::Variable("Y".to_string())
    ]));
    
    let mut subst2 = HashMap::new();
    subst2.insert("Y".to_string(), Term::Number(42));
    
    let composed = Unifier::compose_substitutions(&subst1, &subst2);
    
    // X should map to f(42)
    // The Y inside f should be replaced
    let expected = Term::Compound("f".to_string(), vec![Term::Number(42)]);
    assert_eq!(composed.get("X"), Some(&expected));
}

// ===== Idempotent Tests =====
// Tests for checking if substitutions are in normal form

#[test]
fn test_is_idempotent_empty() {
    // Empty substitution is trivially idempotent
    let subst = HashMap::new();
    assert!(Unifier::is_idempotent(&subst));
}

#[test]
fn test_is_idempotent_true() {
    // A substitution where all variables map directly to non-variables
    // is idempotent (applying it twice gives the same result)
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Atom("hello".to_string()));
    subst.insert("Y".to_string(), Term::Number(42));
    
    assert!(Unifier::is_idempotent(&subst));
}

#[test]
fn test_is_idempotent_false() {
    // A substitution with chains is NOT idempotent
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Variable("Y".to_string()));
    subst.insert("Y".to_string(), Term::Atom("hello".to_string()));
    
    // Not idempotent because X -> Y and Y -> hello
    // Applying subst to X gives Y, applying again gives hello
    assert!(!Unifier::is_idempotent(&subst));
}

#[test]
fn test_is_idempotent_circular() {
    // Circular references are definitely not idempotent
    // They would cause infinite loops if not handled properly
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Variable("Y".to_string()));
    subst.insert("Y".to_string(), Term::Variable("X".to_string()));
    
    // Circular references are not idempotent
    // The cycle detection should identify this as non-idempotent
    assert!(!Unifier::is_idempotent(&subst));
}

// ===== Remove Identity Bindings Tests =====
// Tests for cleaning up redundant self-bindings

#[test]
fn test_remove_identity_bindings_empty() {
    // Empty substitution should remain empty
    let mut subst = HashMap::new();
    Unifier::remove_identity_bindings(&mut subst);
    assert!(subst.is_empty());
}

#[test]
fn test_remove_identity_bindings() {
    // Test removing X -> X while preserving other bindings
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Variable("X".to_string())); // Identity
    subst.insert("Y".to_string(), Term::Variable("Z".to_string())); // Not identity
    subst.insert("Z".to_string(), Term::Atom("hello".to_string())); // Not identity
    
    Unifier::remove_identity_bindings(&mut subst);
    
    // X -> X should be removed
    assert!(!subst.contains_key("X"));
    // Other bindings should remain
    assert!(subst.contains_key("Y"));
    assert!(subst.contains_key("Z"));
}

#[test]
fn test_remove_identity_bindings_preserves_non_variable_bindings() {
    // Test that X -> "X" (atom) is NOT removed
    // This is not an identity binding because "X" is an atom, not a variable
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Atom("X".to_string())); // Not identity (atom, not variable)
    
    Unifier::remove_identity_bindings(&mut subst);
    
    // Should still contain the binding since it's not X -> Variable(X)
    assert!(subst.contains_key("X"));
}

// ===== Edge Cases and Complex Scenarios =====
// Tests for special cases and complex unification scenarios

#[test]
fn test_unify_lists() {
    // Test unification with Prolog list structures
    // Lists in Prolog are represented as .(head, tail) compounds
    let mut subst = HashMap::new();
    
    // Create list-like structures [1, 2] using . functor
    // This is .(1, .(2, []))
    let list1 = Term::Compound(".".to_string(), vec![
        Term::Number(1),
        Term::Compound(".".to_string(), vec![
            Term::Number(2),
            Term::Atom("[]".to_string())
        ])
    ]);
    
    let list2 = Term::Compound(".".to_string(), vec![
        Term::Variable("H".to_string()),
        Term::Variable("T".to_string())
    ]);
    
    assert!(Unifier::unify(&list1, &list2, &mut subst));
    // H should be bound to 1 (the head)
    assert_eq!(subst.get("H"), Some(&Term::Number(1)));
    // T should be bound to [2] (the tail)
}

#[test]
fn test_unify_multiple_variables_to_same_term() {
    // Test the important case where the same variable appears multiple times
    // This tests that all occurrences must unify to the same value
    let mut subst = HashMap::new();
    
    // f(X, X) with f(a, a) should succeed
    let term1 = Term::Compound("f".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Variable("X".to_string())
    ]);
    let term2 = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Atom("a".to_string())
    ]);
    
    assert!(Unifier::unify(&term1, &term2, &mut subst));
    assert_eq!(subst.get("X"), Some(&Term::Atom("a".to_string())));
    
    // f(X, X) with f(a, b) should fail
    // Should fail because X can't be both 'a' and 'b'
    let mut subst2 = HashMap::new();
    let term3 = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Atom("b".to_string())
    ]);
    
    assert!(!Unifier::unify(&term1, &term3, &mut subst2));
}

#[test]
fn test_unify_preserves_existing_bindings() {
    // Test that unification respects pre-existing bindings
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Atom("existing".to_string()));
    
    // Try to unify Y with X
    let var_y = Term::Variable("Y".to_string());
    let var_x = Term::Variable("X".to_string());
    
    assert!(Unifier::unify(&var_y, &var_x, &mut subst));
    
    // Y should be bound to the existing binding of X
    // Y should be bound to X's existing binding, not to X itself
    let y_result = Unifier::apply_substitution(&var_y, &subst);
    assert_eq!(y_result, Term::Atom("existing".to_string()));
}

// ===== Substitution Utils Tests =====
// Tests for the utility functions in the substitution_utils module

#[test]
fn test_substitution_utils_new() {
    use super::substitution_utils;
    
    // Test creating a new empty substitution
    let subst = substitution_utils::new();
    assert!(substitution_utils::is_empty(&subst));
    assert_eq!(substitution_utils::len(&subst), 0);
}

#[test]
fn test_substitution_utils_operations() {
    use super::substitution_utils;
    
    // Test basic operations on substitutions
    let mut subst = substitution_utils::new();
    assert!(substitution_utils::is_empty(&subst));
    
    subst.insert("X".to_string(), Term::Atom("hello".to_string()));
    assert!(!substitution_utils::is_empty(&subst));
    assert_eq!(substitution_utils::len(&subst), 1);
    
    subst.insert("Y".to_string(), Term::Number(42));
    assert_eq!(substitution_utils::len(&subst), 2);
    
    substitution_utils::clear(&mut subst);
    assert!(substitution_utils::is_empty(&subst));
    assert_eq!(substitution_utils::len(&subst), 0);
}

#[test]
fn test_substitution_utils_format_empty() {
    use super::substitution_utils;
    
    // Test formatting an empty substitution
    let subst = substitution_utils::new();
    let formatted = substitution_utils::format_substitution(&subst);
    assert_eq!(formatted, "{}");
}

#[test]
fn test_substitution_utils_format_single() {
    use super::substitution_utils;
    
    // Test formatting a substitution with one binding
    let mut subst = substitution_utils::new();
    subst.insert("X".to_string(), Term::Atom("hello".to_string()));
    
    let formatted = substitution_utils::format_substitution(&subst);
    assert_eq!(formatted, "{X -> hello}");
}

#[test]
fn test_substitution_utils_format_multiple() {
    use super::substitution_utils;
    
    // Test formatting a substitution with multiple bindings
    let mut subst = substitution_utils::new();
    subst.insert("X".to_string(), Term::Atom("hello".to_string()));
    subst.insert("Y".to_string(), Term::Number(42));
    
    let formatted = substitution_utils::format_substitution(&subst);
    // Should contain both bindings (order may vary due to HashMap)
    assert!(formatted.contains("X -> hello"));
    assert!(formatted.contains("Y -> 42"));
    assert!(formatted.starts_with('{'));
    assert!(formatted.ends_with('}'));
}

#[test]
fn test_substitution_utils_format_complex() {
    use super::substitution_utils;
    
    // Test formatting with compound terms
    let mut subst = substitution_utils::new();
    subst.insert("X".to_string(), Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Variable("Y".to_string())
    ]));
    
    let formatted = substitution_utils::format_substitution(&subst);
    assert!(formatted.contains("X -> f(a, Y)"));
}

#[test]
fn test_substitution_utils_clear() {
    use super::substitution_utils;
    
    // Test that clear removes all bindings
    let mut subst = substitution_utils::new();
    subst.insert("X".to_string(), Term::Atom("test".to_string()));
    subst.insert("Y".to_string(), Term::Number(123));
    
    assert_eq!(substitution_utils::len(&subst), 2);
    
    substitution_utils::clear(&mut subst);
    
    assert_eq!(substitution_utils::len(&subst), 0);
    assert!(substitution_utils::is_empty(&subst));
}

#[test]
fn test_substitution_utils_with_lists() {
    use super::substitution_utils;
    
    // Test utilities with list-like structures
    let mut subst = substitution_utils::new();
    
    // Create a list-like term
    // Create a Prolog list structure [1, 2]
    let list = Term::Compound(".".to_string(), vec![
        Term::Number(1),
        Term::Compound(".".to_string(), vec![
            Term::Number(2),
            Term::Atom("[]".to_string())
        ])
    ]);
    
    subst.insert("List".to_string(), list);
    
    let formatted = substitution_utils::format_substitution(&subst);
    // Should format the list structure correctly
    assert!(formatted.contains("List ->"));
    assert!(!substitution_utils::is_empty(&subst));
}