// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: engine_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the engine module
//! 
//! This test suite validates all aspects of the Prolog engine including:
//! - ExecutionContext management and stack protection
//! - EngineStats tracking and reporting
//! - PrologEngine query execution and clause management
//! - Edge cases, error handling, and performance limits

use super::*;

// ===== ExecutionContext Tests =====
// These tests verify that the ExecutionContext properly manages execution state,
// including stack depth tracking, cut operations, and overflow prevention.

#[test]
fn test_execution_context_creation() {
    // Tests that a new ExecutionContext is properly initialized with default values.
    // The context tracks:
    // - Stack depth (starts at 0, no predicates called yet)
    // - Cut flag (false, no cut has been called)
    // - Cut level (0, no nested cuts)
    // - Max stack depth (100, default safety limit)
    // - Current predicate ("unknown", no predicate being executed)
    
    let context = ExecutionContext::new();
    
    // Verify all default values are set correctly
    assert_eq!(context.get_stack_depth(), 0);
    assert!(!context.is_cut_called());
    assert_eq!(context.get_cut_level(), 0);
    assert_eq!(context.get_max_stack_depth(), 100);
    assert_eq!(context.get_current_predicate(), "unknown");
}

#[test]
fn test_execution_context_with_max_depth() {
    // Tests the custom constructor that allows setting a specific max stack depth.
    // This is useful for queries that need deeper recursion or for limiting
    // recursion in resource-constrained environments.
    
    let context = ExecutionContext::with_max_depth(50);
    
    // Should have the custom max depth
    assert_eq!(context.get_max_stack_depth(), 50);
    // But other values should still be defaults
    assert_eq!(context.get_stack_depth(), 0);
}

#[test]
fn test_enter_exit_predicate() {
    // Tests the mechanism for tracking predicate call stack.
    // When the engine calls a predicate, it "enters" it (incrementing stack depth).
    // When the predicate completes, it "exits" (decrementing stack depth).
    // This is crucial for detecting infinite recursion and stack overflow.
    
    let mut context = ExecutionContext::new();
    
    // Enter a predicate - simulates calling test/1
    // The /1 notation means the predicate takes 1 argument
    assert!(context.enter_predicate("test/1".to_string()).is_ok());
    assert_eq!(context.get_stack_depth(), 1);
    assert_eq!(context.get_current_predicate(), "test/1");
    
    // Enter another predicate - simulates test/1 calling foo/2
    // This creates a call stack: test/1 -> foo/2
    assert!(context.enter_predicate("foo/2".to_string()).is_ok());
    assert_eq!(context.get_stack_depth(), 2);
    assert_eq!(context.get_current_predicate(), "foo/2");
    
    // Exit predicates - simulates returning from calls
    // First exit: foo/2 returns
    context.exit_predicate();
    assert_eq!(context.get_stack_depth(), 1);
    
    // Second exit: test/1 returns
    context.exit_predicate();
    assert_eq!(context.get_stack_depth(), 0);
    
    // Exit when already at 0 should stay at 0 (safety check)
    // This prevents underflow if exit is called too many times
    context.exit_predicate();
    assert_eq!(context.get_stack_depth(), 0);
}

#[test]
fn test_stack_overflow_detection() {
    // Tests that the context properly detects and prevents stack overflow.
    // This is a critical safety feature that prevents infinite recursion
    // from causing actual stack overflow or consuming all memory.
    
    // Create context with very low limit (3) for easy testing
    let mut context = ExecutionContext::with_max_depth(3);
    
    // Can enter 3 predicates (up to the limit)
    assert!(context.enter_predicate("pred1".to_string()).is_ok());
    assert!(context.enter_predicate("pred2".to_string()).is_ok());
    assert!(context.enter_predicate("pred3".to_string()).is_ok());
    
    // This should cause stack overflow - exceeding the limit of 3
    let result = context.enter_predicate("pred4".to_string());
    assert!(result.is_err());
    
    // Verify the error contains the correct information
    if let Err(RuntimeError::StackOverflow { depth, predicate }) = result {
        assert_eq!(depth, 4);  // Tried to go to depth 4
        assert_eq!(predicate, "pred4");  // Failed on pred4
    } else {
        panic!("Expected StackOverflow error");
    }
}

#[test]
fn test_cut_operations() {
    // Tests the cut (!) operation tracking.
    // Cut is a special Prolog operator that prevents backtracking.
    // The context needs to track whether cut has been called to
    // inform the engine to stop trying alternative solutions.
    
    let mut context = ExecutionContext::new();
    
    // Initially, no cut has been called
    assert!(!context.is_cut_called());
    
    // Call cut - this sets the flag
    context.cut();
    assert!(context.is_cut_called());
    
    // Reset cut - used when entering a new branch of execution
    context.reset_cut();
    assert!(!context.is_cut_called());
}

#[test]
fn test_cut_levels() {
    // Tests cut level tracking for nested cut operations.
    // When cuts appear in nested rule calls, the engine needs to
    // track which level the cut applies to. This prevents a cut
    // in a nested rule from affecting the parent rule incorrectly.
    
    let mut context = ExecutionContext::new();
    
    // Initially at level 0
    assert_eq!(context.get_cut_level(), 0);
    
    // Set cut level to 5 (simulating 5 levels of nesting)
    context.set_cut_level(5);
    assert_eq!(context.get_cut_level(), 5);
    
    // Can change the level as execution proceeds
    context.set_cut_level(10);
    assert_eq!(context.get_cut_level(), 10);
}

#[test]
fn test_set_max_stack_depth() {
    // Tests runtime modification of the stack depth limit.
    // This allows adjusting the limit based on query complexity
    // or available resources.
    
    let mut context = ExecutionContext::new();
    
    // Check default limit
    assert_eq!(context.get_max_stack_depth(), 100);
    
    // Increase limit for complex queries
    context.set_max_stack_depth(200);
    assert_eq!(context.get_max_stack_depth(), 200);
    
    // Test that the new limit is enforced
    // Set very low limit
    context.set_max_stack_depth(1);
    assert!(context.enter_predicate("pred1".to_string()).is_ok());  // OK - at limit
    assert!(context.enter_predicate("pred2".to_string()).is_err()); // Error - exceeds limit
}

#[test]
fn test_execution_context_edge_cases() {
    // Tests edge cases and boundary conditions for ExecutionContext.
    // These ensure the context handles unusual but valid inputs correctly.
    
    // Test 1: Max depth of 0 should prevent any predicate entry
    // This effectively disables all predicate calls
    let mut context = ExecutionContext::with_max_depth(0);
    let result = context.enter_predicate("test".to_string());
    assert!(result.is_err());
    
    // Test 2: Empty predicate name
    // The system should handle this gracefully even though it's unusual
    let mut context2 = ExecutionContext::new();
    assert!(context2.enter_predicate("".to_string()).is_ok());
    assert_eq!(context2.get_current_predicate(), "");
    
    // Test 3: Very long predicate name
    // Should handle long names without buffer overflow or truncation
    let long_name = "a".repeat(1000);
    assert!(context2.enter_predicate(long_name.clone()).is_ok());
    assert_eq!(context2.get_current_predicate(), &long_name);
}

// ===== EngineStats Tests =====
// These tests verify that statistics are properly tracked and reported.

#[test]
fn test_engine_stats_creation() {
    // Tests that EngineStats is properly initialized with default values.
    // Stats track various metrics about the engine's operation and database.
    
    let stats = EngineStats::new();
    
    // All counters should start at 0
    assert_eq!(stats.clause_count, 0);
    assert_eq!(stats.variable_counter, 0);
    assert_eq!(stats.queries_executed, 0);
    
    // Default limits
    assert_eq!(stats.max_solutions, 100);
    assert_eq!(stats.max_stack_depth, 100);
    
    // No predicates defined yet
    assert!(stats.predicates_defined.is_empty());
}

#[test]
fn test_add_predicate() {
    // Tests tracking of predicate definitions.
    // When clauses are added, stats track which predicates are defined
    // and how many clauses each has.
    
    let mut stats = EngineStats::new();
    
    // Add first clause for parent/2
    stats.add_predicate("parent", 2);
    assert_eq!(stats.predicate_count(), 1);
    // The key format is "functor/arity" (standard Prolog notation)
    assert_eq!(stats.predicates_defined.get("parent/2"), Some(&1));
    
    // Add same predicate again (second clause for parent/2)
    stats.add_predicate("parent", 2);
    assert_eq!(stats.predicate_count(), 1);  // Still one unique predicate
    assert_eq!(stats.predicates_defined.get("parent/2"), Some(&2));  // But 2 clauses
    
    // Add different predicate
    stats.add_predicate("likes", 2);
    assert_eq!(stats.predicate_count(), 2);  // Now 2 unique predicates
    
    // Add predicate with different arity (parent/3 is different from parent/2)
    stats.add_predicate("parent", 3);
    assert_eq!(stats.predicate_count(), 3);  // 3 unique predicates
}

#[test]
fn test_most_common_predicate() {
    // Tests finding the predicate with the most clauses.
    // This helps identify which predicates have the most rules/facts,
    // useful for optimization and understanding program structure.
    
    let mut stats = EngineStats::new();
    
    // Empty stats should return None
    assert!(stats.most_common_predicate().is_none());
    
    // Add predicates with different frequencies
    stats.add_predicate("parent", 2);  // 1 clause
    stats.add_predicate("parent", 2);  // 2 clauses
    stats.add_predicate("parent", 2);  // 3 clauses
    stats.add_predicate("likes", 2);   // 1 clause
    stats.add_predicate("likes", 2);   // 2 clauses
    stats.add_predicate("friend", 2);  // 1 clause
    
    let (pred, count) = stats.most_common_predicate().unwrap();
    assert_eq!(pred, "parent/2");  // parent/2 has the most clauses
    assert_eq!(count, 3);          // with 3 clauses
}

#[test]
fn test_engine_stats_display() {
    // Tests the Display trait implementation for EngineStats.
    // This formats stats into a human-readable report.
    
    let mut stats = EngineStats::new();
    stats.clause_count = 10;
    stats.queries_executed = 5;
    stats.add_predicate("test", 1);
    stats.add_predicate("test", 1);
    
    let display = format!("{}", stats);
    
    // Verify the report contains expected information
    assert!(display.contains("Total clauses: 10"));
    assert!(display.contains("Queries executed: 5"));
    assert!(display.contains("test/1"));
    assert!(display.contains("2 clauses"));
}

#[test]
fn test_engine_stats_edge_cases() {
    // Tests edge cases for EngineStats to ensure robustness.
    
    let mut stats = EngineStats::new();
    
    // Test with empty predicate name
    // Should handle this gracefully even though it's unusual
    stats.add_predicate("", 0);
    assert_eq!(stats.predicate_count(), 1);
    assert!(stats.predicates_defined.contains_key("/0"));
    
    // Test with very large arity
    // Should handle without overflow
    stats.add_predicate("big", usize::MAX);
    assert_eq!(stats.predicate_count(), 2);
    
    // Test that all stats can handle large values
    // Set all counters to maximum values
    stats.clause_count = usize::MAX;
    stats.variable_counter = usize::MAX;
    stats.max_solutions = usize::MAX;
    stats.max_stack_depth = usize::MAX;
    stats.queries_executed = usize::MAX;
    
    // Should not panic when displaying (even with huge numbers)
    let _ = format!("{}", stats);
}

// ===== PrologEngine Tests =====
// These tests verify the main engine functionality.

#[test]
fn test_engine_creation() {
    // Tests that a new PrologEngine is properly initialized.
    // The engine starts with an empty database and default settings.
    
    let engine = PrologEngine::new();
    
    assert_eq!(engine.clauses.len(), 0);      // No clauses in database
    assert_eq!(engine.max_solutions, 100);    // Default solution limit
    assert_eq!(engine.variable_counter, 0);   // No variables renamed yet
}

#[test]
fn test_engine_with_limits() {
    // Tests creating an engine with custom solution limits.
    // This is useful for controlling resource usage.
    
    let engine = PrologEngine::with_limits(50);
    
    assert_eq!(engine.max_solutions, 50);
    assert_eq!(engine.stats.max_solutions, 50);  // Stats should match
}

#[test]
fn test_engine_with_config() {
    // Tests creating an engine with full configuration.
    // Allows setting both solution limit and stack depth limit.
    
    let engine = PrologEngine::with_config(25, 200);
    
    assert_eq!(engine.max_solutions, 25);
    assert_eq!(engine.stats.max_solutions, 25);
    assert_eq!(engine.stats.max_stack_depth, 200);
}

#[test]
fn test_add_facts() {
    // Tests adding facts (clauses with no body) to the database.
    // Facts are assertions that are always true, like parent(tom, bob).
    
    let mut engine = PrologEngine::new();
    
    // Create a fact: parent(tom, bob)
    engine.add_fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("tom".to_string()),
        Term::Atom("bob".to_string())
    ]));
    
    // Verify the fact was added
    assert_eq!(engine.clauses.len(), 1);
    assert!(engine.clauses[0].is_fact());
    
    // Stats should be updated
    assert_eq!(engine.stats.clause_count, 1);
    assert_eq!(engine.stats.predicate_count(), 1);
}

#[test]
fn test_add_rules() {
    // Tests adding rules (clauses with body) to the database.
    // Rules define relationships that hold when conditions are met.
    
    let mut engine = PrologEngine::new();
    
    // Create a rule: grandparent(X, Z) :- parent(X, Y), parent(Y, Z)
    let head = Term::Compound("grandparent".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Variable("Z".to_string())
    ]);
    
    let body = vec![
        Term::Compound("parent".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Variable("Y".to_string())
        ]),
        Term::Compound("parent".to_string(), vec![
            Term::Variable("Y".to_string()),
            Term::Variable("Z".to_string())
        ])
    ];
    
    engine.add_rule(head, body);
    
    // Verify the rule was added
    assert_eq!(engine.clauses.len(), 1);
    assert!(engine.clauses[0].is_rule());
    assert_eq!(engine.clauses[0].body.len(), 2);  // Two goals in body
}

#[test]
fn test_parse_and_add() {
    // Tests parsing Prolog source code and adding to the database.
    // This is the main way users add clauses to the engine.
    
    let mut engine = PrologEngine::new();
    
    // Parse and add facts from strings
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    
    // Verify both were added
    assert_eq!(engine.clauses.len(), 2);
    assert_eq!(engine.stats.clause_count, 2);
}

#[test]
fn test_parse_error() {
    // Tests that parse errors are properly reported and don't corrupt the engine.
    
    let mut engine = PrologEngine::new();
    
    // Try to parse invalid syntax
    let result = engine.parse_and_add("invalid syntax");
    assert!(result.is_err());
    
    // Engine should still be usable after error
    assert_eq!(engine.clauses.len(), 0);  // No clauses added
}

#[test]
fn test_simple_query() {
    // Tests basic query execution against facts in the database.
    // This demonstrates the core functionality of the Prolog engine.
    
    let mut engine = PrologEngine::new();
    
    // Add facts to the database
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    
    // Query 1: parent(tom, bob) - should succeed (exact match)
    let solutions = engine.parse_query("parent(tom, bob).").unwrap();
    assert_eq!(solutions.len(), 1);  // One solution (true)
    
    // Query 2: parent(tom, X) - should find X = bob
    let solutions = engine.parse_query("parent(tom, X).").unwrap();
    assert_eq!(solutions.len(), 1);  // One solution
    // The solution should bind X to bob
    
    // Query 3: parent(mary, X) - should fail (no match)
    let solutions = engine.parse_query("parent(mary, X).").unwrap();
    assert_eq!(solutions.len(), 0);  // No solutions
}

#[test]
fn test_variable_query() {
    // Tests queries with variables that can match multiple facts.
    // This demonstrates backtracking - finding all possible solutions.
    
    let mut engine = PrologEngine::new();
    
    // Add multiple facts
    engine.parse_and_add("likes(mary, food).").unwrap();
    engine.parse_and_add("likes(mary, wine).").unwrap();
    engine.parse_and_add("likes(john, wine).").unwrap();
    
    // Query: likes(mary, X) - should find all things mary likes
    let solutions = engine.parse_query("likes(mary, X).").unwrap();
    assert_eq!(solutions.len(), 2);  // Two things: food and wine
    
    // Query: likes(X, wine) - should find all who like wine
    let solutions = engine.parse_query("likes(X, wine).").unwrap();
    assert_eq!(solutions.len(), 2);  // Two people: mary and john
}

#[test]
fn test_rule_execution() {
    // Tests execution of rules that derive new facts from existing ones.
    // This demonstrates the inference capabilities of Prolog.
    
    let mut engine = PrologEngine::new();
    
    // Add facts
    engine.parse_and_add("parent(alice, bob).").unwrap();
    engine.parse_and_add("parent(bob, charlie).").unwrap();
    
    // Add rule: grandparent(X, Z) :- parent(X, Y), parent(Y, Z)
    engine.parse_and_add("grandparent(X, Z) :- parent(X, Y), parent(Y, Z).").unwrap();
    
    // Query: grandparent(alice, charlie) - should succeed via the rule
    let solutions = engine.parse_query("grandparent(alice, charlie).").unwrap();
    assert_eq!(solutions.len(), 1);  // Alice is Charlie's grandparent
    
    // Query: grandparent(alice, X) - should find X = charlie
    let solutions = engine.parse_query("grandparent(alice, X).").unwrap();
    assert_eq!(solutions.len(), 1);
}

#[test]
fn test_arithmetic() {
    // Tests built-in arithmetic predicates.
    // Prolog has special handling for arithmetic evaluation.
    
    let mut engine = PrologEngine::new();
    
    // Test arithmetic evaluation: X is 2 + 3
    let solutions = engine.parse_query("X is 2 + 3.").unwrap();
    assert_eq!(solutions.len(), 1);  // X should be bound to 5
    
    // Test comparison: 5 > 3 (should succeed)
    let solutions = engine.parse_query("5 > 3.").unwrap();
    assert_eq!(solutions.len(), 1);  // True
    
    // Test comparison: 3 > 5 (should fail)
    let solutions = engine.parse_query("3 > 5.").unwrap();
    assert_eq!(solutions.len(), 0);  // False
}

#[test]
fn test_list_operations() {
    // Tests built-in list predicates.
    // Lists are fundamental data structures in Prolog.
    
    let mut engine = PrologEngine::new();
    
    // Test append: append([1, 2], [3, 4], X)
    let solutions = engine.parse_query("append([1, 2], [3, 4], X).").unwrap();
    assert_eq!(solutions.len(), 1);  // X = [1, 2, 3, 4]
    
    // Test member: member(2, [1, 2, 3])
    let solutions = engine.parse_query("member(2, [1, 2, 3]).").unwrap();
    assert_eq!(solutions.len(), 1);  // 2 is a member
    
    // Test length: length([a, b, c], X)
    let solutions = engine.parse_query("length([a, b, c], X).").unwrap();
    assert_eq!(solutions.len(), 1);  // X = 3
}

#[test]
fn test_cut_operation() {
    // Tests the cut (!) operator which prevents backtracking.
    // Cut is used to commit to a choice and improve efficiency.
    
    let mut engine = PrologEngine::new();
    
    // Define max/3 with cut:
    // max(X, Y, X) :- X >= Y, !.  (if X >= Y, X is max, don't try other clause)
    // max(X, Y, Y).               (otherwise Y is max)
    engine.parse_and_add("max(X, Y, X) :- X >= Y, !.").unwrap();
    engine.parse_and_add("max(X, Y, Y).").unwrap();
    
    // Query: max(5, 3, Z)
    let solutions = engine.parse_query("max(5, 3, Z).").unwrap();
    assert_eq!(solutions.len(), 1); // Cut should prevent second clause from being tried
    // Without cut, we might get two solutions (Z=5 and Z=3)
}

#[test]
fn test_engine_stats() {
    // Tests that the engine properly tracks statistics during operation.
    
    let mut engine = PrologEngine::new();
    
    // Add clauses
    engine.parse_and_add("fact1(a).").unwrap();
    engine.parse_and_add("fact1(b).").unwrap();
    engine.parse_and_add("fact2(x).").unwrap();
    
    let stats = engine.get_stats();
    assert_eq!(stats.clause_count, 3);      // 3 clauses added
    assert_eq!(stats.predicate_count(), 2); // 2 unique predicates: fact1/1 and fact2/1
    
    // Test query counting
    engine.parse_query("fact1(a).").unwrap();
    assert_eq!(engine.get_stats().queries_executed, 1);
}

#[test]
fn test_predicate_finding() {
    // Tests finding clauses for specific predicates.
    // This is useful for debugging and understanding the database.
    
    let mut engine = PrologEngine::new();
    
    // Add clauses for different predicates
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    engine.parse_and_add("likes(mary, wine).").unwrap();
    
    // Find all parent/2 clauses
    let parent_clauses = engine.find_clauses("parent", 2);
    assert_eq!(parent_clauses.len(), 2);
    
    // Find all likes/2 clauses
    let likes_clauses = engine.find_clauses("likes", 2);
    assert_eq!(likes_clauses.len(), 1);
    
    // Find clauses for non-existent predicate
    let unknown_clauses = engine.find_clauses("unknown", 1);
    assert_eq!(unknown_clauses.len(), 0);
    
    // Test is_predicate_defined
    assert!(engine.is_predicate_defined("parent", 2));    // User-defined
    assert!(engine.is_predicate_defined("append", 3));    // Built-in
    assert!(!engine.is_predicate_defined("unknown", 1));  // Not defined
}

#[test]
fn test_database_export_import() {
    // Tests exporting the database to text and importing it back.
    // This enables saving and loading Prolog programs.
    
    let mut engine = PrologEngine::new();
    
    // Add clauses
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    engine.parse_and_add("grandparent(X, Z) :- parent(X, Y), parent(Y, Z).").unwrap();
    
    // Export to string
    let exported = engine.export_database();
    assert!(exported.contains("parent(tom, bob)"));
    assert!(exported.contains("grandparent"));
    
    // Import into a new engine
    let mut new_engine = PrologEngine::new();
    let errors = new_engine.load_database(&exported);
    assert!(errors.is_empty());  // No errors during import
    assert_eq!(new_engine.clauses.len(), 3);  // All clauses imported
}

#[test]
fn test_error_handling() {
    // Tests that runtime errors are properly detected and reported.
    
    let mut engine = PrologEngine::new();
    
    // Test division by zero
    let result = engine.parse_query("X is 5 // 0.");
    assert!(result.is_err());  // Should error
    
    // Test uninstantiated variable in arithmetic
    // Y is unbound, so Y + 1 can't be evaluated
    let result = engine.parse_query("X is Y + 1.");
    assert!(result.is_err());  // Should error
}

#[test]
fn test_solution_limits() {
    // Tests that the engine respects solution limits.
    // This prevents runaway queries from consuming too many resources.
    
    let mut engine = PrologEngine::with_limits(3);  // Max 3 solutions
    
    // Add many facts
    for i in 1..=10 {
        engine.parse_and_add(&format!("number({}).", i)).unwrap();
    }
    
    // Query that would find 10 solutions
    let result = engine.parse_query("number(X).");
    
    // Should either succeed with limited solutions or fail with limit error
    match result {
        Ok(solutions) => assert!(solutions.len() <= 3),  // At most 3 solutions
        Err(_) => {} // Limit error is acceptable
    }
}

#[test]
fn test_stack_overflow_protection() {
    // Tests that infinite recursion is detected and prevented.
    // This is a critical safety feature.
    
    let mut engine = PrologEngine::with_config(10, 5); // Very low stack limit
    
    // Add an infinitely recursive rule: infinite(X) :- infinite(X)
    engine.parse_and_add("infinite(X) :- infinite(X).").unwrap();
    
    // Query should hit stack overflow
    let result = engine.parse_query("infinite(test).");
    assert!(result.is_err());
    
    // Should be a stack overflow error
    if let Err(e) = result {
        let error_msg = format!("{}", e);
        assert!(error_msg.contains("Stack overflow") || error_msg.contains("overflow"));
    }
}

#[test]
fn test_variable_renaming() {
    // Tests that variables are properly renamed to avoid conflicts.
    // When the same clause is used multiple times, each use needs
    // fresh variable names to prevent unwanted variable sharing.
    
    let mut engine = PrologEngine::new();
    
    // Add clauses with variable X
    engine.parse_and_add("test(X) :- X = 1.").unwrap();
    engine.parse_and_add("test(X) :- X = 2.").unwrap();
    
    // Query with variable Y (different from X in clauses)
    let solutions = engine.parse_query("test(Y).").unwrap();
    assert_eq!(solutions.len(), 2);  // Should find both solutions
    
    // Extract the values that Y is bound to
    let mut values = Vec::new();
    
    for solution in &solutions {
        // Find what Y resolves to - follow the substitution chain
        if let Some(term) = solution.get("Y") {
            let final_value = Unifier::apply_substitution(term, solution);
            if let Term::Number(n) = final_value {
                values.push(n);
            }
        }
    }
    
    // Sort values to ensure consistent comparison
    values.sort();
    assert_eq!(values, vec![1, 2], 
              "Expected Y to be bound to values [1, 2], found: {:?}", values);
}

#[test]
fn test_complex_unification() {
    // Tests unification with complex compound terms.
    // Unification is the core mechanism for pattern matching in Prolog.
    
    let mut engine = PrologEngine::new();
    
    // Add a rule that unifies complex structures
    engine.parse_and_add("complex(f(X, Y), f(a, b)) :- X = a, Y = b.").unwrap();
    
    // Query with matching structure
    let solutions = engine.parse_query("complex(f(a, b), Z).").unwrap();
    assert_eq!(solutions.len(), 1);  // Should succeed
    
    // Test unification failure with non-matching structure
    let solutions = engine.parse_query("complex(f(c, d), f(a, b)).").unwrap();
    assert_eq!(solutions.len(), 0);  // Should fail (c != a, d != b)
}

#[test]
fn test_list_predicates() {
    // Tests the list_predicates function which returns all defined predicates.
    
    let mut engine = PrologEngine::new();
    
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    engine.parse_and_add("likes(mary, wine).").unwrap();
    
    let predicates = engine.list_predicates();
    assert_eq!(predicates.len(), 2); // parent/2 and likes/2
    
    // Test listing built-ins
    let builtins = engine.list_builtins();
    assert!(!builtins.is_empty());
    
    // Check that some expected built-ins are there
    let builtin_names: Vec<&String> = builtins.iter().map(|(name, _, _)| name).collect();
    assert!(builtin_names.contains(&&"append".to_string()));
    assert!(builtin_names.contains(&&"is".to_string()));
}

#[test]
fn test_clear_database() {
    // Tests clearing all clauses from the database.
    // This resets the engine to a clean state.
    
    let mut engine = PrologEngine::new();
    
    // Add some clauses
    engine.parse_and_add("fact(a).").unwrap();
    engine.parse_and_add("fact(b).").unwrap();
    
    assert_eq!(engine.clauses.len(), 2);
    assert_eq!(engine.get_stats().clause_count, 2);
    
    // Clear the database
    engine.clear();
    
    // Everything should be reset
    assert_eq!(engine.clauses.len(), 0);
    assert_eq!(engine.get_stats().clause_count, 0);
    assert_eq!(engine.get_stats().predicate_count(), 0);
    assert_eq!(engine.variable_counter, 0);
}

#[test]
fn test_reset_stats() {
    // Tests resetting statistics while preserving the database.
    
    let mut engine = PrologEngine::new();
    
    // Add a clause and execute a query
    engine.parse_and_add("fact(a).").unwrap();
    engine.parse_query("fact(a).").unwrap();
    
    assert_eq!(engine.get_stats().queries_executed, 1);
    
    // Reset stats
    engine.reset_stats();
    
    // Query count should be reset but clauses still there
    assert_eq!(engine.get_stats().queries_executed, 0);
    assert_eq!(engine.get_stats().clause_count, 1); // Clauses still there
}

#[test]
fn test_set_limits() {
    // Tests runtime modification of engine limits.
    
    let mut engine = PrologEngine::new();
    
    // Test setting solution limit
    assert_eq!(engine.max_solutions, 100);  // Default
    engine.set_max_solutions(50);
    assert_eq!(engine.max_solutions, 50);
    assert_eq!(engine.stats.max_solutions, 50);  // Stats should match
    
    // Test setting stack depth limit
    assert_eq!(engine.stats.max_stack_depth, 100);  // Default
    engine.set_max_stack_depth(200);
    assert_eq!(engine.stats.max_stack_depth, 200);
}

#[test]
fn test_engine_edge_cases() {
    // Tests various edge cases to ensure engine robustness.
    
    let mut engine = PrologEngine::new();
    
    // Test with empty clause database
    // Should return no solutions but not error
    let solutions = engine.parse_query("unknown(X).").unwrap();
    assert_eq!(solutions.len(), 0);
    
    // Test with max_solutions = 0
    // Should immediately hit the limit
    engine.set_max_solutions(0);
    engine.parse_and_add("fact(a).").unwrap();
    let result = engine.parse_query("fact(X).");
    assert!(result.is_err()); // Should hit solution limit immediately
    
    // Test load_database with invalid input
    // Should collect errors but not crash
    let errors = engine.load_database("invalid syntax here\nmore invalid");
    assert_eq!(errors.len(), 2);  // Two lines of invalid input
    
    // Test export with empty database
    engine.clear();
    let exported = engine.export_database();
    assert_eq!(exported, "");  // Empty database exports as empty string
    
    // Test parse_term static method
    // This is a convenience function for parsing single terms
    let term = PrologEngine::parse_term("foo(bar, X)").unwrap();
    assert!(matches!(term, Term::Compound(_, _)));
}

#[test]
fn test_circular_reference_handling() {
    // Tests that circular references (infinite loops) are handled safely.
    
    let mut engine = PrologEngine::new();
    
    // Add a circular reference rule: loop(X) :- loop(X)
    engine.parse_and_add("loop(X) :- loop(X).").unwrap();
    
    // Should not cause infinite loop due to stack protection
    let result = engine.parse_query("loop(test).");
    assert!(result.is_err());  // Should error due to stack overflow
}

#[test]
fn test_empty_goal_list() {
    // Tests querying with an empty list of goals.
    // This is an edge case that should succeed trivially.
    
    let mut engine = PrologEngine::new();
    
    // Query with empty goals should succeed immediately
    let solutions = engine.query(vec![]).unwrap();
    assert_eq!(solutions.len(), 1);  // One solution (true)
}

#[test]
fn test_print_solutions() {
    // Tests the solution printing functions.
    // These format solutions for human-readable output.
    
    let engine = PrologEngine::new();
    let mut solutions = Vec::new();
    
    // Create a test solution
    let mut subst = HashMap::new();
    subst.insert("X".to_string(), Term::Atom("test".to_string()));
    solutions.push(subst);
    
    // Should not panic when printing
    engine.print_solutions(&solutions, &["X".to_string()]);
    engine.print_solutions_detailed(&solutions, &["X".to_string()]);
    
    // Test with empty solutions (no solutions found)
    engine.print_solutions(&[], &["X".to_string()]);
    engine.print_solutions_detailed(&[], &["X".to_string()]);
    
    // Test with no variables (query succeeded but no variables to show)
    engine.print_solutions(&solutions, &[]);
    engine.print_solutions_detailed(&solutions, &[]);
}

#[test]
fn test_error_printing() {
    // Tests error printing functions for debugging.
    
    let engine = PrologEngine::new();
    
    // Create a test error
    let error = RuntimeError::DivisionByZero {
        expression: Term::Number(0),
    };
    
    // Should not panic when printing
    engine.print_error(&error);
    
    // Test with boxed error (type-erased error)
    let boxed_error: Box<dyn std::error::Error> = Box::new(error);
    engine.print_boxed_error(&boxed_error);
}

#[test]
fn test_default_trait() {
    // Tests that PrologEngine implements the Default trait correctly.
    // Default::default() should create the same engine as new().
    
    let engine = PrologEngine::default();
    assert_eq!(engine.clauses.len(), 0);
    assert_eq!(engine.max_solutions, 100);
}

#[test]
fn test_database_with_comments() {
    // Tests loading a database with comments and blank lines.
    // Comments start with % and should be ignored.
    
    let mut engine = PrologEngine::new();
    
    let db = "% This is a comment\nparent(tom, bob).\n% Another comment\nparent(bob, ann).\n\n";
    let errors = engine.load_database(db);
    
    assert!(errors.is_empty());  // No errors
    assert_eq!(engine.clauses.len(), 2);  // Only non-comment lines added
}

#[test]
fn test_rename_clause_variables() {
    // Tests the internal variable renaming mechanism.
    // This is crucial for avoiding variable conflicts when
    // the same clause is used multiple times.
    
    let mut engine = PrologEngine::new();
    
    // Create a clause with variables
    let clause = Clause::rule(
        Term::Compound("test".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Variable("Y".to_string())
        ]),
        vec![
            Term::Compound("foo".to_string(), vec![
                Term::Variable("X".to_string()),
                Term::Variable("Z".to_string())
            ])
        ]
    );
    
    // Rename variables
    let renamed = engine.rename_clause_variables(&clause);
    
    // Should have renamed all variables with _G prefix
    // _G stands for "generated" - a Prolog convention
    if let Term::Compound(_, args) = &renamed.head {
        for arg in args {
            if let Term::Variable(var) = arg {
                assert!(var.starts_with("_G"));
            }
        }
    }
    
    // Variable counter should have increased
    assert!(engine.variable_counter > 0);
}

#[test]
fn test_multiple_solutions_with_limits() {
    // Tests that solution limits are enforced when queries
    // would otherwise return many solutions.
    
    let mut engine = PrologEngine::with_limits(2);  // Max 2 solutions
    
    // Add 3 facts
    engine.parse_and_add("choice(1).").unwrap();
    engine.parse_and_add("choice(2).").unwrap();
    engine.parse_and_add("choice(3).").unwrap();
    
    let result = engine.parse_query("choice(X).");
    
    match result {
        Ok(solutions) => {
            assert!(solutions.len() <= 2);  // Should respect limit
        }
        Err(e) => {
            // Error due to solution limit is also acceptable
            let error_msg = format!("{}", e);
            assert!(error_msg.contains("Too many solutions"));
        }
    }
}

#[test]
fn test_query_with_question_mark() {
    // Tests that queries can end with either ? or .
    // Different Prolog systems use different conventions.
    
    let mut engine = PrologEngine::new();
    
    engine.parse_and_add("fact(a).").unwrap();
    
    // Test that query can end with ?
    let result1 = engine.parse_query("fact(a)?");
    assert!(result1.is_ok());
    
    // Test that query can end with .
    let result2 = engine.parse_query("fact(a).");
    assert!(result2.is_ok());
}

#[test]
fn test_stats_mutation() {
    // Tests that mutable access to stats works correctly.
    
    let mut engine = PrologEngine::new();
    
    // Get mutable reference to stats and modify
    let stats = engine.get_stats_mut();
    stats.queries_executed = 100;
    
    // Verify the change persisted
    assert_eq!(engine.get_stats().queries_executed, 100);
}

#[test]
fn test_builtin_vs_user_defined() {
    // Tests distinguishing between built-in and user-defined predicates.
    // The engine needs to know which predicates are built-in (like append/3)
    // versus user-defined to route them correctly.
    
    let mut engine = PrologEngine::new();
    
    // Add a user-defined predicate with same name as builtin (different arity)
    // append/1 is user-defined, append/3 is built-in
    engine.parse_and_add("append(single).").unwrap();
    
    // Should distinguish between append/1 (user) and append/3 (builtin)
    assert!(engine.is_predicate_defined("append", 1)); // User-defined
    assert!(engine.is_predicate_defined("append", 3)); // Built-in
    
    // Find clauses should only find user-defined ones
    let clauses = engine.find_clauses("append", 1);
    assert_eq!(clauses.len(), 1);  // The user-defined one
    
    let clauses = engine.find_clauses("append", 3);
    assert_eq!(clauses.len(), 0); // Built-ins not in clause database
}