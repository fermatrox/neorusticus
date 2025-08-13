// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: utils_tests.rs
// Creator: Jonas Forsman

//! Comprehensive tests for the utils module

use super::*;
use std::collections::{HashMap, HashSet};
use crate::ast::{Term, Clause};
use crate::engine::PrologEngine;

// ===== PrettyPrinter Tests =====
// These tests verify that terms and clauses are formatted correctly for display

#[test]
fn test_pretty_printer_format_term() {
    // Test simple atoms
    // Atoms should be displayed as-is without any decoration
    let atom = Term::Atom("hello".to_string());
    assert_eq!(PrettyPrinter::format_term(&atom, 0), "hello");
    
    // Test variables
    // Variables should display their name (uppercase convention)
    let var = Term::Variable("X".to_string());
    assert_eq!(PrettyPrinter::format_term(&var, 0), "X");
    
    // Test numbers
    // Positive numbers should display normally
    let num = Term::Number(42);
    assert_eq!(PrettyPrinter::format_term(&num, 0), "42");
    
    // Test negative numbers
    // Negative numbers should include the minus sign
    let neg = Term::Number(-17);
    assert_eq!(PrettyPrinter::format_term(&neg, 0), "-17");
    
    // Test compound with no args
    // Empty argument list should still show parentheses to distinguish from atom
    // foo() is different from foo in Prolog
    let compound_empty = Term::Compound("foo".to_string(), vec![]);
    assert_eq!(PrettyPrinter::format_term(&compound_empty, 0), "foo()");
    
    // Test compound with single arg
    // Single argument should be inline: foo(bar)
    let compound_single = Term::Compound("foo".to_string(), vec![
        Term::Atom("bar".to_string())
    ]);
    assert_eq!(PrettyPrinter::format_term(&compound_single, 0), "foo(bar)");
    
    // Test compound with multiple args
    // Multiple arguments should be comma-separated: foo(bar, X)
    let compound_multi = Term::Compound("foo".to_string(), vec![
        Term::Atom("bar".to_string()),
        Term::Variable("X".to_string())
    ]);
    assert_eq!(PrettyPrinter::format_term(&compound_multi, 0), "foo(bar, X)");
    
    // Test nested compound
    // Nested structures should format correctly: f(g(1))
    let nested = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![Term::Number(1)])
    ]);
    assert_eq!(PrettyPrinter::format_term(&nested, 0), "f(g(1))");
}

#[test]
fn test_pretty_printer_long_format() {
    // Test that very long terms trigger multi-line formatting
    // When total argument length exceeds 60 chars, formatter should use line breaks
    
    // Create a term with many long arguments to exceed the threshold
    let long_args = vec![
        Term::Atom("very_long_atom_name_that_exceeds_limit".to_string()),
        Term::Atom("another_very_long_atom_name".to_string()),
        Term::Atom("third_long_atom_name".to_string()),
    ];
    let compound = Term::Compound("predicate".to_string(), long_args);
    let formatted = PrettyPrinter::format_term(&compound, 0);
    
    // Verify that line breaks were inserted for readability
    assert!(formatted.contains("\n")); // Should have line breaks
}

#[test]
fn test_pretty_printer_format_clause() {
    // Test formatting of facts (clauses with no body)
    // Facts should end with a period: parent(tom, bob).
    let fact = Clause::fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("tom".to_string()),
        Term::Atom("bob".to_string())
    ]));
    assert_eq!(PrettyPrinter::format_clause(&fact, 0), "parent(tom, bob).");
    
    // Test formatting of rules (clauses with body)
    // Rules should use :- notation and end with period
    let rule = Clause::rule(
        Term::Compound("grandparent".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Variable("Z".to_string())
        ]),
        vec![
            Term::Compound("parent".to_string(), vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string())
            ])
        ]
    );
    let formatted = PrettyPrinter::format_clause(&rule, 0);
    
    // Verify rule format includes the implication arrow and period
    assert!(formatted.contains(":-"));
    assert!(formatted.ends_with("."));
}

#[test]
fn test_pretty_printer_format_substitution() {
    // Test formatting empty substitution
    // Empty substitution should display as {}
    let empty = HashMap::new();
    assert_eq!(PrettyPrinter::format_substitution(&empty), "{}");
    
    // Test formatting single binding
    // Single binding should show variable -> value format
    let mut single = HashMap::new();
    single.insert("X".to_string(), Term::Atom("hello".to_string()));
    assert_eq!(PrettyPrinter::format_substitution(&single), "{X -> hello}");
    
    // Test formatting multiple bindings
    // Multiple bindings should be comma-separated and sorted
    let mut multi = HashMap::new();
    multi.insert("X".to_string(), Term::Number(42));
    multi.insert("Y".to_string(), Term::Atom("world".to_string()));
    let formatted = PrettyPrinter::format_substitution(&multi);
    
    // Both bindings should be present (order is alphabetical)
    assert!(formatted.contains("X -> 42"));
    assert!(formatted.contains("Y -> world"));
}

#[test]
fn test_pretty_printer_format_solutions() {
    // Test formatting when no solutions are found
    // Should display a clear "No solutions" message
    let empty_solutions: Vec<Substitution> = vec![];
    let vars = vec!["X".to_string()];
    assert_eq!(PrettyPrinter::format_solutions(&empty_solutions, &vars), "No solutions.");
    
    // Test formatting solutions with no variables (ground queries)
    // When query has no variables, just report success/failure
    let solution = HashMap::new();
    let solutions = vec![solution];
    let no_vars: Vec<String> = vec![];
    assert_eq!(PrettyPrinter::format_solutions(&solutions, &no_vars), "1 solution(s): true");
    
    // Test formatting solutions with variables
    // Should create a table with columns for each variable
    let mut sol1 = HashMap::new();
    sol1.insert("X".to_string(), Term::Number(1));
    sol1.insert("Y".to_string(), Term::Atom("a".to_string()));
    
    let mut sol2 = HashMap::new();
    sol2.insert("X".to_string(), Term::Number(2));
    sol2.insert("Y".to_string(), Term::Atom("b".to_string()));
    
    let solutions = vec![sol1, sol2];
    let vars = vec!["X".to_string(), "Y".to_string()];
    let formatted = PrettyPrinter::format_solutions(&solutions, &vars);
    
    // Verify table structure includes header, values, and formatting
    assert!(formatted.contains("Found 2 solution(s)"));
    assert!(formatted.contains("X"));  // Column header
    assert!(formatted.contains("Y"));  // Column header
    assert!(formatted.contains("1"));  // First solution X value
    assert!(formatted.contains("2"));  // Second solution X value
    assert!(formatted.contains("a"));  // First solution Y value
    assert!(formatted.contains("b"));  // Second solution Y value
}

// ===== TermUtils Tests =====
// These tests verify term manipulation and analysis functions

#[test]
fn test_term_utils_get_all_variables() {
    // Test that atoms contain no variables
    let atom = Term::Atom("hello".to_string());
    assert!(TermUtils::get_all_variables(&atom).is_empty());
    
    // Test single variable extraction
    let var = Term::Variable("X".to_string());
    let vars = TermUtils::get_all_variables(&var);
    assert_eq!(vars.len(), 1);
    assert!(vars.contains("X"));
    
    // Test extraction from compound with multiple variables
    // Should collect unique variables (no duplicates)
    let compound = Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Variable("Y".to_string()),
        Term::Variable("X".to_string()), // Duplicate - should only count once
    ]);
    let vars = TermUtils::get_all_variables(&compound);
    assert_eq!(vars.len(), 2); // X and Y (no duplicates)
    assert!(vars.contains("X"));
    assert!(vars.contains("Y"));
    
    // Test extraction from nested compound structures
    // Should find variables at any depth
    let nested = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![
            Term::Variable("Z".to_string())
        ])
    ]);
    let vars = TermUtils::get_all_variables(&nested);
    assert_eq!(vars.len(), 1);
    assert!(vars.contains("Z"));
}

#[test]
fn test_term_utils_depth() {
    // Test depth calculation for simple terms
    // Atoms, variables, and numbers all have depth 1
    assert_eq!(TermUtils::term_depth(&Term::Atom("a".to_string())), 1);
    assert_eq!(TermUtils::term_depth(&Term::Variable("X".to_string())), 1);
    assert_eq!(TermUtils::term_depth(&Term::Number(42)), 1);
    
    // Test compound with no args still has depth 1
    let empty = Term::Compound("f".to_string(), vec![]);
    assert_eq!(TermUtils::term_depth(&empty), 1);
    
    // Test compound with args at same level
    // f(a, b) has depth 2: the compound plus its arguments
    let flat = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Atom("b".to_string())
    ]);
    assert_eq!(TermUtils::term_depth(&flat), 2);
    
    // Test deeply nested compound
    // f(g(h(a))) has depth 4: each nesting level adds 1
    let nested = Term::Compound("f".to_string(), vec![
        Term::Compound("g".to_string(), vec![
            Term::Compound("h".to_string(), vec![
                Term::Atom("a".to_string())
            ])
        ])
    ]);
    assert_eq!(TermUtils::term_depth(&nested), 4);
}

#[test]
fn test_term_utils_size() {
    // Test size calculation for simple terms
    // Each simple term counts as 1
    assert_eq!(TermUtils::term_size(&Term::Atom("a".to_string())), 1);
    assert_eq!(TermUtils::term_size(&Term::Variable("X".to_string())), 1);
    assert_eq!(TermUtils::term_size(&Term::Number(42)), 1);
    
    // Test size of compound term
    // Size includes the compound itself plus all subterms
    let compound = Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Compound("bar".to_string(), vec![
            Term::Variable("Y".to_string()),
            Term::Number(42)
        ])
    ]);
    // Structure: foo + X + bar + Y + 42 = 5 total terms
    assert_eq!(TermUtils::term_size(&compound), 5);
}

#[test]
fn test_term_utils_contains_variable() {
    // Test variable detection in compound terms
    let term = Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Atom("a".to_string())
    ]);
    
    // Should find X but not Y
    assert!(TermUtils::contains_variable(&term, "X"));
    assert!(!TermUtils::contains_variable(&term, "Y"));
    
    // Atoms don't contain variables
    assert!(!TermUtils::contains_variable(&Term::Atom("a".to_string()), "X"));
}

#[test]
fn test_term_utils_replace_variable() {
    // Test replacing all occurrences of a variable with another term
    let term = Term::Compound("foo".to_string(), vec![
        Term::Variable("X".to_string()),
        Term::Variable("Y".to_string()),
        Term::Variable("X".to_string()),  // X appears twice
    ]);
    
    let replacement = Term::Atom("replaced".to_string());
    let result = TermUtils::replace_variable(&term, "X", &replacement);
    
    // Verify that both occurrences of X were replaced, but Y remains
    match result {
        Term::Compound(_, args) => {
            assert_eq!(args[0], Term::Atom("replaced".to_string()));
            assert_eq!(args[1], Term::Variable("Y".to_string()));  // Y unchanged
            assert_eq!(args[2], Term::Atom("replaced".to_string()));
        }
        _ => panic!("Expected compound term"),
    }
}

#[test]
fn test_term_utils_is_ground() {
    // Test ground term detection (terms with no variables)
    
    // Atoms and numbers are always ground
    assert!(TermUtils::is_ground(&Term::Atom("a".to_string())));
    assert!(TermUtils::is_ground(&Term::Number(42)));
    
    // Compound with only ground terms is ground
    let ground_compound = Term::Compound("f".to_string(), vec![
        Term::Atom("a".to_string()),
        Term::Number(42)
    ]);
    assert!(TermUtils::is_ground(&ground_compound));
    
    // Variables are never ground
    assert!(!TermUtils::is_ground(&Term::Variable("X".to_string())));
    
    // Compound containing a variable is not ground
    let non_ground = Term::Compound("f".to_string(), vec![
        Term::Variable("X".to_string())
    ]);
    assert!(!TermUtils::is_ground(&non_ground));
}

#[test]
fn test_term_utils_list_conversion() {
    // Test conversion between Prolog list representation and Rust Vec
    
    // Test empty list conversion
    // [] in Prolog becomes empty Vec in Rust
    let empty_vec: Vec<Term> = vec![];
    let empty_list = TermUtils::vec_to_list(empty_vec.clone());
    assert_eq!(empty_list, Term::Atom("[]".to_string()));
    assert_eq!(TermUtils::list_to_vec(&empty_list), Some(empty_vec));
    
    // Test regular list conversion
    // [1,2,3] in Prolog is .(1, .(2, .(3, [])))
    let vec = vec![
        Term::Number(1),
        Term::Number(2),
        Term::Number(3)
    ];
    let list = TermUtils::vec_to_list(vec.clone());
    
    // Should be able to convert back to the same Vec
    assert_eq!(TermUtils::list_to_vec(&list), Some(vec));
    
    // Test invalid list structure detection
    // A regular atom is not a list
    let not_a_list = Term::Atom("not_a_list".to_string());
    assert_eq!(TermUtils::list_to_vec(&not_a_list), None);
    
    // Test improper list detection (doesn't end with [])
    // [1|X] is improper - has variable tail instead of []
    let improper = Term::Compound(".".to_string(), vec![
        Term::Number(1),
        Term::Variable("X".to_string())
    ]);
    assert_eq!(TermUtils::list_to_vec(&improper), None);
}

#[test]
fn test_term_utils_fresh_variable() {
    // Test generation of unique variable names
    
    // Create a set of existing variables
    let mut existing = HashSet::new();
    existing.insert("X".to_string());
    existing.insert("Y".to_string());
    existing.insert("X1".to_string());
    
    // Should generate X2 since X, X1 already exist
    let fresh = TermUtils::fresh_variable(&existing, "X");
    assert_eq!(fresh, "X2");
    
    // Should generate Z since it doesn't exist at all
    let fresh_new = TermUtils::fresh_variable(&existing, "Z");
    assert_eq!(fresh_new, "Z");
    
    // Test with empty set - should use base name as-is
    let empty = HashSet::new();
    let fresh_empty = TermUtils::fresh_variable(&empty, "Var");
    assert_eq!(fresh_empty, "Var");
}

// ===== ClauseUtils Tests =====
// These tests verify clause analysis and manipulation functions

#[test]
fn test_clause_utils_group_by_predicate() {
    // Test grouping clauses by their predicate (functor/arity)
    
    // Create clauses for different predicates
    let clause1 = Clause::fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("tom".to_string()),
        Term::Atom("bob".to_string())
    ]));
    
    let clause2 = Clause::fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("bob".to_string()),
        Term::Atom("ann".to_string())
    ]));
    
    let clause3 = Clause::fact(Term::Compound("likes".to_string(), vec![
        Term::Atom("mary".to_string()),
        Term::Atom("wine".to_string())
    ]));
    
    let clauses = vec![clause1, clause2, clause3];
    let groups = ClauseUtils::group_by_predicate(&clauses);
    
    // Should have 2 groups: parent/2 and likes/2
    assert_eq!(groups.len(), 2);
    
    // parent/2 should have 2 clauses
    assert_eq!(groups.get("parent/2").map(|v| v.len()), Some(2));
    
    // likes/2 should have 1 clause
    assert_eq!(groups.get("likes/2").map(|v| v.len()), Some(1));
}

#[test]
fn test_clause_utils_find_dependencies() {
    // Test finding predicates that depend on another predicate
    
    // Create a rule that uses parent/2 in its body
    let clause1 = Clause::rule(
        Term::Compound("grandparent".to_string(), vec![
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
    
    // Create a fact for parent/2
    let clause2 = Clause::fact(Term::Compound("parent".to_string(), vec![
        Term::Atom("tom".to_string()),
        Term::Atom("bob".to_string())
    ]));
    
    let clauses = vec![clause1, clause2];
    
    // Find what depends on parent/2
    let deps = ClauseUtils::find_dependencies(&clauses, "parent", 2);
    
    // grandparent/2 depends on parent/2
    assert_eq!(deps.len(), 1);
    assert!(deps.contains(&"grandparent/2".to_string()));
}

#[test]
fn test_clause_utils_find_recursive_predicates() {
    // Test detection of recursive predicates (predicates that call themselves)
    
    // Non-recursive clause - simple fact
    let non_recursive = Clause::fact(Term::Compound("fact".to_string(), vec![
        Term::Atom("a".to_string())
    ]));
    
    // Recursive clause - ancestor calls itself
    let recursive = Clause::rule(
        Term::Compound("ancestor".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Variable("Z".to_string())
        ]),
        vec![
            Term::Compound("parent".to_string(), vec![
                Term::Variable("X".to_string()),
                Term::Variable("Y".to_string())
            ]),
            Term::Compound("ancestor".to_string(), vec![  // Recursive call
                Term::Variable("Y".to_string()),
                Term::Variable("Z".to_string())
            ])
        ]
    );
    
    let clauses = vec![non_recursive, recursive];
    let recursive_preds = ClauseUtils::find_recursive_predicates(&clauses);
    
    // Should find ancestor/2 as recursive
    assert_eq!(recursive_preds.len(), 1);
    assert!(recursive_preds.contains(&"ancestor/2".to_string()));
}

#[test]
fn test_clause_utils_validate_clauses() {
    // Test validation of clause well-formedness
    
    // Valid clause - properly formed fact
    let valid = Clause::fact(Term::Compound("fact".to_string(), vec![
        Term::Atom("a".to_string())
    ]));
    
    // Invalid: head is a variable (not allowed in Prolog)
    let invalid_head = Clause::fact(Term::Variable("X".to_string()));
    
    // Invalid: singleton variable (Y appears only once - likely a typo)
    let singleton = Clause::rule(
        Term::Compound("pred".to_string(), vec![
            Term::Variable("X".to_string())
        ]),
        vec![
            Term::Compound("other".to_string(), vec![
                Term::Variable("Y".to_string()) // Y appears only here
            ])
        ]
    );
    
    let clauses = vec![valid, invalid_head, singleton];
    let errors = ClauseUtils::validate_clauses(&clauses);
    
    // Should detect at least two errors
    assert!(errors.len() >= 2);
    
    // Should detect variable as head
    assert!(errors.iter().any(|e| e.contains("Head cannot be a variable")));
    
    // Should detect singleton variable
    assert!(errors.iter().any(|e| e.contains("Singleton variable")));
}

#[test]
fn test_clause_utils_with_underscore_variables() {
    // Test that underscore-prefixed variables don't trigger singleton warnings
    // In Prolog, _Variable is intentionally singleton (don't-care variable)
    
    let clause = Clause::rule(
        Term::Compound("pred".to_string(), vec![
            Term::Variable("X".to_string())
        ]),
        vec![
            Term::Compound("other".to_string(), vec![
                Term::Variable("_Temp".to_string()) // Underscore prefix - OK to be singleton
            ])
        ]
    );
    
    let clauses = vec![clause];
    let errors = ClauseUtils::validate_clauses(&clauses);
    
    // Should not report error for _Temp (underscore convention)
    assert!(!errors.iter().any(|e| e.contains("_Temp")));
}

// ===== EngineUtils Tests =====
// These tests verify engine helper functions

#[test]
fn test_engine_utils_load_program() {
    // Test loading a multi-line Prolog program
    
    let mut engine = PrologEngine::new();
    
    // Valid program with multiple clauses
    let valid_program = "parent(tom, bob).\nparent(bob, ann).";
    let result = EngineUtils::load_program(&mut engine, valid_program);
    
    // Should load successfully
    assert!(result.is_ok());
    
    // Should have added 2 clauses
    assert_eq!(engine.get_clauses().len(), 2);
    
    // Test program with comments and empty lines
    // Comments (%) and blank lines should be ignored
    let mut engine2 = PrologEngine::new();
    let program_with_comments = "% Comment\nparent(tom, bob).\n\nparent(bob, ann).\n% Another comment";
    let result = EngineUtils::load_program(&mut engine2, program_with_comments);
    
    // Should still load 2 clauses (comments ignored)
    assert!(result.is_ok());
    assert_eq!(engine2.get_clauses().len(), 2);
    
    // Test invalid program with syntax error
    let mut engine3 = PrologEngine::new();
    let invalid_program = "parent(tom, bob\nmissing_closing_paren";
    let result = EngineUtils::load_program(&mut engine3, invalid_program);
    
    // Should report error with line number
    assert!(result.is_err());
    if let Err(errors) = result {
        assert!(!errors.is_empty());
    }
}

#[test]
fn test_engine_utils_batch_query() {
    // Test running multiple queries in batch
    
    let mut engine = PrologEngine::new();
    
    // Add some facts to query against
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    
    // Define batch of queries to test
    // IMPORTANT: Queries must end with ? according to our rules
    let queries = vec![
        "parent(tom, bob)?",  // Should succeed (fact exists)
        "parent(tom, ann)?",  // Should fail (no such fact)
        "parent(X, bob)?",    // Should find X = tom
    ];
    
    let results = EngineUtils::batch_query(&mut engine, &queries);
    
    // Should have results for all 3 queries
    assert_eq!(results.len(), 3);
    
    // First query should succeed with at least one solution
    assert!(results[0].1.is_ok());
    if let Ok(solutions) = &results[0].1 {
        assert!(!solutions.is_empty());
    }
    
    // Second query should succeed but with no solutions
    assert!(results[1].1.is_ok());
    if let Ok(solutions) = &results[1].1 {
        assert!(solutions.is_empty());
    }
    
    // Third query should find X = tom
    assert!(results[2].1.is_ok());
    if let Ok(solutions) = &results[2].1 {
        assert!(!solutions.is_empty());
        // Solution should bind X to tom
    }
}

#[test]
fn test_engine_utils_analyze_database() {
    // Test database analysis and statistics generation
    
    let mut engine = PrologEngine::new();
    
    // Add various types of clauses for analysis
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    engine.parse_and_add("parent(ann, joe).").unwrap();
    engine.parse_and_add("likes(mary, wine).").unwrap();
    
    // Add recursive predicate
    engine.parse_and_add("ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).").unwrap();
    engine.parse_and_add("ancestor(X, Y) :- parent(X, Y).").unwrap();
    
    let analysis = EngineUtils::analyze_database(&engine);
    
    // Verify statistics are correct
    assert_eq!(analysis.total_clauses, 6);
    assert_eq!(analysis.total_predicates, 3); // parent/2, likes/2, ancestor/2
    
    // Should detect ancestor/2 as recursive
    assert_eq!(analysis.recursive_predicates.len(), 1);
    assert!(analysis.recursive_predicates.contains(&"ancestor/2".to_string()));
    
    // Check largest predicate (parent/2 has most clauses)
    assert!(analysis.largest_predicate.is_some());
    if let Some((name, count)) = analysis.largest_predicate {
        assert_eq!(name, "parent/2");
        assert_eq!(count, 3);
    }
}

#[test]
fn test_engine_utils_extract_query_variables() {
    // Test extraction of variable names from query strings
    
    // Test simple query with two variables
    let vars = EngineUtils::extract_query_variables("parent(X, Y)");
    assert_eq!(vars.len(), 2);
    assert!(vars.contains(&"X".to_string()));
    assert!(vars.contains(&"Y".to_string()));
    
    // Test query with repeated variables (should count only once)
    let vars = EngineUtils::extract_query_variables("foo(X, X, Y)");
    assert_eq!(vars.len(), 2); // X appears twice but counted once
    
    // Test query with underscore variables
    // _ is anonymous and ignored, _Temp is a named underscore variable
    let vars = EngineUtils::extract_query_variables("foo(_, X, _Temp)");
    assert_eq!(vars.len(), 2); // _ is ignored, _Temp is included
    assert!(vars.contains(&"X".to_string()));
    assert!(vars.contains(&"_Temp".to_string()));
    
    // Test query with no variables (ground query)
    let vars = EngineUtils::extract_query_variables("parent(tom, bob)");
    assert!(vars.is_empty());
    
    // Test complex query with alphanumeric variable names
    let vars = EngineUtils::extract_query_variables("parent(X, Y), ancestor(Y, Z123)");
    assert_eq!(vars.len(), 3);
    assert!(vars.contains(&"X".to_string()));
    assert!(vars.contains(&"Y".to_string()));
    assert!(vars.contains(&"Z123".to_string()));  // Variables can contain numbers
}

// ===== DatabaseAnalysis Tests =====
// These tests verify the database analysis structure and display

#[test]
fn test_database_analysis_display() {
    // Test formatting of database analysis results
    
    let analysis = DatabaseAnalysis {
        total_clauses: 10,
        total_predicates: 3,
        recursive_predicates: vec!["ancestor/2".to_string()],
        largest_predicate: Some(("parent/2".to_string(), 5)),
        average_clause_size: 3.5,
        predicate_distribution: vec![
            ("parent/2".to_string(), 5),
            ("likes/2".to_string(), 3),
            ("ancestor/2".to_string(), 2),
        ],
    };
    
    let display = format!("{}", analysis);
    
    // Verify all statistics are included in the display
    assert!(display.contains("Total clauses: 10"));
    assert!(display.contains("Total predicates: 3"));
    assert!(display.contains("Average clause size: 3.5"));
    assert!(display.contains("Largest predicate: parent/2 (5 clauses)"));
    assert!(display.contains("Recursive predicates: ancestor/2"));
    assert!(display.contains("parent/2: 5 clauses"));
}

#[test]
fn test_database_analysis_empty() {
    // Test display of empty database analysis
    
    let analysis = DatabaseAnalysis {
        total_clauses: 0,
        total_predicates: 0,
        recursive_predicates: vec![],
        largest_predicate: None,
        average_clause_size: 0.0,
        predicate_distribution: vec![],
    };
    
    let display = format!("{}", analysis);
    
    // Should show zeros but not missing sections
    assert!(display.contains("Total clauses: 0"));
    assert!(display.contains("Total predicates: 0"));
    
    // These should not appear when empty/None
    assert!(!display.contains("Largest predicate:")); // None
    assert!(!display.contains("Recursive predicates:")); // Empty
}

// ===== Edge Case Tests =====
// These tests verify behavior with unusual or boundary inputs

#[test]
fn test_edge_case_empty_inputs() {
    // Test all functions with empty inputs
    
    // Empty term collections - no variables to find
    assert!(TermUtils::get_all_variables(&Term::Atom("a".to_string())).is_empty());
    
    // Empty clause list - nothing to group or analyze
    let empty_clauses: Vec<Clause> = vec![];
    assert!(ClauseUtils::group_by_predicate(&empty_clauses).is_empty());
    assert!(ClauseUtils::find_recursive_predicates(&empty_clauses).is_empty());
    assert!(ClauseUtils::validate_clauses(&empty_clauses).is_empty());
    
    // Empty substitution - should format as {}
    let empty_subst = HashMap::new();
    assert_eq!(PrettyPrinter::format_substitution(&empty_subst), "{}");
    
    // Empty variable set for fresh variable generation
    let empty_vars = HashSet::new();
    assert_eq!(TermUtils::fresh_variable(&empty_vars, "X"), "X");
}

#[test]
fn test_edge_case_circular_references() {
    // Test handling of circular/recursive structures
    // Note: We can't create actual circular references in our AST,
    // but we can test functions handle recursive predicates properly
    
    // Create a directly recursive clause (loop calls loop)
    let recursive_clause = Clause::rule(
        Term::Compound("loop".to_string(), vec![Term::Variable("X".to_string())]),
        vec![Term::Compound("loop".to_string(), vec![Term::Variable("X".to_string())])]
    );
    
    let clauses = vec![recursive_clause];
    
    // Should correctly identify as recursive
    let recursive_preds = ClauseUtils::find_recursive_predicates(&clauses);
    assert!(recursive_preds.contains(&"loop/1".to_string()));
}

#[test]
fn test_edge_case_very_deep_nesting() {
    // Test handling of extremely deep term nesting
    // This tests stack safety and performance with deep recursion
    
    // Create a term nested 100 levels deep
    let mut term = Term::Atom("base".to_string());
    for i in 0..100 {
        term = Term::Compound(format!("f{}", i), vec![term]);
    }
    
    // Should handle deep nesting without stack overflow
    assert_eq!(TermUtils::term_depth(&term), 101);  // 100 compounds + 1 atom
    assert_eq!(TermUtils::term_size(&term), 101);   // Total of 101 terms
    assert!(TermUtils::is_ground(&term));           // No variables, so ground
}

#[test]
fn test_edge_case_large_collections() {
    // Test performance with large collections
    
    // Test fresh variable generation with many existing variables
    let mut large_set = HashSet::new();
    
    // Add base name and 1000 numbered variants
    large_set.insert("Var".to_string());
    for i in 0..1000 {
        large_set.insert(format!("Var{}", i));
    }
    
    // Should still find the next available name efficiently
    let fresh = TermUtils::fresh_variable(&large_set, "Var");
    assert_eq!(fresh, "Var1000");
    
    // Test grouping with many clauses
    let mut many_clauses = Vec::new();
    for i in 0..100 {
        many_clauses.push(Clause::fact(Term::Compound(
            format!("pred{}", i),
            vec![Term::Number(i as i64)]
        )));
    }
    
    // Should create 100 groups (one per predicate)
    let groups = ClauseUtils::group_by_predicate(&many_clauses);
    assert_eq!(groups.len(), 100);
}

#[test]
fn test_edge_case_special_characters_in_atoms() {
    // Test formatting with atoms containing special characters
    
    // Atoms can contain various characters in Prolog
    let special = Term::Atom("atom-with-special_chars!".to_string());
    assert_eq!(PrettyPrinter::format_term(&special, 0), "atom-with-special_chars!");
    
    // Test empty string atom (unusual but valid)
    let empty = Term::Atom("".to_string());
    assert_eq!(PrettyPrinter::format_term(&empty, 0), "");
}

#[test]
fn test_edge_case_boundary_numbers() {
    // Test with i64 boundary values
    
    // Maximum i64 value
    let max = Term::Number(i64::MAX);
    let min = Term::Number(i64::MIN);
    
    // Should format correctly without overflow
    assert_eq!(PrettyPrinter::format_term(&max, 0), i64::MAX.to_string());
    assert_eq!(PrettyPrinter::format_term(&min, 0), i64::MIN.to_string());
}

#[test]
fn test_replace_variable_with_self_reference() {
    // Test replacing a variable with a term containing that same variable
    // This creates a kind of expansion but not infinite recursion
    
    let term = Term::Variable("X".to_string());
    let replacement = Term::Compound("f".to_string(), vec![
        Term::Variable("X".to_string())  // Contains X
    ]);
    
    // Replace X with f(X) - creates f(X) where X was
    let result = TermUtils::replace_variable(&term, "X", &replacement);
    match result {
        Term::Compound(functor, args) => {
            assert_eq!(functor, "f");
            // The X inside remains as-is (no infinite recursion)
            assert_eq!(args[0], Term::Variable("X".to_string()));
        }
        _ => panic!("Expected compound"),
    }
}

#[test]
fn test_validate_clauses_with_head_as_number() {
    // Test validation with invalid head type (number)
    
    // Numbers cannot be clause heads in Prolog
    let invalid = Clause::fact(Term::Number(42));
    let clauses = vec![invalid];
    let errors = ClauseUtils::validate_clauses(&clauses);
    
    // Should detect and report the error
    assert!(!errors.is_empty());
    assert!(errors[0].contains("Head cannot be a number"));
}

#[test]
fn test_list_operations_with_nested_lists() {
    // Test list conversion with lists containing other lists
    // Prolog supports nested list structures like [[1,2], 3, [4,5]]
    
    // Create a list containing numbers and another list
    let nested_list = vec![
        Term::Number(1),
        TermUtils::vec_to_list(vec![Term::Number(2), Term::Number(3)]),  // Nested list
        Term::Number(4)
    ];
    
    // Convert to Prolog list and back
    let prolog_list = TermUtils::vec_to_list(nested_list.clone());
    let back = TermUtils::list_to_vec(&prolog_list);
    
    // Should preserve the nested structure
    assert_eq!(back, Some(nested_list));
}