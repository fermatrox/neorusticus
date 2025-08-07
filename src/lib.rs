// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: lib.rs
// Creator: Jonas Forsman

//! Neorusticus - A Prolog implementation in Rust
//! 
//! This library provides a complete Prolog interpreter with enhanced error handling,
//! arithmetic operations, list processing, and cut operations.
//!
//! # Quick Start
//!
//! ```rust
//! use neorusticus::parse_term;
//!
//! let term = parse_term("foo(bar, X)").unwrap();
//! println!("Parsed: {}", term);
//! ```
//!
//! # Architecture
//!
//! The library is organized into several modules:
//! - [`ast`] - Abstract syntax tree types
//! - [`lexer`] - Tokenization of Prolog source code
//! - [`parser`] - Parsing tokens into AST
//! - [`unification`] - Unification algorithm
//! - [`error`] - Error types and handling
//! - [`builtins`] - Built-in predicates and functions
//! - [`engine`] - The main Prolog engine for executing queries
//! - [`utils`] - Utility functions for pretty printing, term manipulation, etc.

// Module declarations
// Each module contains a specific aspect of the Prolog implementation
pub mod error;        // Error types and position tracking for detailed error reporting
pub mod lexer;        // Converts raw text into tokens (lexical analysis)
pub mod parser;       // Converts tokens into AST structures (syntactic analysis)
pub mod ast;          // Defines the abstract syntax tree types (Term, Clause)
pub mod unification; // Implements the unification algorithm (pattern matching)
pub mod builtins;    // Built-in predicates like append/3, is/2, etc.
pub mod engine;       // The main execution engine that resolves queries
pub mod utils;        // Helper utilities for formatting, analysis, etc.

// Re-export the main types and functions for easy use
// This allows users to import directly from the crate root
// Instead of: use neorusticus::engine::PrologEngine;
// They can:   use neorusticus::PrologEngine;
pub use engine::{PrologEngine, EngineStats, ExecutionContext};
pub use ast::{Term, Clause};
pub use error::{ParseError, RuntimeError, ParseResult, RuntimeResult};
pub use lexer::{Token, Tokenizer};
pub use parser::Parser;
pub use unification::{Unifier, Substitution};
pub use builtins::BuiltinPredicates;
pub use utils::{PrettyPrinter, TermUtils, ClauseUtils, EngineUtils, DatabaseAnalysis};

/// Convenience function for parsing a single term from a string
/// 
/// This function handles the complete parsing pipeline:
/// 1. Creates a tokenizer to convert the string to tokens
/// 2. Tokenizes the input string
/// 3. Creates a parser with the tokens
/// 4. Parses the tokens into an AST Term
/// 
/// # Example
/// ```
/// use neorusticus::parse_term;
/// 
/// let term = parse_term("foo(bar, X)").unwrap();
/// println!("Parsed: {}", term);
/// ```
/// 
/// # Errors
/// Returns a ParseError if:
/// - The input contains invalid Prolog syntax
/// - The tokenizer encounters invalid characters
/// - The parser cannot construct a valid term
pub fn parse_term(input: &str) -> ParseResult<Term> {
    // Step 1: Create a tokenizer
    // The tokenizer is responsible for breaking the input string into
    // meaningful tokens (atoms, variables, operators, delimiters, etc.)
    // It tracks position information for error reporting
    let mut tokenizer = lexer::Tokenizer::new(input);
    
    // Step 2: Tokenize the input
    // This converts the raw string into a vector of Token enums
    // The ? operator propagates any tokenization errors
    // Tokenization can fail if there are invalid characters,
    // unclosed strings, mismatched delimiters, etc.
    let tokens = tokenizer.tokenize()?;
    
    // Step 3: Create a parser with the tokens
    // The parser takes the flat list of tokens and builds
    // a hierarchical AST structure from them
    let mut parser = parser::Parser::new(tokens);
    
    // Step 4: Parse the tokens into a Term
    // This is the actual parsing - converting tokens into
    // a structured Term that represents the Prolog syntax
    // The parser handles operator precedence, list syntax,
    // compound terms, and all other Prolog constructs
    parser.parse_term()
}

/// Convenience function for creating and running a simple query
/// 
/// This function creates a new engine, adds the given clauses, and executes the query.
/// Useful for quick one-off queries without managing engine state.
/// 
/// # Example
/// ```
/// use neorusticus::quick_query;
/// 
/// let clauses = &[
///     "parent(tom, bob).",
///     "parent(bob, ann).",
///     "grandparent(X, Z) :- parent(X, Y), parent(Y, Z)."
/// ];
/// 
/// let solutions = quick_query(clauses, "grandparent(tom, X).").unwrap();
/// println!("Found {} solutions", solutions.len());
/// ```
/// 
/// # Errors
/// Returns a boxed error if:
/// - Any clause has invalid syntax
/// - The query has invalid syntax
/// - Runtime errors occur during query execution
pub fn quick_query(clauses: &[&str], query: &str) -> Result<Vec<Substitution>, Box<dyn std::error::Error>> {
    // Step 1: Create a new Prolog engine
    // The engine manages the clause database and executes queries
    // It starts with an empty database and default configuration
    let mut engine = PrologEngine::new();
    
    // Step 2: Add all provided clauses to the engine
    // Each clause is a string that needs to be parsed and added
    // to the engine's knowledge base
    for clause in clauses {
        // parse_and_add handles the complete pipeline:
        // 1. Tokenizes the clause string
        // 2. Parses the tokens into a Clause AST
        // 3. Validates the clause is well-formed
        // 4. Adds it to the engine's database
        // The ? operator propagates any errors (parse errors, etc.)
        engine.parse_and_add(clause)?;
    }
    
    // Step 3: Execute the query against the populated database
    // parse_query handles:
    // 1. Tokenizing the query string
    // 2. Parsing it into a list of goals (Terms)
    // 3. Running the unification/resolution algorithm
    // 4. Collecting all possible solutions (variable bindings)
    // The query is resolved using:
    // - Unification to match goals with clause heads
    // - Backtracking to find all solutions
    // - Built-in predicates when applicable
    // The result is a vector of Substitutions, where each
    // Substitution is a HashMap mapping variable names to Terms
    engine.parse_query(query)
}

// Link to the test module
// This includes the test file when compiling in test mode
// The cfg(test) attribute ensures tests are only compiled when running tests
#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;