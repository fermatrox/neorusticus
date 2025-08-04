// lib.rs
//
// TODO: Add lib.rs content from restructure plan

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

pub mod error;
pub mod lexer;
pub mod parser;
pub mod ast;
pub mod unification;
pub mod builtins;
pub mod engine;
pub mod utils;        // Uncommented

// Re-export the main types and functions for easy use
pub use engine::{PrologEngine, EngineStats, ExecutionContext};
pub use ast::{Term, Clause};
pub use error::{ParseError, RuntimeError, ParseResult, RuntimeResult};
pub use lexer::{Token, Tokenizer};
pub use parser::Parser;
pub use unification::{Unifier, Substitution};
pub use builtins::BuiltinPredicates;
pub use utils::{PrettyPrinter, TermUtils, ClauseUtils, EngineUtils, DatabaseAnalysis}; // Added

/// Convenience function for parsing a single term from a string
/// 
/// # Example
/// ```
/// use neorusticus::parse_term;
/// 
/// let term = parse_term("foo(bar, X)").unwrap();
/// println!("Parsed: {}", term);
/// ```
pub fn parse_term(input: &str) -> ParseResult<Term> {
    let mut tokenizer = lexer::Tokenizer::new(input);
    let tokens = tokenizer.tokenize()?;
    let mut parser = parser::Parser::new(tokens);
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
pub fn quick_query(clauses: &[&str], query: &str) -> Result<Vec<Substitution>, Box<dyn std::error::Error>> {
    let mut engine = PrologEngine::new();
    
    for clause in clauses {
        engine.parse_and_add(clause)?;
    }
    
    engine.parse_query(query)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_term() {
        let term = parse_term("foo(bar, X)").unwrap();
        match term {
            Term::Compound(functor, args) => {
                assert_eq!(functor, "foo");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_quick_query() {
        let clauses = &["parent(tom, bob).", "parent(bob, ann)."];
        let solutions = quick_query(clauses, "parent(tom, X).").unwrap();
        assert_eq!(solutions.len(), 1);
    }
}