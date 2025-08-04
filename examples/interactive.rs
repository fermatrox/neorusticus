// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: interactive.rs
// Creator: Jonas Forsman

//! Interactive REPL for the Neorusticus Prolog engine
//! 
//! This example provides a simple command-line interface for interacting
//! with the Prolog engine, similar to traditional Prolog systems.

use neorusticus::PrologEngine;
use std::io::{self, Write};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Neorusticus Prolog Interactive Shell ===");
    println!("Enter Prolog clauses (ending with .) or queries (ending with ? or .)");
    println!("Type 'help' for commands, 'quit' to exit.\n");
    
    let mut engine = PrologEngine::with_limits(100);
    let stdin = io::stdin();
    
    loop {
        print!("?- ");
        io::stdout().flush()?;
        
        let mut input = String::new();
        stdin.read_line(&mut input)?;
        
        let input = input.trim();
        
        if input.is_empty() {
            continue;
        }
        
        match input {
            "quit" | "exit" | "halt" => {
                println!("Goodbye!");
                break;
            }
            "help" => {
                print_help();
                continue;
            }
            "stats" => {
                println!("{}", engine.get_stats());
                continue;
            }
            "clear" => {
                engine = PrologEngine::with_limits(100);
                println!("Database cleared.");
                continue;
            }
            _ => {}
        }
        
        // Handle multi-line input
        let mut complete_input = input.to_string();
        while !complete_input.ends_with('.') && !complete_input.ends_with('?') {
            print!("   ");
            io::stdout().flush()?;
            
            let mut continuation = String::new();
            stdin.read_line(&mut continuation)?;
            complete_input.push(' ');
            complete_input.push_str(continuation.trim());
        }
        
        if complete_input.ends_with('?') {
            // Query
            let query_input = complete_input.trim_end_matches('?').to_string() + ".";
            handle_query(&mut engine, &query_input);
        } else if complete_input.ends_with('.') {
            // Check if it's a query or a clause
            if looks_like_query(&complete_input) {
                handle_query(&mut engine, &complete_input);
            } else {
                handle_clause(&mut engine, &complete_input);
            }
        } else {
            println!("Error: Input must end with '.' or '?'");
        }
    }
    
    Ok(())
}

fn print_help() {
    println!("Commands:");
    println!("  help    - Show this help message");
    println!("  quit    - Exit the shell");
    println!("  stats   - Show engine statistics");
    println!("  clear   - Clear the database");
    println!();
    println!("Usage:");
    println!("  Facts:     parent(tom, bob).");
    println!("  Rules:     grandparent(X, Z) :- parent(X, Y), parent(Y, Z).");
    println!("  Queries:   parent(tom, X)?   or   parent(tom, X).");
    println!();
    println!("Built-in predicates:");
    println!("  Arithmetic: is/2, =:=/2, =\\=/2, >/2, </2, >=/2, =</2");
    println!("  Unification: =/2, \\=/2");
    println!("  Type checking: var/1, nonvar/1, atom/1, number/1, compound/1");
    println!("  Lists: append/3, member/2, length/2");
    println!("  Control: true/0, fail/0, !/0 (cut)");
}

fn looks_like_query(input: &str) -> bool {
    // Simple heuristic: if it doesn't contain :-, it's probably a query
    // But we need to be more careful - facts like "parent(tom, bob)." should NOT be queries
    
    if input.contains(":-") {
        // Definitely a rule, not a query
        return false;
    }
    
    // Check for common query patterns:
    // - Contains variables in significant positions
    // - Looks like it's asking for information rather than stating a fact
    
    // For now, let's be conservative: assume everything without :- is a fact/clause
    // unless it contains obvious query indicators
    
    // Check if it contains unbound variables (common in queries)
    let has_variables = input.chars()
        .any(|c| c.is_ascii_uppercase() && c != 'A' && c != 'I'); // Avoid common atom starts
        
    // If it has variables and no specific facts (like quoted atoms), might be a query
    // But "parent(tom, bob)" has no variables, so it's clearly a fact
    
    // Better heuristic: only treat as query if it has variables or is asking something
    has_variables && !input.trim_end_matches('.').contains('(') || 
    input.trim().starts_with("?-") ||
    input.contains("=") && has_variables // Unification queries
}

fn handle_clause(engine: &mut PrologEngine, input: &str) {
    println!("Adding clause: {}", input.trim());
    match engine.parse_and_add(input) {
        Ok(()) => println!("Clause added successfully."),
        Err(e) => {
            println!("Parse error: {}", e);
            engine.print_error(&e);
        }
    }
}

fn handle_query(engine: &mut PrologEngine, input: &str) {
    println!("Executing query: {}", input.trim());
    // Extract variable names from the query for display
    let variables = extract_query_variables(input);
    
    match engine.parse_query(input) {
        Ok(solutions) => {
            if solutions.is_empty() {
                println!("false.");
            } else {
                println!("Solutions:");
                engine.print_solutions(&solutions, &variables);
                
                if solutions.len() >= engine.get_stats().max_solutions {
                    println!("(Maximum solutions reached - there may be more)");
                }
            }
        }
        Err(e) => {
            println!("Query error: {}", e);
            engine.print_boxed_error(&e);
        }
    }
}

fn extract_query_variables(input: &str) -> Vec<String> {
    // Simple variable extraction - find uppercase identifiers
    let mut variables = Vec::new();
    let mut chars = input.chars().peekable();
    
    while let Some(ch) = chars.next() {
        if ch.is_ascii_uppercase() || ch == '_' {
            let mut var_name = String::new();
            var_name.push(ch);
            
            while let Some(&next_ch) = chars.peek() {
                if next_ch.is_alphanumeric() || next_ch == '_' {
                    var_name.push(chars.next().unwrap());
                } else {
                    break;
                }
            }
            
            if !variables.contains(&var_name) && var_name != "_" {
                variables.push(var_name);
            }
        }
    }
    
    variables
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_looks_like_query() {
        // These should be treated as queries
        assert!(looks_like_query("parent(tom, X)."));  // Has variable
        assert!(looks_like_query("X is 2 + 3."));      // Has arithmetic
        assert!(looks_like_query("?- parent(tom, bob).")); // Explicit query
        assert!(looks_like_query("X = Y."));           // Unification
        
        // These should be treated as clauses/facts
        assert!(!looks_like_query("parent(tom, bob)."));       // Fact
        assert!(!looks_like_query("parent(X, Y) :- father(X, Y).")); // Rule
        assert!(!looks_like_query("happy(mary)."));            // Fact
        assert!(!looks_like_query("likes(john, pizza)."));     // Fact
    }

    #[test]
    fn test_extract_query_variables() {
        let vars = extract_query_variables("parent(tom, X).");
        assert_eq!(vars, vec!["X"]);
        
        let vars = extract_query_variables("append(A, B, C).");
        assert_eq!(vars, vec!["A", "B", "C"]);
        
        let vars = extract_query_variables("X is Y + Z.");
        assert_eq!(vars, vec!["X", "Y", "Z"]);
        
        let vars = extract_query_variables("parent(tom, bob).");
        assert!(vars.is_empty());
    }
}