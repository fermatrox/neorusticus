// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: utils.rs
// Creator: Jonas Forsman

//! Utility functions for the Neorusticus Prolog engine
//! 
//! This module provides helpful utility functions for working with Prolog terms,
//! clauses, and engine operations. It includes term manipulation, pretty printing,
//! validation, and convenience functions for common operations.

use std::collections::{HashMap, HashSet};
use std::fmt;
use crate::ast::{Term, Clause};
use crate::unification::Substitution;
use crate::engine::PrologEngine;

/// Pretty printing utilities for Prolog terms and structures
pub struct PrettyPrinter;

impl PrettyPrinter {
    /// Format a term with proper indentation and line breaks
    /// 
    /// This function recursively formats Prolog terms into human-readable strings.
    /// It handles different term types (atoms, variables, numbers, compounds) and
    /// applies intelligent formatting based on term complexity and length.
    pub fn format_term(term: &Term, indent: usize) -> String {
        // Create indentation string based on the current nesting level
        let spaces = " ".repeat(indent);
        
        match term {
            // Atoms are simply their string representation
            Term::Atom(name) => name.clone(),
            
            // Variables are their name (e.g., "X", "Y", "_temp")
            Term::Variable(name) => name.clone(),
            
            // Numbers are converted to string representation
            Term::Number(n) => n.to_string(),
            
            // Compound terms require more complex formatting
            Term::Compound(functor, args) => {
                if args.is_empty() {
                    // Empty argument list: foo()
                    // Always show parentheses to distinguish from atom
                    format!("{}()", functor)
                } else if args.len() == 1 {
                    // Single argument: format inline
                    // Example: foo(bar) or parent(tom)
                    format!("{}({})", functor, Self::format_term(&args[0], 0))
                } else {
                    // Multiple arguments: decide between single-line and multi-line format
                    
                    // First, format all arguments
                    let formatted_args: Vec<String> = args.iter()
                        .map(|arg| Self::format_term(arg, indent + 2))
                        .collect();
                    
                    // Calculate total length of all arguments combined
                    // If under 60 chars, use single-line format for readability
                    if formatted_args.iter().map(|s| s.len()).sum::<usize>() < 60 {
                        // Short format - single line: foo(bar, baz, qux)
                        format!("{}({})", functor, formatted_args.join(", "))
                    } else {
                        // Long format - multiple lines for better readability
                        // Example:
                        // foo(
                        //   very_long_argument_1,
                        //   very_long_argument_2,
                        //   very_long_argument_3
                        // )
                        format!("{}(\n{}{}\n{})", 
                               functor,
                               " ".repeat(indent + 2),  // Indentation for first arg
                               formatted_args.join(&format!(",\n{}", " ".repeat(indent + 2))),
                               spaces)  // Closing paren at original indent level
                    }
                }
            }
        }
    }
    
    /// Format a clause with proper indentation
    /// 
    /// Formats Prolog clauses (facts and rules) into standard notation.
    /// Facts are formatted as "head." and rules as "head :- body."
    pub fn format_clause(clause: &Clause, indent: usize) -> String {
        // Format the head of the clause (the conclusion part)
        let head_str = Self::format_term(&clause.head, indent);
        
        if clause.body.is_empty() {
            // Fact: just head followed by period
            // Example: parent(tom, bob).
            format!("{}.", head_str)
        } else {
            // Rule: head :- body1, body2, ..., bodyN.
            
            // Format each goal in the body
            let body_strs: Vec<String> = clause.body.iter()
                .map(|goal| Self::format_term(goal, indent + 4))
                .collect();
            
            // Decide between single-line and multi-line format based on length
            if body_strs.iter().map(|s| s.len()).sum::<usize>() < 60 {
                // Short format on single line
                // Example: grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
                format!("{} :- {}.", head_str, body_strs.join(", "))
            } else {
                // Long format with line breaks for readability
                // Example:
                // complex_rule(X, Y, Z) :-
                //     first_condition(X),
                //     second_condition(Y),
                //     third_condition(Z).
                let spaces = " ".repeat(indent + 4);
                format!("{} :-\n{}{}.", 
                       head_str,
                       spaces,
                       body_strs.join(&format!(",\n{}", spaces)))
            }
        }
    }
    
    /// Format a substitution in a readable way
    /// 
    /// Converts a substitution map into a string representation showing
    /// all variable bindings in the format: {X -> value1, Y -> value2}
    pub fn format_substitution(subst: &Substitution) -> String {
        if subst.is_empty() {
            // Empty substitution represented as {}
            "{}".to_string()
        } else {
            // Convert each binding to "var -> term" format
            let mut bindings: Vec<String> = subst.iter()
                .map(|(var, term)| format!("{} -> {}", var, Self::format_term(term, 0)))
                .collect();
            
            // Sort alphabetically for consistent, predictable output
            // This makes testing easier and output more readable
            bindings.sort();
            
            // Join all bindings with commas and wrap in braces
            format!("{{{}}}", bindings.join(", "))
        }
    }
    
    /// Format multiple solutions in a table-like format
    /// 
    /// Creates a nicely formatted table showing all solutions to a query.
    /// Each row represents one solution, with columns for each variable.
    pub fn format_solutions(solutions: &[Substitution], variables: &[String]) -> String {
        // Handle edge case: no solutions found
        if solutions.is_empty() {
            return "No solutions.".to_string();
        }
        
        // Handle edge case: query with no variables (e.g., "parent(tom, bob)?")
        if variables.is_empty() {
            // Just report success/failure
            return format!("{} solution(s): true", solutions.len());
        }
        
        let mut result = String::new();
        result.push_str(&format!("Found {} solution(s):\n", solutions.len()));
        
        // Calculate column widths for proper alignment
        // Start with variable name lengths as minimum widths
        let mut col_widths: HashMap<String, usize> = HashMap::new();
        for var in variables {
            col_widths.insert(var.clone(), var.len());
        }
        
        // Expand column widths based on actual values in solutions
        for solution in solutions {
            for var in variables {
                if let Some(term) = solution.get(var) {
                    // Format the term and check its length
                    let term_str = Self::format_term(term, 0);
                    let current_width = col_widths.get(var).unwrap_or(&0);
                    
                    // Update width if this value is wider
                    if term_str.len() > *current_width {
                        col_widths.insert(var.clone(), term_str.len());
                    }
                }
            }
        }
        
        // Build the header row with variable names
        for (i, var) in variables.iter().enumerate() {
            if i > 0 { 
                result.push_str(" | ");  // Column separator
            }
            let width = col_widths.get(var).copied().unwrap_or(var.len());
            // Pad variable name to column width
            result.push_str(&format!("{:width$}", var, width = width));
        }
        result.push('\n');
        
        // Build separator line (e.g., "-----+-----+-----")
        for (i, var) in variables.iter().enumerate() {
            if i > 0 { 
                result.push_str("-+-");  // Separator between columns
            }
            let width = col_widths.get(var).copied().unwrap_or(var.len());
            result.push_str(&"-".repeat(width));
        }
        result.push('\n');
        
        // Build solution rows
        for solution in solutions {
            for (i, var) in variables.iter().enumerate() {
                if i > 0 { 
                    result.push_str(" | ");  // Column separator
                }
                let width = col_widths.get(var).copied().unwrap_or(var.len());
                
                if let Some(term) = solution.get(var) {
                    // Variable has a binding in this solution
                    let term_str = Self::format_term(term, 0);
                    result.push_str(&format!("{:width$}", term_str, width = width));
                } else {
                    // Variable is unbound in this solution, show underscore
                    result.push_str(&format!("{:width$}", "_", width = width));
                }
            }
            result.push('\n');
        }
        
        result
    }
}

/// Term manipulation utilities
pub struct TermUtils;

impl TermUtils {
    /// Get all variables in a term (including nested ones)
    /// 
    /// Collects all unique variable names that appear anywhere in the term.
    /// This includes variables nested inside compound terms.
    pub fn get_all_variables(term: &Term) -> HashSet<String> {
        let mut vars = HashSet::new();
        Self::collect_variables(term, &mut vars);
        vars
    }
    
    /// Recursively collect variables from a term into a set
    /// 
    /// This is a helper function that traverses the term tree and adds
    /// any variables it finds to the provided set.
    fn collect_variables(term: &Term, vars: &mut HashSet<String>) {
        match term {
            Term::Variable(var) => {
                // Found a variable, add it to the set
                // HashSet automatically handles duplicates
                vars.insert(var.clone());
            }
            Term::Compound(_, args) => {
                // Recursively collect from all arguments
                for arg in args {
                    Self::collect_variables(arg, vars);
                }
            }
            _ => {
                // Atoms and numbers don't contain variables
                // Nothing to collect
            }
        }
    }
    
    /// Count the depth of nested terms
    /// 
    /// Returns the maximum nesting depth of a term.
    /// Simple terms (atoms, variables, numbers) have depth 1.
    /// Compound terms have depth 1 + max depth of arguments.
    pub fn term_depth(term: &Term) -> usize {
        match term {
            Term::Compound(_, args) => {
                if args.is_empty() {
                    // Compound with no args still has depth 1
                    1
                } else {
                    // Find the maximum depth among all arguments
                    // and add 1 for this level
                    1 + args.iter()
                        .map(|arg| Self::term_depth(arg))
                        .max()
                        .unwrap_or(0)
                }
            }
            _ => 1,  // Atoms, variables, and numbers have depth 1
        }
    }
    
    /// Count the total number of subterms
    /// 
    /// Returns the total size of a term, counting all nodes in the tree.
    /// This includes the term itself and all nested subterms.
    pub fn term_size(term: &Term) -> usize {
        match term {
            Term::Compound(_, args) => {
                // Count this compound (1) plus the size of all arguments
                1 + args.iter()
                    .map(|arg| Self::term_size(arg))
                    .sum::<usize>()
            }
            _ => 1,  // Simple terms count as 1
        }
    }
    
    /// Check if a term contains a specific variable
    /// 
    /// Returns true if the given variable name appears anywhere in the term.
    /// This is useful for checking variable dependencies.
    pub fn contains_variable(term: &Term, var_name: &str) -> bool {
        match term {
            // Direct variable match
            Term::Variable(var) => var == var_name,
            
            // Check recursively in compound arguments
            Term::Compound(_, args) => {
                // Use any() for short-circuit evaluation
                // Stops as soon as variable is found
                args.iter().any(|arg| Self::contains_variable(arg, var_name))
            }
            
            // Atoms and numbers never contain variables
            _ => false,
        }
    }
    
    /// Replace all occurrences of a variable with a term
    /// 
    /// Creates a new term where all instances of the specified variable
    /// are replaced with the given replacement term.
    pub fn replace_variable(term: &Term, var_name: &str, replacement: &Term) -> Term {
        match term {
            // If this is the variable we're looking for, replace it
            Term::Variable(var) if var == var_name => replacement.clone(),
            
            // For compounds, recursively replace in all arguments
            Term::Compound(functor, args) => {
                let new_args: Vec<Term> = args.iter()
                    .map(|arg| Self::replace_variable(arg, var_name, replacement))
                    .collect();
                Term::Compound(functor.clone(), new_args)
            }
            
            // Other terms (atoms, numbers, different variables) remain unchanged
            _ => term.clone(),
        }
    }
    
    /// Check if a term is ground (contains no variables)
    /// 
    /// A ground term is fully instantiated with no unbound variables.
    /// This is important for certain Prolog operations.
    pub fn is_ground(term: &Term) -> bool {
        match term {
            // Variables are by definition not ground
            Term::Variable(_) => false,
            
            // Compound is ground if all arguments are ground
            Term::Compound(_, args) => {
                // Use all() for short-circuit evaluation
                // Returns false as soon as a variable is found
                args.iter().all(|arg| Self::is_ground(arg))
            }
            
            // Atoms and numbers are always ground (no variables)
            _ => true,
        }
    }
    
    /// Convert a Prolog list term to a Rust Vec
    /// 
    /// Prolog lists are represented as nested compound terms with the '.' functor.
    /// [1,2,3] is actually .(1, .(2, .(3, [])))
    /// This function unpacks that structure into a Rust vector.
    pub fn list_to_vec(term: &Term) -> Option<Vec<Term>> {
        let mut elements = Vec::new();
        let mut current = term;
        
        // Traverse the list structure
        loop {
            match current {
                // Empty list marker - we've reached the end
                Term::Atom(name) if name == "[]" => return Some(elements),
                
                // List constructor .(head, tail)
                Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                    // Extract head element and add to vector
                    elements.push(args[0].clone());
                    // Move to the tail for next iteration
                    current = &args[1];
                }
                
                // Not a proper list structure
                _ => return None,
            }
        }
    }
    
    /// Convert a Rust Vec to a Prolog list term
    /// 
    /// Builds the nested structure that represents a Prolog list.
    /// Uses right-to-left folding to build from the tail up.
    pub fn vec_to_list(elements: Vec<Term>) -> Term {
        // Start with empty list and build backwards
        // For [1,2,3]:
        // Start with []
        // Add 3: .(3, [])
        // Add 2: .(2, .(3, []))
        // Add 1: .(1, .(2, .(3, [])))
        elements.into_iter().rev().fold(
            Term::Atom("[]".to_string()),  // Initial value: empty list
            |acc, elem| Term::Compound(".".to_string(), vec![elem, acc])
        )
    }
    
    /// Generate a fresh variable name not present in the given set
    /// 
    /// Creates a unique variable name by appending numbers to a base name
    /// until a name not in the existing set is found.
    pub fn fresh_variable(existing_vars: &HashSet<String>, base_name: &str) -> String {
        let mut counter = 0;
        
        // Keep trying until we find an unused name
        loop {
            let candidate = if counter == 0 {
                // First try: use base name as-is
                base_name.to_string()
            } else {
                // Subsequent tries: append counter
                // Example: X, X1, X2, X3, ...
                format!("{}{}", base_name, counter)
            };
            
            // Check if this name is already taken
            if !existing_vars.contains(&candidate) {
                return candidate;
            }
            
            // Try next number
            counter += 1;
        }
    }
}

/// Clause analysis utilities
pub struct ClauseUtils;

impl ClauseUtils {
    /// Group clauses by predicate (functor/arity)
    /// 
    /// Organizes clauses into groups based on their head predicate.
    /// This is useful for finding all clauses that define a particular predicate.
    pub fn group_by_predicate(clauses: &[Clause]) -> HashMap<String, Vec<&Clause>> {
        let mut groups: HashMap<String, Vec<&Clause>> = HashMap::new();
        
        for clause in clauses {
            // Extract functor and arity from the head
            if let Some((functor, arity)) = clause.head_functor_arity() {
                // Create key in format "functor/arity"
                // This is standard Prolog notation for predicates
                let key = format!("{}/{}", functor, arity);
                
                // Add clause to appropriate group
                // or_insert_with creates empty vector if key doesn't exist
                groups.entry(key).or_insert_with(Vec::new).push(clause);
            }
        }
        
        groups
    }
    
    /// Find all predicates that depend on a given predicate
    /// 
    /// Identifies which predicates call the target predicate in their body.
    /// This is useful for dependency analysis and understanding program structure.
    pub fn find_dependencies(clauses: &[Clause], target_functor: &str, target_arity: usize) -> Vec<String> {
        let target_key = format!("{}/{}", target_functor, target_arity);
        let mut dependencies = HashSet::new();
        
        for clause in clauses {
            // Check if this clause references the target predicate
            if Self::clause_references_predicate(clause, target_functor, target_arity) {
                // Extract the predicate this clause defines
                if let Some((functor, arity)) = clause.head_functor_arity() {
                    let key = format!("{}/{}", functor, arity);
                    
                    // Don't include self-references (recursive predicates)
                    if key != target_key {
                        dependencies.insert(key);
                    }
                }
            }
        }
        
        // Convert set to vector for return
        dependencies.into_iter().collect()
    }
    
    /// Check if a clause references a specific predicate
    /// 
    /// Scans the body of a clause to see if it calls the specified predicate.
    fn clause_references_predicate(clause: &Clause, functor: &str, arity: usize) -> bool {
        // Check each goal in the body
        clause.body.iter().any(|goal| {
            if let Some((goal_functor, goal_arity)) = goal.functor_arity() {
                // Check if this goal matches the target predicate
                goal_functor == functor && goal_arity == arity
            } else {
                false
            }
        })
    }
    
    /// Find recursive predicates (predicates that call themselves)
    /// 
    /// Identifies predicates that have recursive definitions.
    /// Recursive predicates are common in Prolog for list processing and traversals.
    pub fn find_recursive_predicates(clauses: &[Clause]) -> Vec<String> {
        let mut recursive = Vec::new();
        
        for clause in clauses {
            if let Some((head_functor, head_arity)) = clause.head_functor_arity() {
                // Check if the clause body references its own head predicate
                if Self::clause_references_predicate(clause, head_functor, head_arity) {
                    let key = format!("{}/{}", head_functor, head_arity);
                    
                    // Avoid duplicates in the result
                    if !recursive.contains(&key) {
                        recursive.push(key);
                    }
                }
            }
        }
        
        recursive
    }
    
    /// Validate that clauses are well-formed
    /// 
    /// Performs various checks to ensure clauses follow Prolog conventions
    /// and best practices. Returns a list of error/warning messages.
    pub fn validate_clauses(clauses: &[Clause]) -> Vec<String> {
        let mut errors = Vec::new();
        
        for (i, clause) in clauses.iter().enumerate() {
            // Check 1: Head must be valid (not a variable or number)
            match &clause.head {
                Term::Variable(_) => {
                    // Variables can't be clause heads in Prolog
                    errors.push(format!("Clause {}: Head cannot be a variable", i + 1));
                }
                Term::Number(_) => {
                    // Numbers can't be clause heads in Prolog
                    errors.push(format!("Clause {}: Head cannot be a number", i + 1));
                }
                _ => {
                    // Atoms and compounds are valid heads
                }
            }
            
            // Check 2: Look for singleton variables
            // These are variables that appear only once, often indicating typos
            let all_vars = Self::get_clause_variables(clause);
            for var in &all_vars {
                let count = Self::count_variable_occurrences(clause, var);
                
                // Singleton check: variable appears exactly once
                // Exception: underscore-prefixed variables are intentionally singleton
                if count == 1 && !var.starts_with('_') {
                    errors.push(format!(
                        "Clause {}: Singleton variable '{}' (use '_{}' if intentional)", 
                        i + 1, var, var
                    ));
                }
            }
        }
        
        errors
    }
    
    /// Get all variables in a clause (head and body)
    /// 
    /// Collects all unique variable names from both the head and body of a clause.
    fn get_clause_variables(clause: &Clause) -> HashSet<String> {
        // Start with variables from the head
        let mut vars = TermUtils::get_all_variables(&clause.head);
        
        // Add variables from each goal in the body
        for goal in &clause.body {
            vars.extend(TermUtils::get_all_variables(goal));
        }
        
        vars
    }
    
    /// Count how many times a variable appears in a clause
    /// 
    /// Used for singleton variable detection.
    fn count_variable_occurrences(clause: &Clause, var_name: &str) -> usize {
        let mut count = 0;
        
        // Count in head
        count += Self::count_variable_in_term(&clause.head, var_name);
        
        // Count in each body goal
        for goal in &clause.body {
            count += Self::count_variable_in_term(goal, var_name);
        }
        
        count
    }
    
    /// Count occurrences of a variable in a term
    /// 
    /// Recursively counts how many times a specific variable appears in a term.
    fn count_variable_in_term(term: &Term, var_name: &str) -> usize {
        match term {
            // Found the variable we're counting
            Term::Variable(var) if var == var_name => 1,
            
            // Recursively count in compound arguments
            Term::Compound(_, args) => {
                args.iter()
                    .map(|arg| Self::count_variable_in_term(arg, var_name))
                    .sum()
            }
            
            // Not the variable we're looking for
            _ => 0,
        }
    }
}

/// Engine helper utilities
pub struct EngineUtils;

impl EngineUtils {
    /// Load a Prolog program from a string with better error reporting
    /// 
    /// Parses a multi-line Prolog program and adds clauses to the engine.
    /// Provides line-by-line error reporting for debugging.
    pub fn load_program(engine: &mut PrologEngine, program: &str) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        let mut line_num = 1;
        
        // Process each line of the program
        for line in program.lines() {
            let line = line.trim();
            
            // Skip empty lines and comments
            // Prolog comments start with %
            if line.is_empty() || line.starts_with('%') {
                line_num += 1;
                continue;
            }
            
            // Try to parse and add the line to the engine
            if let Err(e) = engine.parse_and_add(line) {
                // Record error with line number for debugging
                errors.push(format!("Line {}: {}", line_num, e));
            }
            
            line_num += 1;
        }
        
        // Return Ok if no errors, Err with all errors otherwise
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    /// Execute multiple queries and collect results
    /// 
    /// Runs a batch of queries against the engine and collects all results.
    /// Useful for testing or running multiple related queries.
    pub fn batch_query(engine: &mut PrologEngine, queries: &[&str]) -> Vec<(String, Result<Vec<Substitution>, String>)> {
        let mut results = Vec::new();
        
        for query in queries {
            // Ensure query ends with proper terminator
            // Queries MUST end with '?' not '.'
            let query_str = if query.ends_with('?') {
                query.to_string()
            } else if query.ends_with('.') {
                // Query has wrong terminator - still try it but it will likely fail
                // Let the engine produce the proper error message
                query.to_string()
            } else {
                // Add question mark if missing (queries use ?, not .)
                format!("{}?", query)
            };
            
            // Execute query and convert result to standardized format
            let result = match engine.parse_query(&query_str) {
                Ok(solutions) => Ok(solutions),
                Err(e) => Err(format!("{}", e)),
            };
            
            // Store query and its result
            results.push((query.to_string(), result));
        }
        
        results
    }
    
    /// Get detailed statistics about the engine's database
    /// 
    /// Analyzes the clauses in the engine to provide insights about
    /// the program structure, complexity, and characteristics.
    pub fn analyze_database(engine: &PrologEngine) -> DatabaseAnalysis {
        let clauses = engine.get_clauses();
        let groups = ClauseUtils::group_by_predicate(clauses);
        
        // Basic counts
        let total_clauses = clauses.len();
        let total_predicates = groups.len();
        
        // Find recursive predicates
        let recursive_predicates = ClauseUtils::find_recursive_predicates(clauses);
        
        // Find largest predicate (most clauses)
        let mut predicate_sizes: Vec<(String, usize)> = groups.iter()
            .map(|(name, clauses)| (name.clone(), clauses.len()))
            .collect();
        
        // Sort by size (descending) to find largest
        predicate_sizes.sort_by(|a, b| b.1.cmp(&a.1));
        
        let largest_predicate = predicate_sizes.first().cloned();
        
        // Calculate average clause complexity
        let total_terms: usize = clauses.iter()
            .map(|clause| {
                // Count terms in head plus all body goals
                1 + clause.body.iter()
                    .map(|goal| TermUtils::term_size(goal))
                    .sum::<usize>()
            })
            .sum();
        
        // Calculate average, handling empty database
        let avg_clause_size = if total_clauses > 0 {
            total_terms as f64 / total_clauses as f64
        } else {
            0.0
        };
        
        DatabaseAnalysis {
            total_clauses,
            total_predicates,
            recursive_predicates,
            largest_predicate,
            average_clause_size: avg_clause_size,
            predicate_distribution: predicate_sizes,
        }
    }
    
    /// Extract variable names from a query string
    /// 
    /// Parses a query string to find all variable names (uppercase identifiers).
    /// This is useful for determining which variables to display in results.
    pub fn extract_query_variables(query: &str) -> Vec<String> {
        let mut variables = Vec::new();
        let mut chars = query.chars().peekable();
        
        // Scan through the query character by character
        while let Some(ch) = chars.next() {
            // Check if this could be the start of a variable
            // Variables start with uppercase or underscore
            if ch.is_ascii_uppercase() || ch == '_' {
                let mut var_name = String::new();
                var_name.push(ch);
                
                // Continue reading the variable name
                // Variables can contain letters, digits, and underscores
                while let Some(&next_ch) = chars.peek() {
                    if next_ch.is_alphanumeric() || next_ch == '_' {
                        var_name.push(chars.next().unwrap());
                    } else {
                        // End of variable name
                        break;
                    }
                }
                
                // Add to list if it's a real variable (not anonymous _)
                // and not already in the list
                if !variables.contains(&var_name) && var_name != "_" && var_name.len() > 0 {
                    variables.push(var_name);
                }
            }
        }
        
        variables
    }
}

/// Database analysis results
/// 
/// Contains statistics and insights about a Prolog program database.
#[derive(Debug, Clone)]
pub struct DatabaseAnalysis {
    /// Total number of clauses in the database
    pub total_clauses: usize,
    
    /// Number of distinct predicates (functor/arity pairs)
    pub total_predicates: usize,
    
    /// List of predicates that are defined recursively
    pub recursive_predicates: Vec<String>,
    
    /// The predicate with the most clauses
    pub largest_predicate: Option<(String, usize)>,
    
    /// Average complexity of clauses (in terms)
    pub average_clause_size: f64,
    
    /// Distribution of clauses per predicate
    pub predicate_distribution: Vec<(String, usize)>,
}

impl fmt::Display for DatabaseAnalysis {
    /// Format the analysis results for human-readable display
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Database Analysis:")?;
        writeln!(f, "  Total clauses: {}", self.total_clauses)?;
        writeln!(f, "  Total predicates: {}", self.total_predicates)?;
        writeln!(f, "  Average clause size: {:.1} terms", self.average_clause_size)?;
        
        // Show largest predicate if there is one
        if let Some((name, count)) = &self.largest_predicate {
            writeln!(f, "  Largest predicate: {} ({} clauses)", name, count)?;
        }
        
        // List recursive predicates if any
        if !self.recursive_predicates.is_empty() {
            writeln!(f, "  Recursive predicates: {}", self.recursive_predicates.join(", "))?;
        }
        
        // Show full distribution only if not too many predicates
        // Otherwise it would clutter the output
        if self.predicate_distribution.len() <= 10 {
            writeln!(f, "  Predicate distribution:")?;
            for (name, count) in &self.predicate_distribution {
                writeln!(f, "    {}: {} clauses", name, count)?;
            }
        }
        
        Ok(())
    }
}

// Link to the test module
#[cfg(test)]
#[path = "utils_tests.rs"]
mod tests;