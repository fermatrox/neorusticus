// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: engine.rs
// Creator: Jonas Forsman

//! Main Prolog execution engine
//! 
//! This module provides the core Prolog execution engine that resolves queries
//! against a database of clauses. It includes stack overflow protection,
//! cut handling, variable renaming, and comprehensive error reporting.

use std::collections::HashMap;
use std::fmt;
use crate::ast::{Term, Clause};
use crate::error::{ParseError, RuntimeError, ParseResult, RuntimeResult};
use crate::lexer::{Token, Tokenizer};
use crate::parser::Parser;
use crate::unification::{Unifier, Substitution};
use crate::builtins::BuiltinPredicates;

/// Execution context for tracking cut operations and stack depth
#[derive(Debug)]
pub struct ExecutionContext {
    cut_called: bool,
    cut_level: usize,
    stack_depth: usize,
    max_stack_depth: usize,
    current_predicate: String,
}

impl ExecutionContext {
    /// Create a new execution context with default settings
    pub fn new() -> Self {
        ExecutionContext {
            cut_called: false,
            cut_level: 0,
            stack_depth: 0,
            max_stack_depth: 100, // Conservative default for safety
            current_predicate: "unknown".to_string(),
        }
    }
    
    /// Create a new execution context with custom stack depth limit
    pub fn with_max_depth(max_depth: usize) -> Self {
        // Create default context and then customize the max depth
        // This ensures all other defaults are properly set
        let mut ctx = Self::new();
        ctx.max_stack_depth = max_depth;
        ctx
    }
    
    /// Enter a predicate call (increments stack depth)
    pub fn enter_predicate(&mut self, predicate: String) -> RuntimeResult<()> {
        // Increment depth FIRST to check against limit
        // This prevents off-by-one errors in stack overflow detection
        self.stack_depth += 1;
        self.current_predicate = predicate.clone();
        
        // Check stack depth immediately to prevent runaway recursion
        // We check AFTER incrementing to ensure we catch the overflow
        // at the right depth (e.g., max_depth=5 means 5 levels deep)
        if self.stack_depth > self.max_stack_depth {
            return Err(RuntimeError::StackOverflow {
                depth: self.stack_depth,
                predicate,
            });
        }
        
        Ok(())
    }
    
    /// Exit a predicate call (decrements stack depth)
    pub fn exit_predicate(&mut self) {
        // Guard against underflow - should never happen in correct usage
        // but provides safety against bugs
        if self.stack_depth > 0 {
            self.stack_depth -= 1;
        }
        // Note: We don't reset current_predicate as it may be useful
        // for debugging to know the last predicate even after exit
    }
    
    /// Set the cut flag (prevents backtracking)
    pub fn cut(&mut self) {
        // Cut is a Prolog operation that commits to the current choice
        // Once set, the engine won't try alternative clauses
        self.cut_called = true;
    }
    
    /// Check if cut has been called
    pub fn is_cut_called(&self) -> bool {
        self.cut_called
    }
    
    /// Reset the cut flag
    pub fn reset_cut(&mut self) {
        // Used when entering a new branch of execution where
        // the previous cut should not apply
        self.cut_called = false;
    }
    
    /// Set the cut level for nested cuts
    pub fn set_cut_level(&mut self, level: usize) {
        // Cut levels help manage nested cuts in complex rule structures
        // Higher levels represent deeper nesting
        self.cut_level = level;
    }
    
    /// Get the current cut level
    pub fn get_cut_level(&self) -> usize {
        self.cut_level
    }
    
    /// Get the current stack depth
    pub fn get_stack_depth(&self) -> usize {
        self.stack_depth
    }
    
    /// Get the current predicate name
    pub fn get_current_predicate(&self) -> &str {
        &self.current_predicate
    }
    
    /// Get the maximum allowed stack depth
    pub fn get_max_stack_depth(&self) -> usize {
        self.max_stack_depth
    }
    
    /// Set the maximum allowed stack depth
    pub fn set_max_stack_depth(&mut self, max_depth: usize) {
        // Allows runtime adjustment of stack limits
        // Useful for different query complexity requirements
        self.max_stack_depth = max_depth;
    }
}

/// Statistics about the Prolog engine state
#[derive(Debug, Clone)]
pub struct EngineStats {
    pub clause_count: usize,
    pub variable_counter: usize,
    pub max_solutions: usize,
    pub max_stack_depth: usize,
    pub queries_executed: usize,
    pub predicates_defined: HashMap<String, usize>, // functor/arity -> count
}

impl EngineStats {
    /// Create new empty statistics
    pub fn new() -> Self {
        EngineStats {
            clause_count: 0,
            variable_counter: 0,
            max_solutions: 100,
            max_stack_depth: 100,
            queries_executed: 0,
            predicates_defined: HashMap::new(),
        }
    }
    
    /// Update predicate count when a clause is added
    pub fn add_predicate(&mut self, functor: &str, arity: usize) {
        // Create a key in Prolog notation: functor/arity (e.g., "parent/2")
        // This is the standard way to identify predicates in Prolog
        let key = format!("{}/{}", functor, arity);
        
        // Use entry API to either increment existing count or insert 1
        // This efficiently handles both new and existing predicates
        *self.predicates_defined.entry(key).or_insert(0) += 1;
    }
    
    /// Get the number of different predicates defined
    pub fn predicate_count(&self) -> usize {
        // Each key in the HashMap represents a unique predicate signature
        // e.g., parent/2 and parent/3 are counted as different predicates
        self.predicates_defined.len()
    }
    
    /// Get the most frequently defined predicate
    pub fn most_common_predicate(&self) -> Option<(String, usize)> {
        // Find the predicate with the maximum number of clauses
        // This helps identify which predicates have the most rules/facts
        self.predicates_defined.iter()
            .max_by_key(|(_, count)| *count)  // Compare by clause count
            .map(|(name, count)| (name.clone(), *count))  // Clone to return owned data
    }
}

impl fmt::Display for EngineStats {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Engine Statistics:")?;
        writeln!(f, "  Total clauses: {}", self.clause_count)?;
        writeln!(f, "  Unique predicates: {}", self.predicate_count())?;
        writeln!(f, "  Variables created: {}", self.variable_counter)?;
        writeln!(f, "  Queries executed: {}", self.queries_executed)?;
        writeln!(f, "  Max solutions limit: {}", self.max_solutions)?;
        writeln!(f, "  Max stack depth: {}", self.max_stack_depth)?;
        
        if let Some((pred, count)) = self.most_common_predicate() {
            writeln!(f, "  Most common predicate: {} ({} clauses)", pred, count)?;
        }
        
        Ok(())
    }
}

/// Main Prolog execution engine
pub struct PrologEngine {
    clauses: Vec<Clause>,
    variable_counter: usize,
    max_solutions: usize,
    stats: EngineStats,
}

impl PrologEngine {
    /// Create a new Prolog engine with default settings
    pub fn new() -> Self {
        PrologEngine {
            clauses: Vec::new(),
            variable_counter: 0,
            max_solutions: 100,
            stats: EngineStats::new(),
        }
    }
    
    /// Create a new Prolog engine with custom limits
    pub fn with_limits(max_solutions: usize) -> Self {
        let mut engine = Self::new();
        engine.max_solutions = max_solutions;
        engine.stats.max_solutions = max_solutions;
        engine
    }
    
    /// Create a new Prolog engine with full customization
    pub fn with_config(max_solutions: usize, max_stack_depth: usize) -> Self {
        let mut engine = Self::with_limits(max_solutions);
        engine.stats.max_stack_depth = max_stack_depth;
        engine
    }
    
    /// Parse and add a clause from a string
    pub fn parse_and_add(&mut self, input: &str) -> ParseResult<()> {
        // Step 1: Tokenize the input string into a sequence of tokens
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize().map_err(|e| {
            // Log tokenization errors for debugging
            eprintln!("Tokenization error: {}", e);
            e
        })?;
        
        // Step 2: Parse the tokens into a clause (fact or rule)
        let mut parser = Parser::new(tokens);
        let clause = parser.parse_clause().map_err(|e| {
            eprintln!("Parse error in clause: {}", e);
            e
        })?;
        
        // Step 3: Ensure the clause ends with a dot (Prolog convention)
        parser.expect(Token::Dot).map_err(|e| {
            eprintln!("Expected '.' at end of clause: {}", e);
            e
        })?;
        
        // Step 4: Validate the clause
        // Facts (clauses with no body) must be ground (no variables)
        if clause.is_fact() && !clause.is_ground() {
            return Err(ParseError::InvalidSyntax {
                message: format!("Facts cannot contain variables. Found variables in: {}", clause.head),
                position: crate::error::Position::start(),
                suggestion: Some("Either provide concrete values for all variables, or make it a rule with a body".to_string()),
            });
        }
        
        // Step 5: Update statistics with the new predicate information
        // This tracks what predicates are defined and how many clauses each has
        if let Some((functor, arity)) = clause.head_functor_arity() {
            self.stats.add_predicate(functor, arity);
        }
        
        // Step 6: Add the parsed clause to the database
        self.add_clause(clause);
        Ok(())
    }
    
    /// Parse and execute a query from a string
    pub fn parse_query(&mut self, input: &str) -> Result<Vec<Substitution>, Box<dyn std::error::Error>> {
        // Step 1: Tokenize the query string
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize()?;
        let mut parser = Parser::new(tokens);
        
        // Step 2: Parse the query as a list of goals (comma-separated terms)
        let goals = parser.parse_query()?;
        
        // Step 3: Accept either '?' or '.' at end of query
        // Different Prolog systems use different conventions
        if *parser.current_token() == Token::Question {
            parser.advance();
        } else {
            parser.expect(Token::Dot)?;
        }
        
        // Step 4: Track query execution in statistics
        self.stats.queries_executed += 1;
        
        // Step 5: Execute the query and return solutions
        // Box the error for uniform error type across parse and runtime errors
        self.query(goals).map_err(|e| Box::new(e) as Box<dyn std::error::Error>)
    }
    
    /// Parse a single term from a string (useful for testing)
    pub fn parse_term(input: &str) -> ParseResult<Term> {
        // Static method for parsing a term without needing an engine instance
        // Useful for unit tests and REPL interactions
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize()?;
        let mut parser = Parser::new(tokens);
        
        parser.parse_expression()
    }
    
    /// Add a clause to the database
    pub fn add_clause(&mut self, clause: Clause) {
        // Update the clause count for statistics
        self.stats.clause_count += 1;
        // Add to the clause vector (acts as our knowledge base)
        self.clauses.push(clause);
    }
    
    /// Add a fact (clause with no body)
    /// Facts must be ground (contain no variables)
    pub fn add_fact(&mut self, head: Term) {
        // Create a fact from the head term
        let clause = Clause::fact(head);
        
        // Update predicate statistics if the head has a valid functor
        if let Some((functor, arity)) = clause.head_functor_arity() {
            self.stats.add_predicate(functor, arity);
        }
        
        // Add the fact to the database
        self.add_clause(clause);
    }
    
    /// Add a rule (clause with body)
    pub fn add_rule(&mut self, head: Term, body: Vec<Term>) {
        // Create a rule from head and body terms
        let clause = Clause::rule(head, body);
        
        // Update predicate statistics
        if let Some((functor, arity)) = clause.head_functor_arity() {
            self.stats.add_predicate(functor, arity);
        }
        
        // Add the rule to the database
        self.add_clause(clause);
    }
    
    /// Get all clauses in the database
    pub fn get_clauses(&self) -> &[Clause] {
        &self.clauses
    }
    
    /// Clear all clauses from the database
    pub fn clear(&mut self) {
        // Remove all clauses from the knowledge base
        self.clauses.clear();
        
        // Reset statistics but preserve the configured limits
        // We keep max_solutions as it's a configuration, not a statistic
        self.stats = EngineStats::new();
        self.stats.max_solutions = self.max_solutions;
        
        // Reset the variable counter used for renaming
        self.variable_counter = 0;
    }
    
    /// Rename variables in a clause to avoid conflicts
    fn rename_clause_variables(&mut self, clause: &Clause) -> Clause {
        // Create a mapping from original variable names to new unique names
        // This prevents variable name conflicts when using the same clause multiple times
        let mut var_map = HashMap::new();
        
        // Inner function to recursively rename variables in a term
        fn rename_term(term: &Term, var_map: &mut HashMap<String, String>, counter: &mut usize) -> Term {
            match term {
                Term::Variable(var) => {
                    // Check if we've already renamed this variable
                    if let Some(new_var) = var_map.get(var) {
                        // Use the existing renamed version for consistency
                        Term::Variable(new_var.clone())
                    } else {
                        // Create a new unique variable name with _G prefix
                        // _G stands for "generated" and is a Prolog convention
                        let new_var = format!("_G{}", counter);
                        *counter += 1;
                        
                        // Store the mapping for future occurrences of this variable
                        var_map.insert(var.clone(), new_var.clone());
                        Term::Variable(new_var)
                    }
                }
                Term::Compound(functor, args) => {
                    // Recursively rename variables in all arguments
                    let new_args: Vec<Term> = args.iter()
                        .map(|arg| rename_term(arg, var_map, counter))
                        .collect();
                    Term::Compound(functor.clone(), new_args)
                }
                // Atoms and numbers don't contain variables, return as-is
                _ => term.clone(),
            }
        }
        
        // Rename variables in the head
        let new_head = rename_term(&clause.head, &mut var_map, &mut self.variable_counter);
        
        // Rename variables in the body, using the same var_map to ensure consistency
        // Variables with the same name in head and body get the same new name
        let new_body: Vec<Term> = clause.body.iter()
            .map(|goal| rename_term(goal, &mut var_map, &mut self.variable_counter))
            .collect();
        
        Clause { head: new_head, body: new_body }
    }
    
    /// Query the database with a list of goals
    pub fn query(&mut self, goals: Vec<Term>) -> RuntimeResult<Vec<Substitution>> {
        // Initialize the solution collector
        let mut solutions = Vec::new();
        
        // Create execution context with configured stack depth limit
        let mut context = ExecutionContext::with_max_depth(self.stats.max_stack_depth);
        
        // Start with empty substitution (no variables bound yet)
        let initial_subst = HashMap::new();
        
        // Apply substitutions to goals to ensure they're properly grounded
        // This handles cases where goals might already contain some substitutions
        let substituted_goals: Vec<Term> = goals.iter()
            .map(|goal| Unifier::apply_substitution(goal, &initial_subst))
            .collect();
        
        // Start the recursive goal solving process
        self.solve_goals_with_cut(substituted_goals, initial_subst, &mut context, &mut solutions)?;
        Ok(solutions)
    }
    
    /// Recursive goal solving with cut handling
    fn solve_goals_with_cut(&mut self, goals: Vec<Term>, subst: Substitution, 
                           context: &mut ExecutionContext, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        // Check solution limit to prevent runaway queries
        // This protects against infinite or very large result sets
        if solutions.len() >= self.max_solutions {
            return Err(RuntimeError::ArithmeticError {
                operation: "query".to_string(),
                operands: vec![],
                reason: format!("Too many solutions (limit: {})", self.max_solutions),
            });
        }
        
        // Base case: all goals solved successfully
        if goals.is_empty() {
            // We have a complete solution - add the current substitution
            solutions.push(subst);
            return Ok(());
        }
        
        // Process the first goal in the list
        let current_goal = &goals[0];
        let remaining_goals = goals[1..].to_vec();
        
        // Track predicate for stack overflow detection
        // Format as functor/arity for clear error messages
        let predicate_name = match current_goal {
            Term::Compound(functor, args) => format!("{}/{}", functor, args.len()),
            Term::Atom(functor) => format!("{}/0", functor),
            _ => "unknown".to_string(),
        };
        
        // CRITICAL: Check stack depth BEFORE any recursive work
        // This prevents stack overflow by catching deep recursion early
        context.enter_predicate(predicate_name.clone())?;
        
        // Delegate to internal method for actual goal solving
        // This separation ensures consistent stack tracking
        let result = self.solve_goal_internal(current_goal, remaining_goals, subst, context, solutions);
        
        // Always exit the predicate, even if solving failed
        context.exit_predicate();
        result
    }
    
    /// Internal goal solving to ensure consistent stack tracking
    fn solve_goal_internal(&mut self, current_goal: &Term, remaining_goals: Vec<Term>, 
                          subst: Substitution, context: &mut ExecutionContext, 
                          solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        // First, check if this is a built-in predicate
        // Built-ins are handled specially and don't search the clause database
        let is_builtin = match current_goal {
            Term::Compound(functor, args) => BuiltinPredicates::is_builtin(functor, args.len()),
            Term::Atom(functor) => BuiltinPredicates::is_builtin(functor, 0),
            _ => false,
        };
        
        if is_builtin {
            // Handle built-in predicate through the builtins module
            let mut builtin_solutions = Vec::new();
            let mut builtin_subst = subst.clone();
            
            // Execute the built-in, which may produce multiple solutions
            BuiltinPredicates::execute(current_goal, &mut builtin_subst, &mut builtin_solutions, context)?;
            
            // For each solution from the built-in, continue with remaining goals
            for solution_subst in builtin_solutions {
                // Apply the new substitution to remaining goals
                // This ensures variables bound by the built-in are propagated
                let substituted_goals: Vec<Term> = remaining_goals.iter()
                    .map(|goal| Unifier::apply_substitution(goal, &solution_subst))
                    .collect();
                
                // Recursively solve the remaining goals
                self.solve_goals_with_cut(substituted_goals, solution_subst, context, solutions)?;
                
                // If cut was called, stop trying more solutions
                // Cut prevents backtracking to alternative solutions
                if context.is_cut_called() {
                    break;
                }
            }
        } else {
            // User-defined predicate: search the clause database
            // Clone clauses to avoid borrowing issues during recursion
            let clauses = self.clauses.clone();
            
            // Try to unify with each clause in the database
            for clause in clauses.iter() {
                // Rename variables in the clause to avoid conflicts
                // Each use of a clause gets fresh variable names
                let renamed_clause = self.rename_clause_variables(clause);
                let mut new_subst = subst.clone();
                
                // Try to unify the goal with the clause head
                if Unifier::unify(current_goal, &renamed_clause.head, &mut new_subst) {
                    // Unification succeeded - the clause matches our goal
                    
                    // Add the clause body goals to the remaining goals
                    // Body goals must be satisfied for the clause to succeed
                    let mut new_goals = renamed_clause.body;
                    new_goals.extend(remaining_goals.iter().cloned());
                    
                    // Apply current substitution to all new goals
                    // This propagates variable bindings from unification
                    let substituted_goals: Vec<Term> = new_goals.iter()
                        .map(|goal| Unifier::apply_substitution(goal, &new_subst))
                        .collect();
                    
                    // Save and reset cut state for this branch
                    // Each branch gets its own cut context
                    let cut_was_called = context.is_cut_called();
                    context.reset_cut();
                    
                    // Recursively solve the new goal list
                    self.solve_goals_with_cut(substituted_goals, new_subst, context, solutions)?;
                    
                    // If cut was called in this branch, don't try more clauses
                    // Cut commits to the current clause choice
                    if context.is_cut_called() {
                        break;
                    }
                    
                    // Restore cut state for parent context
                    if cut_was_called {
                        context.cut();
                    }
                }
            }
        }
        
        Ok(())
    }
    
    /// Pretty print solutions with variable bindings
    pub fn print_solutions(&self, solutions: &[Substitution], original_vars: &[String]) {
        // Handle the case of no solutions (query failed)
        if solutions.is_empty() {
            println!("false.");
            return;
        }
        
        // Print each solution, separated by semicolons (Prolog convention)
        for (i, solution) in solutions.iter().enumerate() {
            if i > 0 { 
                println!(" ;");  // Semicolon indicates alternative solutions
            }
            
            // Collect variable bindings for this solution
            let mut bindings = Vec::new();
            for var in original_vars {
                if let Some(value) = solution.get(var) {
                    // Apply substitution recursively to get the final value
                    // This resolves chains like X -> Y, Y -> 5 to X -> 5
                    let final_value = Unifier::apply_substitution(value, solution);
                    bindings.push(format!("{} = {}", var, final_value));
                }
            }
            
            // Print the bindings or "true" if no variables
            if bindings.is_empty() {
                print!("true");  // Query succeeded with no variable bindings
            } else {
                print!("{}", bindings.join(", "));
            }
        }
        println!(".");  // End with a dot (Prolog convention)
    }
    
    /// Print solutions in a more detailed format
    pub fn print_solutions_detailed(&self, solutions: &[Substitution], original_vars: &[String]) {
        // Handle no solutions case
        if solutions.is_empty() {
            println!("No solutions found.");
            return;
        }
        
        // Print header with solution count
        println!("Found {} solution(s):", solutions.len());
        
        // Print each solution with clear formatting
        for (i, solution) in solutions.iter().enumerate() {
            println!("Solution {}:", i + 1);
            
            let mut has_bindings = false;
            for var in original_vars {
                if let Some(value) = solution.get(var) {
                    // Resolve the final value through substitution chains
                    let final_value = Unifier::apply_substitution(value, solution);
                    println!("  {} = {}", var, final_value);
                    has_bindings = true;
                }
            }
            
            // If no bindings, the query succeeded without binding variables
            if !has_bindings {
                println!("  true");
            }
        }
    }
    
    /// Enhanced error reporting
    pub fn print_error<E: std::error::Error>(&self, error: &E) {
        // Print the main error message
        eprintln!("Error: {}", error);
        
        // Print chain of causation if available
        // This helps debug complex errors with multiple causes
        let mut source = error.source();
        while let Some(err) = source {
            eprintln!("  Caused by: {}", err);
            source = err.source();
        }
    }
    
    /// Alternative method for boxed errors
    pub fn print_boxed_error(&self, error: &Box<dyn std::error::Error>) {
        // Same as print_error but for boxed error types
        // Useful when errors are type-erased
        eprintln!("Error: {}", error);
        
        // Print causation chain
        let mut source = error.source();
        while let Some(err) = source {
            eprintln!("  Caused by: {}", err);
            source = err.source();
        }
    }
    
    /// Get detailed statistics about the engine state
    pub fn get_stats(&self) -> &EngineStats {
        &self.stats
    }
    
    /// Get mutable statistics (for updating)
    pub fn get_stats_mut(&mut self) -> &mut EngineStats {
        &mut self.stats
    }
    
    /// Find clauses that match a given functor and arity
    pub fn find_clauses(&self, functor: &str, arity: usize) -> Vec<&Clause> {
        // Filter clauses to find those matching the given predicate signature
        // This is used for predicate lookup and debugging
        self.clauses.iter()
            .filter(|clause| {
                // Extract functor and arity from the clause head
                if let Some((clause_functor, clause_arity)) = clause.head_functor_arity() {
                    // Check if both functor name and arity match
                    clause_functor == functor && clause_arity == arity
                } else {
                    // Clause head doesn't have a valid functor (shouldn't happen normally)
                    false
                }
            })
            .collect()
    }
    
    /// Check if a predicate is defined in the database
    pub fn is_predicate_defined(&self, functor: &str, arity: usize) -> bool {
        // A predicate is defined if:
        // 1. There are user-defined clauses for it, OR
        // 2. It's a built-in predicate
        self.find_clauses(functor, arity).len() > 0 || BuiltinPredicates::is_builtin(functor, arity)
    }
    
    /// Get a list of all defined predicates
    pub fn list_predicates(&self) -> Vec<(String, usize, usize)> {
        // Create a map to count clauses per predicate
        let mut predicates = HashMap::new();
        
        // Count user-defined predicates
        for clause in &self.clauses {
            if let Some((functor, arity)) = clause.head_functor_arity() {
                // Create a key for the predicate (functor, arity pair)
                let key = (functor.to_string(), arity);
                // Increment the clause count for this predicate
                *predicates.entry(key).or_insert(0) += 1;
            }
        }
        
        // Convert to vector: (functor, arity, clause_count)
        // This format is useful for displaying predicate information
        predicates.into_iter()
            .map(|((functor, arity), count)| (functor, arity, count))
            .collect()
    }
    
    /// Get a list of all built-in predicates
    pub fn list_builtins(&self) -> Vec<(String, usize, String)> {
        // Delegate to the builtins module which maintains the list
        BuiltinPredicates::list_builtins()
    }
    
    /// Export the database as a string (useful for saving/loading)
    pub fn export_database(&self) -> String {
        // Convert each clause to its string representation with a dot
        // Join them with newlines to create a valid Prolog program
        self.clauses.iter()
            .map(|clause| format!("{}.", clause))
            .collect::<Vec<_>>()
            .join("\n")
    }
    
    /// Load a database from a string
    pub fn load_database(&mut self, input: &str) -> Vec<ParseError> {
        // Collect any parse errors encountered during loading
        let mut errors = Vec::new();
        
        // Process each line of the input
        for line in input.lines() {
            let line = line.trim();
            
            // Skip empty lines and comments (lines starting with %)
            if line.is_empty() || line.starts_with('%') {
                continue;
            }
            
            // Try to parse and add the clause, collecting any errors
            if let Err(e) = self.parse_and_add(line) {
                errors.push(e);
            }
        }
        
        // Return all errors encountered (empty if successful)
        errors
    }
    
    /// Set the maximum number of solutions
    pub fn set_max_solutions(&mut self, max_solutions: usize) {
        // Update both the engine's limit and the statistics
        self.max_solutions = max_solutions;
        self.stats.max_solutions = max_solutions;
    }
    
    /// Set the maximum stack depth
    pub fn set_max_stack_depth(&mut self, max_depth: usize) {
        // Update the statistics (used when creating contexts)
        self.stats.max_stack_depth = max_depth;
    }
    
    /// Reset statistics
    pub fn reset_stats(&mut self) {
        // Preserve configuration values
        let max_solutions = self.stats.max_solutions;
        let max_stack_depth = self.stats.max_stack_depth;
        
        // Create fresh statistics
        self.stats = EngineStats::new();
        
        // Restore configuration values
        self.stats.max_solutions = max_solutions;
        self.stats.max_stack_depth = max_stack_depth;
        
        // Recalculate clause count from current database
        self.stats.clause_count = self.clauses.len();
        
        // Recalculate predicate counts by scanning all clauses
        for clause in &self.clauses {
            if let Some((functor, arity)) = clause.head_functor_arity() {
                self.stats.add_predicate(functor, arity);
            }
        }
    }
}

impl Default for PrologEngine {
    fn default() -> Self {
        Self::new()
    }
}

// Link to the test module
#[cfg(test)]
#[path = "engine_tests.rs"]
mod tests;