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
        let mut ctx = Self::new();
        ctx.max_stack_depth = max_depth;
        ctx
    }
    
    /// Enter a predicate call (increments stack depth)
    pub fn enter_predicate(&mut self, predicate: String) -> RuntimeResult<()> {
        self.stack_depth += 1;
        self.current_predicate = predicate.clone();
        
        // Check stack depth immediately to prevent runaway recursion
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
        if self.stack_depth > 0 {
            self.stack_depth -= 1;
        }
    }
    
    /// Set the cut flag (prevents backtracking)
    pub fn cut(&mut self) {
        self.cut_called = true;
    }
    
    /// Check if cut has been called
    pub fn is_cut_called(&self) -> bool {
        self.cut_called
    }
    
    /// Reset the cut flag
    pub fn reset_cut(&mut self) {
        self.cut_called = false;
    }
    
    /// Set the cut level for nested cuts
    pub fn set_cut_level(&mut self, level: usize) {
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
        let key = format!("{}/{}", functor, arity);
        *self.predicates_defined.entry(key).or_insert(0) += 1;
    }
    
    /// Get the number of different predicates defined
    pub fn predicate_count(&self) -> usize {
        self.predicates_defined.len()
    }
    
    /// Get the most frequently defined predicate
    pub fn most_common_predicate(&self) -> Option<(String, usize)> {
        self.predicates_defined.iter()
            .max_by_key(|(_, count)| *count)
            .map(|(name, count)| (name.clone(), *count))
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
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize().map_err(|e| {
            eprintln!("Tokenization error: {}", e);
            e
        })?;
        
        let mut parser = Parser::new(tokens);
        let clause = parser.parse_clause().map_err(|e| {
            eprintln!("Parse error in clause: {}", e);
            e
        })?;
        
        parser.expect(Token::Dot).map_err(|e| {
            eprintln!("Expected '.' at end of clause: {}", e);
            e
        })?;
        
        // Update statistics
        if let Some((functor, arity)) = clause.head_functor_arity() {
            self.stats.add_predicate(functor, arity);
        }
        
        self.add_clause(clause);
        Ok(())
    }
    
    /// Parse and execute a query from a string
    pub fn parse_query(&mut self, input: &str) -> Result<Vec<Substitution>, Box<dyn std::error::Error>> {
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize()?;
        let mut parser = Parser::new(tokens);
        
        let goals = parser.parse_query()?;
        
        // Accept either '?' or '.' at end of query
        if *parser.current_token() == Token::Question {
            parser.advance();
        } else {
            parser.expect(Token::Dot)?;
        }
        
        self.stats.queries_executed += 1;
        self.query(goals).map_err(|e| Box::new(e) as Box<dyn std::error::Error>)
    }
    
    /// Parse a single term from a string (useful for testing)
    pub fn parse_term(input: &str) -> ParseResult<Term> {
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize()?;
        let mut parser = Parser::new(tokens);
        
        parser.parse_expression()
    }
    
    /// Add a clause to the database
    pub fn add_clause(&mut self, clause: Clause) {
        self.stats.clause_count += 1;
        self.clauses.push(clause);
    }
    
    /// Add a fact (clause with no body)
    pub fn add_fact(&mut self, head: Term) {
        let clause = Clause::fact(head);
        if let Some((functor, arity)) = clause.head_functor_arity() {
            self.stats.add_predicate(functor, arity);
        }
        self.add_clause(clause);
    }
    
    /// Add a rule (clause with body)
    pub fn add_rule(&mut self, head: Term, body: Vec<Term>) {
        let clause = Clause::rule(head, body);
        if let Some((functor, arity)) = clause.head_functor_arity() {
            self.stats.add_predicate(functor, arity);
        }
        self.add_clause(clause);
    }
    
    /// Get all clauses in the database
    pub fn get_clauses(&self) -> &[Clause] {
        &self.clauses
    }
    
    /// Clear all clauses from the database
    pub fn clear(&mut self) {
        self.clauses.clear();
        self.stats = EngineStats::new();
        self.stats.max_solutions = self.max_solutions;
        self.variable_counter = 0;
    }
    
    /// Rename variables in a clause to avoid conflicts
    fn rename_clause_variables(&mut self, clause: &Clause) -> Clause {
        let mut var_map = HashMap::new();
        
        fn rename_term(term: &Term, var_map: &mut HashMap<String, String>, counter: &mut usize) -> Term {
            match term {
                Term::Variable(var) => {
                    if let Some(new_var) = var_map.get(var) {
                        Term::Variable(new_var.clone())
                    } else {
                        let new_var = format!("_G{}", counter);
                        *counter += 1;
                        var_map.insert(var.clone(), new_var.clone());
                        Term::Variable(new_var)
                    }
                }
                Term::Compound(functor, args) => {
                    let new_args: Vec<Term> = args.iter()
                        .map(|arg| rename_term(arg, var_map, counter))
                        .collect();
                    Term::Compound(functor.clone(), new_args)
                }
                _ => term.clone(),
            }
        }
        
        let new_head = rename_term(&clause.head, &mut var_map, &mut self.variable_counter);
        let new_body: Vec<Term> = clause.body.iter()
            .map(|goal| rename_term(goal, &mut var_map, &mut self.variable_counter))
            .collect();
        
        Clause { head: new_head, body: new_body }
    }
    
    /// Query the database with a list of goals
    pub fn query(&mut self, goals: Vec<Term>) -> RuntimeResult<Vec<Substitution>> {
        let mut solutions = Vec::new();
        let mut context = ExecutionContext::with_max_depth(self.stats.max_stack_depth);
        let initial_subst = HashMap::new();
        
        // Apply substitutions to goals to ensure they're properly grounded
        let substituted_goals: Vec<Term> = goals.iter()
            .map(|goal| Unifier::apply_substitution(goal, &initial_subst))
            .collect();
            
        self.solve_goals_with_cut(substituted_goals, initial_subst, &mut context, &mut solutions)?;
        Ok(solutions)
    }
    
    /// Recursive goal solving with cut handling
    fn solve_goals_with_cut(&mut self, goals: Vec<Term>, subst: Substitution, 
                           context: &mut ExecutionContext, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        // Check solution limit to prevent runaway queries
        if solutions.len() >= self.max_solutions {
            return Err(RuntimeError::ArithmeticError {
                operation: "query".to_string(),
                operands: vec![],
                reason: format!("Too many solutions (limit: {})", self.max_solutions),
            });
        }
        
        if goals.is_empty() {
            // All goals solved - we have a solution
            solutions.push(subst);
            return Ok(());
        }
        
        let current_goal = &goals[0];
        let remaining_goals = goals[1..].to_vec();
        
        // Track predicate for stack overflow detection
        let predicate_name = match current_goal {
            Term::Compound(functor, args) => format!("{}/{}", functor, args.len()),
            Term::Atom(functor) => format!("{}/0", functor),
            _ => "unknown".to_string(),
        };
        
        // CRITICAL: Check stack depth BEFORE any recursive work
        context.enter_predicate(predicate_name.clone())?;
        
        let result = self.solve_goal_internal(current_goal, remaining_goals, subst, context, solutions);
        
        context.exit_predicate();
        result
    }
    
    /// Internal goal solving to ensure consistent stack tracking
    fn solve_goal_internal(&mut self, current_goal: &Term, remaining_goals: Vec<Term>, 
                          subst: Substitution, context: &mut ExecutionContext, 
                          solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        // Check if current goal is a built-in predicate
        let is_builtin = match current_goal {
            Term::Compound(functor, args) => BuiltinPredicates::is_builtin(functor, args.len()),
            Term::Atom(functor) => BuiltinPredicates::is_builtin(functor, 0),
            _ => false,
        };
        
        if is_builtin {
            // Handle built-in predicate
            let mut builtin_solutions = Vec::new();
            let mut builtin_subst = subst.clone();
            BuiltinPredicates::execute(current_goal, &mut builtin_subst, &mut builtin_solutions, context)?;
            
            for solution_subst in builtin_solutions {
                // Apply substitution to remaining goals and continue
                let substituted_goals: Vec<Term> = remaining_goals.iter()
                    .map(|goal| Unifier::apply_substitution(goal, &solution_subst))
                    .collect();
                
                self.solve_goals_with_cut(substituted_goals, solution_subst, context, solutions)?;
                
                // If cut was called, stop trying more solutions
                if context.is_cut_called() {
                    break;
                }
            }
        } else {
            // Clone clauses to avoid borrowing issues
            let clauses = self.clauses.clone();
            
            // Try to unify with each clause in the database
            for clause in clauses.iter() {
                let renamed_clause = self.rename_clause_variables(clause);
                let mut new_subst = subst.clone();
                
                if Unifier::unify(current_goal, &renamed_clause.head, &mut new_subst) {
                    // Unification succeeded - add body goals to remaining goals
                    let mut new_goals = renamed_clause.body;
                    new_goals.extend(remaining_goals.iter().cloned());
                    
                    // Apply current substitution to new goals
                    let substituted_goals: Vec<Term> = new_goals.iter()
                        .map(|goal| Unifier::apply_substitution(goal, &new_subst))
                        .collect();
                    
                    // Reset cut flag for this branch
                    let cut_was_called = context.is_cut_called();
                    context.reset_cut();
                    
                    self.solve_goals_with_cut(substituted_goals, new_subst, context, solutions)?;
                    
                    // If cut was called in this branch, don't try more clauses
                    if context.is_cut_called() {
                        break;
                    }
                    
                    // Restore cut state
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
        if solutions.is_empty() {
            println!("false.");
            return;
        }
        
        for (i, solution) in solutions.iter().enumerate() {
            if i > 0 { println!(" ;"); }
            
            let mut bindings = Vec::new();
            for var in original_vars {
                if let Some(value) = solution.get(var) {
                    // Apply substitution recursively to get the final value
                    let final_value = Unifier::apply_substitution(value, solution);
                    bindings.push(format!("{} = {}", var, final_value));
                }
            }
            
            if bindings.is_empty() {
                print!("true");
            } else {
                print!("{}", bindings.join(", "));
            }
        }
        println!(".");
    }
    
    /// Print solutions in a more detailed format
    pub fn print_solutions_detailed(&self, solutions: &[Substitution], original_vars: &[String]) {
        if solutions.is_empty() {
            println!("No solutions found.");
            return;
        }
        
        println!("Found {} solution(s):", solutions.len());
        
        for (i, solution) in solutions.iter().enumerate() {
            println!("Solution {}:", i + 1);
            
            let mut has_bindings = false;
            for var in original_vars {
                if let Some(value) = solution.get(var) {
                    let final_value = Unifier::apply_substitution(value, solution);
                    println!("  {} = {}", var, final_value);
                    has_bindings = true;
                }
            }
            
            if !has_bindings {
                println!("  true");
            }
        }
    }
    
    /// Enhanced error reporting
    pub fn print_error<E: std::error::Error>(&self, error: &E) {
        eprintln!("Error: {}", error);
        
        // Print additional context if available
        let mut source = error.source();
        while let Some(err) = source {
            eprintln!("  Caused by: {}", err);
            source = err.source();
        }
    }
    
    /// Alternative method for boxed errors
    pub fn print_boxed_error(&self, error: &Box<dyn std::error::Error>) {
        eprintln!("Error: {}", error);
        
        // Print additional context if available
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
        self.clauses.iter()
            .filter(|clause| {
                if let Some((clause_functor, clause_arity)) = clause.head_functor_arity() {
                    clause_functor == functor && clause_arity == arity
                } else {
                    false
                }
            })
            .collect()
    }
    
    /// Check if a predicate is defined in the database
    pub fn is_predicate_defined(&self, functor: &str, arity: usize) -> bool {
        self.find_clauses(functor, arity).len() > 0 || BuiltinPredicates::is_builtin(functor, arity)
    }
    
    /// Get a list of all defined predicates
    pub fn list_predicates(&self) -> Vec<(String, usize, usize)> {
        let mut predicates = HashMap::new();
        
        // Count user-defined predicates
        for clause in &self.clauses {
            if let Some((functor, arity)) = clause.head_functor_arity() {
                let key = (functor.to_string(), arity);
                *predicates.entry(key).or_insert(0) += 1;
            }
        }
        
        // Convert to vector: (functor, arity, clause_count)
        predicates.into_iter()
            .map(|((functor, arity), count)| (functor, arity, count))
            .collect()
    }
    
    /// Get a list of all built-in predicates
    pub fn list_builtins(&self) -> Vec<(String, usize, String)> {
        BuiltinPredicates::list_builtins()
    }
    
    /// Export the database as a string (useful for saving/loading)
    pub fn export_database(&self) -> String {
        self.clauses.iter()
            .map(|clause| format!("{}.", clause))
            .collect::<Vec<_>>()
            .join("\n")
    }
    
    /// Load a database from a string
    pub fn load_database(&mut self, input: &str) -> Vec<ParseError> {
        let mut errors = Vec::new();
        
        for line in input.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('%') {
                continue; // Skip empty lines and comments
            }
            
            if let Err(e) = self.parse_and_add(line) {
                errors.push(e);
            }
        }
        
        errors
    }
    
    /// Set the maximum number of solutions
    pub fn set_max_solutions(&mut self, max_solutions: usize) {
        self.max_solutions = max_solutions;
        self.stats.max_solutions = max_solutions;
    }
    
    /// Set the maximum stack depth
    pub fn set_max_stack_depth(&mut self, max_depth: usize) {
        self.stats.max_stack_depth = max_depth;
    }
    
    /// Reset statistics
    pub fn reset_stats(&mut self) {
        let max_solutions = self.stats.max_solutions;
        let max_stack_depth = self.stats.max_stack_depth;
        self.stats = EngineStats::new();
        self.stats.max_solutions = max_solutions;
        self.stats.max_stack_depth = max_stack_depth;
        self.stats.clause_count = self.clauses.len();
        
        // Recalculate predicate counts
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_engine_creation() {
        let engine = PrologEngine::new();
        assert_eq!(engine.clauses.len(), 0);
        assert_eq!(engine.max_solutions, 100);
    }

    #[test]
    fn test_add_facts() {
        let mut engine = PrologEngine::new();
        
        engine.add_fact(Term::Compound("parent".to_string(), vec![
            Term::Atom("tom".to_string()),
            Term::Atom("bob".to_string())
        ]));
        
        assert_eq!(engine.clauses.len(), 1);
        assert!(engine.clauses[0].is_fact());
    }

    #[test]
    fn test_add_rules() {
        let mut engine = PrologEngine::new();
        
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
        
        assert_eq!(engine.clauses.len(), 1);
        assert!(engine.clauses[0].is_rule());
        assert_eq!(engine.clauses[0].body.len(), 2);
    }

    #[test]
    fn test_parse_and_add() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("parent(tom, bob).").unwrap();
        engine.parse_and_add("parent(bob, ann).").unwrap();
        
        assert_eq!(engine.clauses.len(), 2);
    }

    #[test]
    fn test_parse_error() {
        let mut engine = PrologEngine::new();
        
        let result = engine.parse_and_add("invalid syntax");
        assert!(result.is_err());
    }

    #[test]
    fn test_simple_query() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("parent(tom, bob).").unwrap();
        engine.parse_and_add("parent(bob, ann).").unwrap();
        
        let solutions = engine.parse_query("parent(tom, bob).").unwrap();
        assert_eq!(solutions.len(), 1);
        
        let solutions = engine.parse_query("parent(tom, X).").unwrap();
        assert_eq!(solutions.len(), 1);
        
        let solutions = engine.parse_query("parent(mary, X).").unwrap();
        assert_eq!(solutions.len(), 0);
    }

    #[test]
    fn test_variable_query() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("likes(mary, food).").unwrap();
        engine.parse_and_add("likes(mary, wine).").unwrap();
        engine.parse_and_add("likes(john, wine).").unwrap();
        
        let solutions = engine.parse_query("likes(mary, X).").unwrap();
        assert_eq!(solutions.len(), 2);
        
        let solutions = engine.parse_query("likes(X, wine).").unwrap();
        assert_eq!(solutions.len(), 2);
    }

    #[test]
    fn test_rule_execution() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("parent(alice, bob).").unwrap();
        engine.parse_and_add("parent(bob, charlie).").unwrap();
        engine.parse_and_add("grandparent(X, Z) :- parent(X, Y), parent(Y, Z).").unwrap();
        
        let solutions = engine.parse_query("grandparent(alice, charlie).").unwrap();
        assert_eq!(solutions.len(), 1);
        
        let solutions = engine.parse_query("grandparent(alice, X).").unwrap();
        assert_eq!(solutions.len(), 1);
    }

    #[test]
    fn test_arithmetic() {
        let mut engine = PrologEngine::new();
        
        let solutions = engine.parse_query("X is 2 + 3.").unwrap();
        assert_eq!(solutions.len(), 1);
        
        let solutions = engine.parse_query("5 > 3.").unwrap();
        assert_eq!(solutions.len(), 1);
        
        let solutions = engine.parse_query("3 > 5.").unwrap();
        assert_eq!(solutions.len(), 0);
    }

    #[test]
    fn test_list_operations() {
        let mut engine = PrologEngine::new();
        
        let solutions = engine.parse_query("append([1, 2], [3, 4], X).").unwrap();
        assert_eq!(solutions.len(), 1);
        
        let solutions = engine.parse_query("member(2, [1, 2, 3]).").unwrap();
        assert_eq!(solutions.len(), 1);
        
        let solutions = engine.parse_query("length([a, b, c], X).").unwrap();
        assert_eq!(solutions.len(), 1);
    }

    #[test]
    fn test_cut_operation() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("max(X, Y, X) :- X >= Y, !.").unwrap();
        engine.parse_and_add("max(X, Y, Y).").unwrap();
        
        let solutions = engine.parse_query("max(5, 3, Z).").unwrap();
        assert_eq!(solutions.len(), 1); // Cut should prevent second clause
    }

    #[test]
    fn test_engine_stats() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("fact1(a).").unwrap();
        engine.parse_and_add("fact1(b).").unwrap();
        engine.parse_and_add("fact2(x).").unwrap();
        
        let stats = engine.get_stats();
        assert_eq!(stats.clause_count, 3);
        assert_eq!(stats.predicate_count(), 2); // fact1/1 and fact2/1
        
        // Test query counting
        engine.parse_query("fact1(a).").unwrap();
        assert_eq!(engine.get_stats().queries_executed, 1);
    }

    #[test]
    fn test_predicate_finding() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("parent(tom, bob).").unwrap();
        engine.parse_and_add("parent(bob, ann).").unwrap();
        engine.parse_and_add("likes(mary, wine).").unwrap();
        
        let parent_clauses = engine.find_clauses("parent", 2);
        assert_eq!(parent_clauses.len(), 2);
        
        let likes_clauses = engine.find_clauses("likes", 2);
        assert_eq!(likes_clauses.len(), 1);
        
        let unknown_clauses = engine.find_clauses("unknown", 1);
        assert_eq!(unknown_clauses.len(), 0);
        
        assert!(engine.is_predicate_defined("parent", 2));
        assert!(engine.is_predicate_defined("append", 3)); // Built-in
        assert!(!engine.is_predicate_defined("unknown", 1));
    }

    #[test]
    fn test_database_export_import() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("parent(tom, bob).").unwrap();
        engine.parse_and_add("parent(bob, ann).").unwrap();
        engine.parse_and_add("grandparent(X, Z) :- parent(X, Y), parent(Y, Z).").unwrap();
        
        let exported = engine.export_database();
        assert!(exported.contains("parent(tom, bob)"));
        assert!(exported.contains("grandparent"));
        
        let mut new_engine = PrologEngine::new();
        let errors = new_engine.load_database(&exported);
        assert!(errors.is_empty());
        assert_eq!(new_engine.clauses.len(), 3);
    }

    #[test]
    fn test_error_handling() {
        let mut engine = PrologEngine::new();
        
        // Test division by zero
        let result = engine.parse_query("X is 5 // 0.");
        assert!(result.is_err());
        
        // Test uninstantiated variable
        let result = engine.parse_query("X is Y + 1.");
        assert!(result.is_err());
    }

    #[test]
    fn test_solution_limits() {
        let mut engine = PrologEngine::with_limits(3);
        
        // Add many facts
        for i in 1..=10 {
            engine.parse_and_add(&format!("number({}).", i)).unwrap();
        }
        
        let result = engine.parse_query("number(X).");
        
        // Should either succeed with limited solutions or fail with limit error
        match result {
            Ok(solutions) => assert!(solutions.len() <= 3),
            Err(_) => {} // Limit error is acceptable
        }
    }

    #[test]
    fn test_stack_overflow_protection() {
        let mut engine = PrologEngine::with_config(10, 5); // Very low limits
        
        engine.parse_and_add("infinite(X) :- infinite(X).").unwrap();
        
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
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("test(X) :- X = 1.").unwrap();
        engine.parse_and_add("test(X) :- X = 2.").unwrap();
        
        let solutions = engine.parse_query("test(Y).").unwrap();
        assert_eq!(solutions.len(), 2);
        
        // Extract the values that Y is bound to - FIXED VERSION
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
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("complex(f(X, Y), f(a, b)) :- X = a, Y = b.").unwrap();
        
        let solutions = engine.parse_query("complex(f(a, b), Z).").unwrap();
        assert_eq!(solutions.len(), 1);
        
        // Test unification failure
        let solutions = engine.parse_query("complex(f(c, d), f(a, b)).").unwrap();
        assert_eq!(solutions.len(), 0);
    }

    #[test]
    fn test_list_predicates() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("parent(tom, bob).").unwrap();
        engine.parse_and_add("parent(bob, ann).").unwrap();
        engine.parse_and_add("likes(mary, wine).").unwrap();
        
        let predicates = engine.list_predicates();
        assert_eq!(predicates.len(), 2); // parent/2 and likes/2
        
        let builtins = engine.list_builtins();
        assert!(!builtins.is_empty());
        
        // Check that some expected built-ins are there
        let builtin_names: Vec<&String> = builtins.iter().map(|(name, _, _)| name).collect();
        assert!(builtin_names.contains(&&"append".to_string()));
        assert!(builtin_names.contains(&&"is".to_string()));
    }

    #[test]
    fn test_execution_context() {
        let mut context = ExecutionContext::new();
        
        assert_eq!(context.get_stack_depth(), 0);
        assert!(!context.is_cut_called());
        
        context.enter_predicate("test/1".to_string()).unwrap();
        assert_eq!(context.get_stack_depth(), 1);
        assert_eq!(context.get_current_predicate(), "test/1");
        
        context.cut();
        assert!(context.is_cut_called());
        
        context.reset_cut();
        assert!(!context.is_cut_called());
        
        context.exit_predicate();
        assert_eq!(context.get_stack_depth(), 0);
    }

    #[test]
    fn test_context_stack_overflow() {
        let mut context = ExecutionContext::with_max_depth(2);
        
        context.enter_predicate("pred1".to_string()).unwrap();
        context.enter_predicate("pred2".to_string()).unwrap();
        
        let result = context.enter_predicate("pred3".to_string());
        assert!(result.is_err());
        
        if let Err(RuntimeError::StackOverflow { depth, predicate }) = result {
            assert_eq!(depth, 3);
            assert_eq!(predicate, "pred3");
        } else {
            panic!("Expected StackOverflow error");
        }
    }

    #[test]
    fn test_engine_configuration() {
        let mut engine = PrologEngine::with_config(50, 200);
        
        assert_eq!(engine.max_solutions, 50);
        assert_eq!(engine.get_stats().max_stack_depth, 200);
        
        engine.set_max_solutions(75);
        engine.set_max_stack_depth(150);
        
        assert_eq!(engine.max_solutions, 75);
        assert_eq!(engine.get_stats().max_stack_depth, 150);
    }

    #[test]
    fn test_stats_tracking() {
        let mut engine = PrologEngine::new();
        
        // Add clauses and track stats
        engine.parse_and_add("fact(a).").unwrap();
        engine.parse_and_add("fact(b).").unwrap();
        engine.parse_and_add("rule(X) :- fact(X).").unwrap();
        
        let stats = engine.get_stats();
        assert_eq!(stats.clause_count, 3);
        assert_eq!(stats.predicate_count(), 2); // fact/1 and rule/1
        
        if let Some((pred, count)) = stats.most_common_predicate() {
            assert_eq!(pred, "fact/1");
            assert_eq!(count, 2);
        }
        
        // Test query tracking
        engine.parse_query("fact(a).").unwrap();
        engine.parse_query("rule(X).").unwrap();
        
        assert_eq!(engine.get_stats().queries_executed, 2);
    }

    #[test]
    fn test_clear_database() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("fact(a).").unwrap();
        engine.parse_and_add("fact(b).").unwrap();
        
        assert_eq!(engine.clauses.len(), 2);
        assert_eq!(engine.get_stats().clause_count, 2);
        
        engine.clear();
        
        assert_eq!(engine.clauses.len(), 0);
        assert_eq!(engine.get_stats().clause_count, 0);
        assert_eq!(engine.get_stats().predicate_count(), 0);
    }

    #[test]
    fn test_reset_stats() {
        let mut engine = PrologEngine::new();
        
        engine.parse_and_add("fact(a).").unwrap();
        engine.parse_query("fact(a).").unwrap();
        
        assert_eq!(engine.get_stats().queries_executed, 1);
        
        engine.reset_stats();
        
        assert_eq!(engine.get_stats().queries_executed, 0);
        assert_eq!(engine.get_stats().clause_count, 1); // Clauses still there
    }
}