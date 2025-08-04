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
    pub fn format_term(term: &Term, indent: usize) -> String {
        let spaces = " ".repeat(indent);
        match term {
            Term::Atom(name) => name.clone(),
            Term::Variable(name) => name.clone(),
            Term::Number(n) => n.to_string(),
            Term::Compound(functor, args) => {
                if args.is_empty() {
                    functor.clone()
                } else if args.len() == 1 {
                    format!("{}({})", functor, Self::format_term(&args[0], 0))
                } else {
                    let formatted_args: Vec<String> = args.iter()
                        .map(|arg| Self::format_term(arg, indent + 2))
                        .collect();
                    
                    if formatted_args.iter().map(|s| s.len()).sum::<usize>() < 60 {
                        // Short format - single line
                        format!("{}({})", functor, formatted_args.join(", "))
                    } else {
                        // Long format - multiple lines
                        format!("{}(\n{}{}\n{})", 
                               functor,
                               spaces,
                               formatted_args.join(&format!(",\n{}", spaces)),
                               " ".repeat(indent.saturating_sub(2)))
                    }
                }
            }
        }
    }
    
    /// Format a clause with proper indentation
    pub fn format_clause(clause: &Clause, indent: usize) -> String {
        let head_str = Self::format_term(&clause.head, indent);
        
        if clause.body.is_empty() {
            format!("{}.", head_str)
        } else {
            let body_strs: Vec<String> = clause.body.iter()
                .map(|goal| Self::format_term(goal, indent + 4))
                .collect();
            
            if body_strs.iter().map(|s| s.len()).sum::<usize>() < 60 {
                // Short format
                format!("{} :- {}.", head_str, body_strs.join(", "))
            } else {
                // Long format with line breaks
                let spaces = " ".repeat(indent + 4);
                format!("{} :-\n{}{}.)", 
                       head_str,
                       spaces,
                       body_strs.join(&format!(",\n{}", spaces)))
            }
        }
    }
    
    /// Format a substitution in a readable way
    pub fn format_substitution(subst: &Substitution) -> String {
        if subst.is_empty() {
            "{}".to_string()
        } else {
            let mut bindings: Vec<String> = subst.iter()
                .map(|(var, term)| format!("{} -> {}", var, Self::format_term(term, 0)))
                .collect();
            bindings.sort(); // Sort for consistent output
            format!("{{{}}}", bindings.join(", "))
        }
    }
    
    /// Format multiple solutions in a table-like format
    pub fn format_solutions(solutions: &[Substitution], variables: &[String]) -> String {
        if solutions.is_empty() {
            return "No solutions.".to_string();
        }
        
        if variables.is_empty() {
            return format!("{} solution(s): true", solutions.len());
        }
        
        let mut result = String::new();
        result.push_str(&format!("Found {} solution(s):\n", solutions.len()));
        
        // Calculate column widths
        let mut col_widths: HashMap<String, usize> = HashMap::new();
        for var in variables {
            col_widths.insert(var.clone(), var.len());
        }
        
        for solution in solutions {
            for var in variables {
                if let Some(term) = solution.get(var) {
                    let term_str = Self::format_term(term, 0);
                    let current_width = col_widths.get(var).unwrap_or(&0);
                    if term_str.len() > *current_width {
                        col_widths.insert(var.clone(), term_str.len());
                    }
                }
            }
        }
        
        // Header
        for (i, var) in variables.iter().enumerate() {
            if i > 0 { result.push_str(" | "); }
            let width = col_widths.get(var).copied().unwrap_or(var.len());
            result.push_str(&format!("{:width$}", var, width = width));
        }
        result.push('\n');
        
        // Separator
        for (i, var) in variables.iter().enumerate() {
            if i > 0 { result.push_str("-+-"); }
            let width = col_widths.get(var).copied().unwrap_or(var.len());
            result.push_str(&"-".repeat(width));
        }
        result.push('\n');
        
        // Solutions
        for solution in solutions {
            for (i, var) in variables.iter().enumerate() {
                if i > 0 { result.push_str(" | "); }
                let width = col_widths.get(var).copied().unwrap_or(var.len());
                
                if let Some(term) = solution.get(var) {
                    let term_str = Self::format_term(term, 0);
                    result.push_str(&format!("{:width$}", term_str, width = width));
                } else {
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
    pub fn get_all_variables(term: &Term) -> HashSet<String> {
        let mut vars = HashSet::new();
        Self::collect_variables(term, &mut vars);
        vars
    }
    
    fn collect_variables(term: &Term, vars: &mut HashSet<String>) {
        match term {
            Term::Variable(var) => {
                vars.insert(var.clone());
            }
            Term::Compound(_, args) => {
                for arg in args {
                    Self::collect_variables(arg, vars);
                }
            }
            _ => {}
        }
    }
    
    /// Count the depth of nested terms
    pub fn term_depth(term: &Term) -> usize {
        match term {
            Term::Compound(_, args) => {
                if args.is_empty() {
                    1
                } else {
                    1 + args.iter().map(|arg| Self::term_depth(arg)).max().unwrap_or(0)
                }
            }
            _ => 1,
        }
    }
    
    /// Count the total number of subterms
    pub fn term_size(term: &Term) -> usize {
        match term {
            Term::Compound(_, args) => {
                1 + args.iter().map(|arg| Self::term_size(arg)).sum::<usize>()
            }
            _ => 1,
        }
    }
    
    /// Check if a term contains a specific variable
    pub fn contains_variable(term: &Term, var_name: &str) -> bool {
        match term {
            Term::Variable(var) => var == var_name,
            Term::Compound(_, args) => {
                args.iter().any(|arg| Self::contains_variable(arg, var_name))
            }
            _ => false,
        }
    }
    
    /// Replace all occurrences of a variable with a term
    pub fn replace_variable(term: &Term, var_name: &str, replacement: &Term) -> Term {
        match term {
            Term::Variable(var) if var == var_name => replacement.clone(),
            Term::Compound(functor, args) => {
                let new_args: Vec<Term> = args.iter()
                    .map(|arg| Self::replace_variable(arg, var_name, replacement))
                    .collect();
                Term::Compound(functor.clone(), new_args)
            }
            _ => term.clone(),
        }
    }
    
    /// Check if a term is ground (contains no variables)
    pub fn is_ground(term: &Term) -> bool {
        match term {
            Term::Variable(_) => false,
            Term::Compound(_, args) => args.iter().all(|arg| Self::is_ground(arg)),
            _ => true,
        }
    }
    
    /// Convert a Prolog list term to a Rust Vec
    pub fn list_to_vec(term: &Term) -> Option<Vec<Term>> {
        let mut elements = Vec::new();
        let mut current = term;
        
        loop {
            match current {
                Term::Atom(name) if name == "[]" => return Some(elements),
                Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                    elements.push(args[0].clone());
                    current = &args[1];
                }
                _ => return None,
            }
        }
    }
    
    /// Convert a Rust Vec to a Prolog list term
    pub fn vec_to_list(elements: Vec<Term>) -> Term {
        elements.into_iter().rev().fold(
            Term::Atom("[]".to_string()),
            |acc, elem| Term::Compound(".".to_string(), vec![elem, acc])
        )
    }
    
    /// Generate a fresh variable name not present in the given set
    pub fn fresh_variable(existing_vars: &HashSet<String>, base_name: &str) -> String {
        let mut counter = 0;
        loop {
            let candidate = if counter == 0 {
                base_name.to_string()
            } else {
                format!("{}{}", base_name, counter)
            };
            
            if !existing_vars.contains(&candidate) {
                return candidate;
            }
            counter += 1;
        }
    }
}

/// Clause analysis utilities
pub struct ClauseUtils;

impl ClauseUtils {
    /// Group clauses by predicate (functor/arity)
    pub fn group_by_predicate(clauses: &[Clause]) -> HashMap<String, Vec<&Clause>> {
        let mut groups: HashMap<String, Vec<&Clause>> = HashMap::new();
        
        for clause in clauses {
            if let Some((functor, arity)) = clause.head_functor_arity() {
                let key = format!("{}/{}", functor, arity);
                groups.entry(key).or_insert_with(Vec::new).push(clause);
            }
        }
        
        groups
    }
    
    /// Find all predicates that depend on a given predicate
    pub fn find_dependencies(clauses: &[Clause], target_functor: &str, target_arity: usize) -> Vec<String> {
        let target_key = format!("{}/{}", target_functor, target_arity);
        let mut dependencies = HashSet::new();
        
        for clause in clauses {
            if Self::clause_references_predicate(clause, target_functor, target_arity) {
                if let Some((functor, arity)) = clause.head_functor_arity() {
                    let key = format!("{}/{}", functor, arity);
                    if key != target_key {
                        dependencies.insert(key);
                    }
                }
            }
        }
        
        dependencies.into_iter().collect()
    }
    
    /// Check if a clause references a specific predicate
    fn clause_references_predicate(clause: &Clause, functor: &str, arity: usize) -> bool {
        clause.body.iter().any(|goal| {
            if let Some((goal_functor, goal_arity)) = goal.functor_arity() {
                goal_functor == functor && goal_arity == arity
            } else {
                false
            }
        })
    }
    
    /// Find recursive predicates (predicates that call themselves)
    pub fn find_recursive_predicates(clauses: &[Clause]) -> Vec<String> {
        let mut recursive = Vec::new();
        
        for clause in clauses {
            if let Some((head_functor, head_arity)) = clause.head_functor_arity() {
                if Self::clause_references_predicate(clause, head_functor, head_arity) {
                    let key = format!("{}/{}", head_functor, head_arity);
                    if !recursive.contains(&key) {
                        recursive.push(key);
                    }
                }
            }
        }
        
        recursive
    }
    
    /// Validate that clauses are well-formed
    pub fn validate_clauses(clauses: &[Clause]) -> Vec<String> {
        let mut errors = Vec::new();
        
        for (i, clause) in clauses.iter().enumerate() {
            // Check head is valid
            match &clause.head {
                Term::Variable(_) => {
                    errors.push(format!("Clause {}: Head cannot be a variable", i + 1));
                }
                Term::Number(_) => {
                    errors.push(format!("Clause {}: Head cannot be a number", i + 1));
                }
                _ => {}
            }
            
            // Check for singleton variables (variables that appear only once)
            let all_vars = Self::get_clause_variables(clause);
            for var in &all_vars {
                let count = Self::count_variable_occurrences(clause, var);
                if count == 1 && !var.starts_with('_') {
                    errors.push(format!("Clause {}: Singleton variable '{}' (use '_{}' if intentional)", i + 1, var, var));
                }
            }
        }
        
        errors
    }
    
    fn get_clause_variables(clause: &Clause) -> HashSet<String> {
        let mut vars = TermUtils::get_all_variables(&clause.head);
        for goal in &clause.body {
            vars.extend(TermUtils::get_all_variables(goal));
        }
        vars
    }
    
    fn count_variable_occurrences(clause: &Clause, var_name: &str) -> usize {
        let mut count = 0;
        count += Self::count_variable_in_term(&clause.head, var_name);
        for goal in &clause.body {
            count += Self::count_variable_in_term(goal, var_name);
        }
        count
    }
    
    fn count_variable_in_term(term: &Term, var_name: &str) -> usize {
        match term {
            Term::Variable(var) if var == var_name => 1,
            Term::Compound(_, args) => {
                args.iter().map(|arg| Self::count_variable_in_term(arg, var_name)).sum()
            }
            _ => 0,
        }
    }
}

/// Engine helper utilities
pub struct EngineUtils;

impl EngineUtils {
    /// Load a Prolog program from a string with better error reporting
    pub fn load_program(engine: &mut PrologEngine, program: &str) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        let mut line_num = 1;
        
        for line in program.lines() {
            let line = line.trim();
            
            // Skip empty lines and comments
            if line.is_empty() || line.starts_with('%') {
                line_num += 1;
                continue;
            }
            
            if let Err(e) = engine.parse_and_add(line) {
                errors.push(format!("Line {}: {}", line_num, e));
            }
            
            line_num += 1;
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    /// Execute multiple queries and collect results
    pub fn batch_query(engine: &mut PrologEngine, queries: &[&str]) -> Vec<(String, Result<Vec<Substitution>, String>)> {
        let mut results = Vec::new();
        
        for query in queries {
            let query_str = if query.ends_with('.') || query.ends_with('?') {
                query.to_string()
            } else {
                format!("{}.", query)
            };
            
            let result = match engine.parse_query(&query_str) {
                Ok(solutions) => Ok(solutions),
                Err(e) => Err(format!("{}", e)),
            };
            
            results.push((query.to_string(), result));
        }
        
        results
    }
    
    /// Get detailed statistics about the engine's database
    pub fn analyze_database(engine: &PrologEngine) -> DatabaseAnalysis {
        let clauses = engine.get_clauses();
        let groups = ClauseUtils::group_by_predicate(clauses);
        
        let total_clauses = clauses.len();
        let total_predicates = groups.len();
        let recursive_predicates = ClauseUtils::find_recursive_predicates(clauses);
        
        let mut predicate_sizes: Vec<(String, usize)> = groups.iter()
            .map(|(name, clauses)| (name.clone(), clauses.len()))
            .collect();
        predicate_sizes.sort_by(|a, b| b.1.cmp(&a.1));
        
        let largest_predicate = predicate_sizes.first().cloned();
        
        // Calculate average clause size
        let total_terms: usize = clauses.iter()
            .map(|clause| {
                1 + clause.body.iter().map(|goal| TermUtils::term_size(goal)).sum::<usize>()
            })
            .sum();
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
    pub fn extract_query_variables(query: &str) -> Vec<String> {
        let mut variables = Vec::new();
        let mut chars = query.chars().peekable();
        
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
                
                if !variables.contains(&var_name) && var_name != "_" && var_name.len() > 0 {
                    variables.push(var_name);
                }
            }
        }
        
        variables
    }
}

/// Database analysis results
#[derive(Debug, Clone)]
pub struct DatabaseAnalysis {
    pub total_clauses: usize,
    pub total_predicates: usize,
    pub recursive_predicates: Vec<String>,
    pub largest_predicate: Option<(String, usize)>,
    pub average_clause_size: f64,
    pub predicate_distribution: Vec<(String, usize)>,
}

impl fmt::Display for DatabaseAnalysis {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "Database Analysis:")?;
        writeln!(f, "  Total clauses: {}", self.total_clauses)?;
        writeln!(f, "  Total predicates: {}", self.total_predicates)?;
        writeln!(f, "  Average clause size: {:.1} terms", self.average_clause_size)?;
        
        if let Some((name, count)) = &self.largest_predicate {
            writeln!(f, "  Largest predicate: {} ({} clauses)", name, count)?;
        }
        
        if !self.recursive_predicates.is_empty() {
            writeln!(f, "  Recursive predicates: {}", self.recursive_predicates.join(", "))?;
        }
        
        if self.predicate_distribution.len() <= 10 {
            writeln!(f, "  Predicate distribution:")?;
            for (name, count) in &self.predicate_distribution {
                writeln!(f, "    {}: {} clauses", name, count)?;
            }
        }
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_utils() {
        let term = Term::Compound("foo".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Compound("bar".to_string(), vec![
                Term::Variable("Y".to_string()),
                Term::Number(42)
            ])
        ]);
        
        let vars = TermUtils::get_all_variables(&term);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains("X"));
        assert!(vars.contains("Y"));
        
        assert_eq!(TermUtils::term_depth(&term), 3);
        // Fixed: The term structure is:
        // foo(X, bar(Y, 42))
        // 1. foo (compound)
        // 2. X (variable) 
        // 3. bar (compound)
        // 4. Y (variable)
        // 5. 42 (number)
        // Total: 5 subterms
        assert_eq!(TermUtils::term_size(&term), 5);
        
        assert!(TermUtils::contains_variable(&term, "X"));
        assert!(!TermUtils::contains_variable(&term, "Z"));
        
        assert!(!TermUtils::is_ground(&term));
        
        let ground_term = Term::Compound("foo".to_string(), vec![
            Term::Atom("a".to_string()),
            Term::Number(42)
        ]);
        assert!(TermUtils::is_ground(&ground_term));
    }

    #[test]
    fn test_list_conversion() {
        let list = vec![
            Term::Number(1),
            Term::Number(2),
            Term::Number(3)
        ];
        
        let prolog_list = TermUtils::vec_to_list(list.clone());
        let converted_back = TermUtils::list_to_vec(&prolog_list).unwrap();
        
        assert_eq!(converted_back, list);
    }

    #[test]
    fn test_fresh_variable() {
        let mut existing = HashSet::new();
        existing.insert("X".to_string());
        existing.insert("Y".to_string());
        existing.insert("X1".to_string());
        
        let fresh = TermUtils::fresh_variable(&existing, "X");
        assert_eq!(fresh, "X2");
        
        let fresh_new = TermUtils::fresh_variable(&existing, "Z");
        assert_eq!(fresh_new, "Z");
    }

    #[test]
    fn test_pretty_printer() {
        let term = Term::Compound("foo".to_string(), vec![
            Term::Atom("bar".to_string()),
            Term::Variable("X".to_string())
        ]);
        
        let formatted = PrettyPrinter::format_term(&term, 0);
        assert_eq!(formatted, "foo(bar, X)");
        
        let subst = {
            let mut s = HashMap::new();
            s.insert("X".to_string(), Term::Number(42));
            s.insert("Y".to_string(), Term::Atom("hello".to_string()));
            s
        };
        
        let formatted_subst = PrettyPrinter::format_substitution(&subst);
        assert!(formatted_subst.contains("X -> 42"));
        assert!(formatted_subst.contains("Y -> hello"));
    }

    #[test]
    fn test_clause_utils() {
        let clause1 = Clause::fact(Term::Compound("parent".to_string(), vec![
            Term::Atom("tom".to_string()),
            Term::Atom("bob".to_string())
        ]));
        
        let clause2 = Clause::rule(
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
        
        let clauses = vec![clause1, clause2];
        let groups = ClauseUtils::group_by_predicate(&clauses);
        
        assert_eq!(groups.len(), 2);
        assert!(groups.contains_key("parent/2"));
        assert!(groups.contains_key("grandparent/2"));
        
        let deps = ClauseUtils::find_dependencies(&clauses, "parent", 2);
        assert!(deps.contains(&"grandparent/2".to_string()));
    }
}