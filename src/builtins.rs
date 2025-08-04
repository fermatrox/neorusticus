// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: builtins.rs
// Creator: Jonas Forsman

//! Built-in predicates for the Prolog engine
//! 
//! This module provides all the built-in predicates that are available in the Prolog system,
//! including arithmetic operations, unification, type checking, list operations, and control
//! predicates. Each predicate is implemented with proper error handling and type checking.

use crate::ast::Term;
use crate::error::{RuntimeError, RuntimeResult, levenshtein_distance};
use crate::unification::{Unifier, Substitution};

/// Built-in predicate handler
pub struct BuiltinPredicates;

impl BuiltinPredicates {
    /// Check if a predicate is built-in
    pub fn is_builtin(functor: &str, arity: usize) -> bool {
        match (functor, arity) {
            // Arithmetic predicates
            ("is", 2) | ("=:=", 2) | ("=\\=", 2) | (">", 2) | ("<", 2) | (">=", 2) | ("=<", 2) => true,
            
            // Unification predicates
            ("=", 2) | ("\\=", 2) => true,
            
            // Type checking predicates
            ("var", 1) | ("nonvar", 1) | ("atom", 1) | ("number", 1) | ("compound", 1) => true,
            
            // List operations
            ("append", 3) | ("member", 2) | ("length", 2) => true,
            
            // Control predicates
            ("true", 0) | ("fail", 0) | ("!", 0) => true,
            
            // I/O predicates (basic)
            ("write", 1) | ("nl", 0) => true,
            
            _ => false,
        }
    }
    
    /// Execute a built-in predicate
    pub fn execute(
        goal: &Term, 
        subst: &mut Substitution, 
        solutions: &mut Vec<Substitution>,
        context: &mut crate::engine::ExecutionContext
    ) -> RuntimeResult<()> {
        match goal {
            Term::Compound(functor, args) => {
                match (functor.as_str(), args.len()) {
                    // Arithmetic predicates
                    ("is", 2) => Self::handle_is(&args[0], &args[1], subst, solutions)?,
                    ("=:=", 2) => Self::handle_arithmetic_equal(&args[0], &args[1], subst, solutions)?,
                    ("=\\=", 2) => Self::handle_arithmetic_not_equal(&args[0], &args[1], subst, solutions)?,
                    (">", 2) => Self::handle_greater(&args[0], &args[1], subst, solutions)?,
                    ("<", 2) => Self::handle_less(&args[0], &args[1], subst, solutions)?,
                    (">=", 2) => Self::handle_greater_equal(&args[0], &args[1], subst, solutions)?,
                    ("=<", 2) => Self::handle_less_equal(&args[0], &args[1], subst, solutions)?,
                    
                    // Unification predicates
                    ("=", 2) => Self::handle_unify(&args[0], &args[1], subst, solutions),
                    ("\\=", 2) => Self::handle_not_unify(&args[0], &args[1], subst, solutions),
                    
                    // Type checking predicates
                    ("var", 1) => Self::handle_var(&args[0], subst, solutions),
                    ("nonvar", 1) => Self::handle_nonvar(&args[0], subst, solutions),
                    ("atom", 1) => Self::handle_atom(&args[0], subst, solutions),
                    ("number", 1) => Self::handle_number(&args[0], subst, solutions),
                    ("compound", 1) => Self::handle_compound(&args[0], subst, solutions),
                    
                    // List operations
                    ("append", 3) => Self::handle_append(&args[0], &args[1], &args[2], subst, solutions)?,
                    ("member", 2) => Self::handle_member(&args[0], &args[1], subst, solutions)?,
                    ("length", 2) => Self::handle_length(&args[0], &args[1], subst, solutions)?,
                    
                    // I/O predicates
                    ("write", 1) => Self::handle_write(&args[0], subst, solutions),
                    
                    _ => return Err(RuntimeError::PredicateNotFound {
                        functor: functor.clone(),
                        arity: args.len(),
                        suggestion: Self::suggest_predicate(functor, args.len()),
                    }),
                }
            }
            Term::Atom(functor) => {
                match functor.as_str() {
                    "true" => solutions.push(subst.clone()),
                    "fail" => {} // Don't add any solutions
                    "!" => {
                        // Cut: succeed and set cut flag
                        context.cut();
                        solutions.push(subst.clone());
                    }
                    "nl" => {
                        println!(); // Print newline
                        solutions.push(subst.clone());
                    }
                    _ => return Err(RuntimeError::PredicateNotFound {
                        functor: functor.clone(),
                        arity: 0,
                        suggestion: Self::suggest_predicate(functor, 0),
                    }),
                }
            }
            _ => return Err(RuntimeError::TypeMismatch {
                expected: "compound term or atom".to_string(),
                found: goal.clone(),
                context: "predicate call".to_string(),
            }),
        }
        Ok(())
    }
    
    /// Suggest similar predicate names for typos
    fn suggest_predicate(functor: &str, arity: usize) -> Option<String> {
        let known_predicates = vec![
            ("is", 2), ("=:=", 2), ("=\\=", 2), (">", 2), ("<", 2), (">=", 2), ("=<", 2),
            ("=", 2), ("\\=", 2), ("var", 1), ("nonvar", 1), ("atom", 1), ("number", 1),
            ("compound", 1), ("append", 3), ("member", 2), ("length", 2), ("true", 0), 
            ("fail", 0), ("write", 1), ("nl", 0)
        ];
        
        let mut best_match = None;
        let mut best_score = f64::MAX;
        
        for (pred_name, pred_arity) in known_predicates {
            // Calculate name similarity using Levenshtein distance
            let name_distance = levenshtein_distance(functor, pred_name) as f64;
            
            // Calculate arity penalty - exact arity match gets no penalty
            let arity_penalty = if arity == pred_arity {
                0.0
            } else {
                (arity as i32 - pred_arity as i32).abs() as f64 * 0.5
            };
            
            let total_score = name_distance + arity_penalty;
            
            // Only suggest if the name is reasonably similar (distance <= 3)
            if name_distance <= 3.0 && total_score < best_score {
                best_score = total_score;
                best_match = Some(format!("{}/{}", pred_name, pred_arity));
            }
        }
        
        // Only return suggestion if the score is reasonable
        if best_score <= 4.0 {
            best_match
        } else {
            None
        }
    }
    
    // Arithmetic evaluation with comprehensive error handling
    fn evaluate_arithmetic(term: &Term, subst: &Substitution) -> RuntimeResult<i64> {
        let resolved = Unifier::apply_substitution(term, subst);
        match &resolved {
            Term::Number(n) => Ok(*n),
            Term::Variable(var) => Err(RuntimeError::UninstantiatedVariable {
                variable: var.clone(),
                context: "arithmetic evaluation".to_string(),
            }),
            Term::Compound(op, args) => {
                match (op.as_str(), args.len()) {
                    ("+", 2) => {
                        let left = Self::evaluate_arithmetic(&args[0], subst)?;
                        let right = Self::evaluate_arithmetic(&args[1], subst)?;
                        left.checked_add(right).ok_or_else(|| RuntimeError::ArithmeticError {
                            operation: "+".to_string(),
                            operands: args.clone(),
                            reason: "Integer overflow".to_string(),
                        })
                    }
                    ("-", 2) => {
                        let left = Self::evaluate_arithmetic(&args[0], subst)?;
                        let right = Self::evaluate_arithmetic(&args[1], subst)?;
                        left.checked_sub(right).ok_or_else(|| RuntimeError::ArithmeticError {
                            operation: "-".to_string(),
                            operands: args.clone(),
                            reason: "Integer overflow".to_string(),
                        })
                    }
                    ("-", 1) => {
                        // Unary minus
                        let operand = Self::evaluate_arithmetic(&args[0], subst)?;
                        operand.checked_neg().ok_or_else(|| RuntimeError::ArithmeticError {
                            operation: "unary -".to_string(),
                            operands: args.clone(),
                            reason: "Integer overflow".to_string(),
                        })
                    }
                    ("*", 2) => {
                        let left = Self::evaluate_arithmetic(&args[0], subst)?;
                        let right = Self::evaluate_arithmetic(&args[1], subst)?;
                        left.checked_mul(right).ok_or_else(|| RuntimeError::ArithmeticError {
                            operation: "*".to_string(),
                            operands: args.clone(),
                            reason: "Integer overflow".to_string(),
                        })
                    }
                    ("//", 2) => {
                        let left = Self::evaluate_arithmetic(&args[0], subst)?;
                        let right = Self::evaluate_arithmetic(&args[1], subst)?;
                        if right == 0 {
                            Err(RuntimeError::DivisionByZero {
                                expression: resolved.clone(),
                            })
                        } else {
                            Ok(left / right)
                        }
                    }
                    ("mod", 2) => {
                        let left = Self::evaluate_arithmetic(&args[0], subst)?;
                        let right = Self::evaluate_arithmetic(&args[1], subst)?;
                        if right == 0 {
                            Err(RuntimeError::DivisionByZero {
                                expression: resolved.clone(),
                            })
                        } else {
                            Ok(left % right)
                        }
                    }
                    ("abs", 1) => {
                        let operand = Self::evaluate_arithmetic(&args[0], subst)?;
                        Ok(operand.abs())
                    }
                    ("max", 2) => {
                        let left = Self::evaluate_arithmetic(&args[0], subst)?;
                        let right = Self::evaluate_arithmetic(&args[1], subst)?;
                        Ok(left.max(right))
                    }
                    ("min", 2) => {
                        let left = Self::evaluate_arithmetic(&args[0], subst)?;
                        let right = Self::evaluate_arithmetic(&args[1], subst)?; 
                        Ok(left.min(right))
                    }
                    _ => Err(RuntimeError::TypeMismatch {
                        expected: "arithmetic expression".to_string(),
                        found: resolved.clone(),
                        context: "arithmetic evaluation".to_string(),
                    }),
                }
            }
            _ => Err(RuntimeError::TypeMismatch {
                expected: "number or arithmetic expression".to_string(),
                found: resolved.clone(),
                context: "arithmetic evaluation".to_string(),
            }),
        }
    }
    
    // Arithmetic predicates
    fn handle_is(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let value = Self::evaluate_arithmetic(right, subst)?;
        let result_term = Term::Number(value);
        let mut new_subst = subst.clone();
        if Unifier::unify(left, &result_term, &mut new_subst) {
            solutions.push(new_subst);
        }
        Ok(())
    }
    
    fn handle_arithmetic_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val == right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    fn handle_arithmetic_not_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val != right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    fn handle_greater(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val > right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    fn handle_less(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val < right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    fn handle_greater_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val >= right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    fn handle_less_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val <= right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    // Unification predicates
    fn handle_unify(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let mut new_subst = subst.clone();
        if Unifier::unify(left, right, &mut new_subst) {
            solutions.push(new_subst);
        }
    }
    
    fn handle_not_unify(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let mut test_subst = subst.clone();
        if !Unifier::unify(left, right, &mut test_subst) {
            solutions.push(subst.clone());
        }
    }
    
    // Type checking predicates
    fn handle_var(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Variable(_)) {
            solutions.push(subst.clone());
        }
    }
    
    fn handle_nonvar(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if !matches!(resolved, Term::Variable(_)) {
            solutions.push(subst.clone());
        }
    }
    
    fn handle_atom(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Atom(_)) {
            solutions.push(subst.clone());
        }
    }
    
    fn handle_number(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Number(_)) {
            solutions.push(subst.clone());
        }
    }
    
    fn handle_compound(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Compound(_, _)) {
            solutions.push(subst.clone());
        }
    }
    
    // List operations
    fn handle_append(list1: &Term, list2: &Term, result: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        // append([], L, L).
        let mut subst1 = subst.clone();
        let empty_list = Term::Atom("[]".to_string());
        if Unifier::unify(list1, &empty_list, &mut subst1) && 
           Unifier::unify(list2, result, &mut subst1) {
            solutions.push(subst1);
        }
        
        // append([H|T], L, [H|R]) :- append(T, L, R).
        // Use a counter to generate unique variable names
        let var_suffix = format!("_{}", solutions.len() + subst.len()); // More unique suffix
        let h_var = Term::Variable(format!("H{}", var_suffix));
        let t_var = Term::Variable(format!("T{}", var_suffix));
        let r_var = Term::Variable(format!("R{}", var_suffix));
        
        let list1_pattern = Term::Compound(".".to_string(), vec![h_var.clone(), t_var.clone()]);
        let result_pattern = Term::Compound(".".to_string(), vec![h_var.clone(), r_var.clone()]);
        
        let mut subst2 = subst.clone();
        if Unifier::unify(list1, &list1_pattern, &mut subst2) && 
           Unifier::unify(result, &result_pattern, &mut subst2) {
            
            // Apply substitutions to get the actual terms for recursion
            let resolved_t = Unifier::apply_substitution(&t_var, &subst2);
            let resolved_list2 = Unifier::apply_substitution(list2, &subst2);
            let resolved_r = Unifier::apply_substitution(&r_var, &subst2);
            
            // Add depth check to prevent infinite recursion
            if Self::get_list_length(&resolved_t).unwrap_or(0) < 100 { // Safety limit
                // Recursive call: append(T, L, R)
                Self::handle_append(&resolved_t, &resolved_list2, &resolved_r, &mut subst2, solutions)?;
            }
        }
        Ok(())
    }
    
    // Helper function to safely get list length
    fn get_list_length(term: &Term) -> Option<usize> {
        match term {
            Term::Atom(name) if name == "[]" => Some(0),
            Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                Self::get_list_length(&args[1]).map(|len| len + 1)
            }
            _ => None, // Not a proper list or contains variables
        }
    }
    
    fn handle_member(element: &Term, list: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let resolved_list = Unifier::apply_substitution(list, subst);
        
        match resolved_list {
            Term::Compound(ref functor, ref args) if functor == "." && args.len() == 2 => {
                // member(X, [H|T]) :- X = H.
                let mut subst1 = subst.clone();
                if Unifier::unify(element, &args[0], &mut subst1) {
                    solutions.push(subst1);
                }
                
                // member(X, [H|T]) :- member(X, T).
                Self::handle_member(element, &args[1], subst, solutions)?;
            }
            Term::Atom(ref name) if name == "[]" => {
                // Empty list - member fails
            }
            Term::Variable(_) => {
                return Err(RuntimeError::UninstantiatedVariable {
                    variable: format!("{}", resolved_list),
                    context: "member/2 second argument".to_string(),
                });
            }
            _ => {
                return Err(RuntimeError::InvalidListStructure {
                    term: resolved_list,
                    expected: "proper list".to_string(),
                });
            }
        }
        Ok(())
    }
    
    fn handle_length(list: &Term, length: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let resolved_list = Unifier::apply_substitution(list, subst);
        
        match Self::calculate_list_length(&resolved_list) {
            Ok(len) => {
                let length_term = Term::Number(len);
                let mut new_subst = subst.clone();
                if Unifier::unify(length, &length_term, &mut new_subst) {
                    solutions.push(new_subst);
                }
            }
            Err(e) => return Err(e),
        }
        Ok(())
    }
    
    fn calculate_list_length(list: &Term) -> RuntimeResult<i64> {
        match list {
            Term::Atom(name) if name == "[]" => Ok(0),
            Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                let tail_len = Self::calculate_list_length(&args[1])?;
                Ok(tail_len + 1)
            }
            Term::Variable(_) => Err(RuntimeError::UninstantiatedVariable {
                variable: format!("{}", list),
                context: "length/2 first argument".to_string(),
            }),
            _ => Err(RuntimeError::InvalidListStructure {
                term: list.clone(),
                expected: "proper list".to_string(),
            }),
        }
    }
    
    // I/O predicates
    fn handle_write(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        print!("{}", resolved);
        solutions.push(subst.clone());
    }
    
    /// Get a list of all available built-in predicates
    pub fn list_builtins() -> Vec<(String, usize, String)> {
        vec![
            // Arithmetic
            ("is".to_string(), 2, "Arithmetic evaluation".to_string()),
            ("=:=".to_string(), 2, "Arithmetic equality".to_string()),
            ("=\\=".to_string(), 2, "Arithmetic inequality".to_string()),
            (">".to_string(), 2, "Greater than".to_string()),
            ("<".to_string(), 2, "Less than".to_string()),
            (">=".to_string(), 2, "Greater than or equal".to_string()),
            ("=<".to_string(), 2, "Less than or equal".to_string()),
            
            // Unification
            ("=".to_string(), 2, "Unification".to_string()),
            ("\\=".to_string(), 2, "Non-unification".to_string()),
            
            // Type checking
            ("var".to_string(), 1, "Test if term is variable".to_string()),
            ("nonvar".to_string(), 1, "Test if term is not variable".to_string()),
            ("atom".to_string(), 1, "Test if term is atom".to_string()),
            ("number".to_string(), 1, "Test if term is number".to_string()),
            ("compound".to_string(), 1, "Test if term is compound".to_string()),
            
            // List operations
            ("append".to_string(), 3, "List concatenation".to_string()),
            ("member".to_string(), 2, "List membership".to_string()),
            ("length".to_string(), 2, "List length".to_string()),
            
            // Control
            ("true".to_string(), 0, "Always succeeds".to_string()),
            ("fail".to_string(), 0, "Always fails".to_string()),
            ("!".to_string(), 0, "Cut (prevents backtracking)".to_string()),
            
            // I/O
            ("write".to_string(), 1, "Write term to output".to_string()),
            ("nl".to_string(), 0, "Write newline".to_string()),
        ]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    fn create_test_context() -> crate::engine::ExecutionContext {
        crate::engine::ExecutionContext::new()
    }

    #[test]
    fn test_is_builtin() {
        assert!(BuiltinPredicates::is_builtin("is", 2));
        assert!(BuiltinPredicates::is_builtin("append", 3));
        assert!(BuiltinPredicates::is_builtin("!", 0));
        assert!(!BuiltinPredicates::is_builtin("unknown", 1));
    }

    #[test]
    fn test_arithmetic_is() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        let left = Term::Variable("X".to_string());
        let right = Term::Compound("+".to_string(), vec![
            Term::Number(2),
            Term::Number(3)
        ]);
        
        BuiltinPredicates::handle_is(&left, &right, &mut subst, &mut solutions).unwrap();
        
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0].get("X"), Some(&Term::Number(5)));
    }

    #[test]
    fn test_arithmetic_comparison() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        let left = Term::Number(5);
        let right = Term::Number(3);
        
        BuiltinPredicates::handle_greater(&left, &right, &mut subst, &mut solutions).unwrap();
        assert_eq!(solutions.len(), 1);
        
        solutions.clear();
        BuiltinPredicates::handle_less(&left, &right, &mut subst, &mut solutions).unwrap();
        assert_eq!(solutions.len(), 0);
    }

    #[test]
    fn test_unification() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        let term1 = Term::Variable("X".to_string());
        let term2 = Term::Atom("hello".to_string());
        
        BuiltinPredicates::handle_unify(&term1, &term2, &mut subst, &mut solutions);
        
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0].get("X"), Some(&Term::Atom("hello".to_string())));
    }

    #[test]
    fn test_type_checking() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        let var = Term::Variable("X".to_string());
        let atom = Term::Atom("hello".to_string());
        
        // Test var/1
        BuiltinPredicates::handle_var(&var, &mut subst, &mut solutions);
        assert_eq!(solutions.len(), 1);
        
        solutions.clear();
        BuiltinPredicates::handle_var(&atom, &mut subst, &mut solutions);
        assert_eq!(solutions.len(), 0);
        
        // Test atom/1
        solutions.clear();
        BuiltinPredicates::handle_atom(&atom, &mut subst, &mut solutions);
        assert_eq!(solutions.len(), 1);
    }

    #[test]
    fn test_list_append() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        let list1 = Term::from_list(vec![Term::Number(1), Term::Number(2)]);
        let list2 = Term::from_list(vec![Term::Number(3)]);
        let result = Term::Variable("X".to_string());
        
        BuiltinPredicates::handle_append(&list1, &list2, &result, &mut subst, &mut solutions).unwrap();
        
        assert!(solutions.len() > 0, "Should find at least one solution");
        
        // Check that we can find the appended result
        let mut found_correct_result = false;
        for solution in &solutions {
            if let Some(x_binding) = solution.get("X") {
                let resolved = Unifier::apply_substitution(x_binding, solution);
                if let Some(elements) = resolved.to_list() {
                    if elements.len() == 3 &&
                       elements[0] == Term::Number(1) &&
                       elements[1] == Term::Number(2) &&
                       elements[2] == Term::Number(3) {
                        found_correct_result = true;
                        break;
                    }
                }
            }
        }
        
        assert!(found_correct_result, "Should find the correct append result [1,2,3]");
        
        // Test the base case: append([], [3], X)
        solutions.clear();
        subst.clear();
        let empty_list = Term::Atom("[]".to_string());
        BuiltinPredicates::handle_append(&empty_list, &list2, &result, &mut subst, &mut solutions).unwrap();
        
        assert_eq!(solutions.len(), 1, "Empty list append should have exactly one solution");
        if let Some(x_binding) = solutions[0].get("X") {
            let resolved = Unifier::apply_substitution(x_binding, &solutions[0]);
            if let Some(elements) = resolved.to_list() {
                assert_eq!(elements.len(), 1);
                assert_eq!(elements[0], Term::Number(3));
            } else {
                panic!("Result should be a proper list");
            }
        }
    }

    #[test]
    fn test_list_member() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        let element = Term::Number(2);
        let list = Term::from_list(vec![Term::Number(1), Term::Number(2), Term::Number(3)]);
        
        BuiltinPredicates::handle_member(&element, &list, &mut subst, &mut solutions).unwrap();
        
        assert!(solutions.len() > 0); // Should find the element
        
        // Test non-member
        solutions.clear();
        let non_element = Term::Number(4);
        BuiltinPredicates::handle_member(&non_element, &list, &mut subst, &mut solutions).unwrap();
        assert_eq!(solutions.len(), 0); // Should not find the element
    }

    #[test]
    fn test_list_length() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        let list = Term::from_list(vec![Term::Number(1), Term::Number(2), Term::Number(3)]);
        let length = Term::Variable("L".to_string());
        
        BuiltinPredicates::handle_length(&list, &length, &mut subst, &mut solutions).unwrap();
        
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0].get("L"), Some(&Term::Number(3)));
    }

    #[test]
    fn test_control_predicates() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        let mut context = create_test_context();
        
        // Test true/0
        let true_goal = Term::Atom("true".to_string());
        BuiltinPredicates::execute(&true_goal, &mut subst, &mut solutions, &mut context).unwrap();
        assert_eq!(solutions.len(), 1);
        
        // Test fail/0
        solutions.clear();
        let fail_goal = Term::Atom("fail".to_string());
        BuiltinPredicates::execute(&fail_goal, &mut subst, &mut solutions, &mut context).unwrap();
        assert_eq!(solutions.len(), 0);
        
        // Test cut/0
        solutions.clear();
        context.reset_cut();
        let cut_goal = Term::Atom("!".to_string());
        BuiltinPredicates::execute(&cut_goal, &mut subst, &mut solutions, &mut context).unwrap();
        assert_eq!(solutions.len(), 1);
        assert!(context.is_cut_called());
    }

    #[test]
    fn test_arithmetic_evaluation() {
        // Test complex arithmetic expression
        let expr = Term::Compound("+".to_string(), vec![
            Term::Compound("*".to_string(), vec![Term::Number(2), Term::Number(3)]),
            Term::Number(4)
        ]);
        
        let subst = HashMap::new();
        let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap();
        assert_eq!(result, 10); // (2 * 3) + 4 = 10
    }

    #[test]
    fn test_division_by_zero() {
        let expr = Term::Compound("//".to_string(), vec![
            Term::Number(5),
            Term::Number(0)
        ]);
        
        let subst = HashMap::new();
        let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
        assert!(result.is_err());
        
        if let Err(RuntimeError::DivisionByZero { .. }) = result {
            // Expected error
        } else {
            panic!("Expected DivisionByZero error");
        }
    }

    #[test]
    fn test_uninstantiated_variable_error() {
        let expr = Term::Compound("+".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Number(1)
        ]);
        
        let subst = HashMap::new();
        let result = BuiltinPredicates::evaluate_arithmetic(&expr, &subst);
        assert!(result.is_err());
        
        if let Err(RuntimeError::UninstantiatedVariable { .. }) = result {
            // Expected error
        } else {
            panic!("Expected UninstantiatedVariable error");
        }
    }

    #[test]
    fn test_predicate_suggestions() {
        // Test typo suggestions
        let suggestion = BuiltinPredicates::suggest_predicate("lentgh", 2);
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("length"));
        
        let suggestion = BuiltinPredicates::suggest_predicate("appendd", 3);
        assert!(suggestion.is_some());
        assert!(suggestion.unwrap().contains("append"));
        
        // Test completely wrong predicate
        let suggestion = BuiltinPredicates::suggest_predicate("totally_wrong", 5);
        assert!(suggestion.is_none());
    }

    #[test]
    fn test_arithmetic_operators() {
        let subst = HashMap::new();
        
        // Test subtraction
        let expr = Term::Compound("-".to_string(), vec![Term::Number(10), Term::Number(3)]);
        assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 7);
        
        // Test multiplication
        let expr = Term::Compound("*".to_string(), vec![Term::Number(4), Term::Number(5)]);
        assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 20);
        
        // Test modulo
        let expr = Term::Compound("mod".to_string(), vec![Term::Number(17), Term::Number(5)]);
        assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 2);
        
        // Test unary minus
        let expr = Term::Compound("-".to_string(), vec![Term::Number(42)]);
        assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), -42);
    }

    #[test]
    fn test_extended_arithmetic() {
        let subst = HashMap::new();
        
        // Test abs
        let expr = Term::Compound("abs".to_string(), vec![Term::Number(-5)]);
        assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 5);
        
        // Test max
        let expr = Term::Compound("max".to_string(), vec![Term::Number(3), Term::Number(7)]);
        assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 7);
        
        // Test min
        let expr = Term::Compound("min".to_string(), vec![Term::Number(3), Term::Number(7)]);
        assert_eq!(BuiltinPredicates::evaluate_arithmetic(&expr, &subst).unwrap(), 3);
    }

    #[test]
    fn test_list_builtin_info() {
        let builtins = BuiltinPredicates::list_builtins();
        assert!(!builtins.is_empty());
        
        // Check that some expected predicates are listed
        let names: Vec<&String> = builtins.iter().map(|(name, _, _)| name).collect();
        assert!(names.contains(&&"is".to_string()));
        assert!(names.contains(&&"append".to_string()));
        assert!(names.contains(&&"member".to_string()));
        assert!(names.contains(&&"true".to_string()));
    }

    #[test]
    fn test_complex_list_operations() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        
        // Test append with variables
        let x = Term::Variable("X".to_string());
        let y = Term::Variable("Y".to_string());
        let result = Term::from_list(vec![Term::Number(1), Term::Number(2), Term::Number(3)]);
        
        BuiltinPredicates::handle_append(&x, &y, &result, &mut subst, &mut solutions).unwrap();
        
        // Should find multiple solutions for different ways to split the list
        assert!(solutions.len() > 1);
    }

    #[test]
    fn test_error_handling_in_execute() {
        let mut subst = HashMap::new();
        let mut solutions = Vec::new();
        let mut context = create_test_context();
        
        // Test unknown predicate
        let unknown_goal = Term::Compound("unknown_predicate".to_string(), vec![Term::Number(1)]);
        let result = BuiltinPredicates::execute(&unknown_goal, &mut subst, &mut solutions, &mut context);
        
        assert!(result.is_err());
        if let Err(RuntimeError::PredicateNotFound { functor, arity, .. }) = result {
            assert_eq!(functor, "unknown_predicate");
            assert_eq!(arity, 1);
        } else {
            panic!("Expected PredicateNotFound error");
        }
    }
}