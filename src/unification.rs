// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: unification.rs
// Creator: Jonas Forsman

//! Unification algorithm for Prolog terms
//! 
//! This module implements the core unification algorithm that determines
//! whether two terms can be made identical by substituting variables.
//! It includes occurs check to prevent infinite structures.

use std::collections::HashMap;
use crate::ast::Term;

/// Variable substitution map - maps variable names to their bound terms
pub type Substitution = HashMap<String, Term>;

/// Unification algorithm implementation
pub struct Unifier;

impl Unifier {
    /// Attempt to unify two terms, updating the substitution if successful
    /// 
    /// Returns true if unification succeeds, false otherwise.
    /// If successful, the substitution map is updated with any new bindings.
    /// 
    /// # Examples
    /// ```
    /// use std::collections::HashMap;
    /// use neorusticus::ast::Term;
    /// use neorusticus::unification::Unifier;
    /// 
    /// let mut subst = HashMap::new();
    /// let term1 = Term::Variable("X".to_string());
    /// let term2 = Term::Atom("hello".to_string());
    /// 
    /// assert!(Unifier::unify(&term1, &term2, &mut subst));
    /// assert_eq!(subst.get("X"), Some(&Term::Atom("hello".to_string())));
    /// ```
    pub fn unify(term1: &Term, term2: &Term, subst: &mut Substitution) -> bool {
        match (term1, term2) {
            // Variable cases - handle variable unification
            // This pattern matches when at least one term is a variable
            // The bidirectional pattern (var, term) | (term, var) ensures we catch
            // variables in either position without duplicating code
            (Term::Variable(var), term) | (term, Term::Variable(var)) => {
                Self::unify_variable(var, term, subst)
            }
            
            // Atom cases - atoms unify if they have the same name
            // This is a simple string comparison - atoms are constants in Prolog
            (Term::Atom(a1), Term::Atom(a2)) => a1 == a2,
            
            // Number cases - numbers unify if they have the same value
            // Direct integer comparison for numeric literals
            (Term::Number(n1), Term::Number(n2)) => n1 == n2,
            
            // Compound term cases - unify functor and all arguments
            // For compound terms like f(a, b), we need:
            // 1. Same functor name (f)
            // 2. Same arity (number of arguments)
            // 3. All corresponding arguments must unify recursively
            (Term::Compound(f1, args1), Term::Compound(f2, args2)) => {
                f1 == f2 && 
                args1.len() == args2.len() &&
                args1.iter().zip(args2.iter()).all(|(a1, a2)| Self::unify(a1, a2, subst))
            }
            
            // Different types don't unify
            // e.g., an atom can't unify with a number or compound term
            _ => false,
        }
    }
    
    /// Unify a variable with a term
    /// 
    /// This is the core of the unification algorithm, handling the complex cases
    /// where variables need to be bound or their existing bindings need to be unified.
    fn unify_variable(var: &str, term: &Term, subst: &mut Substitution) -> bool {
        // Case 1: Variable is already bound in the substitution
        // We need to unify the existing binding with the new term
        if let Some(existing) = subst.get(var).cloned() {
            // Recursively unify the existing binding with the term
            // This handles chains like X -> Y -> atom
            Self::unify(&existing, term, subst)
        } 
        // Case 2: Unifying with another variable
        else if let Term::Variable(other_var) = term {
            // Special case: same variable (X = X) always succeeds
            if var == other_var {
                // Don't create a self-binding, just return true
                return true;
            }
            
            // Check if the other variable is bound
            if let Some(other_binding) = subst.get(other_var).cloned() {
                // The other variable is bound, so unify our variable with its binding
                // This handles cases like: X unifies with Y, where Y -> atom
                Self::unify_variable(var, &other_binding, subst)
            } else {
                // Both variables are unbound
                // We can bind either one to the other - we choose to bind var to other_var
                // This creates: var -> other_var in the substitution
                subst.insert(var.to_string(), term.clone());
                true
            }
        } 
        // Case 3: Unifying variable with a non-variable term
        else if Self::occurs_check(var, term, subst) {
            // Occurs check failed - the variable appears in the term
            // This would create an infinite structure like X = f(X)
            // which expands to X = f(f(f(...)))
            false
        } else {
            // Safe to bind the variable to the term
            // This is the normal case: X unifies with atom, number, or compound
            subst.insert(var.to_string(), term.clone());
            true
        }
    }
    
    /// Occurs check: prevent infinite structures like X = f(X)
    /// 
    /// Returns true if the variable occurs in the term (which would be bad),
    /// false if it's safe to unify.
    /// 
    /// The occurs check is crucial for maintaining logical consistency.
    /// Without it, we could create infinite recursive structures that
    /// would cause infinite loops when trying to resolve them.
    fn occurs_check(var: &str, term: &Term, subst: &Substitution) -> bool {
        match term {
            Term::Variable(v) => {
                if v == var {
                    // Direct occurrence: the variable appears in the term
                    true 
                } else if let Some(bound_term) = subst.get(v) {
                    // This variable is bound to something else
                    // Recursively check if our variable occurs in that binding
                    // This handles chains: if Y -> f(X) and we're checking X occurs in Y
                    Self::occurs_check(var, bound_term, subst)
                } else {
                    // Different unbound variable - no occurrence
                    false
                }
            }
            Term::Compound(_, args) => {
                // For compound terms, check if the variable occurs in any argument
                // For example, checking if X occurs in f(g(X), h(Y))
                // We need to recursively check each argument
                args.iter().any(|arg| Self::occurs_check(var, arg, subst))
            }
            _ => false, // Atoms and numbers can't contain variables
        }
    }
    
    /// Apply substitutions to a term, resolving all variable bindings
    /// 
    /// This follows the substitution chain to get the final value of any variables.
    /// For example, if X -> Y and Y -> atom, applying substitution to X gives atom.
    /// 
    /// # Examples
    /// ```
    /// use std::collections::HashMap;
    /// use neorusticus::ast::Term;
    /// use neorusticus::unification::Unifier;
    /// 
    /// let mut subst = HashMap::new();
    /// subst.insert("X".to_string(), Term::Atom("hello".to_string()));
    /// 
    /// let term = Term::Variable("X".to_string());
    /// let result = Unifier::apply_substitution(&term, &subst);
    /// 
    /// assert_eq!(result, Term::Atom("hello".to_string()));
    /// ```
    pub fn apply_substitution(term: &Term, subst: &Substitution) -> Term {
        match term {
            Term::Variable(var) => {
                if let Some(replacement) = subst.get(var) {
                    // Recursively apply substitution to handle chains
                    // This is important for cases like X -> Y, Y -> Z, Z -> atom
                    // We need to follow the chain all the way to the final value
                    Self::apply_substitution(replacement, subst)
                } else {
                    // Variable is not bound, return it as-is
                    term.clone()
                }
            }
            Term::Compound(functor, args) => {
                // For compound terms, apply substitution to each argument
                // This ensures all variables in the structure are resolved
                let new_args: Vec<Term> = args.iter()
                    .map(|arg| Self::apply_substitution(arg, subst))
                    .collect();
                Term::Compound(functor.clone(), new_args)
            }
            _ => term.clone(), // Atoms and numbers are unchanged by substitution
        }
    }
    
    /// Apply substitutions to multiple terms
    pub fn apply_substitution_to_terms(terms: &[Term], subst: &Substitution) -> Vec<Term> {
        terms.iter()
            .map(|term| Self::apply_substitution(term, subst))
            .collect()
    }
    
    /// Check if two terms are unifiable without actually performing the unification
    /// 
    /// This is useful for testing unifiability without modifying any substitution.
    /// It creates a temporary substitution internally and discards it after checking.
    pub fn can_unify(term1: &Term, term2: &Term) -> bool {
        let mut temp_subst = HashMap::new();
        Self::unify(term1, term2, &mut temp_subst)
    }
    
    /// Create a renamed copy of a term with fresh variables
    /// 
    /// This is useful for avoiding variable name conflicts when using clauses.
    /// The suffix is appended to all variable names in the term.
    /// 
    /// For example, renaming f(X, Y) with suffix "_1" produces f(X_1, Y_1).
    /// This is essential when using the same clause multiple times in a proof,
    /// as each use needs fresh variables to avoid unwanted bindings.
    pub fn rename_variables(term: &Term, suffix: &str) -> Term {
        match term {
            Term::Variable(var) => {
                // Append suffix to variable name to create a fresh variable
                Term::Variable(format!("{}{}", var, suffix))
            }
            Term::Compound(functor, args) => {
                // Recursively rename variables in all arguments
                // The functor itself is not renamed (it's not a variable)
                let new_args: Vec<Term> = args.iter()
                    .map(|arg| Self::rename_variables(arg, suffix))
                    .collect();
                Term::Compound(functor.clone(), new_args)
            }
            _ => term.clone(), // Atoms and numbers don't contain variables
        }
    }
    
    /// Get all variables mentioned in the substitution (both keys and values)
    /// 
    /// This collects variables from two places:
    /// 1. The keys of the substitution (variables that are bound)
    /// 2. Any variables that appear in the values (terms that variables are bound to)
    /// 
    /// The result is sorted alphabetically for consistent output.
    pub fn get_all_variables(subst: &Substitution) -> Vec<String> {
        let mut vars = Vec::new();
        
        // Add all bound variables (keys)
        // These are the variables that have bindings in the substitution
        for var in subst.keys() {
            if !vars.contains(var) {
                vars.push(var.clone());
            }
        }
        
        // Add all variables in the values
        // A binding might be X -> f(Y, Z), so we need to find Y and Z too
        for term in subst.values() {
            for var in term.variables() {
                if !vars.contains(var) {
                    vars.push(var.clone());
                }
            }
        }
        
        vars.sort(); // Sort for consistent, predictable output
        vars
    }
    
    /// Compose two substitutions: apply subst2 to the results of subst1
    /// 
    /// Composition means: first apply subst1, then apply subst2 to the result.
    /// This is useful when combining substitutions from different unification steps.
    /// 
    /// For example:
    /// - subst1: {X -> Y}
    /// - subst2: {Y -> atom}
    /// - Result: {X -> atom, Y -> atom}
    pub fn compose_substitutions(subst1: &Substitution, subst2: &Substitution) -> Substitution {
        let mut result = HashMap::new();
        
        // Apply subst2 to all terms in subst1
        // This ensures that if subst1 has X -> Y and subst2 has Y -> atom,
        // the result will have X -> atom (not X -> Y)
        for (var, term) in subst1 {
            let new_term = Self::apply_substitution(term, subst2);
            result.insert(var.clone(), new_term);
        }
        
        // Add bindings from subst2 that aren't in subst1
        // These are new bindings that weren't affected by subst1
        for (var, term) in subst2 {
            if !result.contains_key(var) {
                result.insert(var.clone(), term.clone());
            }
        }
        
        result
    }
    
    /// Check if a substitution is idempotent (applying it twice gives the same result)
    /// 
    /// This is useful for debugging and ensuring substitutions are in normal form.
    /// A substitution is idempotent if no variable in a binding refers to another
    /// variable that's also bound in the substitution.
    /// 
    /// Non-idempotent example: {X -> Y, Y -> atom}
    /// Applying once to X gives Y, applying twice gives atom.
    /// 
    /// Idempotent example: {X -> atom, Y -> atom}
    /// Applying any number of times gives the same result.
    pub fn is_idempotent(subst: &Substitution) -> bool {
        // Track visited variables to detect cycles
        // Cycles like X -> Y, Y -> X make the substitution non-idempotent
        let mut visited = std::collections::HashSet::new();
        
        for (var, term) in subst {
            visited.clear(); // Reset for each variable we check
            if !Self::is_term_idempotent(var, term, subst, &mut visited) {
                return false;
            }
        }
        true
    }
    
    /// Helper function to check if a term is idempotent with cycle detection
    /// 
    /// This recursively checks if applying the substitution to a term would
    /// change it, while also detecting cycles that would cause infinite loops.
    fn is_term_idempotent(
        var: &str,
        term: &Term,
        subst: &Substitution,
        visited: &mut std::collections::HashSet<String>
    ) -> bool {
        // Check for cycles - if we've seen this variable before in this chain,
        // we have a cycle and the substitution is not idempotent
        if visited.contains(var) {
            return false; // Cycle detected, not idempotent
        }
        visited.insert(var.to_string());
        
        match term {
            Term::Variable(v) => {
                if let Some(next_term) = subst.get(v) {
                    // Follow the chain but detect cycles
                    // If this variable leads to another binding, check that too
                    if !Self::is_term_idempotent(v, next_term, subst, visited) {
                        return false;
                    }
                }
            }
            Term::Compound(_, args) => {
                // For compound terms, check all arguments for variables
                // that might not be idempotent
                for arg in args {
                    if let Term::Variable(v) = arg {
                        if let Some(next_term) = subst.get(v) {
                            let mut new_visited = visited.clone();
                            if !Self::is_term_idempotent(v, next_term, subst, &mut new_visited) {
                                return false;
                            }
                        }
                    }
                }
            }
            _ => {} // Atoms and numbers are always idempotent
        }
        
        // Check that applying substitution doesn't change the term
        // This is the actual idempotency check
        let applied = Self::apply_substitution_with_cycle_detection(term, subst, visited);
        match applied {
            Some(result) => &result == term,
            None => false, // Cycle detected during application
        }
    }
    
    /// Apply substitution with cycle detection to prevent infinite recursion
    /// 
    /// Returns None if a cycle is detected, Some(term) otherwise.
    /// This is a safer version of apply_substitution that won't stack overflow
    /// on circular substitutions.
    fn apply_substitution_with_cycle_detection(
        term: &Term,
        subst: &Substitution,
        visited: &std::collections::HashSet<String>
    ) -> Option<Term> {
        match term {
            Term::Variable(var) => {
                // If we've already visited this variable, we have a cycle
                if visited.contains(var) {
                    return None; // Cycle detected
                }
                if let Some(replacement) = subst.get(var) {
                    // Add this variable to visited set for cycle detection
                    let mut new_visited = visited.clone();
                    new_visited.insert(var.clone());
                    // Recursively apply with the updated visited set
                    Self::apply_substitution_with_cycle_detection(replacement, subst, &new_visited)
                } else {
                    Some(term.clone())
                }
            }
            Term::Compound(functor, args) => {
                // Apply to each argument, returning None if any has a cycle
                let mut new_args = Vec::new();
                for arg in args {
                    match Self::apply_substitution_with_cycle_detection(arg, subst, visited) {
                        Some(new_arg) => new_args.push(new_arg),
                        None => return None, // Cycle detected in argument
                    }
                }
                Some(Term::Compound(functor.clone(), new_args))
            }
            _ => Some(term.clone()), // Atoms and numbers are unchanged
        }
    }
    
    /// Remove identity bindings (X -> X) from a substitution
    /// 
    /// Identity bindings are redundant and can be safely removed.
    /// This cleans up the substitution by removing entries where a variable
    /// is bound to itself.
    /// 
    /// Note: X -> Y where X and Y are different variables is NOT an identity binding.
    /// Only X -> X (same variable name) is removed.
    pub fn remove_identity_bindings(subst: &mut Substitution) {
        subst.retain(|var, term| {
            match term {
                // Only remove if it's a variable with the same name
                Term::Variable(bound_var) => var != bound_var,
                // Keep all other bindings (atoms, numbers, compounds)
                _ => true,
            }
        });
    }
}

/// Utility functions for working with substitutions
pub mod substitution_utils {
    use super::*;
    
    /// Create a new empty substitution
    pub fn new() -> Substitution {
        HashMap::new()
    }
    
    /// Check if the substitution is empty
    pub fn is_empty(subst: &Substitution) -> bool {
        subst.is_empty()
    }
    
    /// Get the number of variable bindings
    pub fn len(subst: &Substitution) -> usize {
        subst.len()
    }
    
    /// Clear all bindings
    pub fn clear(subst: &mut Substitution) {
        subst.clear();
    }
    
    /// Pretty print a substitution for debugging
    pub fn format_substitution(subst: &Substitution) -> String {
        if subst.is_empty() {
            "{}".to_string()
        } else {
            let bindings: Vec<String> = subst.iter()
                .map(|(var, term)| format!("{} -> {}", var, term))
                .collect();
            format!("{{{}}}", bindings.join(", "))
        }
    }
}

// Link to the test module
#[cfg(test)]
#[path = "unification_tests.rs"]
mod tests;