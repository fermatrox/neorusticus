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
            (Term::Variable(var), term) | (term, Term::Variable(var)) => {
                Self::unify_variable(var, term, subst)
            }
            
            // Atom cases - atoms unify if they have the same name
            (Term::Atom(a1), Term::Atom(a2)) => a1 == a2,
            
            // Number cases - numbers unify if they have the same value
            (Term::Number(n1), Term::Number(n2)) => n1 == n2,
            
            // Compound term cases - unify functor and all arguments
            (Term::Compound(f1, args1), Term::Compound(f2, args2)) => {
                f1 == f2 && 
                args1.len() == args2.len() &&
                args1.iter().zip(args2.iter()).all(|(a1, a2)| Self::unify(a1, a2, subst))
            }
            
            // Different types don't unify
            _ => false,
        }
    }
    
    /// Unify a variable with a term
    fn unify_variable(var: &str, term: &Term, subst: &mut Substitution) -> bool {
        if let Some(existing) = subst.get(var).cloned() {
            // Variable is already bound, unify with existing binding
            Self::unify(&existing, term, subst)
        } else if let Term::Variable(other_var) = term {
            if var == other_var {
                // Same variable - trivially unifies
                return true;
            }
            
            // Check if the other variable is bound
            if let Some(other_binding) = subst.get(other_var).cloned() {
                Self::unify_variable(var, &other_binding, subst)
            } else {
                // Both variables are unbound, bind one to the other
                subst.insert(var.to_string(), term.clone());
                true
            }
        } else if Self::occurs_check(var, term, subst) {
            // Occurs check failed - would create infinite structure
            false
        } else {
            // Bind variable to term
            subst.insert(var.to_string(), term.clone());
            true
        }
    }
    
    /// Occurs check: prevent infinite structures like X = f(X)
    /// 
    /// Returns true if the variable occurs in the term (which would be bad),
    /// false if it's safe to unify.
    fn occurs_check(var: &str, term: &Term, subst: &Substitution) -> bool {
        match term {
            Term::Variable(v) => {
                if v == var {
                    true // Variable occurs in itself
                } else if let Some(bound_term) = subst.get(v) {
                    Self::occurs_check(var, bound_term, subst)
                } else {
                    false
                }
            }
            Term::Compound(_, args) => {
                args.iter().any(|arg| Self::occurs_check(var, arg, subst))
            }
            _ => false, // Atoms and numbers can't contain variables
        }
    }
    
    /// Apply substitutions to a term, resolving all variable bindings
    /// 
    /// This follows the substitution chain to get the final value of any variables.
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
                    Self::apply_substitution(replacement, subst)
                } else {
                    term.clone()
                }
            }
            Term::Compound(functor, args) => {
                let new_args: Vec<Term> = args.iter()
                    .map(|arg| Self::apply_substitution(arg, subst))
                    .collect();
                Term::Compound(functor.clone(), new_args)
            }
            _ => term.clone(), // Atoms and numbers are unchanged
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
    pub fn can_unify(term1: &Term, term2: &Term) -> bool {
        let mut temp_subst = HashMap::new();
        Self::unify(term1, term2, &mut temp_subst)
    }
    
    /// Create a renamed copy of a term with fresh variables
    /// 
    /// This is useful for avoiding variable name conflicts when using clauses.
    /// The suffix is appended to all variable names in the term.
    pub fn rename_variables(term: &Term, suffix: &str) -> Term {
        match term {
            Term::Variable(var) => Term::Variable(format!("{}{}", var, suffix)),
            Term::Compound(functor, args) => {
                let new_args: Vec<Term> = args.iter()
                    .map(|arg| Self::rename_variables(arg, suffix))
                    .collect();
                Term::Compound(functor.clone(), new_args)
            }
            _ => term.clone(),
        }
    }
    
    /// Get all variables mentioned in the substitution (both keys and values)
    pub fn get_all_variables(subst: &Substitution) -> Vec<String> {
        let mut vars = Vec::new();
        
        // Add all bound variables (keys)
        for var in subst.keys() {
            if !vars.contains(var) {
                vars.push(var.clone());
            }
        }
        
        // Add all variables in the values
        for term in subst.values() {
            for var in term.variables() {
                if !vars.contains(var) {
                    vars.push(var.clone());
                }
            }
        }
        
        vars.sort();
        vars
    }
    
    /// Compose two substitutions: apply subst2 to the results of subst1
    pub fn compose_substitutions(subst1: &Substitution, subst2: &Substitution) -> Substitution {
        let mut result = HashMap::new();
        
        // Apply subst2 to all terms in subst1
        for (var, term) in subst1 {
            let new_term = Self::apply_substitution(term, subst2);
            result.insert(var.clone(), new_term);
        }
        
        // Add bindings from subst2 that aren't in subst1
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
    pub fn is_idempotent(subst: &Substitution) -> bool {
        for (_var, term) in subst {  // Fixed: prefix unused variable with underscore
            let applied = Self::apply_substitution(term, subst);
            if &applied != term {
                return false;
            }
        }
        true
    }
    
    /// Remove identity bindings (X -> X) from a substitution
    pub fn remove_identity_bindings(subst: &mut Substitution) {
        subst.retain(|var, term| {
            match term {
                Term::Variable(bound_var) => var != bound_var,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_atoms() {
        let mut subst = HashMap::new(); // Use HashMap::new() instead
        
        // Same atoms should unify
        let atom1 = Term::Atom("hello".to_string());
        let atom2 = Term::Atom("hello".to_string());
        assert!(Unifier::unify(&atom1, &atom2, &mut subst));
        assert!(subst.is_empty());
        
        // Different atoms should not unify
        let atom3 = Term::Atom("world".to_string());
        assert!(!Unifier::unify(&atom1, &atom3, &mut subst));
    }

    #[test]
    fn test_unify_numbers() {
        let mut subst = HashMap::new();
        
        // Same numbers should unify
        let num1 = Term::Number(42);
        let num2 = Term::Number(42);
        assert!(Unifier::unify(&num1, &num2, &mut subst));
        
        // Different numbers should not unify
        let num3 = Term::Number(17);
        assert!(!Unifier::unify(&num1, &num3, &mut subst));
    }

    #[test]
    fn test_unify_variables() {
        let mut subst = HashMap::new();
        
        // Variable with atom
        let var = Term::Variable("X".to_string());
        let atom = Term::Atom("hello".to_string());
        assert!(Unifier::unify(&var, &atom, &mut subst));
        assert_eq!(subst.get("X"), Some(&atom));
        
        // Same variable again should unify with existing binding
        let atom2 = Term::Atom("hello".to_string());
        assert!(Unifier::unify(&var, &atom2, &mut subst));
        
        // Different atom should not unify
        let atom3 = Term::Atom("world".to_string());
        assert!(!Unifier::unify(&var, &atom3, &mut subst));
    }

    #[test]
    fn test_unify_compound_terms() {
        let mut subst = HashMap::new();
        
        // f(a, b) with f(a, b)
        let term1 = Term::Compound("f".to_string(), vec![
            Term::Atom("a".to_string()),
            Term::Atom("b".to_string())
        ]);
        let term2 = Term::Compound("f".to_string(), vec![
            Term::Atom("a".to_string()),
            Term::Atom("b".to_string())
        ]);
        assert!(Unifier::unify(&term1, &term2, &mut subst));
        
        // f(X, b) with f(a, b)
        let term3 = Term::Compound("f".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Atom("b".to_string())
        ]);
        assert!(Unifier::unify(&term3, &term2, &mut subst));
        assert_eq!(subst.get("X"), Some(&Term::Atom("a".to_string())));
    }

    #[test]
    fn test_occurs_check() {
        let mut subst = HashMap::new();
        
        // X = f(X) should fail occurs check
        let var = Term::Variable("X".to_string());
        let recursive = Term::Compound("f".to_string(), vec![var.clone()]);
        assert!(!Unifier::unify(&var, &recursive, &mut subst));
        assert!(subst.is_empty());
    }

    #[test]
    fn test_apply_substitution() {
        let mut subst = HashMap::new();
        subst.insert("X".to_string(), Term::Atom("hello".to_string()));
        subst.insert("Y".to_string(), Term::Number(42));
        
        // Apply to variable
        let var = Term::Variable("X".to_string());
        let result = Unifier::apply_substitution(&var, &subst);
        assert_eq!(result, Term::Atom("hello".to_string()));
        
        // Apply to compound term
        let compound = Term::Compound("f".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Variable("Y".to_string())
        ]);
        let result = Unifier::apply_substitution(&compound, &subst);
        match result {
            Term::Compound(functor, args) => {
                assert_eq!(functor, "f");
                assert_eq!(args[0], Term::Atom("hello".to_string()));
                assert_eq!(args[1], Term::Number(42));
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_can_unify() {
        let term1 = Term::Variable("X".to_string());
        let term2 = Term::Atom("hello".to_string());
        assert!(Unifier::can_unify(&term1, &term2));
        
        let term3 = Term::Atom("hello".to_string());
        let term4 = Term::Atom("world".to_string());
        assert!(!Unifier::can_unify(&term3, &term4));
    }

    #[test]
    fn test_rename_variables() {
        let term = Term::Compound("f".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Atom("a".to_string()),
            Term::Variable("Y".to_string())
        ]);
        
        let renamed = Unifier::rename_variables(&term, "_1");
        match renamed {
            Term::Compound(functor, args) => {
                assert_eq!(functor, "f");
                assert_eq!(args[0], Term::Variable("X_1".to_string()));
                assert_eq!(args[1], Term::Atom("a".to_string()));
                assert_eq!(args[2], Term::Variable("Y_1".to_string()));
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_variable_chains() {
        let mut subst = HashMap::new();
        
        // X = Y, Y = Z, Z = hello
        subst.insert("X".to_string(), Term::Variable("Y".to_string()));
        subst.insert("Y".to_string(), Term::Variable("Z".to_string()));
        subst.insert("Z".to_string(), Term::Atom("hello".to_string()));
        
        let var_x = Term::Variable("X".to_string());
        let result = Unifier::apply_substitution(&var_x, &subst);
        assert_eq!(result, Term::Atom("hello".to_string()));
    }

    #[test]
    fn test_compose_substitutions() {
        let mut subst1 = HashMap::new();
        subst1.insert("X".to_string(), Term::Variable("Y".to_string()));
        
        let mut subst2 = HashMap::new();
        subst2.insert("Y".to_string(), Term::Atom("hello".to_string()));
        
        let composed = Unifier::compose_substitutions(&subst1, &subst2);
        
        // X should map to hello (through Y)
        let x_result = Unifier::apply_substitution(&Term::Variable("X".to_string()), &composed);
        assert_eq!(x_result, Term::Atom("hello".to_string()));
    }
    
    #[test]
    fn test_substitution_utils() {
        use super::substitution_utils;
        
        let mut subst = substitution_utils::new();
        assert!(substitution_utils::is_empty(&subst));
        assert_eq!(substitution_utils::len(&subst), 0);
        
        subst.insert("X".to_string(), Term::Atom("hello".to_string()));
        assert!(!substitution_utils::is_empty(&subst));
        assert_eq!(substitution_utils::len(&subst), 1);
        
        let formatted = substitution_utils::format_substitution(&subst);
        assert!(formatted.contains("X -> hello"));
        
        substitution_utils::clear(&mut subst);
        assert!(substitution_utils::is_empty(&subst));
    }
}