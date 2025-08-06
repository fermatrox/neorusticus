// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: ast.rs
// Creator: Jonas Forsman

//! Abstract Syntax Tree types for Prolog terms and clauses
//! 
//! This module defines the core data structures that represent Prolog programs
//! after parsing: terms, clauses, and their associated operations.

use std::fmt;

/// Core Prolog term representation
/// 
/// Terms are the fundamental building blocks of Prolog programs.
/// They can be atoms, variables, compound terms, or numbers.

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// An atom: a constant identifier like `foo` or `hello`
    Atom(String),
    
    /// A variable: an identifier that can be unified with other terms
    /// Variables start with uppercase letters or underscore
    Variable(String),
    
    /// A compound term: functor with arguments like `foo(bar, X)`
    /// The functor is the name, and the Vec contains the arguments
    Compound(String, Vec<Term>),
    
    /// A numeric literal: integer values
    Number(i64),
}

impl Term {
    /// Get the functor name and arity of a term
    /// 
    /// In Prolog, predicates are identified by their functor (name) and arity (number of arguments).
    /// For example, `parent/2` means the `parent` predicate with 2 arguments.
    /// 
    /// # Returns
    /// - `Some((functor, arity))` for atoms (arity 0) and compound terms
    /// - `None` for variables and numbers (they don't have functors)
    /// 
    /// # Examples
    /// ```
    /// use neorusticus::ast::Term;
    /// 
    /// let term = Term::Compound("foo".to_string(), vec![Term::Atom("bar".to_string())]);
    /// assert_eq!(term.functor_arity(), Some(("foo", 1)));
    /// 
    /// let atom = Term::Atom("hello".to_string());
    /// assert_eq!(atom.functor_arity(), Some(("hello", 0)));
    /// ```
    pub fn functor_arity(&self) -> Option<(&str, usize)> {
        match self {
            // Atoms are treated as 0-arity functors (predicates with no arguments)
            Term::Atom(name) => Some((name, 0)),
            // Compound terms have a functor name and the arity is the number of arguments
            Term::Compound(functor, args) => Some((functor, args.len())),
            // Variables and numbers don't have functors in Prolog
            _ => None,
        }
    }
    
    /// Check if this term is a variable
    /// 
    /// Uses Rust's pattern matching to efficiently check the enum variant.
    /// The `matches!` macro is a concise way to test if a value matches a pattern.
    pub fn is_variable(&self) -> bool {
        matches!(self, Term::Variable(_))
    }
    
    /// Check if this term is an atom
    pub fn is_atom(&self) -> bool {
        matches!(self, Term::Atom(_))
    }
    
    /// Check if this term is a number
    pub fn is_number(&self) -> bool {
        matches!(self, Term::Number(_))
    }
    
    /// Check if this term is a compound term
    /// 
    /// Note: We use (_, _) pattern to match any compound regardless of its contents.
    /// Using (..) would be incorrect as it's for tuple structs, not enum variants.
    pub fn is_compound(&self) -> bool {
        matches!(self, Term::Compound(_, _))  // Fixed: use (_, _) instead of (..)
    }
    
    /// Get all variables in this term
    /// 
    /// Collects all unique variable names that appear in the term.
    /// Variables can appear multiple times, but each is only included once in the result.
    /// The order of variables in the result preserves the first occurrence order.
    /// 
    /// # Implementation
    /// Uses a helper function to recursively traverse the term structure
    /// and collect variables while avoiding duplicates.
    pub fn variables(&self) -> Vec<&String> {
        let mut vars = Vec::new();
        self.collect_variables(&mut vars);
        vars
    }
    
    /// Helper function to recursively collect variables from a term
    /// 
    /// # Parameters
    /// - `vars`: Accumulator vector that stores references to variable names
    /// 
    /// # Algorithm
    /// 1. If the term is a variable, add it to the collection if not already present
    /// 2. If the term is compound, recursively collect from all arguments
    /// 3. Atoms and numbers contain no variables, so do nothing
    fn collect_variables<'a>(&'a self, vars: &mut Vec<&'a String>) {
        match self {
            Term::Variable(var) => {
                // Only add if not already in the collection (maintains uniqueness)
                if !vars.contains(&var) {
                    vars.push(var);
                }
            }
            Term::Compound(_, args) => {
                // Recursively collect variables from all arguments
                for arg in args {
                    arg.collect_variables(vars);
                }
            }
            // Atoms and numbers don't contain variables
            _ => {}
        }
    }
    
    /// Check if this term represents a proper Prolog list
    /// 
    /// In Prolog, lists are represented using the dot notation:
    /// - Empty list: `[]` (an atom)
    /// - Non-empty list: `.(Head, Tail)` where Tail is also a list
    /// 
    /// For example, `[1,2,3]` is internally `.(1, .(2, .(3, [])))`
    /// 
    /// # Returns
    /// `true` if the term is a proper list (ends with `[]`), `false` otherwise
    pub fn is_proper_list(&self) -> bool {
        match self {
            // Base case: empty list is represented as the atom "[]"
            Term::Atom(name) if name == "[]" => true,
            // Recursive case: check if it's a cons cell with proper tail
            Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                // A proper list has a proper list as its tail
                args[1].is_proper_list()
            }
            // Anything else is not a proper list
            _ => false,
        }
    }
    
    /// Convert a proper list term to a Vec of terms
    /// 
    /// Traverses the list structure and extracts all elements into a Vec.
    /// 
    /// # Algorithm
    /// Iteratively walks through the list structure:
    /// 1. Start with the current term
    /// 2. If it's `[]`, we've reached the end - return collected elements
    /// 3. If it's `.(Head, Tail)`, collect Head and continue with Tail
    /// 4. If it's anything else, it's not a proper list - return None
    /// 
    /// # Returns
    /// - `Some(vec)` containing all list elements if it's a proper list
    /// - `None` if the term is not a proper list
    pub fn to_list(&self) -> Option<Vec<Term>> {
        let mut elements = Vec::new();
        let mut current = self;
        
        loop {
            match current {
                // Base case: empty list marks the end
                Term::Atom(name) if name == "[]" => return Some(elements),
                // Recursive case: extract head and continue with tail
                Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                    elements.push(args[0].clone());
                    current = &args[1];
                }
                // Not a proper list (e.g., has a variable tail like [1,2|X])
                _ => return None,
            }
        }
    }
    
    /// Create a list term from a Vec of terms
    /// 
    /// Builds a Prolog list structure from a vector of elements.
    /// 
    /// # Algorithm
    /// Uses right-fold to build the list from right to left:
    /// 1. Start with empty list `[]` as the accumulator
    /// 2. For each element (traversed in reverse), create `.(element, accumulator)`
    /// 3. This builds the nested structure correctly
    /// 
    /// # Example
    /// `vec![1, 2, 3]` becomes `.(1, .(2, .(3, [])))`
    pub fn from_list(elements: Vec<Term>) -> Term {
        elements.into_iter().rev().fold(
            Term::Atom("[]".to_string()),
            |acc, elem| Term::Compound(".".to_string(), vec![elem, acc])
        )
    }
    
    /// Get the string representation of a variable name, if this is a variable
    /// 
    /// Safe accessor that returns `Some(&String)` only if the term is a Variable variant.
    /// This avoids the need for pattern matching in calling code.
    pub fn as_variable(&self) -> Option<&String> {
        match self {
            Term::Variable(name) => Some(name),
            _ => None,
        }
    }
    
    /// Get the string representation of an atom name, if this is an atom
    /// 
    /// Safe accessor that returns `Some(&String)` only if the term is an Atom variant.
    pub fn as_atom(&self) -> Option<&String> {
        match self {
            Term::Atom(name) => Some(name),
            _ => None,
        }
    }
    
    /// Get the numeric value, if this is a number
    /// 
    /// Safe accessor that returns `Some(i64)` only if the term is a Number variant.
    /// Note: Returns a copy of the number, not a reference, since i64 is Copy.
    pub fn as_number(&self) -> Option<i64> {
        match self {
            Term::Number(n) => Some(*n),
            _ => None,
        }
    }
    
    /// Get the functor and arguments, if this is a compound term
    /// 
    /// Safe accessor that returns references to both the functor name and argument vector.
    /// This is useful for pattern matching on compound terms without cloning.
    pub fn as_compound(&self) -> Option<(&String, &Vec<Term>)> {
        match self {
            Term::Compound(functor, args) => Some((functor, args)),
            _ => None,
        }
    }
    
    /// Check if this term is ground (contains no variables)
    /// 
    /// A ground term is fully instantiated with no unbound variables.
    /// This is important in Prolog for checking if a term is fully resolved.
    /// 
    /// # Algorithm
    /// - Variables are never ground
    /// - Atoms and numbers are always ground
    /// - Compound terms are ground if all their arguments are ground (recursive check)
    pub fn is_ground(&self) -> bool {
        match self {
            Term::Variable(_) => false,
            // For compound terms, all arguments must be ground
            Term::Compound(_, args) => args.iter().all(|arg| arg.is_ground()),
            // Atoms and numbers are always ground (no variables)
            _ => true,
        }
    }
    
    /// Count the total number of subterms (including self)
    /// 
    /// Useful for measuring term complexity or for algorithms that need term size.
    /// 
    /// # Counting rules
    /// - Atoms, variables, and numbers count as 1
    /// - Compound terms count as 1 + sum of all argument sizes (recursive)
    /// 
    /// # Example
    /// `foo(bar, baz(42))` has size 4: foo + bar + baz + 42
    pub fn size(&self) -> usize {
        match self {
            // Compound term: count self (1) plus the size of all arguments
            Term::Compound(_, args) => 1 + args.iter().map(|arg| arg.size()).sum::<usize>(),
            // Atomic terms (atoms, variables, numbers) have size 1
            _ => 1,
        }
    }
}

impl fmt::Display for Term {
    /// Format a term for display
    /// 
    /// Provides human-readable output with special handling for lists.
    /// Lists are displayed using square bracket notation when possible.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Simple cases: just write the string representation
            Term::Atom(name) => write!(f, "{}", name),
            Term::Variable(name) => write!(f, "{}", name),
            Term::Number(n) => write!(f, "{}", n),
            Term::Compound(functor, args) => {
                // Special handling for list notation
                // The dot functor with 2 args represents a list cons cell
                if functor == "." && args.len() == 2 {
                    // Try to format as a proper list [1, 2, 3]
                    if let Some(list_elements) = self.to_list() {
                        write!(f, "[")?;
                        for (i, elem) in list_elements.iter().enumerate() {
                            if i > 0 { write!(f, ", ")?; }
                            write!(f, "{}", elem)?;
                        }
                        write!(f, "]")
                    } else {
                        // Not a proper list, show with tail notation [Head|Tail]
                        // This handles cases like [1, 2|X] where X is a variable
                        write!(f, "[{}|{}]", args[0], args[1])
                    }
                } else {
                    // Regular compound term: functor(arg1, arg2, ...)
                    write!(f, "{}(", functor)?;
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 { write!(f, ", ")?; }
                        write!(f, "{}", arg)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

/// A Prolog clause: either a fact or a rule
/// 
/// Facts have no body (empty body vector).
/// Rules have a head and one or more body goals.
#[derive(Debug, Clone)]
pub struct Clause {
    /// The head of the clause (what it defines)
    pub head: Term,
    
    /// The body of the clause (conditions that must be satisfied)
    /// Empty for facts
    pub body: Vec<Term>,
}

impl Clause {
    /// Create a new fact (clause with no body)
    /// 
    /// Facts are assertions that are always true.
    /// Example: `parent(tom, bob).` is a fact.
    pub fn fact(head: Term) -> Self {
        Clause { head, body: vec![] }
    }
    
    /// Create a new rule (clause with body)
    /// 
    /// Rules define relationships that hold when certain conditions are met.
    /// Example: `grandparent(X, Z) :- parent(X, Y), parent(Y, Z).` is a rule.
    pub fn rule(head: Term, body: Vec<Term>) -> Self {
        Clause { head, body }
    }
    
    /// Check if this clause is a fact (has no body)
    /// 
    /// Facts are clauses with empty bodies - they're always true.
    pub fn is_fact(&self) -> bool {
        self.body.is_empty()
    }
    
    /// Check if this clause is a rule (has a body)
    /// 
    /// Rules have at least one goal in the body that must be satisfied.
    pub fn is_rule(&self) -> bool {
        !self.body.is_empty()
    }
    
    /// Get the functor and arity of the head
    /// 
    /// Delegates to the Term's functor_arity method.
    /// This identifies which predicate this clause defines.
    pub fn head_functor_arity(&self) -> Option<(&str, usize)> {
        self.head.functor_arity()
    }
    
    /// Get all variables in this clause
    /// 
    /// Collects variables from both the head and all body goals.
    /// Each variable is included only once, even if it appears multiple times.
    /// 
    /// # Algorithm
    /// 1. Collect variables from the head
    /// 2. For each body goal, collect its variables
    /// 3. Add only new variables (not already in the collection)
    /// 4. Return the complete list of unique variables
    pub fn variables(&self) -> Vec<&String> {
        // Start with variables from the head
        let mut vars = self.head.variables();
        
        // Add variables from each body goal
        for goal in &self.body {
            for var in goal.variables() {
                // Only add if not already present (maintain uniqueness)
                if !vars.contains(&var) {
                    vars.push(var);
                }
            }
        }
        vars
    }
    
    /// Check if this clause is ground (contains no variables)
    /// 
    /// A clause is ground if both its head and all body goals are ground.
    /// Ground clauses are fully instantiated with no unbound variables.
    pub fn is_ground(&self) -> bool {
        // Check head is ground AND all body goals are ground
        self.head.is_ground() && self.body.iter().all(|goal| goal.is_ground())
    }
    
    /// Get the arity (number of arguments) of the head predicate
    /// 
    /// Convenience method that extracts just the arity from head_functor_arity.
    /// Returns 0 if the head doesn't have a functor (e.g., if it's a variable).
    pub fn arity(&self) -> usize {
        self.head_functor_arity().map(|(_, arity)| arity).unwrap_or(0)
    }
    
    /// Get the functor name of the head predicate
    /// 
    /// Convenience method that extracts just the functor from head_functor_arity.
    /// Returns None if the head doesn't have a functor.
    pub fn functor(&self) -> Option<&str> {
        self.head_functor_arity().map(|(functor, _)| functor)
    }
}

impl fmt::Display for Clause {
    /// Format a clause for display
    /// 
    /// Facts are displayed as: `head.`
    /// Rules are displayed as: `head :- goal1, goal2, ...`
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Always display the head
        write!(f, "{}", self.head)?;
        
        // If there's a body, add the rule operator and goals
        if !self.body.is_empty() {
            write!(f, " :- ")?;
            for (i, goal) in self.body.iter().enumerate() {
                if i > 0 { write!(f, ", ")?; }
                write!(f, "{}", goal)?;
            }
        }
        Ok(())
    }
}

// Link to the test module
#[cfg(test)]
#[path = "ast_tests.rs"]
mod tests;