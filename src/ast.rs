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
            Term::Atom(name) => Some((name, 0)),
            Term::Compound(functor, args) => Some((functor, args.len())),
            _ => None,
        }
    }
    
    /// Check if this term is a variable
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
    pub fn is_compound(&self) -> bool {
        matches!(self, Term::Compound(_, _))  // Fixed: use (_, _) instead of (..)
    }
    
    /// Get all variables in this term
    pub fn variables(&self) -> Vec<&String> {
        let mut vars = Vec::new();
        self.collect_variables(&mut vars);
        vars
    }
    
    fn collect_variables<'a>(&'a self, vars: &mut Vec<&'a String>) {
        match self {
            Term::Variable(var) => {
                if !vars.contains(&var) {
                    vars.push(var);
                }
            }
            Term::Compound(_, args) => {
                for arg in args {
                    arg.collect_variables(vars);
                }
            }
            _ => {}
        }
    }
    
    /// Check if this term represents a proper Prolog list
    pub fn is_proper_list(&self) -> bool {
        match self {
            Term::Atom(name) if name == "[]" => true,
            Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                args[1].is_proper_list()
            }
            _ => false,
        }
    }
    
    /// Convert a proper list term to a Vec of terms
    /// Returns None if the term is not a proper list
    pub fn to_list(&self) -> Option<Vec<Term>> {
        let mut elements = Vec::new();
        let mut current = self;
        
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
    
    /// Create a list term from a Vec of terms
    pub fn from_list(elements: Vec<Term>) -> Term {
        elements.into_iter().rev().fold(
            Term::Atom("[]".to_string()),
            |acc, elem| Term::Compound(".".to_string(), vec![elem, acc])
        )
    }
    
    /// Get the string representation of a variable name, if this is a variable
    pub fn as_variable(&self) -> Option<&String> {
        match self {
            Term::Variable(name) => Some(name),
            _ => None,
        }
    }
    
    /// Get the string representation of an atom name, if this is an atom
    pub fn as_atom(&self) -> Option<&String> {
        match self {
            Term::Atom(name) => Some(name),
            _ => None,
        }
    }
    
    /// Get the numeric value, if this is a number
    pub fn as_number(&self) -> Option<i64> {
        match self {
            Term::Number(n) => Some(*n),
            _ => None,
        }
    }
    
    /// Get the functor and arguments, if this is a compound term
    pub fn as_compound(&self) -> Option<(&String, &Vec<Term>)> {
        match self {
            Term::Compound(functor, args) => Some((functor, args)),
            _ => None,
        }
    }
    
    /// Check if this term is ground (contains no variables)
    pub fn is_ground(&self) -> bool {
        match self {
            Term::Variable(_) => false,
            Term::Compound(_, args) => args.iter().all(|arg| arg.is_ground()),
            _ => true,
        }
    }
    
    /// Count the total number of subterms (including self)
    pub fn size(&self) -> usize {
        match self {
            Term::Compound(_, args) => 1 + args.iter().map(|arg| arg.size()).sum::<usize>(),
            _ => 1,
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Atom(name) => write!(f, "{}", name),
            Term::Variable(name) => write!(f, "{}", name),
            Term::Number(n) => write!(f, "{}", n),
            Term::Compound(functor, args) => {
                // Special handling for list notation
                if functor == "." && args.len() == 2 {
                    if let Some(list_elements) = self.to_list() {
                        write!(f, "[")?;
                        for (i, elem) in list_elements.iter().enumerate() {
                            if i > 0 { write!(f, ", ")?; }
                            write!(f, "{}", elem)?;
                        }
                        write!(f, "]")
                    } else {
                        // Not a proper list, show with tail
                        write!(f, "[{}|{}]", args[0], args[1])
                    }
                } else {
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
    pub fn fact(head: Term) -> Self {
        Clause { head, body: vec![] }
    }
    
    /// Create a new rule (clause with body)
    pub fn rule(head: Term, body: Vec<Term>) -> Self {
        Clause { head, body }
    }
    
    /// Check if this clause is a fact (has no body)
    pub fn is_fact(&self) -> bool {
        self.body.is_empty()
    }
    
    /// Check if this clause is a rule (has a body)
    pub fn is_rule(&self) -> bool {
        !self.body.is_empty()
    }
    
    /// Get the functor and arity of the head
    pub fn head_functor_arity(&self) -> Option<(&str, usize)> {
        self.head.functor_arity()
    }
    
    /// Get all variables in this clause
    pub fn variables(&self) -> Vec<&String> {
        let mut vars = self.head.variables();
        for goal in &self.body {
            for var in goal.variables() {
                if !vars.contains(&var) {
                    vars.push(var);
                }
            }
        }
        vars
    }
    
    /// Check if this clause is ground (contains no variables)
    pub fn is_ground(&self) -> bool {
        self.head.is_ground() && self.body.iter().all(|goal| goal.is_ground())
    }
    
    /// Get the arity (number of arguments) of the head predicate
    pub fn arity(&self) -> usize {
        self.head_functor_arity().map(|(_, arity)| arity).unwrap_or(0)
    }
    
    /// Get the functor name of the head predicate
    pub fn functor(&self) -> Option<&str> {
        self.head_functor_arity().map(|(functor, _)| functor)
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_creation_and_display() {
        let atom = Term::Atom("hello".to_string());
        assert_eq!(format!("{}", atom), "hello");
        
        let var = Term::Variable("X".to_string());
        assert_eq!(format!("{}", var), "X");
        
        let num = Term::Number(42);
        assert_eq!(format!("{}", num), "42");
        
        let compound = Term::Compound("foo".to_string(), vec![
            Term::Atom("bar".to_string()),
            Term::Variable("X".to_string())
        ]);
        assert_eq!(format!("{}", compound), "foo(bar, X)");
    }

    #[test]
    fn test_functor_arity() {
        let atom = Term::Atom("hello".to_string());
        assert_eq!(atom.functor_arity(), Some(("hello", 0)));
        
        let compound = Term::Compound("foo".to_string(), vec![
            Term::Atom("bar".to_string()),
            Term::Variable("X".to_string())
        ]);
        assert_eq!(compound.functor_arity(), Some(("foo", 2)));
        
        let var = Term::Variable("X".to_string());
        assert_eq!(var.functor_arity(), None);
    }

    #[test]
    fn test_type_checks() {
        let atom = Term::Atom("hello".to_string());
        assert!(atom.is_atom());
        assert!(!atom.is_variable());
        assert!(!atom.is_compound());
        
        let var = Term::Variable("X".to_string());
        assert!(var.is_variable());
        assert!(!var.is_atom());
        assert!(!var.is_compound());
        
        let num = Term::Number(42);
        assert!(num.is_number());
        assert!(!num.is_compound());
        
        let compound = Term::Compound("foo".to_string(), vec![]);
        assert!(compound.is_compound());  // This should now work!
        assert!(!compound.is_atom());
    }

    #[test]
    fn test_list_operations() {
        // Create a list [1, 2, 3]
        let list = Term::from_list(vec![
            Term::Number(1),
            Term::Number(2),
            Term::Number(3)
        ]);
        
        assert!(list.is_proper_list());
        
        let elements = list.to_list().unwrap();
        assert_eq!(elements.len(), 3);
        assert_eq!(elements[0], Term::Number(1));
        assert_eq!(elements[1], Term::Number(2));
        assert_eq!(elements[2], Term::Number(3));
        
        // Test display
        assert_eq!(format!("{}", list), "[1, 2, 3]");
        
        // Test empty list
        let empty = Term::Atom("[]".to_string());
        assert!(empty.is_proper_list());
        assert_eq!(empty.to_list().unwrap().len(), 0);
    }

    #[test]
    fn test_variable_collection() {
        let term = Term::Compound("foo".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Compound("bar".to_string(), vec![
                Term::Variable("Y".to_string()),
                Term::Variable("X".to_string()), // Duplicate
            ])
        ]);
        
        let vars = term.variables();
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&&"X".to_string()));
        assert!(vars.contains(&&"Y".to_string()));
    }

    #[test]
    fn test_ground_terms() {
        let ground_term = Term::Compound("foo".to_string(), vec![
            Term::Atom("a".to_string()),
            Term::Number(42)
        ]);
        assert!(ground_term.is_ground());
        
        let non_ground_term = Term::Compound("foo".to_string(), vec![
            Term::Variable("X".to_string()),
            Term::Number(42)
        ]);
        assert!(!non_ground_term.is_ground());
    }

    #[test]
    fn test_accessor_methods() {
        let var = Term::Variable("X".to_string());
        assert_eq!(var.as_variable(), Some(&"X".to_string()));
        assert_eq!(var.as_atom(), None);
        
        let atom = Term::Atom("hello".to_string());
        assert_eq!(atom.as_atom(), Some(&"hello".to_string()));
        assert_eq!(atom.as_variable(), None);
        
        let num = Term::Number(42);
        assert_eq!(num.as_number(), Some(42));
        
        let compound = Term::Compound("foo".to_string(), vec![Term::Atom("bar".to_string())]);
        if let Some((functor, args)) = compound.as_compound() {
            assert_eq!(functor, "foo");
            assert_eq!(args.len(), 1);
        } else {
            panic!("Expected compound term");
        }
    }

    #[test]
    fn test_clause_creation() {
        let fact = Clause::fact(Term::Atom("parent(tom, bob)".to_string()));
        assert!(fact.is_fact());
        assert!(!fact.is_rule());
        
        let rule = Clause::rule(
            Term::Atom("grandparent(X, Z)".to_string()),
            vec![
                Term::Atom("parent(X, Y)".to_string()),
                Term::Atom("parent(Y, Z)".to_string()),
            ]
        );
        assert!(rule.is_rule());
        assert!(!rule.is_fact());
    }

    #[test]
    fn test_clause_display() {
        let fact = Clause::fact(Term::Atom("likes(mary, wine)".to_string()));
        assert_eq!(format!("{}", fact), "likes(mary, wine)");
        
        let rule = Clause::rule(
            Term::Atom("happy(X)".to_string()),
            vec![Term::Atom("likes(X, wine)".to_string())]
        );
        assert_eq!(format!("{}", rule), "happy(X) :- likes(X, wine)");
    }

    #[test]
    fn test_term_size() {
        let atom = Term::Atom("hello".to_string());
        assert_eq!(atom.size(), 1);
        
        let compound = Term::Compound("foo".to_string(), vec![
            Term::Atom("bar".to_string()),
            Term::Compound("baz".to_string(), vec![Term::Number(42)])
        ]);
        assert_eq!(compound.size(), 4); // foo + bar + baz + 42
    }
}