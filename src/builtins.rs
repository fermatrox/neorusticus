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
    /// 
    /// This function is used by the engine to determine whether a goal should be
    /// handled by the built-in system or searched for in the user-defined clauses.
    /// The pattern matching groups predicates by category for clarity.
    pub fn is_builtin(functor: &str, arity: usize) -> bool {
        match (functor, arity) {
            // Arithmetic predicates
            // These evaluate arithmetic expressions and compare numeric values
            ("is", 2) | ("=:=", 2) | ("=\\=", 2) | (">", 2) | ("<", 2) | (">=", 2) | ("=<", 2) => true,
            
            // Unification predicates
            // These perform structural unification or check non-unifiability
            ("=", 2) | ("\\=", 2) => true,
            
            // Type checking predicates
            // These test the type of a term (with or without substitution applied)
            ("var", 1) | ("nonvar", 1) | ("atom", 1) | ("number", 1) | ("compound", 1) => true,
            
            // List operations
            // Standard Prolog list manipulation predicates
            ("append", 3) | ("member", 2) | ("length", 2) => true,
            
            // Control predicates
            // These control the flow of execution and backtracking
            ("true", 0) | ("fail", 0) | ("!", 0) => true,
            
            // I/O predicates (basic)
            // Simple output operations
            ("write", 1) | ("nl", 0) => true,
            
            _ => false,
        }
    }
    
    /// Execute a built-in predicate
    /// 
    /// This is the main dispatcher for built-in predicates. It:
    /// 1. Pattern matches on the goal to extract the functor and arguments
    /// 2. Dispatches to the appropriate handler function
    /// 3. Handles special atom predicates (true, fail, !, nl)
    /// 4. Returns appropriate errors for unknown predicates or type mismatches
    /// 
    /// The `context` parameter is used for cut operation, which sets a flag
    /// to prevent backtracking in the engine.
    pub fn execute(
        goal: &Term, 
        subst: &mut Substitution, 
        solutions: &mut Vec<Substitution>,
        context: &mut crate::engine::ExecutionContext
    ) -> RuntimeResult<()> {
        match goal {
            Term::Compound(functor, args) => {
                // Most built-in predicates are compound terms with arguments
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
    /// 
    /// Uses the Levenshtein distance algorithm to find the most similar built-in
    /// predicate to what the user typed. This helps users discover typos and
    /// learn the correct predicate names.
    /// 
    /// The algorithm:
    /// 1. Computes edit distance between the input and each known predicate
    /// 2. Adds a penalty for arity mismatches (0.5 per difference)
    /// 3. Returns the best match if the score is reasonable (≤ 4.0)
    /// 
    /// This provides helpful "Did you mean...?" suggestions in error messages.
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
            // This helps distinguish between predicates with the same name but different arities
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
        // This avoids suggesting completely unrelated predicates
        if best_score <= 4.0 {
            best_match
        } else {
            None
        }
    }
    
    // Arithmetic evaluation with comprehensive error handling
    /// 
    /// Recursively evaluates arithmetic expressions to produce an i64 value.
    /// This function handles:
    /// - Simple numbers (return as-is)
    /// - Variables (must be bound to a numeric value)
    /// - Compound expressions with operators (+, -, *, //, mod, abs, max, min)
    /// 
    /// All operations use checked arithmetic to detect overflow. The special case
    /// of abs(i64::MIN) is handled explicitly since it would overflow i64::MAX.
    /// 
    /// The recursion allows complex nested expressions like: (2 + 3) * (4 - 1)
    pub(crate) fn evaluate_arithmetic(term: &Term, subst: &Substitution) -> RuntimeResult<i64> {
        // First, apply any existing substitutions to resolve variables
        let resolved = Unifier::apply_substitution(term, subst);
        match &resolved {
            Term::Number(n) => Ok(*n),
            Term::Variable(var) => {
                // Variables must be instantiated before arithmetic evaluation
                Err(RuntimeError::UninstantiatedVariable {
                    variable: var.clone(),
                    context: "arithmetic evaluation".to_string(),
                })
            },
            Term::Compound(op, args) => {
                // Dispatch based on operator and arity
                match (op.as_str(), args.len()) {
                    ("+", 2) => {
                        // Binary addition with overflow check
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
                        // Absolute value with special handling for i64::MIN
                        let operand = Self::evaluate_arithmetic(&args[0], subst)?;
                        // Handle i64::MIN special case - abs would overflow
                        // i64::MIN is -9223372036854775808, but i64::MAX is 9223372036854775807
                        // So abs(i64::MIN) would be 9223372036854775808, which overflows
                        if operand == i64::MIN {
                            Err(RuntimeError::ArithmeticError {
                                operation: "abs".to_string(),
                                operands: args.clone(),
                                reason: "Integer overflow: abs(i64::MIN) exceeds i64::MAX".to_string(),
                            })
                        } else {
                            Ok(operand.abs())
                        }
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
    
    /// Handle the 'is' predicate: X is Expression
    /// 
    /// Evaluates the arithmetic expression on the right and attempts to unify
    /// the result with the left term. This is how Prolog performs arithmetic:
    /// - If left is a variable, it gets bound to the computed value
    /// - If left is a number, it must equal the computed value
    /// - If left is a compound term, unification rules apply
    /// 
    /// Example: X is 2 + 3 will bind X to 5
    pub(crate) fn handle_is(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let value = Self::evaluate_arithmetic(right, subst)?;
        let result_term = Term::Number(value);
        let mut new_subst = subst.clone();
        if Unifier::unify(left, &result_term, &mut new_subst) {
            solutions.push(new_subst);
        }
        Ok(())
    }
    
    /// Handle arithmetic equality: Expr1 =:= Expr2
    /// 
    /// Evaluates both expressions and succeeds if they produce the same value.
    /// Unlike unification (=), this performs arithmetic evaluation first.
    /// Example: 2+3 =:= 5 succeeds, but 2+3 = 5 fails (structures differ)
    pub(crate) fn handle_arithmetic_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val == right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    pub(crate) fn handle_arithmetic_not_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val != right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    pub(crate) fn handle_greater(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val > right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    pub(crate) fn handle_less(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val < right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    pub(crate) fn handle_greater_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val >= right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    pub(crate) fn handle_less_equal(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let left_val = Self::evaluate_arithmetic(left, subst)?;
        let right_val = Self::evaluate_arithmetic(right, subst)?;
        if left_val <= right_val {
            solutions.push(subst.clone());
        }
        Ok(())
    }
    
    // Unification predicates
    
    /// Handle unification: Term1 = Term2
    /// 
    /// Attempts to make two terms identical through variable substitution.
    /// This is structural unification - it doesn't evaluate arithmetic.
    /// Creates a new substitution that includes any new bindings needed.
    /// 
    /// Example: f(X, 2) = f(1, Y) succeeds with X->1, Y->2
    pub(crate) fn handle_unify(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let mut new_subst = subst.clone();
        if Unifier::unify(left, right, &mut new_subst) {
            solutions.push(new_subst);
        }
    }
    
    /// Handle non-unification: Term1 \= Term2
    /// 
    /// Succeeds if the terms cannot be unified. This is the negation of =.
    /// Note: We test unification on a copy of the substitution to avoid
    /// modifying the original if unification would succeed.
    /// 
    /// Example: 1 \= 2 succeeds, X \= X fails
    pub(crate) fn handle_not_unify(left: &Term, right: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let mut test_subst = subst.clone();
        if !Unifier::unify(left, right, &mut test_subst) {
            solutions.push(subst.clone());
        }
    }
    
    // Type checking predicates
    
    /// Check if a term is an unbound variable
    /// 
    /// First applies substitutions to see if the variable is bound.
    /// Succeeds only if the result is still a variable (unbound).
    /// Example: var(X) succeeds if X is unbound, fails if X = 5
    pub(crate) fn handle_var(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Variable(_)) {
            solutions.push(subst.clone());
        }
    }
    
    /// Check if a term is not a variable (or is a bound variable)
    /// 
    /// The opposite of var/1. Succeeds if the term is an atom, number,
    /// compound, or a variable that's bound to a non-variable.
    pub(crate) fn handle_nonvar(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if !matches!(resolved, Term::Variable(_)) {
            solutions.push(subst.clone());
        }
    }
    
    /// Check if a term is an atom
    /// 
    /// Atoms are constants like 'hello', 'foo', or '[]'.
    /// Variables bound to atoms also succeed.
    pub(crate) fn handle_atom(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Atom(_)) {
            solutions.push(subst.clone());
        }
    }
    
    /// Check if a term is a number
    /// 
    /// Succeeds for integer literals or variables bound to numbers.
    pub(crate) fn handle_number(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Number(_)) {
            solutions.push(subst.clone());
        }
    }
    
    /// Check if a term is a compound term
    /// 
    /// Compound terms have a functor and arguments, like f(a, b).
    /// Note: In Prolog, f() with zero arguments is still compound, not an atom.
    pub(crate) fn handle_compound(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        let resolved = Unifier::apply_substitution(term, subst);
        if matches!(resolved, Term::Compound(_, _)) {
            solutions.push(subst.clone());
        }
    }
    
    // List operations
    
    /// Handle list concatenation: append(List1, List2, Result)
    /// 
    /// This implements the classic Prolog append predicate with two clauses:
    /// 1. Base case: append([], L, L) - appending empty list to L gives L
    /// 2. Recursive case: append([H|T], L, [H|R]) :- append(T, L, R)
    /// 
    /// The implementation generates unique variable names to avoid conflicts
    /// during recursion. It also includes a depth check to prevent stack
    /// overflow on very long lists (limit of 100 elements).
    /// 
    /// This predicate can be used in multiple modes:
    /// - append([1,2], [3,4], X) - concatenate two lists
    /// - append(X, Y, [1,2,3]) - find ways to split a list
    /// - append([1|X], [3], [1,2,3]) - find middle elements
    pub(crate) fn handle_append(list1: &Term, list2: &Term, result: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        // Base case: append([], L, L).
        let mut subst1 = subst.clone();
        let empty_list = Term::Atom("[]".to_string());
        if Unifier::unify(list1, &empty_list, &mut subst1) && 
           Unifier::unify(list2, result, &mut subst1) {
            solutions.push(subst1);
        }
        
        // Recursive case: append([H|T], L, [H|R]) :- append(T, L, R).
        // Generate unique variable names to avoid conflicts
        // We use the current solution count and substitution size for uniqueness
        let var_suffix = format!("_{}", solutions.len() + subst.len());
        let h_var = Term::Variable(format!("H{}", var_suffix));
        let t_var = Term::Variable(format!("T{}", var_suffix));
        let r_var = Term::Variable(format!("R{}", var_suffix));
        
        // Create patterns for unification
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
            // This limits recursion to lists of length < 100
            if Self::get_list_length(&resolved_t).unwrap_or(0) < 100 {
                // Recursive call: append(T, L, R)
                Self::handle_append(&resolved_t, &resolved_list2, &resolved_r, &mut subst2, solutions)?;
            }
        }
        Ok(())
    }
    
    /// Helper function to safely get list length
    /// 
    /// Returns Some(length) for proper lists ending in []
    /// Returns None for improper lists or lists containing variables
    /// This is used to implement the recursion depth limit in append/3
    pub(crate) fn get_list_length(term: &Term) -> Option<usize> {
        match term {
            Term::Atom(name) if name == "[]" => Some(0),
            Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                // Recursively count elements in the tail
                Self::get_list_length(&args[1]).map(|len| len + 1)
            }
            _ => None, // Not a proper list or contains variables
        }
    }
    
    /// Handle list membership: member(Element, List)
    /// 
    /// Checks if Element is a member of List, or generates all members.
    /// Implements two clauses:
    /// 1. member(X, [H|T]) :- X = H. (element is the head)
    /// 2. member(X, [H|T]) :- member(X, T). (element is in the tail)
    /// 
    /// This predicate can be used in multiple modes:
    /// - member(2, [1,2,3]) - check if 2 is in the list
    /// - member(X, [1,2,3]) - generate all members
    /// - member(2, X) - error (list must be instantiated)
    /// 
    /// The implementation is naturally recursive, checking the head first,
    /// then recursively checking the tail.
    pub(crate) fn handle_member(element: &Term, list: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let resolved_list = Unifier::apply_substitution(list, subst);
        
        match resolved_list {
            Term::Compound(ref functor, ref args) if functor == "." && args.len() == 2 => {
                // Case 1: member(X, [H|T]) :- X = H.
                // Try to unify the element with the head of the list
                let mut subst1 = subst.clone();
                if Unifier::unify(element, &args[0], &mut subst1) {
                    solutions.push(subst1);
                }
                
                // Case 2: member(X, [H|T]) :- member(X, T).
                // Recursively check the tail
                Self::handle_member(element, &args[1], subst, solutions)?;
            }
            Term::Atom(ref name) if name == "[]" => {
                // Empty list - member fails (no solutions added)
            }
            Term::Variable(_) => {
                // List must be instantiated for member/2 to work
                return Err(RuntimeError::UninstantiatedVariable {
                    variable: format!("{}", resolved_list),
                    context: "member/2 second argument".to_string(),
                });
            }
            _ => {
                // Not a valid list structure
                return Err(RuntimeError::InvalidListStructure {
                    term: resolved_list,
                    expected: "proper list".to_string(),
                });
            }
        }
        Ok(())
    }
    
    /// Handle list length: length(List, Length)
    /// 
    /// Computes or checks the length of a list.
    /// The list must be instantiated (no unbound variables).
    /// 
    /// Modes of use:
    /// - length([1,2,3], X) - compute length, bind X to 3
    /// - length([1,2,3], 3) - check that length is 3
    /// - length(X, 3) - error (can't generate lists of given length)
    /// 
    /// The implementation walks the list structure counting elements.
    pub(crate) fn handle_length(list: &Term, length: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) -> RuntimeResult<()> {
        let resolved_list = Unifier::apply_substitution(list, subst);
        
        match Self::calculate_list_length(&resolved_list) {
            Ok(len) => {
                // Create a number term with the computed length
                let length_term = Term::Number(len);
                let mut new_subst = subst.clone();
                // Try to unify with the provided length term
                if Unifier::unify(length, &length_term, &mut new_subst) {
                    solutions.push(new_subst);
                }
            }
            Err(e) => return Err(e),
        }
        Ok(())
    }
    
    /// Calculate the length of a list
    /// 
    /// Recursively walks the list structure counting elements.
    /// Returns an error if:
    /// - The list contains unbound variables
    /// - The structure is not a proper list (doesn't end with [])
    /// 
    /// This is a helper for length/2 that does the actual counting.
    pub(crate) fn calculate_list_length(list: &Term) -> RuntimeResult<i64> {
        match list {
            Term::Atom(name) if name == "[]" => Ok(0),
            Term::Compound(functor, args) if functor == "." && args.len() == 2 => {
                // Recursively count the tail and add 1 for the head
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
    
    /// Handle output: write(Term)
    /// 
    /// Outputs a term to standard output. Variables are shown with their
    /// current bindings applied. Always succeeds after writing.
    /// 
    /// Note: This uses print! without a newline, so multiple writes
    /// appear on the same line. Use nl/0 to output a newline.
    pub(crate) fn handle_write(term: &Term, subst: &mut Substitution, solutions: &mut Vec<Substitution>) {
        // Apply substitutions to show the current value of any variables
        let resolved = Unifier::apply_substitution(term, subst);
        print!("{}", resolved);
        // write/1 always succeeds
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

// Link to the test module
#[cfg(test)]
#[path = "builtins_tests.rs"]
mod tests;