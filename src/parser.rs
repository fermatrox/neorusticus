// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: parser.rs
// Creator: Jonas Forsman

//! Parser for Prolog source code
//! 
//! This module provides parsing of tokenized Prolog code into Abstract Syntax Trees.
//! It handles operator precedence, list syntax, and provides detailed error reporting
//! with recovery suggestions.

use crate::ast::{Term, Clause};
use crate::error::{ParseError, ParseResult, Position};
use crate::lexer::Token;

/// Parser for converting tokens into Prolog AST
/// 
/// The parser uses recursive descent with operator precedence parsing
/// for expressions. It handles all Prolog constructs including facts,
/// rules, queries, and complex expressions with proper precedence.
pub struct Parser {
    /// The complete list of tokens from the lexer
    tokens: Vec<Token>,
    /// Current position in the token stream (0-indexed)
    position: usize,
}

impl Parser {
    /// Create a new parser with the given tokens
    /// 
    /// The parser starts at position 0, ready to process the first token.
    /// The token stream should end with an EOF token.
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, position: 0 }
    }
    
    /// Get the current token without consuming it
    /// 
    /// This is a lookahead of 0 - we examine the current token
    /// without advancing the position. Returns EOF if we're past
    /// the end of the token stream.
    pub fn current_token(&self) -> &Token {
        self.tokens.get(self.position).unwrap_or(&Token::Eof)
    }
    
    /// Peek at the next token without consuming the current one
    /// 
    /// This is a lookahead of 1 - we can see what's coming next
    /// without moving our position. Useful for making parsing decisions
    /// based on what follows the current token.
    pub fn peek_token(&self) -> &Token {
        self.tokens.get(self.position + 1).unwrap_or(&Token::Eof)
    }
    
    /// Advance to the next token
    /// 
    /// Moves the position forward by one, effectively "consuming"
    /// the current token. Safe to call even at the end of the stream
    /// (position won't go past the length of the token vector).
    pub fn advance(&mut self) {
        if self.position < self.tokens.len() {
            self.position += 1;
        }
    }
    
    /// Get the current position for error reporting
    /// 
    /// Creates a Position struct that can be included in error messages.
    /// Currently simplified - a full implementation would track actual
    /// line and column numbers from the source text.
    pub fn current_position(&self) -> Position {
        Position::new(0, 0, self.position) // Simplified - lexer should provide real positions
    }
    
    /// Expect a specific token and advance, or return an error
    /// 
    /// This is a common pattern in recursive descent parsing:
    /// 1. Check if the current token matches what we expect
    /// 2. If yes, consume it and continue
    /// 3. If no, return an error with helpful information
    /// 
    /// We use discriminant comparison to check token types without
    /// comparing the associated data (e.g., any Atom matches any Atom).
    pub fn expect(&mut self, expected: Token) -> ParseResult<()> {
        if std::mem::discriminant(self.current_token()) == std::mem::discriminant(&expected) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken {
                token: format!("{:?}", self.current_token()),
                position: self.current_position(),
                expected: Some(vec![expected.description().to_string()]),
            })
        }
    }
    
    /// Check if current token matches expected without consuming it
    /// 
    /// Similar to expect() but doesn't advance or return an error.
    /// Used for conditional parsing - "if we see X, do Y".
    /// Uses discriminant comparison like expect().
    pub fn check(&self, expected: &Token) -> bool {
        std::mem::discriminant(self.current_token()) == std::mem::discriminant(expected)
    }
    
    /// Parse a complete term
    /// 
    /// Entry point for parsing any Prolog term. Delegates to parse_expression
    /// which handles the full operator precedence hierarchy.
    pub fn parse_term(&mut self) -> ParseResult<Term> {
        self.parse_expression()
    }
    
    /// Parse expressions with full operator precedence
    /// 
    /// This is the top level of our precedence climbing parser.
    /// It starts with the lowest precedence operators and works its way up.
    /// 
    /// Precedence levels (highest to lowest binding):
    /// 1. Primary terms (atoms, variables, numbers, parentheses) - tightest binding
    /// 2. Multiplicative (*, //, mod)
    /// 3. Additive (+, -)
    /// 4. Comparison (>, <, >=, =<, =:=, =\=)
    /// 5. Unification (=, \=, is) - loosest binding
    /// 
    /// Each level calls the next higher precedence level to get its operands.
    pub fn parse_expression(&mut self) -> ParseResult<Term> {
        self.parse_unification()
    }
    
    /// Parse unification operators (=, \=, is) - lowest precedence
    /// 
    /// These operators bind the loosest, so they're parsed first.
    /// The pattern here is:
    /// 1. Parse a higher-precedence expression (comparison) as the left operand
    /// 2. While we see a unification operator:
    ///    a. Consume the operator
    ///    b. Parse another comparison expression as the right operand
    ///    c. Build a compound term with the operator and both operands
    ///    d. This compound becomes the new left operand (left-associative)
    /// 
    /// This creates left-associative parsing: X = Y = Z becomes (X = Y) = Z
    pub fn parse_unification(&mut self) -> ParseResult<Term> {
        let mut left = self.parse_comparison()?;
        
        // Keep parsing as long as we see unification operators
        while let Some(op) = self.get_unification_op() {
            self.advance(); // consume operator
            let right = self.parse_comparison()?;
            // Build compound term: operator(left, right)
            left = Term::Compound(op, vec![left, right]);
        }
        
        Ok(left)
    }
    
    /// Parse comparison operators (>, <, =:=, etc.)
    /// 
    /// Same pattern as unification, but at a higher precedence level.
    /// Comparison operators bind tighter than unification but looser
    /// than arithmetic operators.
    /// 
    /// Examples:
    /// - X > 5 = true  parses as (X > 5) = true
    /// - 3 + 2 > 4     parses as (3 + 2) > 4
    pub fn parse_comparison(&mut self) -> ParseResult<Term> {
        let mut left = self.parse_additive()?;
        
        while let Some(op) = self.get_comparison_op() {
            self.advance(); // consume operator
            let right = self.parse_additive()?;
            left = Term::Compound(op, vec![left, right]);
        }
        
        Ok(left)
    }
    
    /// Parse additive operators (+ and -)
    /// 
    /// Addition and subtraction have the same precedence and are left-associative.
    /// They bind tighter than comparisons but looser than multiplication.
    /// 
    /// Example: 1 + 2 - 3 parses as (1 + 2) - 3
    /// 
    /// The pattern continues: parse multiplicative expressions as operands,
    /// build compound terms for the operations.
    pub fn parse_additive(&mut self) -> ParseResult<Term> {
        let mut left = self.parse_multiplicative()?;
        
        // matches! macro is a concise way to check if token is Plus or Minus
        while matches!(self.current_token(), Token::Plus | Token::Minus) {
            let op = match self.current_token() {
                Token::Plus => "+".to_string(),
                Token::Minus => "-".to_string(),
                _ => unreachable!(), // We just checked it's Plus or Minus
            };
            self.advance();
            let right = self.parse_multiplicative()?;
            left = Term::Compound(op, vec![left, right]);
        }
        
        Ok(left)
    }
    
    /// Parse multiplicative operators (*, //, mod)
    /// 
    /// Multiplication, division, and modulo have the same precedence
    /// and bind tighter than addition/subtraction.
    /// 
    /// Example: 2 + 3 * 4 parses as 2 + (3 * 4)
    /// 
    /// Note: Prolog uses // for integer division (not /)
    pub fn parse_multiplicative(&mut self) -> ParseResult<Term> {
        let mut left = self.parse_unary()?;
        
        while matches!(self.current_token(), Token::Multiply | Token::Divide | Token::Mod) {
            let op = match self.current_token() {
                Token::Multiply => "*".to_string(),
                Token::Divide => "//".to_string(),  // Integer division in Prolog
                Token::Mod => "mod".to_string(),
                _ => unreachable!(),
            };
            self.advance();
            let right = self.parse_unary()?;
            left = Term::Compound(op, vec![left, right]);
        }
        
        Ok(left)
    }
    
    /// Parse unary operators (currently just unary minus handled in lexer)
    /// 
    /// This is a placeholder for unary operator parsing.
    /// Currently, negative numbers are handled by the lexer (e.g., -42),
    /// but this could be extended to handle other unary operators like
    /// logical not (\+) or arithmetic negation as an operator.
    /// 
    /// For now, it just delegates to parse_primary().
    pub fn parse_unary(&mut self) -> ParseResult<Term> {
        // For now, unary operators are handled in the lexer (negative numbers)
        // This could be extended for other unary operators like logical not
        self.parse_primary()
    }
    
    /// Parse primary terms (atoms, variables, numbers, parenthesized expressions, lists)
    /// 
    /// This is the highest precedence level - the basic building blocks of expressions.
    /// Primary terms are:
    /// - Atoms (constants): foo, 'hello world'
    /// - Variables: X, _temp
    /// - Numbers: 42, -17
    /// - Compound terms: foo(bar, baz)
    /// - Lists: [1, 2, 3] or [H|T]
    /// - Parenthesized expressions: (X + 1)
    /// - Cut operator: !
    /// 
    /// This function dispatches based on the current token type.
    pub fn parse_primary(&mut self) -> ParseResult<Term> {
        match self.current_token().clone() {
            Token::Atom(name) => {
                self.advance();
                
                // Check if this atom is followed by parentheses
                // If yes, it's a compound term (functor with arguments)
                // If no, it's just a simple atom
                if self.check(&Token::LeftParen) {
                    // Compound term: functor(arg1, arg2, ...)
                    self.advance(); // consume '('
                    let args = self.parse_argument_list()?;
                    self.expect(Token::RightParen)?;
                    Ok(Term::Compound(name, args))
                } else {
                    // Simple atom
                    Ok(Term::Atom(name))
                }
            }
            Token::Variable(name) => {
                // Variables are simple - just consume and create Variable term
                self.advance();
                Ok(Term::Variable(name))
            }
            Token::Number(n) => {
                // Numbers are also simple - consume and create Number term
                self.advance();
                Ok(Term::Number(n))
            }
            Token::Cut => {
                // The cut operator (!) is represented as a special atom
                self.advance();
                Ok(Term::Atom("!".to_string()))
            }
            Token::LeftBracket => {
                // Lists have special syntax and structure, delegate to parse_list
                self.parse_list()
            }
            Token::LeftParen => {
                // Parenthesized expression - parse the inner expression
                // This allows overriding precedence: (1 + 2) * 3
                self.advance(); // consume '('
                let expr = self.parse_expression()?; // Parse what's inside
                self.expect(Token::RightParen)?; // Must close the parenthesis
                Ok(expr)
            }
            Token::Minus => {
                // Handle unary minus that wasn't caught by lexer
                // This could happen if minus appears in a position where
                // it can't be part of a negative number literal
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Term::Compound("-".to_string(), vec![operand]))
            }
            _ => {
                // Anything else is an error - provide helpful feedback
                Err(ParseError::UnexpectedToken {
                    token: format!("{:?}", self.current_token()),
                    position: self.current_position(),
                    expected: Some(vec![
                        "atom".to_string(), 
                        "variable".to_string(),
                        "number".to_string(), 
                        "'('".to_string(), 
                        "'['".to_string()
                    ]),
                })
            }
        }
    }
    
    /// Parse a list of arguments separated by commas
    /// 
    /// Used for parsing the arguments in compound terms like foo(a, b, c).
    /// Arguments can be any valid term/expression.
    /// 
    /// The algorithm:
    /// 1. If we immediately see ')', there are no arguments - return empty list
    /// 2. Otherwise, parse the first argument
    /// 3. While we see commas, consume the comma and parse the next argument
    /// 4. Return the list of all arguments
    /// 
    /// This handles both foo() (empty args) and foo(a, b, c) (multiple args).
    pub fn parse_argument_list(&mut self) -> ParseResult<Vec<Term>> {
        let mut args = Vec::new();
        
        // Check for empty argument list
        if !self.check(&Token::RightParen) {
            // Parse first argument
            args.push(self.parse_expression()?);
            
            // Parse remaining arguments (comma-separated)
            while self.check(&Token::Comma) {
                self.advance(); // consume ','
                args.push(self.parse_expression()?);
            }
        }
        
        Ok(args)
    }
    
    /// Get unification operator if current token is one
    /// 
    /// Helper function that checks if the current token is a unification
    /// operator and returns its string representation if so.
    /// Returns None if the current token is not a unification operator.
    /// 
    /// Unification operators: =, \=, is
    pub fn get_unification_op(&self) -> Option<String> {
        match self.current_token() {
            Token::Unify => Some("=".to_string()),
            Token::NotUnify => Some("\\=".to_string()),
            Token::Is => Some("is".to_string()),
            _ => None,
        }
    }
    
    /// Get comparison operator if current token is one
    /// 
    /// Helper function that checks if the current token is a comparison
    /// operator and returns its string representation if so.
    /// 
    /// Comparison operators: >, <, >=, =<, =:=, =\=
    /// Note: Prolog uses =< for less-than-or-equal (not <=)
    pub fn get_comparison_op(&self) -> Option<String> {
        match self.current_token() {
            Token::Greater => Some(">".to_string()),
            Token::Less => Some("<".to_string()),
            Token::GreaterEq => Some(">=".to_string()),
            Token::LessEq => Some("=<".to_string()),      // Note: =< not <=
            Token::ArithEq => Some("=:=".to_string()),     // Arithmetic equality
            Token::ArithNeq => Some("=\\=".to_string()),   // Arithmetic inequality
            _ => None,
        }
    }
    
    /// Parse Prolog lists [a, b, c] or [H|T]
    /// 
    /// Lists in Prolog have special syntax but are actually compound terms:
    /// - Empty list: [] is an atom
    /// - Non-empty list: [1,2,3] is .(1, .(2, .(3, [])))
    /// - List with tail: [H|T] is .(H, T)
    /// 
    /// The algorithm:
    /// 1. Consume the opening bracket
    /// 2. Check for empty list []
    /// 3. Parse comma-separated elements
    /// 4. Check for pipe | indicating a tail variable
    /// 5. Build the nested structure from right to left
    /// 
    /// The right-to-left building is important: we start with the tail
    /// (either [] or a variable) and prepend each element using the
    /// dot functor to create the proper nested structure.
    pub fn parse_list(&mut self) -> ParseResult<Term> {
        self.expect(Token::LeftBracket)?;
        
        // Check for empty list
        if self.check(&Token::RightBracket) {
            // Empty list [] is represented as a special atom
            self.advance();
            return Ok(Term::Atom("[]".to_string()));
        }
        
        // Parse list elements
        let mut elements = Vec::new();
        elements.push(self.parse_expression()?);
        
        // Parse additional comma-separated elements
        while self.check(&Token::Comma) {
            self.advance(); // consume ','
            elements.push(self.parse_expression()?);
        }
        
        // Check for tail notation [H|T]
        let tail = if self.check(&Token::Pipe) {
            self.advance(); // consume '|'
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        
        self.expect(Token::RightBracket)?;
        
        // Build list structure from right to left
        // Start with the tail (empty list or variable)
        let mut result = tail.unwrap_or_else(|| Box::new(Term::Atom("[]".to_string())));
        
        // Prepend each element using the dot functor
        // [1,2,3] becomes .(1, .(2, .(3, [])))
        for element in elements.into_iter().rev() {
            result = Box::new(Term::Compound(".".to_string(), vec![element, *result]));
        }
        
        Ok(*result)
    }
    
    /// Parse a clause (fact or rule)
    /// 
    /// A clause is either:
    /// - A fact: head.
    /// - A rule: head :- body.
    /// 
    /// The algorithm:
    /// 1. Parse the head (any expression, though typically a compound term)
    /// 2. Check if there's a :- operator
    /// 3. If yes, parse the body (comma-separated goals) -> rule
    /// 4. If no, it's a fact
    pub fn parse_clause(&mut self) -> ParseResult<Clause> {
        let head = self.parse_expression()?;
        
        if self.check(&Token::Rule) {
            // Rule: head :- body
            self.advance(); // consume ':-'
            let body = self.parse_goal_list()?;
            Ok(Clause::rule(head, body))
        } else {
            // Fact: just head
            Ok(Clause::fact(head))
        }
    }
    
    /// Parse a list of goals separated by commas
    /// 
    /// Goals are the expressions in a rule body or query.
    /// They're separated by commas which represent logical AND.
    /// 
    /// Example: parent(X, Y), ancestor(Y, Z)
    /// 
    /// Each goal can be any expression (typically compound terms).
    pub fn parse_goal_list(&mut self) -> ParseResult<Vec<Term>> {
        let mut goals = Vec::new();
        
        // Parse first goal (required - empty goal list is not allowed)
        goals.push(self.parse_expression()?);
        
        // Parse additional comma-separated goals
        while self.check(&Token::Comma) {
            self.advance(); // consume ','
            goals.push(self.parse_expression()?);
        }
        
        Ok(goals)
    }
    
    /// Parse a query (goals ending with ? or .)
    /// 
    /// A query is just a list of goals. The terminator (? or .)
    /// is handled by the caller. This separation allows the same
    /// goal list parsing to be used for both queries and rule bodies.
    pub fn parse_query(&mut self) -> ParseResult<Vec<Term>> {
        self.parse_goal_list()
    }
    
    /// Parse multiple clauses separated by dots
    /// 
    /// This parses a complete Prolog program consisting of multiple
    /// clauses (facts and rules), each terminated by a dot.
    /// 
    /// The algorithm:
    /// 1. Skip any leading dots (error recovery)
    /// 2. Parse a clause
    /// 3. Expect a dot after the clause
    /// 4. Repeat until EOF
    /// 
    /// This is tolerant of extra dots between clauses.
    pub fn parse_program(&mut self) -> ParseResult<Vec<Clause>> {
        let mut clauses = Vec::new();
        
        while !self.check(&Token::Eof) {
            // Skip any extra dots (helps with error recovery)
            while self.check(&Token::Dot) {
                self.advance();
            }
            
            // Check if we've reached the end after skipping dots
            if self.check(&Token::Eof) {
                break;
            }
            
            // Parse the next clause
            let clause = self.parse_clause()?;
            clauses.push(clause);
            
            // Expect dot after clause
            self.expect(Token::Dot)?;
        }
        
        Ok(clauses)
    }
    
    /// Get current parsing position (for error reporting)
    /// 
    /// Returns the current position in the token stream as a simple index.
    /// Useful for debugging and understanding parser state.
    pub fn position(&self) -> usize {
        self.position
    }
    
    /// Check if we're at the end of input
    /// 
    /// Returns true if the current token is EOF, indicating we've
    /// consumed all meaningful tokens from the input.
    pub fn is_at_end(&self) -> bool {
        matches!(self.current_token(), Token::Eof)
    }
    
    /// Skip to the next likely recovery point (typically a dot or eof)
    /// 
    /// Used by the error recovery mechanism to skip past problematic
    /// tokens and find a place where parsing can resume.
    /// 
    /// Recovery points are:
    /// - Dot: End of a clause, safe to start parsing the next clause
    /// - EOF: End of input, nothing more to parse
    pub fn skip_to_recovery_point(&mut self) {
        while !matches!(self.current_token(), Token::Dot | Token::Eof) {
            self.advance();
        }
    }
    
    /// Parse with error recovery - continues parsing even after errors
    /// 
    /// This is a fault-tolerant parsing mode that tries to parse as much
    /// as possible even when encountering errors. It's useful for IDEs
    /// and tools that want to provide feedback on multiple errors at once.
    /// 
    /// The algorithm:
    /// 1. Try to parse a clause
    /// 2. If successful, check for the terminating dot
    /// 3. If parsing fails, record the error and skip to a recovery point
    /// 4. Continue until EOF
    /// 
    /// Returns both the successfully parsed clauses and all errors encountered.
    pub fn parse_with_recovery(&mut self) -> (Vec<Clause>, Vec<ParseError>) {
        let mut clauses = Vec::new();
        let mut errors = Vec::new();
        
        while !self.is_at_end() {
            // Skip extra dots (common error: multiple dots)
            while self.check(&Token::Dot) {
                self.advance();
            }
            
            if self.is_at_end() {
                break;
            }
            
            // Try to parse a clause
            match self.parse_clause() {
                Ok(clause) => {
                    // Clause parsed successfully, now check for dot
                    if let Err(e) = self.expect(Token::Dot) {
                        // Missing dot - record error and try to recover
                        errors.push(e);
                        self.skip_to_recovery_point();
                    } else {
                        // Complete success - add the clause
                        clauses.push(clause);
                    }
                }
                Err(e) => {
                    // Failed to parse clause - record error and recover
                    errors.push(e);
                    self.skip_to_recovery_point();
                    if self.check(&Token::Dot) {
                        self.advance(); // consume the dot and continue
                    }
                }
            }
        }
        
        (clauses, errors)
    }
    
    /// Validate that a term can be used as a valid Prolog head
    /// 
    /// In Prolog, not all terms can be clause heads. Valid heads are:
    /// - Atoms: foo
    /// - Compound terms: foo(bar, X)
    /// 
    /// Invalid heads are:
    /// - Variables: X (can't define a clause for a variable)
    /// - Numbers: 42 (can't define a clause for a number)
    /// 
    /// This validation ensures semantic correctness of clauses.
    pub fn validate_clause_head(head: &Term) -> ParseResult<()> {
        match head {
            Term::Atom(_) => Ok(()),
            Term::Compound(_, args) => {
                // Check that all arguments in head are valid
                // Arguments can be atoms, variables, numbers, or compounds
                for arg in args {
                    Self::validate_head_argument(arg)?;
                }
                Ok(())
            }
            Term::Variable(_) => Err(ParseError::InvalidSyntax {
                message: "Variable cannot be used as clause head".to_string(),
                position: Position::start(),
                suggestion: Some("Use an atom or compound term as the head".to_string()),
            }),
            Term::Number(_) => Err(ParseError::InvalidSyntax {
                message: "Number cannot be used as clause head".to_string(), 
                position: Position::start(),
                suggestion: Some("Use an atom or compound term as the head".to_string()),
            }),
        }
    }
    
    /// Validate arguments in clause heads (can be more restrictive than general terms)
    /// 
    /// This recursively validates that all arguments in a clause head are valid.
    /// Currently allows any term type as an argument, but this could be made
    /// more restrictive if needed (e.g., disallowing certain constructs).
    /// 
    /// The recursion handles nested compound terms in arguments.
    fn validate_head_argument(arg: &Term) -> ParseResult<()> {
        match arg {
            Term::Atom(_) | Term::Variable(_) | Term::Number(_) => Ok(()),
            Term::Compound(_, args) => {
                // Recursively validate nested compound arguments
                for nested_arg in args {
                    Self::validate_head_argument(nested_arg)?;
                }
                Ok(())
            }
        }
    }
    
    /// Pretty print the remaining tokens (useful for debugging)
    /// 
    /// Returns a slice of all tokens from the current position to the end.
    /// This is helpful for debugging parser state and understanding what
    /// tokens are left to be processed.
    pub fn remaining_tokens(&self) -> Vec<&Token> {
        self.tokens[self.position..].iter().collect()
    }
}

/// Utility functions for parsing
/// 
/// These are convenience functions that create a parser, perform a specific
/// parsing task, and return the result. They handle the common patterns of
/// parsing different types of Prolog constructs from token streams.
impl Parser {
    /// Create a parser and parse a single term from a token stream
    /// 
    /// Convenience function for parsing just a term without needing
    /// to manually create a parser. Used primarily in tests and for
    /// parsing term-only inputs.
    pub fn parse_term_from_tokens(tokens: Vec<Token>) -> ParseResult<Term> {
        let mut parser = Parser::new(tokens);
        parser.parse_term()
    }
    
    /// Create a parser and parse a single clause from a token stream
    /// 
    /// Convenience function that parses a clause and ensures it's
    /// properly terminated with a dot. This enforces the Prolog
    /// convention that clauses end with periods.
    pub fn parse_clause_from_tokens(tokens: Vec<Token>) -> ParseResult<Clause> {
        let mut parser = Parser::new(tokens);
        let clause = parser.parse_clause()?;
        parser.expect(Token::Dot)?;
        Ok(clause)
    }
    
    /// Create a parser and parse a query from a token stream
    /// 
    /// Queries can end with either '?' or '.' in different Prolog systems.
    /// This function accepts both conventions for compatibility.
    /// 
    /// The query itself is just a list of goals (comma-separated terms).
    pub fn parse_query_from_tokens(tokens: Vec<Token>) -> ParseResult<Vec<Term>> {
        let mut parser = Parser::new(tokens);
        let query = parser.parse_query()?;
        
        // Accept either '?' or '.' at end of query
        if parser.check(&Token::Question) {
            parser.advance();
        } else {
            parser.expect(Token::Dot)?;
        }
        
        Ok(query)
    }
}

// Link to the test module
#[cfg(test)]
#[path = "parser_tests.rs"]
mod tests;