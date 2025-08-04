// parser.rs
//
// TODO: Move relevant code from main.rs to this module

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
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    /// Create a new parser with the given tokens
    pub fn new(tokens: Vec<Token>) -> Self {
        Parser { tokens, position: 0 }
    }
    
    /// Get the current token without consuming it
    pub fn current_token(&self) -> &Token {
        self.tokens.get(self.position).unwrap_or(&Token::Eof)
    }
    
    /// Peek at the next token without consuming the current one
    pub fn peek_token(&self) -> &Token {
        self.tokens.get(self.position + 1).unwrap_or(&Token::Eof)
    }
    
    /// Advance to the next token
    pub fn advance(&mut self) {
        if self.position < self.tokens.len() {
            self.position += 1;
        }
    }
    
    /// Get the current position for error reporting
    pub fn current_position(&self) -> Position {
        Position::new(0, 0, self.position) // Simplified - lexer should provide real positions
    }
    
    /// Expect a specific token and advance, or return an error
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
    pub fn check(&self, expected: &Token) -> bool {
        std::mem::discriminant(self.current_token()) == std::mem::discriminant(expected)
    }
    
    /// Parse a complete term
    pub fn parse_term(&mut self) -> ParseResult<Term> {
        self.parse_expression()
    }
    
    /// Parse expressions with full operator precedence
    /// 
    /// Precedence levels (highest to lowest):
    /// 1. Primary terms (atoms, variables, numbers, parentheses)
    /// 2. Multiplicative (*, //, mod)
    /// 3. Additive (+, -)
    /// 4. Comparison (>, <, >=, =<, =:=, =\=)
    /// 5. Unification (=, \=, is)
    pub fn parse_expression(&mut self) -> ParseResult<Term> {
        self.parse_unification()
    }
    
    /// Parse unification operators (=, \=, is) - lowest precedence
    pub fn parse_unification(&mut self) -> ParseResult<Term> {
        let mut left = self.parse_comparison()?;
        
        while let Some(op) = self.get_unification_op() {
            self.advance(); // consume operator
            let right = self.parse_comparison()?;
            left = Term::Compound(op, vec![left, right]);
        }
        
        Ok(left)
    }
    
    /// Parse comparison operators (>, <, =:=, etc.)
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
    pub fn parse_additive(&mut self) -> ParseResult<Term> {
        let mut left = self.parse_multiplicative()?;
        
        while matches!(self.current_token(), Token::Plus | Token::Minus) {
            let op = match self.current_token() {
                Token::Plus => "+".to_string(),
                Token::Minus => "-".to_string(),
                _ => unreachable!(),
            };
            self.advance();
            let right = self.parse_multiplicative()?;
            left = Term::Compound(op, vec![left, right]);
        }
        
        Ok(left)
    }
    
    /// Parse multiplicative operators (*, //, mod)
    pub fn parse_multiplicative(&mut self) -> ParseResult<Term> {
        let mut left = self.parse_unary()?;
        
        while matches!(self.current_token(), Token::Multiply | Token::Divide | Token::Mod) {
            let op = match self.current_token() {
                Token::Multiply => "*".to_string(),
                Token::Divide => "//".to_string(),
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
    pub fn parse_unary(&mut self) -> ParseResult<Term> {
        // For now, unary operators are handled in the lexer (negative numbers)
        // This could be extended for other unary operators like logical not
        self.parse_primary()
    }
    
    /// Parse primary terms (atoms, variables, numbers, parenthesized expressions, lists)
    pub fn parse_primary(&mut self) -> ParseResult<Term> {
        match self.current_token().clone() {
            Token::Atom(name) => {
                self.advance();
                
                if self.check(&Token::LeftParen) {
                    // Compound term
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
                self.advance();
                Ok(Term::Variable(name))
            }
            Token::Number(n) => {
                self.advance();
                Ok(Term::Number(n))
            }
            Token::Cut => {
                self.advance();
                Ok(Term::Atom("!".to_string()))
            }
            Token::LeftBracket => {
                self.parse_list()
            }
            Token::LeftParen => {
                self.advance(); // consume '('
                let expr = self.parse_expression()?;
                self.expect(Token::RightParen)?;
                Ok(expr)
            }
            Token::Minus => {
                // Handle unary minus that wasn't caught by lexer
                self.advance();
                let operand = self.parse_unary()?;
                Ok(Term::Compound("-".to_string(), vec![operand]))
            }
            _ => Err(ParseError::UnexpectedToken {
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
    
    /// Parse a list of arguments separated by commas
    pub fn parse_argument_list(&mut self) -> ParseResult<Vec<Term>> {
        let mut args = Vec::new();
        
        if !self.check(&Token::RightParen) {
            args.push(self.parse_expression()?);
            
            while self.check(&Token::Comma) {
                self.advance(); // consume ','
                args.push(self.parse_expression()?);
            }
        }
        
        Ok(args)
    }
    
    /// Get unification operator if current token is one
    pub fn get_unification_op(&self) -> Option<String> {
        match self.current_token() {
            Token::Unify => Some("=".to_string()),
            Token::NotUnify => Some("\\=".to_string()),
            Token::Is => Some("is".to_string()),
            _ => None,
        }
    }
    
    /// Get comparison operator if current token is one
    pub fn get_comparison_op(&self) -> Option<String> {
        match self.current_token() {
            Token::Greater => Some(">".to_string()),
            Token::Less => Some("<".to_string()),
            Token::GreaterEq => Some(">=".to_string()),
            Token::LessEq => Some("=<".to_string()),
            Token::ArithEq => Some("=:=".to_string()),
            Token::ArithNeq => Some("=\\=".to_string()),
            _ => None,
        }
    }
    
    /// Parse Prolog lists [a, b, c] or [H|T]
    pub fn parse_list(&mut self) -> ParseResult<Term> {
        self.expect(Token::LeftBracket)?;
        
        if self.check(&Token::RightBracket) {
            // Empty list []
            self.advance();
            return Ok(Term::Atom("[]".to_string()));
        }
        
        let mut elements = Vec::new();
        elements.push(self.parse_expression()?);
        
        while self.check(&Token::Comma) {
            self.advance(); // consume ','
            elements.push(self.parse_expression()?);
        }
        
        let tail = if self.check(&Token::Pipe) {
            self.advance(); // consume '|'
            Some(Box::new(self.parse_expression()?))
        } else {
            None
        };
        
        self.expect(Token::RightBracket)?;
        
        // Build list structure from right to left
        let mut result = tail.unwrap_or_else(|| Box::new(Term::Atom("[]".to_string())));
        
        for element in elements.into_iter().rev() {
            result = Box::new(Term::Compound(".".to_string(), vec![element, *result]));
        }
        
        Ok(*result)
    }
    
    /// Parse a clause (fact or rule)
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
    pub fn parse_goal_list(&mut self) -> ParseResult<Vec<Term>> {
        let mut goals = Vec::new();
        
        goals.push(self.parse_expression()?);
        
        while self.check(&Token::Comma) {
            self.advance(); // consume ','
            goals.push(self.parse_expression()?);
        }
        
        Ok(goals)
    }
    
    /// Parse a query (goals ending with ? or .)
    pub fn parse_query(&mut self) -> ParseResult<Vec<Term>> {
        self.parse_goal_list()
    }
    
    /// Parse multiple clauses separated by dots
    pub fn parse_program(&mut self) -> ParseResult<Vec<Clause>> {
        let mut clauses = Vec::new();
        
        while !self.check(&Token::Eof) {
            // Skip any extra dots or whitespace
            while self.check(&Token::Dot) {
                self.advance();
            }
            
            if self.check(&Token::Eof) {
                break;
            }
            
            let clause = self.parse_clause()?;
            clauses.push(clause);
            
            // Expect dot after clause
            self.expect(Token::Dot)?;
        }
        
        Ok(clauses)
    }
    
    /// Get current parsing position (for error reporting)
    pub fn position(&self) -> usize {
        self.position
    }
    
    /// Check if we're at the end of input
    pub fn is_at_end(&self) -> bool {
        matches!(self.current_token(), Token::Eof)
    }
    
    /// Skip to the next likely recovery point (typically a dot or eof)
    pub fn skip_to_recovery_point(&mut self) {
        while !matches!(self.current_token(), Token::Dot | Token::Eof) {
            self.advance();
        }
    }
    
    /// Parse with error recovery - continues parsing even after errors
    pub fn parse_with_recovery(&mut self) -> (Vec<Clause>, Vec<ParseError>) {
        let mut clauses = Vec::new();
        let mut errors = Vec::new();
        
        while !self.is_at_end() {
            // Skip extra dots
            while self.check(&Token::Dot) {
                self.advance();
            }
            
            if self.is_at_end() {
                break;
            }
            
            match self.parse_clause() {
                Ok(clause) => {
                    if let Err(e) = self.expect(Token::Dot) {
                        errors.push(e);
                        self.skip_to_recovery_point();
                    } else {
                        clauses.push(clause);
                    }
                }
                Err(e) => {
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
    pub fn validate_clause_head(head: &Term) -> ParseResult<()> {
        match head {
            Term::Atom(_) => Ok(()),
            Term::Compound(_, args) => {
                // Check that all arguments in head are valid
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
    fn validate_head_argument(arg: &Term) -> ParseResult<()> {
        match arg {
            Term::Atom(_) | Term::Variable(_) | Term::Number(_) => Ok(()),
            Term::Compound(_, args) => {
                for nested_arg in args {
                    Self::validate_head_argument(nested_arg)?;
                }
                Ok(())
            }
        }
    }
    
    /// Pretty print the remaining tokens (useful for debugging)
    pub fn remaining_tokens(&self) -> Vec<&Token> {
        self.tokens[self.position..].iter().collect()
    }
}

/// Utility functions for parsing
impl Parser {
    /// Create a parser and parse a single term from a token stream
    pub fn parse_term_from_tokens(tokens: Vec<Token>) -> ParseResult<Term> {
        let mut parser = Parser::new(tokens);
        parser.parse_term()
    }
    
    /// Create a parser and parse a single clause from a token stream
    pub fn parse_clause_from_tokens(tokens: Vec<Token>) -> ParseResult<Clause> {
        let mut parser = Parser::new(tokens);
        let clause = parser.parse_clause()?;
        parser.expect(Token::Dot)?;
        Ok(clause)
    }
    
    /// Create a parser and parse a query from a token stream
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Tokenizer;

    fn parse_term_string(input: &str) -> ParseResult<Term> {
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize()?;
        Parser::parse_term_from_tokens(tokens)
    }
    
    fn parse_clause_string(input: &str) -> ParseResult<Clause> {
        let mut tokenizer = Tokenizer::new(input);
        let tokens = tokenizer.tokenize()?;
        Parser::parse_clause_from_tokens(tokens)
    }

    #[test]
    fn test_parse_atoms() {
        let term = parse_term_string("hello").unwrap();
        assert_eq!(term, Term::Atom("hello".to_string()));
    }

    #[test]
    fn test_parse_variables() {
        let term = parse_term_string("X").unwrap();
        assert_eq!(term, Term::Variable("X".to_string()));
        
        let term = parse_term_string("_var").unwrap();
        assert_eq!(term, Term::Variable("_var".to_string()));
    }

    #[test]
    fn test_parse_numbers() {
        let term = parse_term_string("42").unwrap();
        assert_eq!(term, Term::Number(42));
        
        let term = parse_term_string("-17").unwrap();
        assert_eq!(term, Term::Number(-17));
    }

    #[test]
    fn test_parse_compound_terms() {
        let term = parse_term_string("foo(bar, X)").unwrap();
        match term {
            Term::Compound(functor, args) => {
                assert_eq!(functor, "foo");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], Term::Atom("bar".to_string()));
                assert_eq!(args[1], Term::Variable("X".to_string()));
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_parse_lists() {
        // Empty list
        let term = parse_term_string("[]").unwrap();
        assert_eq!(term, Term::Atom("[]".to_string()));
        
        // Simple list
        let term = parse_term_string("[1, 2, 3]").unwrap();
        assert!(term.is_proper_list());
        let elements = term.to_list().unwrap();
        assert_eq!(elements.len(), 3);
        
        // List with tail
        let term = parse_term_string("[H|T]").unwrap();
        match term {
            Term::Compound(functor, args) => {
                assert_eq!(functor, ".");
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], Term::Variable("H".to_string()));
                assert_eq!(args[1], Term::Variable("T".to_string()));
            }
            _ => panic!("Expected compound term for list"),
        }
    }

    #[test]
    fn test_parse_arithmetic() {
        let term = parse_term_string("2 + 3 * 4").unwrap();
        // Should parse as: 2 + (3 * 4) due to precedence
        match term {
            Term::Compound(op, args) => {
                assert_eq!(op, "+");
                assert_eq!(args[0], Term::Number(2));
                match &args[1] {
                    Term::Compound(inner_op, inner_args) => {
                        assert_eq!(inner_op, "*");
                        assert_eq!(inner_args[0], Term::Number(3));
                        assert_eq!(inner_args[1], Term::Number(4));
                    }
                    _ => panic!("Expected multiplication term"),
                }
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_parse_comparison() {
        let term = parse_term_string("X > 5").unwrap();
        match term {
            Term::Compound(op, args) => {
                assert_eq!(op, ">");
                assert_eq!(args[0], Term::Variable("X".to_string()));
                assert_eq!(args[1], Term::Number(5));
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_parse_unification() {
        let term = parse_term_string("X = hello").unwrap();
        match term {
            Term::Compound(op, args) => {
                assert_eq!(op, "=");
                assert_eq!(args[0], Term::Variable("X".to_string()));
                assert_eq!(args[1], Term::Atom("hello".to_string()));
            }
            _ => panic!("Expected compound term"),
        }
        
        let term = parse_term_string("Y is 2 + 3").unwrap();
        match term {
            Term::Compound(op, args) => {
                assert_eq!(op, "is");
                assert_eq!(args[0], Term::Variable("Y".to_string()));
                // args[1] should be the parsed arithmetic expression
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_parse_facts() {
        let clause = parse_clause_string("parent(tom, bob).").unwrap();
        assert!(clause.is_fact());
        
        match clause.head {
            Term::Compound(functor, args) => {
                assert_eq!(functor, "parent");
                assert_eq!(args.len(), 2);
            }
            _ => panic!("Expected compound head"),
        }
    }

    #[test]
    fn test_parse_rules() {
        let clause = parse_clause_string("grandparent(X, Z) :- parent(X, Y), parent(Y, Z).").unwrap();
        assert!(clause.is_rule());
        assert_eq!(clause.body.len(), 2);
        
        // Check head
        if let Some(("grandparent", 2)) = clause.head.functor_arity() {
            // OK
        } else {
            panic!("Expected grandparent/2 head");
        }
    }

    #[test]
    fn test_parse_cut() {
        let term = parse_term_string("!").unwrap();
        assert_eq!(term, Term::Atom("!".to_string()));
    }

    #[test]
    fn test_parse_parentheses() {
        let term = parse_term_string("(2 + 3) * 4").unwrap();
        // Should parse as: (2 + 3) * 4
        match term {
            Term::Compound(op, args) => {
                assert_eq!(op, "*");
                match &args[0] {
                    Term::Compound(inner_op, inner_args) => {
                        assert_eq!(inner_op, "+");
                        assert_eq!(inner_args[0], Term::Number(2));
                        assert_eq!(inner_args[1], Term::Number(3));
                    }
                    _ => panic!("Expected addition term"),
                }
                assert_eq!(args[1], Term::Number(4));
            }
            _ => panic!("Expected compound term"),
        }
    }

    #[test]
    fn test_operator_precedence() {
        // Test that * has higher precedence than +
        let term = parse_term_string("1 + 2 * 3").unwrap();
        match term {
            Term::Compound(op, args) => {
                assert_eq!(op, "+");
                assert_eq!(args[0], Term::Number(1));
                match &args[1] {
                    Term::Compound(mult_op, mult_args) => {
                        assert_eq!(mult_op, "*");
                        assert_eq!(mult_args[0], Term::Number(2));
                        assert_eq!(mult_args[1], Term::Number(3));
                    }
                    _ => panic!("Expected multiplication"),
                }
            }
            _ => panic!("Expected addition at top level"),
        }
    }

    #[test]
    fn test_error_handling() {
        // Test unclosed parenthesis - this should be caught by the lexer first
        let mut tokenizer = Tokenizer::new("foo(bar");
        let result = tokenizer.tokenize();
        assert!(result.is_err(), "Lexer should catch unclosed parenthesis");
        
        // Test incomplete expression - operator without right operand
        let tokens = vec![Token::Variable("X".to_string()), Token::Plus, Token::Eof];
        let mut parser = Parser::new(tokens);
        let result = parser.parse_expression();
        assert!(result.is_err(), "Parser should reject incomplete expressions");
        
        // Test unexpected token in primary position
        let tokens = vec![Token::Plus, Token::Eof]; // Starting with operator
        let mut parser = Parser::new(tokens);
        let result = parser.parse_expression();
        assert!(result.is_err(), "Parser should reject expression starting with operator");
        
        // Test mismatched parentheses (caught by lexer)
        let result = parse_term_string("foo)");
        assert!(result.is_err(), "Should reject unexpected closing parenthesis");
        
        // Test incomplete compound term
        let result = parse_term_string("foo(");
        assert!(result.is_err(), "Should reject unclosed function call");
    }

    #[test]
    fn test_complex_expressions() {
        let clause = parse_clause_string("test(X, Y) :- X > 0, Y is X * 2, Y < 20.").unwrap();
        assert!(clause.is_rule());
        assert_eq!(clause.body.len(), 3);
        
        // Verify the goals are parsed correctly
        let goals = &clause.body;
        
        // First goal: X > 0
        if let Term::Compound(op, args) = &goals[0] {
            assert_eq!(op, ">");
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected comparison in first goal");
        }
        
        // Second goal: Y is X * 2
        if let Term::Compound(op, args) = &goals[1] {
            assert_eq!(op, "is");
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected 'is' in second goal");
        }
        
        // Third goal: Y < 20
        if let Term::Compound(op, args) = &goals[2] {
            assert_eq!(op, "<");
            assert_eq!(args.len(), 2);
        } else {
            panic!("Expected comparison in third goal");
        }
    }
}