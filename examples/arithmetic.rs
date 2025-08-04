// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: arithmetic.rs
// Creator: Jonas Forsman

//! Arithmetic operations example for the Neorusticus Prolog engine
//! 
//! This example demonstrates the arithmetic capabilities of the Prolog engine,
//! including basic operations, comparisons, and mathematical expressions.

use neorusticus::PrologEngine;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    println!("=== Neorusticus Prolog Arithmetic Examples ===\n");
    
    let mut engine = PrologEngine::new();
    
    // Basic arithmetic evaluation
    println!("=== Basic Arithmetic ===");
    
    demo_query(&mut engine, "X is 2 + 3", "Simple addition");
    demo_query(&mut engine, "Y is 10 - 4", "Simple subtraction");
    demo_query(&mut engine, "Z is 6 * 7", "Simple multiplication");
    demo_query(&mut engine, "W is 15 // 3", "Integer division");
    demo_query(&mut engine, "R is 17 mod 5", "Modulo operation");
    
    println!("\n=== Complex Expressions ===");
    
    demo_query(&mut engine, "X is 2 + 3 * 4", "Operator precedence (2 + 3 * 4)");
    demo_query(&mut engine, "Y is (2 + 3) * 4", "Parentheses override precedence");
    demo_query(&mut engine, "Z is 100 // (5 + 5)", "Division with parentheses");
    demo_query(&mut engine, "W is 2 * 3 + 4 * 5", "Multiple operations");
    
    println!("\n=== Negative Numbers ===");
    
    demo_query(&mut engine, "X is -5", "Negative number");
    demo_query(&mut engine, "Y is 10 + (-3)", "Adding negative number");
    demo_query(&mut engine, "Z is -10 * -2", "Multiplying negatives");
    demo_query(&mut engine, "W is abs(-42)", "Absolute value");
    
    println!("\n=== Arithmetic Comparisons ===");
    
    demo_query(&mut engine, "5 > 3", "Greater than (true)");
    demo_query(&mut engine, "2 > 8", "Greater than (false)");
    demo_query(&mut engine, "10 >= 10", "Greater than or equal");
    demo_query(&mut engine, "7 < 12", "Less than");
    demo_query(&mut engine, "15 =< 15", "Less than or equal");
    demo_query(&mut engine, "6 =:= 6", "Arithmetic equality");
    demo_query(&mut engine, "5 =\\= 7", "Arithmetic inequality");
    
    println!("\n=== Advanced Functions ===");
    
    demo_query(&mut engine, "X is max(10, 25)", "Maximum of two numbers");
    demo_query(&mut engine, "Y is min(15, 8)", "Minimum of two numbers");
    demo_query(&mut engine, "Z is abs(-17)", "Absolute value");
    
    println!("\n=== Arithmetic in Rules ===");
    
    // Add some rules that use arithmetic
    engine.parse_and_add("double(X, Y) :- Y is X * 2.").unwrap();
    engine.parse_and_add("square(X, Y) :- Y is X * X.").unwrap();
    engine.parse_and_add("factorial(0, 1).").unwrap();
    engine.parse_and_add("factorial(N, F) :- N > 0, N1 is N - 1, factorial(N1, F1), F is N * F1.").unwrap();
    engine.parse_and_add("even(N) :- 0 =:= N mod 2.").unwrap();
    engine.parse_and_add("odd(N) :- 1 =:= N mod 2.").unwrap();
    
    println!("Added arithmetic rules to database...\n");
    
    demo_query(&mut engine, "double(5, X)", "Double a number");
    demo_query(&mut engine, "square(6, Y)", "Square a number");
    demo_query(&mut engine, "factorial(4, F)", "Factorial of 4");
    demo_query(&mut engine, "even(8)", "Test if 8 is even");
    demo_query(&mut engine, "odd(7)", "Test if 7 is odd");
    demo_query(&mut engine, "even(7)", "Test if 7 is even (should fail)");
    
    println!("\n=== Range Checking ===");
    
    engine.parse_and_add("in_range(X, Min, Max) :- X >= Min, X =< Max.").unwrap();
    engine.parse_and_add("temperature_ok(T) :- in_range(T, 18, 25).").unwrap();
    
    demo_query(&mut engine, "in_range(15, 10, 20)", "15 in range 10-20");
    demo_query(&mut engine, "in_range(25, 10, 20)", "25 in range 10-20 (should fail)");
    demo_query(&mut engine, "temperature_ok(22)", "Temperature 22°C OK");
    demo_query(&mut engine, "temperature_ok(30)", "Temperature 30°C OK (should fail)");
    
    println!("\n=== Error Handling Examples ===");
    
    println!("Testing division by zero:");
    match engine.parse_query("X is 10 // 0.") {
        Ok(_) => println!("  Unexpected success!"),
        Err(e) => println!("  ✓ Caught error: {}", e),
    }
    
    println!("\nTesting uninstantiated variable:");
    match engine.parse_query("X is Y + 1.") {
        Ok(_) => println!("  Unexpected success!"),
        Err(e) => println!("  ✓ Caught error: {}", e),
    }
    
    println!("\nTesting type mismatch:");
    match engine.parse_query("X is hello + 1.") {
        Ok(_) => println!("  Unexpected success!"),
        Err(e) => println!("  ✓ Caught error: {}", e),
    }
    
    println!("\n=== Mathematical Sequences ===");
    
    engine.parse_and_add("fibonacci(0, 0).").unwrap();
    engine.parse_and_add("fibonacci(1, 1).").unwrap();
    engine.parse_and_add("fibonacci(N, F) :- N > 1, N1 is N - 1, N2 is N - 2, fibonacci(N1, F1), fibonacci(N2, F2), F is F1 + F2.").unwrap();
    
    demo_query(&mut engine, "fibonacci(6, F)", "6th Fibonacci number");
    demo_query(&mut engine, "fibonacci(8, F)", "8th Fibonacci number");
    
    println!("\n=== Statistics ===");
    println!("{}", engine.get_stats());
    
    println!("\n=== Arithmetic Examples Complete! ===");
    
    Ok(())
}

fn demo_query(engine: &mut PrologEngine, query: &str, description: &str) {
    println!("{}: {}", description, query);
    
    let query_with_dot = if query.ends_with('.') {
        query.to_string()
    } else {
        format!("{}.", query)
    };
    
    match engine.parse_query(&query_with_dot) {
        Ok(solutions) => {
            if solutions.is_empty() {
                println!("  Result: false");
            } else {
                // Extract variables from query for display
                let variables = extract_variables_from_query(query);
                if variables.is_empty() {
                    println!("  Result: true");
                } else {
                    print!("  Result: ");
                    engine.print_solutions(&solutions, &variables);
                }
            }
        }
        Err(e) => {
            println!("  Error: {}", e);
        }
    }
    println!();
}

fn extract_variables_from_query(query: &str) -> Vec<String> {
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
            
            if !variables.contains(&var_name) && var_name != "_" {
                variables.push(var_name);
            }
        }
    }
    
    variables
}