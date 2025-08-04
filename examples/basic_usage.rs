// basic_usage.rs
//

//! Basic usage example for the Neorusticus Prolog library
//! 
//! This example demonstrates the main features and error handling capabilities
//! of the Prolog engine, similar to the original main() function.

use neorusticus::{PrologEngine, quick_query};
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    println!("=== Neorusticus Prolog Engine Demo ===\n");
    
    // Create engine with conservative limits for safety
    let mut engine = PrologEngine::with_limits(50);
    
    // Test basic parsing with error handling
    println!("=== Testing Basic Operations ===");
    
    // Test successful operations
    match engine.parse_and_add("parent(tom, bob).") {
        Ok(()) => println!("✓ Successfully added: parent(tom, bob)."),
        Err(e) => {
            println!("✗ Failed to add clause:");
            engine.print_error(&e);
        }
    }
    
    match engine.parse_and_add("parent(bob, ann).") {
        Ok(()) => println!("✓ Successfully added: parent(bob, ann)."),
        Err(e) => {
            println!("✗ Failed to add clause:");
            engine.print_error(&e);
        }
    }
    
    // Test error cases
    println!("\n=== Testing Error Handling ===");
    
    // Test syntax errors
    println!("Testing syntax errors:");
    
    if let Err(e) = engine.parse_and_add("parent(tom bob).") { // Missing comma
        println!("✓ Caught syntax error: {}", e);
    }
    
    if let Err(e) = engine.parse_and_add("parent(tom, bob") { // Missing closing paren
        println!("✓ Caught delimiter error: {}", e);
    }
    
    if let Err(e) = engine.parse_and_add("parent(tom, bob)") { // Missing dot
        println!("✓ Caught missing dot error: {}", e);
    }
    
    if let Err(e) = engine.parse_and_add("parent(tom, 999999999999999999999).") { // Number too large
        println!("✓ Caught number overflow error: {}", e);
    }
    
    // Test arithmetic operations with error handling
    println!("\n=== Testing Arithmetic Error Handling ===");
    
    engine.parse_and_add("test_arith :- X is 5 + 3.")?;
    
    // Test division by zero
    if let Err(e) = engine.parse_query("X is 5 // 0.") {
        println!("✓ Caught division by zero: {}", e);
    }
    
    // Test uninstantiated variable in arithmetic
    if let Err(e) = engine.parse_query("X is Y + 1.") {
        println!("✓ Caught uninstantiated variable: {}", e);
    }
    
    // Test type mismatch
    if let Err(e) = engine.parse_query("X is atom + 1.") {
        println!("✓ Caught type mismatch: {}", e);
    }
    
    // Test successful arithmetic
    match engine.parse_query("X is 2 + 3 * 4.") {
        Ok(solutions) => {
            println!("✓ Arithmetic success:");
            engine.print_solutions(&solutions, &["X".to_string()]);
        }
        Err(e) => {
            println!("✗ Unexpected arithmetic error:");
            engine.print_boxed_error(&e);
        }
    }
    
    // Test list operations with error handling
    println!("\n=== Testing List Error Handling ===");
    
    // Test invalid list structure
    if let Err(e) = engine.parse_query("member(X, not_a_list).") {
        println!("✓ Caught invalid list structure: {}", e);
    }
    
    // Test uninstantiated list
    if let Err(e) = engine.parse_query("length(L, 3).") {
        println!("✓ Caught uninstantiated list: {}", e);
    }
    
    // Test successful list operations
    match engine.parse_query("append([1, 2], [3, 4], X).") {
        Ok(solutions) => {
            println!("✓ List append success:");
            engine.print_solutions(&solutions, &["X".to_string()]);
        }
        Err(e) => {
            println!("✗ Unexpected list error:");
            engine.print_boxed_error(&e);
        }
    }
    
    // Test predicate suggestions
    println!("\n=== Testing Predicate Suggestions ===");
    
    if let Err(e) = engine.parse_query("lentgh([1, 2, 3], X).") { // Typo in "length"
        println!("✓ Predicate suggestion: {}", e);
    }
    
    if let Err(e) = engine.parse_query("appendd([1], [2], X).") { // Typo in "append"
        println!("✓ Predicate suggestion: {}", e);
    }
    
    // Test stack overflow protection with a safer approach
    println!("\n=== Testing Stack Overflow Protection ===");
    
    // Use a very conservative engine for this test
    let mut test_engine = PrologEngine::with_limits(5);
    
    // Add the infinite recursion rule to the test engine only
    match test_engine.parse_and_add("infinite(X) :- infinite(X).") {
        Ok(_) => {
            // Now test the query with the dangerous rule
            match test_engine.parse_query("infinite(test).") {
                Ok(_) => println!("✗ Failed to catch infinite recursion"),
                Err(e) => println!("✓ Caught infinite recursion: {}", e),
            }
        }
        Err(e) => {
            println!("✗ Failed to add infinite rule: {}", e);
        }
    }
    
    // Test cut operations
    println!("\n=== Testing Cut Operations ===");
    
    engine.parse_and_add("max(X, Y, X) :- X >= Y, !.")?;
    engine.parse_and_add("max(X, Y, Y).")?;
    
    match engine.parse_query("max(5, 3, Z).") {
        Ok(solutions) => {
            println!("✓ Cut operation success:");
            engine.print_solutions(&solutions, &["Z".to_string()]);
        }
        Err(e) => {
            println!("✗ Unexpected cut error:");
            engine.print_boxed_error(&e);
        }
    }
    
    // Display engine statistics
    println!("\n=== Engine Statistics ===");
    println!("{}", engine.get_stats());
    
    // Test complex query with multiple error possibilities
    println!("\n=== Testing Complex Query ===");
    
    engine.parse_and_add("complex(X, Y) :- X > 0, Y is X * 2, Y < 20.")?;
    
    match engine.parse_query("complex(5, Z).") {
        Ok(solutions) => {
            println!("✓ Complex query success:");
            engine.print_solutions(&solutions, &["Z".to_string()]);
        }
        Err(e) => {
            println!("✗ Complex query error:");
            engine.print_boxed_error(&e);
        }
    }
    
    // Test recovery from errors
    println!("\n=== Testing Error Recovery ===");
    
    // Even after errors, the engine should continue to work
    match engine.parse_query("parent(tom, X).") {
        Ok(solutions) => {
            println!("✓ Engine recovered, normal operation:");
            engine.print_solutions(&solutions, &["X".to_string()]);
        }
        Err(e) => {
            println!("✗ Engine failed to recover:");
            engine.print_boxed_error(&e);
        }
    }
    
    // Demonstrate the quick_query convenience function
    println!("\n=== Testing Quick Query Function ===");
    
    let clauses = &[
        "ancestor(X, Y) :- parent(X, Y).",
        "ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).",
        "parent(alice, bob).",
        "parent(bob, charlie).",
        "parent(charlie, diana).",
    ];
    
    match quick_query(clauses, "ancestor(alice, diana).") {
        Ok(solutions) => {
            println!("✓ Quick query found {} solutions", solutions.len());
        }
        Err(e) => {
            println!("✗ Quick query failed: {}", e);
        }
    }
    
    println!("\n=== All tests completed ===");
    Ok(())
}