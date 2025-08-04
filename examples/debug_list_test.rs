// debug_list_test.rs
// Let's test what actually happens with list operations

use neorusticus::PrologEngine;

fn main() {
    let mut engine = PrologEngine::new();
    
    println!("Testing various list operations to see what actually happens...\n");
    
    // Test 1: member(X, L) - two uninstantiated variables
    println!("Test 1: member(X, L).");
    match engine.parse_query("member(X, L).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 2: member(X, atom_not_list) - atom as second argument
    println!("\nTest 2: member(X, atom_not_list).");
    match engine.parse_query("member(X, atom_not_list).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 3: member(X, 123) - number as second argument
    println!("\nTest 3: member(X, 123).");
    match engine.parse_query("member(X, 123).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 4: length(L, 3) - uninstantiated list
    println!("\nTest 4: length(L, 3).");
    match engine.parse_query("length(L, 3).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 5: length(atom, X) - atom as first argument
    println!("\nTest 5: length(atom, X).");
    match engine.parse_query("length(atom, X).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 6: append(atom, [1, 2], X) - atom as first argument
    println!("\nTest 6: append(atom, [1, 2], X).");
    match engine.parse_query("append(atom, [1, 2], X).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 7: append(X, Y, atom) - atom as third argument
    println!("\nTest 7: append(X, Y, atom).");
    match engine.parse_query("append(X, Y, atom).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    println!("\nBased on these results, we can see which operations actually error vs succeed with 0 solutions.");
}