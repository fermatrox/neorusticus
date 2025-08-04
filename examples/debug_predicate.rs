// Copyright 2025 Jonas Forsman
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Project name: neorusticus
// Filename: debug_predicate.rs
// Creator: Jonas Forsman

// Let's test what actually happens with undefined predicates

use neorusticus::PrologEngine;

fn main() {
    let mut engine = PrologEngine::new();
    
    println!("Testing undefined predicates to see what actually happens...\n");
    
    // Test 1: lengthh (typo in length)
    println!("Test 1: lengthh([1, 2, 3], X).");
    match engine.parse_query("lengthh([1, 2, 3], X).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 2: appnd (typo in append)
    println!("\nTest 2: appnd([1], [2], X).");
    match engine.parse_query("appnd([1], [2], X).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 3: append/2 (wrong arity)
    println!("\nTest 3: append([1], [2]).");
    match engine.parse_query("append([1], [2]).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 4: completely made up predicate
    println!("\nTest 4: totally_fake_predicate_xyz(X).");
    match engine.parse_query("totally_fake_predicate_xyz(X).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 5: known built-in (should work)
    println!("\nTest 5: append([1], [2], X). (correct arity)");
    match engine.parse_query("append([1], [2], X).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 6: another known built-in
    println!("\nTest 6: length([1, 2, 3], X). (correct)");
    match engine.parse_query("length([1, 2, 3], X).") {
        Ok(solutions) => println!("  SUCCESS: Found {} solutions", solutions.len()),
        Err(e) => println!("  ERROR: {}", e),
    }
    
    // Test 7: Check if predicates are somehow being added
    println!("\nChecking defined predicates:");
    let predicates = engine.list_predicates();
    println!("  User-defined predicates: {:?}", predicates);
    
    let builtins = engine.list_builtins();
    println!("  Built-in predicates count: {}", builtins.len());
    
    println!("\nThis will show us which queries actually fail vs succeed.");
}