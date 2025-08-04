// engine_bench.rs
//

//! Performance benchmarks for the Neorusticus Prolog engine
//! 
//! These benchmarks measure the performance of various engine operations
//! to help identify bottlenecks and track performance improvements.

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use neorusticus::{PrologEngine, quick_query};

fn bench_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("parsing");
    
    let simple_fact = "parent(tom, bob).";
    let complex_rule = "ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).";
    let arithmetic_rule = "factorial(N, F) :- N > 0, N1 is N - 1, factorial(N1, F1), F is N * F1.";
    
    group.bench_function("simple_fact", |b| {
        b.iter(|| {
            let mut engine = PrologEngine::new();
            engine.parse_and_add(black_box(simple_fact)).unwrap();
        });
    });
    
    group.bench_function("complex_rule", |b| {
        b.iter(|| {
            let mut engine = PrologEngine::new();
            engine.parse_and_add(black_box(complex_rule)).unwrap();
        });
    });
    
    group.bench_function("arithmetic_rule", |b| {
        b.iter(|| {
            let mut engine = PrologEngine::new();
            engine.parse_and_add(black_box(arithmetic_rule)).unwrap();
        });
    });
    
    group.finish();
}

fn bench_simple_queries(c: &mut Criterion) {
    let mut group = c.benchmark_group("simple_queries");
    
    let mut engine = PrologEngine::new();
    engine.parse_and_add("parent(tom, bob).").unwrap();
    engine.parse_and_add("parent(bob, ann).").unwrap();
    engine.parse_and_add("parent(ann, sue).").unwrap();
    engine.parse_and_add("parent(sue, joe).").unwrap();
    
    group.bench_function("direct_fact", |b| {
        b.iter(|| {
            black_box(engine.parse_query("parent(tom, bob).").unwrap());
        });
    });
    
    group.bench_function("variable_query", |b| {
        b.iter(|| {
            black_box(engine.parse_query("parent(tom, X).").unwrap());
        });
    });
    
    group.bench_function("backtracking_query", |b| {
        b.iter(|| {
            black_box(engine.parse_query("parent(X, Y).").unwrap());
        });
    });
    
    group.finish();
}

fn bench_recursive_queries(c: &mut Criterion) {
    let mut group = c.benchmark_group("recursive_queries");
    
    // Create a chain of ancestry
    let mut engine = PrologEngine::new();
    for i in 0..20 {
        engine.parse_and_add(&format!("parent(person{}, person{}).", i, i + 1)).unwrap();
    }
    engine.parse_and_add("ancestor(X, Y) :- parent(X, Y).").unwrap();
    engine.parse_and_add("ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).").unwrap();
    
    for depth in [1, 5, 10, 15].iter() {
        group.bench_with_input(BenchmarkId::new("ancestor_depth", depth), depth, |b, &depth| {
            b.iter(|| {
                let query = format!("ancestor(person0, person{}).", depth);
                black_box(engine.parse_query(&query).unwrap());
            });
        });
    }
    
    group.finish();
}

fn bench_arithmetic(c: &mut Criterion) {
    let mut group = c.benchmark_group("arithmetic");
    
    let mut engine = PrologEngine::new();
    
    group.bench_function("simple_addition", |b| {
        b.iter(|| {
            black_box(engine.parse_query("X is 2 + 3.").unwrap());
        });
    });
    
    group.bench_function("complex_expression", |b| {
        b.iter(|| {
            black_box(engine.parse_query("X is (2 + 3) * (4 - 1) // 2.").unwrap());
        });
    });
    
    group.bench_function("comparison", |b| {
        b.iter(|| {
            black_box(engine.parse_query("10 > 5.").unwrap());
        });
    });
    
    group.bench_function("arithmetic_equality", |b| {
        b.iter(|| {
            black_box(engine.parse_query("6 =:= 2 * 3.").unwrap());
        });
    });
    
    group.finish();
}

fn bench_list_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("list_operations");
    
    let mut engine = PrologEngine::new();
    
    // Create lists of different sizes
    let small_list = "[1, 2, 3]";
    let medium_list = "[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]";
    let large_list = (1..=100).map(|i| i.to_string()).collect::<Vec<_>>().join(", ");
    let large_list = format!("[{}]", large_list);
    
    group.bench_function("append_small", |b| {
        b.iter(|| {
            let query = format!("append({}, [4, 5], X).", small_list);
            black_box(engine.parse_query(&query).unwrap());
        });
    });
    
    group.bench_function("member_small", |b| {
        b.iter(|| {
            let query = format!("member(2, {}).", small_list);
            black_box(engine.parse_query(&query).unwrap());
        });
    });
    
    group.bench_function("length_medium", |b| {
        b.iter(|| {
            let query = format!("length({}, X).", medium_list);
            black_box(engine.parse_query(&query).unwrap());
        });
    });
    
    group.bench_function("member_large_found", |b| {
        b.iter(|| {
            let query = format!("member(50, {}).", large_list);
            black_box(engine.parse_query(&query).unwrap());
        });
    });
    
    group.bench_function("member_large_not_found", |b| {
        b.iter(|| {
            let query = format!("member(999, {}).", large_list);
            black_box(engine.parse_query(&query).unwrap());
        });
    });
    
    group.finish();
}

fn bench_unification(c: &mut Criterion) {
    let mut group = c.benchmark_group("unification");
    
    let mut engine = PrologEngine::new();
    
    group.bench_function("simple_unify", |b| {
        b.iter(|| {
            black_box(engine.parse_query("X = hello.").unwrap());
        });
    });
    
    group.bench_function("compound_unify", |b| {
        b.iter(|| {
            black_box(engine.parse_query("f(X, Y) = f(a, b).").unwrap());
        });
    });
    
    group.bench_function("complex_unify", |b| {
        b.iter(|| {
            black_box(engine.parse_query("f(g(X, h(Y)), Z) = f(g(a, h(b)), c).").unwrap());
        });
    });
    
    group.bench_function("unify_fail", |b| {
        b.iter(|| {
            black_box(engine.parse_query("f(a, b) = g(a, b).").unwrap());
        });
    });
    
    group.finish();
}

fn bench_database_size(c: &mut Criterion) {
    let mut group = c.benchmark_group("database_size");
    
    // Test performance with different database sizes
    for size in [10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("query_time", size), size, |b, &size| {
            let mut engine = PrologEngine::new();
            
            // Add many facts
            for i in 0..size {
                engine.parse_and_add(&format!("fact{0}(value{0}).", i)).unwrap();
            }
            
            b.iter(|| {
                // Query for a fact in the middle
                let query = format!("fact{}(X).", size / 2);
                black_box(engine.parse_query(&query).unwrap());
            });
        });
    }
    
    group.finish();
}

fn bench_quick_query(c: &mut Criterion) {
    let mut group = c.benchmark_group("quick_query");
    
    let clauses = &[
        "parent(alice, bob).",
        "parent(bob, charlie).",
        "parent(charlie, diana).",
        "ancestor(X, Y) :- parent(X, Y).",
        "ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).",
    ];
    
    group.bench_function("convenience_function", |b| {
        b.iter(|| {
            black_box(quick_query(clauses, "ancestor(alice, diana).").unwrap());
        });
    });
    
    group.bench_function("manual_setup", |b| {
        b.iter(|| {
            let mut engine = PrologEngine::new();
            for clause in clauses {
                engine.parse_and_add(clause).unwrap();
            }
            black_box(engine.parse_query("ancestor(alice, diana).").unwrap());
        });
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_parsing,
    bench_simple_queries,
    bench_recursive_queries,
    bench_arithmetic,
    bench_list_operations,
    bench_unification,
    bench_database_size,
    bench_quick_query
);

criterion_main!(benches);