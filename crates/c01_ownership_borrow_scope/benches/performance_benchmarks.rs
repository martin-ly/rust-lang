//! 所有权和借用作用域模块性能基准测试 / Ownership and Borrowing Scope Module Performance Benchmarks

use c01_ownership_borrow_scope::scope::{ScopeManager, ScopeType};
use criterion::{criterion_group, criterion_main, Criterion};

fn bench_scope_creation(c: &mut Criterion) {
    c.bench_function("scope_creation", |b| {
        b.iter(|| {
            let mut manager = ScopeManager::new();
            manager
                .enter_scope(std::hint::black_box("test".to_string()), ScopeType::Block)
                .unwrap();
        });
    });
}

fn bench_variable_operations(c: &mut Criterion) {
    c.bench_function("variable_operations", |b| {
        b.iter(|| {
            let mut manager = ScopeManager::new();
            manager
                .enter_scope(std::hint::black_box("test".to_string()), ScopeType::Block)
                .unwrap();
            manager
                .declare_variable(
                    std::hint::black_box("var".to_string()),
                    "i32".to_string(),
                    "0".to_string(),
                    false,
                    None,
                )
                .unwrap();
        });
    });
}

fn bench_scope_nesting(c: &mut Criterion) {
    c.bench_function("scope_nesting", |b| {
        b.iter(|| {
            let mut manager = ScopeManager::new();
            for i in 0..100 {
                manager
                    .enter_scope(std::hint::black_box(format!("scope_{}", i)), ScopeType::Block)
                    .unwrap();
            }
            for _ in 0..100 {
                manager.exit_scope().unwrap();
            }
        });
    });
}

criterion_group!(benches, bench_scope_creation, bench_variable_operations, bench_scope_nesting);
criterion_main!(benches);
