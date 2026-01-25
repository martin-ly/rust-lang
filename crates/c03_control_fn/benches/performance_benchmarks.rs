//! 控制流与函数模块性能基准测试 / Control Flow and Functions Module Performance Benchmarks

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_control_flow_operations(c: &mut Criterion) {
    c.bench_function("control_flow_operations", |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in 0..1000 {
                sum += black_box(i);
            }
            black_box(sum);
        });
    });
}

fn bench_branch_operations(c: &mut Criterion) {
    c.bench_function("branch_operations", |b| {
        b.iter(|| {
            let mut result = 0;
            for i in 0..1000 {
                if black_box(i) % 2 == 0 {
                    result += 1;
                }
            }
            black_box(result);
        });
    });
}

fn bench_match_operations(c: &mut Criterion) {
    c.bench_function("match_operations", |b| {
        b.iter(|| {
            let mut result = 0;
            for i in 0..1000 {
                match black_box(i) % 3 {
                    0 => result += 1,
                    1 => result += 2,
                    _ => result += 3,
                }
            }
            black_box(result);
        });
    });
}

criterion_group!(benches, bench_control_flow_operations, bench_branch_operations, bench_match_operations);
criterion_main!(benches);
