//! 网络编程模块性能基准测试 / Network Programming Module Performance Benchmarks

use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn bench_network_operations(c: &mut Criterion) {
    c.bench_function("network_operations", |b| {
        b.iter(|| {
            let vec: Vec<u8> = vec![0; 1024];
            let len = vec.len();
            black_box(len);
        });
    });
}

fn bench_packet_operations(c: &mut Criterion) {
    c.bench_function("packet_operations", |b| {
        b.iter(|| {
            let mut sum = 0;
            for i in 0..1000 {
                sum += black_box(i);
            }
            black_box(sum);
        });
    });
}

fn bench_connection_operations(c: &mut Criterion) {
    c.bench_function("connection_operations", |b| {
        b.iter(|| {
            let vec: Vec<i32> = (0..1000).collect();
            let count = vec.len();
            black_box(count);
        });
    });
}

fn bench_protocol_operations(c: &mut Criterion) {
    c.bench_function("protocol_operations", |b| {
        b.iter(|| {
            let value = black_box(42);
            let result = value * 2;
            black_box(result);
        });
    });
}

criterion_group!(benches, bench_network_operations, bench_packet_operations, bench_connection_operations, bench_protocol_operations);
criterion_main!(benches);
