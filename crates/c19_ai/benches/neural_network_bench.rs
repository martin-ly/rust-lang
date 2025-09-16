use criterion::{Criterion, criterion_group, criterion_main};
use std::hint::black_box;

fn neural_network_benchmark(c: &mut Criterion) {
    c.bench_function("neural_network_forward", |b| {
        b.iter(|| {
            // 模拟神经网络前向传播
            let input = vec![1.0; 1000];
            let weights = vec![0.5; 1000];
            let output: f32 = input.iter().zip(weights.iter()).map(|(i, w)| i * w).sum();
            black_box(output)
        })
    });
}

criterion_group!(benches, neural_network_benchmark);
criterion_main!(benches);
