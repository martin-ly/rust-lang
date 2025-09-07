use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn ml_algorithms_benchmark(c: &mut Criterion) {
    c.bench_function("linear_regression", |b| {
        b.iter(|| {
            // 模拟线性回归计算
            let x = vec![1.0, 2.0, 3.0, 4.0, 5.0];
            let y = vec![2.0, 4.0, 6.0, 8.0, 10.0];
            let n = x.len() as f32;
            let sum_x: f32 = x.iter().sum();
            let sum_y: f32 = y.iter().sum();
            let sum_xy: f32 = x.iter().zip(y.iter()).map(|(a, b)| a * b).sum();
            let sum_x2: f32 = x.iter().map(|a| a * a).sum();
            
            let slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x);
            let intercept = (sum_y - slope * sum_x) / n;
            
            black_box((slope, intercept))
        })
    });
}

criterion_group!(benches, ml_algorithms_benchmark);
criterion_main!(benches);
