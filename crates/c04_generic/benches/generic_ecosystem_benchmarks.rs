//! C04 泛型与生态系统集成性能基准测试
//!
//! 测试泛型在实际生态库（rayon, itertools, serde）中的性能表现。

use criterion::{Criterion, criterion_group, criterion_main};

/// 基准测试：rayon 并行求和 vs 串行求和
fn bench_parallel_vs_serial_sum(c: &mut Criterion) {
    use c04_generic::ecosystem_examples::parallel_square_sum;

    let data: Vec<i32> = (1..=100_000).collect();

    c.bench_function("serial_square_sum", |b| {
        b.iter(|| {
            let result: i32 = data.iter().map(|x| x * x).sum();
            let _ = std::hint::black_box(result);
        });
    });

    c.bench_function("parallel_square_sum", |b| {
        b.iter(|| {
            let result = parallel_square_sum(&data);
            let _ = std::hint::black_box(result);
        });
    });
}

/// 基准测试：itertools tuples 处理
fn bench_itertools_pairs(c: &mut Criterion) {
    use c04_generic::ecosystem_examples::sum_of_pairs;

    let data: Vec<i32> = (1..=10_000).collect();

    c.bench_function("sum_of_pairs_itertools", |b| {
        b.iter(|| {
            let result = sum_of_pairs(&data);
            let _ = std::hint::black_box(result);
        });
    });
}

/// 基准测试：serde JSON 序列化/反序列化
fn bench_serde_roundtrip(c: &mut Criterion) {
    use c04_generic::ecosystem_examples::{user_from_json, user_to_json, User};

    let user = User {
        id: 42,
        name: "Benchmark User".to_string(),
    };

    c.bench_function("user_serialize", |b| {
        b.iter(|| {
            let json = user_to_json(&user).unwrap();
            std::hint::black_box(json);
        });
    });

    let json_str = user_to_json(&user).unwrap();
    c.bench_function("user_deserialize", |b| {
        b.iter(|| {
            let user_back = user_from_json(&json_str).unwrap();
            std::hint::black_box(user_back);
        });
    });
}

/// 基准测试：anyhow + thiserror 错误处理开销
fn bench_error_handling_overhead(c: &mut Criterion) {
    use c04_generic::ecosystem_examples::find_name;

    let names = ["alice", "bob", "charlie", "david", "eve"];

    c.bench_function("error_handling_success", |b| {
        b.iter(|| {
            let result = find_name(&names, "charlie");
            let _ = std::hint::black_box(result);
        });
    });

    c.bench_function("error_handling_failure", |b| {
        b.iter(|| {
            let result = find_name(&names, "zack");
            let _ = std::hint::black_box(result);
        });
    });
}

/// 基准测试：泛型容器内存分配模式
fn bench_generic_container_ops(c: &mut Criterion) {
    c.bench_function("generic_vec_push", |b| {
        b.iter(|| {
            let mut vec: Vec<u64> = Vec::with_capacity(1000);
            for i in 0..1000 {
                vec.push(i as u64);
            }
            std::hint::black_box(vec);
        });
    });

    c.bench_function("generic_vec_extend", |b| {
        let data: Vec<u64> = (0..1000).map(|x| x as u64).collect();
        b.iter(|| {
            let mut vec: Vec<u64> = Vec::with_capacity(1000);
            vec.extend_from_slice(&data);
            std::hint::black_box(vec);
        });
    });
}

criterion_group!(
    benches,
    bench_parallel_vs_serial_sum,
    bench_itertools_pairs,
    bench_serde_roundtrip,
    bench_error_handling_overhead,
    bench_generic_container_ops,
);
criterion_main!(benches);
