//! Rust 1.94 特性性能基准测试
//!
//! 运行方式:
//!   cargo bench --bench rust_194_benchmarks

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;

// ==================== array_windows 性能测试 ====================

fn bench_array_windows_vs_windows(c: &mut Criterion) {
    let mut group = c.benchmark_group("array_windows_vs_windows");
    
    for size in [100, 1000, 10000].iter() {
        let data: Vec<f64> = (0..*size).map(|x| x as f64).collect();
        
        // array_windows (Rust 1.94)
        group.bench_with_input(
            BenchmarkId::new("array_windows", size),
            &data,
            |b, _data| {
                b.iter(|| {
                    let sum: f64 = data.array_windows::<3>()
                        .map(|&[a, b, c]| a + b + c)
                        .sum();
                    black_box(sum);
                });
            },
        );
        
        // windows (传统)
        group.bench_with_input(
            BenchmarkId::new("windows", size),
            &data,
            |b, _data| {
                b.iter(|| {
                    let sum: f64 = data.windows(3)
                        .map(|w| w[0] + w[1] + w[2])
                        .sum();
                    black_box(sum);
                });
            },
        );
        
        // 手动索引
        group.bench_with_input(
            BenchmarkId::new("manual_index", size),
            &data,
            |b, _data| {
                b.iter(|| {
                    let mut sum = 0.0;
                    for i in 0..data.len() - 2 {
                        sum += data[i] + data[i + 1] + data[i + 2];
                    }
                    black_box(sum);
                });
            },
        );
    }
    
    group.finish();
}

fn bench_array_windows_different_sizes(c: &mut Criterion) {
    let mut group = c.benchmark_group("array_windows_sizes");
    let data: Vec<f64> = (0..10000).map(|x| x as f64).collect();
    
    for window_size in [2, 3, 4, 5].iter() {
        if *window_size == 2 {
            group.bench_function("window_2", |b| {
                b.iter(|| {
                    let sum: f64 = data.array_windows::<2>()
                        .map(|&[a, b]| a + b)
                        .sum();
                    black_box(sum);
                });
            });
        } else if *window_size == 3 {
            group.bench_function("window_3", |b| {
                b.iter(|| {
                    let sum: f64 = data.array_windows::<3>()
                        .map(|&[a, b, c]| a + b + c)
                        .sum();
                    black_box(sum);
                });
            });
        } else if *window_size == 4 {
            group.bench_function("window_4", |b| {
                b.iter(|| {
                    let sum: f64 = data.array_windows::<4>()
                        .map(|&[a, b, c, d]| a + b + c + d)
                        .sum();
                    black_box(sum);
                });
            });
        } else if *window_size == 5 {
            group.bench_function("window_5", |b| {
                b.iter(|| {
                    let sum: f64 = data.array_windows::<5>()
                        .map(|&[a, b, c, d, e]| a + b + c + d + e)
                        .sum();
                    black_box(sum);
                });
            });
        }
    }
    
    group.finish();
}

// ==================== LazyLock 性能测试 ====================

use std::sync::LazyLock;


static BENCH_LAZYLOCK: LazyLock<Vec<i32>> = LazyLock::new(|| {
    (0..1000).collect()
});

fn bench_lazylock_get_vs_deref(c: &mut Criterion) {
    let mut group = c.benchmark_group("lazylock_access");
    
    // 预热
    let _ = &*BENCH_LAZYLOCK;
    
    group.bench_function("get", |b| {
        b.iter(|| {
            if let Some(v) = LazyLock::get(&BENCH_LAZYLOCK) {
                black_box(v.len());
            }
        });
    });
    
    group.bench_function("deref", |b| {
        b.iter(|| {
            black_box(BENCH_LAZYLOCK.len());
        });
    });
    
    group.finish();
}

// ==================== 数学常量性能测试 ====================

fn bench_math_constants(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_constants");
    
    // 硬编码常量
    const GOLDEN_RATIO_HARDCODED: f64 = 1.618033988749895_f64;
    const EULER_GAMMA_HARDCODED: f64 = 0.5772156649015329_f64;
    
    group.bench_function("hardcoded_golden_ratio", |b| {
        b.iter(|| {
            black_box(GOLDEN_RATIO_HARDCODED * 2.0);
        });
    });
    
    group.bench_function("std_consts_golden_ratio", |b| {
        b.iter(|| {
            black_box(std::f64::consts::GOLDEN_RATIO * 2.0);
        });
    });
    
    group.bench_function("hardcoded_euler_gamma", |b| {
        b.iter(|| {
            black_box(EULER_GAMMA_HARDCODED + 1.0);
        });
    });
    
    group.bench_function("std_consts_euler_gamma", |b| {
        b.iter(|| {
            black_box(std::f64::consts::EULER_GAMMA + 1.0);
        });
    });
    
    group.finish();
}

// ==================== ControlFlow 性能测试 ====================

use std::ops::ControlFlow;

fn bench_controlflow_vs_result(c: &mut Criterion) {
    let mut group = c.benchmark_group("controlflow_vs_result");
    let data: Vec<i32> = (0..1000).collect();
    
    // ControlFlow 版本
    group.bench_function("controlflow", |b| {
        b.iter(|| {
            let result: ControlFlow<usize, ()> = (0..100).try_for_each(|i| {
                if data.get(i * 10) == Some(&500) {
                    ControlFlow::Break(i)
                } else {
                    ControlFlow::Continue(())
                }
            });
            let _ = black_box(result);
        });
    });
    
    // Result 版本
    group.bench_function("result", |b| {
        b.iter(|| {
            let result: Result<(), usize> = (0..100).try_for_each(|i| {
                if data.get(i * 10) == Some(&500) {
                    Err(i)
                } else {
                    Ok(())
                }
            });
            let _ = black_box(result);
        });
    });
    
    group.finish();
}

// ==================== 综合场景测试 ====================

fn bench_moving_average(c: &mut Criterion) {
    let mut group = c.benchmark_group("moving_average");
    
    for size in [1000, 10000, 100000].iter() {
        let prices: Vec<f64> = (0..*size).map(|i| (i as f64).sin() * 100.0).collect();
        
        // array_windows 版本 (Rust 1.94)
        group.bench_with_input(
            BenchmarkId::new("array_windows", size),
            &prices,
            |b, _prices| {
                b.iter(|| {
                    let sma: Vec<f64> = prices.array_windows::<20>()
                        .map(|window| window.iter().sum::<f64>() / 20.0)
                        .collect();
                    black_box(sma);
                });
            },
        );
        
        // 手动循环版本
        group.bench_with_input(
            BenchmarkId::new("manual_loop", size),
            &prices,
            |b, _prices| {
                b.iter(|| {
                    let mut sma = Vec::with_capacity(prices.len() - 19);
                    for i in 0..prices.len() - 19 {
                        let sum: f64 = prices[i..i + 20].iter().sum();
                        sma.push(sum / 20.0);
                    }
                    black_box(sma);
                });
            },
        );
    }
    
    group.finish();
}

fn bench_pattern_detection(c: &mut Criterion) {
    let mut group = c.benchmark_group("pattern_detection");
    
    let text = "abbaaccaabbaddacccabba".repeat(100);
    
    // array_windows 版本
    group.bench_function("array_windows", |b| {
        b.iter(|| {
            let count = text.as_bytes()
                .array_windows::<4>()
                .filter(|&&[a, b, c, d]| a == d && b == c && a != b)
                .count();
            black_box(count);
        });
    });
    
    // 手动迭代版本
    group.bench_function("manual", |b| {
        b.iter(|| {
            let bytes = text.as_bytes();
            let mut count = 0;
            for i in 0..bytes.len() - 3 {
                if bytes[i] == bytes[i + 3] && bytes[i + 1] == bytes[i + 2] && bytes[i] != bytes[i + 1] {
                    count += 1;
                }
            }
            black_box(count);
        });
    });
    
    group.finish();
}

criterion_group!(
    benches,
    bench_array_windows_vs_windows,
    bench_array_windows_different_sizes,
    bench_lazylock_get_vs_deref,
    bench_math_constants,
    bench_controlflow_vs_result,
    bench_moving_average,
    bench_pattern_detection
);

criterion_main!(benches);
