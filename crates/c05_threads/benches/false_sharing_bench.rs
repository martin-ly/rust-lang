//! False Sharing 基准测试
//!
//! 对比「有/无缓存行填充」时多线程原子计数器增量的性能差异。
//! 预期：GoodCounters（缓存行隔离）明显快于 BadCounters（伪共享）。

// criterion 0.8.2 的 black_box 已弃用，本文件使用 std::hint::black_box
#![allow(deprecated)]

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::thread;

/// 伪共享：两计数器在同一缓存行
struct BadCounters {
    counter1: AtomicU64,
    counter2: AtomicU64,
}

/// 缓存行隔离：每计数器独占 64 字节
#[repr(align(64))]
struct PaddedCounter {
    value: AtomicU64,
    _pad: [u8; 56],
}

struct GoodCounters {
    counter1: PaddedCounter,
    counter2: PaddedCounter,
}

impl GoodCounters {
    fn new() -> Self {
        Self {
            counter1: PaddedCounter {
                value: AtomicU64::new(0),
                _pad: [0; 56],
            },
            counter2: PaddedCounter {
                value: AtomicU64::new(0),
                _pad: [0; 56],
            },
        }
    }
}

fn bench_false_sharing(c: &mut Criterion) {
    let mut group = c.benchmark_group("false_sharing");
    group.sample_size(50);

    for iters in [10_000, 100_000].iter() {
        // 伪共享：两线程写同一缓存行
        group.bench_with_input(
            BenchmarkId::new("bad_counters", iters),
            iters,
            |b, &iters| {
                b.iter(|| {
                    let counters = Arc::new(BadCounters {
                        counter1: AtomicU64::new(0),
                        counter2: AtomicU64::new(0),
                    });
                    let c1 = Arc::clone(&counters);
                    let c2 = Arc::clone(&counters);
                    let t1 = thread::spawn(move || {
                        for _ in 0..iters {
                            c1.counter1.fetch_add(1, Ordering::Relaxed);
                        }
                    });
                    let t2 = thread::spawn(move || {
                        for _ in 0..iters {
                            c2.counter2.fetch_add(1, Ordering::Relaxed);
                        }
                    });
                    t1.join().unwrap();
                    t2.join().unwrap();
                    std::hint::black_box(counters);
                });
            },
        );

        // 缓存行隔离
        group.bench_with_input(
            BenchmarkId::new("good_counters", iters),
            iters,
            |b, &iters| {
                b.iter(|| {
                    let counters = Arc::new(GoodCounters::new());
                    let c1 = Arc::clone(&counters);
                    let c2 = Arc::clone(&counters);
                    let t1 = thread::spawn(move || {
                        for _ in 0..iters {
                            c1.counter1.value.fetch_add(1, Ordering::Relaxed);
                        }
                    });
                    let t2 = thread::spawn(move || {
                        for _ in 0..iters {
                            c2.counter2.value.fetch_add(1, Ordering::Relaxed);
                        }
                    });
                    t1.join().unwrap();
                    t2.join().unwrap();
                    std::hint::black_box(counters);
                });
            },
        );
    }

    group.finish();
}

criterion_group!(benches, bench_false_sharing);
criterion_main!(benches);
