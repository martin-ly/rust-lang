//! Rust 1.92.0 所有权系统性能基准测试套件
//!
//! 本模块提供 Rust 1.92.0 所有权、借用、生命周期相关特性的性能基准测试，包括：
//! - MaybeUninit 性能影响
//! - 联合体原始引用性能
//! - 零大小数组优化性能
//! - 所有权转移性能
//! - 借用检查性能
//! - 生命周期推断性能
//!
//! 运行方式:
//! ```bash
//! cargo bench --bench rust_192_benchmarks
//! ```

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::hint::black_box;
use c01_ownership_borrow_scope::{
    SafeMaybeUninit,
    Rust192Union,
    Rust192ZeroSizedArray,
    rust_192_tracked_function,
    rust_192_higher_ranked_lifetime,
    OwnershipTracker,
    BorrowTracker,
    LifetimeTracker,
};

/// 基准测试 MaybeUninit 性能
fn bench_maybe_uninit(c: &mut Criterion) {
    let mut group = c.benchmark_group("maybe_uninit");
    group.throughput(Throughput::Elements(1));

    group.bench_function("create", |b| {
        b.iter(|| {
            let _uninit = SafeMaybeUninit::<i32>::new();
            black_box(())
        });
    });

    group.bench_function("write", |b| {
        b.iter(|| {
            let mut uninit = SafeMaybeUninit::<i32>::new();
            uninit.write(black_box(42));
            black_box(uninit)
        });
    });

    group.bench_function("read", |b| {
        let mut uninit = SafeMaybeUninit::<i32>::new();
        uninit.write(42);
        b.iter(|| {
            let _value = uninit.read();
            black_box(())
        });
    });

    group.bench_function("from_initialized", |b| {
        b.iter(|| {
            let uninit = SafeMaybeUninit::from(black_box(42));
            black_box(uninit)
        });
    });

    group.finish();
}

/// 基准测试联合体原始引用性能
fn bench_union_raw_references(c: &mut Criterion) {
    let mut group = c.benchmark_group("union_raw_references");
    group.throughput(Throughput::Elements(1));

    group.bench_function("create", |b| {
        b.iter(|| {
            let _union = Rust192Union::new();
            black_box(())
        });
    });

    group.bench_function("set_get", |b| {
        b.iter(|| {
            let mut union = Rust192Union::new();
            union.set_integer(black_box(0x12345678));
            let _value = union.get_integer();
            black_box(union)
        });
    });

    group.bench_function("get_raw_const", |b| {
        let mut union = Rust192Union::new();
        union.set_integer(0x12345678);
        b.iter(|| {
            let _raw = union.get_integer_raw();
            black_box(())
        });
    });

    group.bench_function("get_raw_mut", |b| {
        let mut union = Rust192Union::new();
        union.set_integer(0x12345678);
        b.iter(|| {
            let _raw = union.get_integer_mut_raw();
            black_box(())
        });
    });

    group.finish();
}

/// 基准测试零大小数组性能
fn bench_zero_sized_array(c: &mut Criterion) {
    let mut group = c.benchmark_group("zero_sized_array");
    group.throughput(Throughput::Elements(1));

    group.bench_function("create", |b| {
        b.iter(|| {
            let _array: Rust192ZeroSizedArray<String> = Rust192ZeroSizedArray::new();
            black_box(())
        });
    });

    group.bench_function("len", |b| {
        let array: Rust192ZeroSizedArray<i32> = Rust192ZeroSizedArray::new();
        b.iter(|| {
            let _len = array.len();
            black_box(())
        });
    });

    group.bench_function("is_empty", |b| {
        let array: Rust192ZeroSizedArray<i32> = Rust192ZeroSizedArray::new();
        b.iter(|| {
            let _empty = array.is_empty();
            black_box(())
        });
    });

    group.finish();
}

/// 基准测试所有权转移性能
fn bench_ownership_transfer(c: &mut Criterion) {
    let mut group = c.benchmark_group("ownership_transfer");

    let sizes: [usize; 4] = [10, 100, 1000, 10000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                b.iter(|| {
                    let vec = vec![0u8; size];
                    let _moved = black_box(vec);
                });
            },
        );
    }

    group.finish();
}

/// 基准测试借用检查性能
fn bench_borrow_checking(c: &mut Criterion) {
    let mut group = c.benchmark_group("borrow_checking");

    let sizes: [usize; 3] = [10, 100, 1000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut tracker = BorrowTracker::new();
                    for i in 0..size {
                        let _ = tracker.record_borrow(
                            format!("owner_{}", i),
                            format!("borrower_{}", i),
                            c01_ownership_borrow_scope::BorrowType::Immutable,
                        );
                    }
                });
            },
        );
    }

    group.finish();
}

/// 基准测试生命周期推断性能
fn bench_lifetime_inference(c: &mut Criterion) {
    let mut group = c.benchmark_group("lifetime_inference");

    let sizes: [usize; 3] = [10, 100, 1000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut tracker = LifetimeTracker::new();
                    for i in 0..size {
                        tracker.record_lifetime_start(
                            format!("var_{}", i),
                            format!("scope_{}", i % 10),
                        );
                    }
                });
            },
        );
    }

    group.finish();
}

/// 基准测试所有权跟踪性能
fn bench_ownership_tracking(c: &mut Criterion) {
    let mut group = c.benchmark_group("ownership_tracking");

    let sizes: [usize; 3] = [10, 100, 1000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                b.iter(|| {
                    let mut tracker = OwnershipTracker::new();
                    // 先创建所有权记录
                    for i in 0..size {
                        tracker.record_ownership(
                            format!("owner_{}", i),
                            "TestType".to_string(),
                        );
                    }
                    // 然后转移所有权
                    for i in 0..size - 1 {
                        let _ = tracker.record_transfer(
                            format!("owner_{}", i),
                            format!("owner_{}", i + 1),
                        );
                    }
                });
            },
        );
    }

    group.finish();
}

/// 基准测试 track_caller 性能
fn bench_track_caller(c: &mut Criterion) {
    let mut group = c.benchmark_group("track_caller");
    group.throughput(Throughput::Elements(1));

    group.bench_function("tracked_function", |b| {
        b.iter(|| {
            let _result = rust_192_tracked_function(black_box(21));
            black_box(())
        });
    });

    group.finish();
}

/// 基准测试高阶生命周期性能
fn bench_higher_ranked_lifetime(c: &mut Criterion) {
    let mut group = c.benchmark_group("higher_ranked_lifetime");
    group.throughput(Throughput::Elements(1));

    group.bench_function("higher_ranked", |b| {
        b.iter(|| {
            rust_192_higher_ranked_lifetime(|s| s);
            black_box(())
        });
    });

    group.finish();
}

/// 基准测试 NonZero::div_ceil 性能
fn bench_nonzero_div_ceil(c: &mut Criterion) {
    let mut group = c.benchmark_group("nonzero_div_ceil");
    group.throughput(Throughput::Elements(1));

    group.bench_function("div_ceil", |b| {
        use std::num::NonZeroU32;
        let n = NonZeroU32::new(1000).unwrap();
        let d = NonZeroU32::new(3).unwrap();
        b.iter(|| {
            let _result = n.div_ceil(d);
            black_box(())
        });
    });

    group.finish();
}

/// 基准测试 rotate_right 性能
fn bench_rotate_right(c: &mut Criterion) {
    let mut group = c.benchmark_group("rotate_right");

    let sizes: [usize; 3] = [100, 1000, 10000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                let mut vec: Vec<i32> = (0..size as i32).collect();
                b.iter(|| {
                    vec.rotate_right(black_box(size / 4));
                });
            },
        );
    }

    group.finish();
}

/// 基准测试迭代器比较性能
fn bench_iterator_eq(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterator_eq");

    let sizes: [usize; 3] = [100, 1000, 10000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                let vec1: Vec<i32> = (0..size as i32).collect();
                let vec2: Vec<i32> = (0..size as i32).collect();
                b.iter(|| {
                    let _equal = vec1.iter().eq(vec2.iter());
                    black_box(())
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_maybe_uninit,
    bench_union_raw_references,
    bench_zero_sized_array,
    bench_ownership_transfer,
    bench_borrow_checking,
    bench_lifetime_inference,
    bench_ownership_tracking,
    bench_track_caller,
    bench_higher_ranked_lifetime,
    bench_nonzero_div_ceil,
    bench_rotate_right,
    bench_iterator_eq
);
criterion_main!(benches);
