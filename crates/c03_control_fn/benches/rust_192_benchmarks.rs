//! Rust 1.92.0 控制流特性性能基准测试套件
//!
//! 本模块提供 Rust 1.92.0 新特性的性能基准测试，包括：
//! - #[track_caller] 性能影响
//! - 控制流分析性能
//! - 控制流优化性能
//! - 错误处理和位置追踪性能
//!
//! 运行方式:
//! ```bash
//! cargo bench --bench rust_192_benchmarks
//! ```

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use std::hint::black_box;
use c03_control_fn::rust_192_features::{
    control_flow_check, control_flow_branch, control_flow_loop, control_flow_match,
    control_flow_with_never, LocatedError, ErrorContext,
    ControlFlowAnalyzer, ControlFlowOptimizer,
    ControlFlowMatcher, ControlFlowCombinator, ControlFlowValidator,
    ControlFlowStateMachine, ControlFlowState,
    IteratorControlFlow,
};

/// 基准测试控制流检查性能
fn bench_control_flow_check(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_check");
    group.throughput(Throughput::Elements(1));

    group.bench_function("check_true", |b| {
        b.iter(|| control_flow_check(black_box(true)))
    });

    group.bench_function("check_false", |b| {
        b.iter(|| control_flow_check(black_box(false)))
    });

    group.finish();
}

/// 基准测试控制流分支性能
fn bench_control_flow_branch(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_branch");
    group.throughput(Throughput::Elements(1));

    let test_values = vec![
        ("valid", 42),
        ("negative", -1),
        ("too_large", 150),
    ];

    for (name, value) in test_values {
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &value,
            |b, &val| {
                b.iter(|| control_flow_branch(black_box(val)))
            },
        );
    }

    group.finish();
}

/// 基准测试控制流循环性能
fn bench_control_flow_loop(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_loop");

    let sizes = [10, 100, 1000, 10000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(size),
            size,
            |b, &size| {
                b.iter(|| control_flow_loop(black_box(size)))
            },
        );
    }

    group.finish();
}

/// 基准测试控制流匹配性能
fn bench_control_flow_match(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_match");
    group.throughput(Throughput::Elements(1));

    let test_values = vec![
        ("some_positive", Some(21)),
        ("some_negative", Some(-21)),
        ("none", None::<i32>),
        ("some_zero", Some(0)),
    ];

    for (name, value) in test_values {
        group.bench_with_input(
            BenchmarkId::from_parameter(name),
            &value,
            |b, val| {
                b.iter(|| control_flow_match(black_box(*val)))
            },
        );
    }

    group.finish();
}

/// 基准测试错误处理性能
fn bench_error_handling(c: &mut Criterion) {
    let mut group = c.benchmark_group("error_handling");
    group.throughput(Throughput::Elements(1));

    group.bench_function("create_located_error", |b| {
        b.iter(|| LocatedError::new(black_box("test error")))
    });

    group.bench_function("create_error_context", |b| {
        b.iter(|| ErrorContext::current())
    });

    group.finish();
}

/// 基准测试控制流分析器性能
fn bench_control_flow_analyzer(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_analyzer");

    let iterations = [10, 100, 1000];

    for &iter in iterations.iter() {
        group.throughput(Throughput::Elements(iter as u64));
        group.bench_with_input(
            BenchmarkId::new("analyze_loop", iter),
            &iter,
            |b, &iter| {
                b.iter(|| {
                    let mut analyzer = ControlFlowAnalyzer::new();
                    analyzer.analyze_loop(iter, |i| i % 2 == 0);
                    analyzer
                })
            },
        );
    }

    group.bench_function("analyze_branch", |b| {
        b.iter(|| {
            let mut analyzer = ControlFlowAnalyzer::new();
            for _ in 0..100 {
                analyzer.analyze_branch(true);
            }
            analyzer
        })
    });

    group.bench_function("analyze_match", |b| {
        b.iter(|| {
            let mut analyzer = ControlFlowAnalyzer::new();
            for _ in 0..100 {
                analyzer.analyze_match(Some(42));
            }
            analyzer
        })
    });

    group.finish();
}

/// 基准测试控制流优化器性能
fn bench_control_flow_optimizer(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_optimizer");

    let sizes = [10, 100, 1000, 10000];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::new("optimize_loop", size),
            size,
            |b, &size| {
                b.iter(|| ControlFlowOptimizer::optimize_loop(black_box(size)))
            },
        );
    }

    group.bench_function("optimize_branch_success", |b| {
        b.iter(|| ControlFlowOptimizer::optimize_branch(black_box(42)))
    });

    group.bench_function("optimize_branch_error", |b| {
        b.iter(|| ControlFlowOptimizer::optimize_branch(black_box(-1)))
    });

    group.bench_function("optimize_match", |b| {
        b.iter(|| {
            ControlFlowOptimizer::optimize_match(Some(black_box(21)));
            ControlFlowOptimizer::optimize_match(Some(black_box(-21)));
            ControlFlowOptimizer::optimize_match(None::<i32>);
        })
    });

    group.finish();
}

/// 基准测试 Never 类型控制流性能
fn bench_never_type_control_flow(c: &mut Criterion) {
    let mut group = c.benchmark_group("never_type_control_flow");
    group.throughput(Throughput::Elements(1));

    group.bench_function("control_flow_with_never_ok", |b| {
        b.iter(|| control_flow_with_never(black_box(Ok(42))))
    });

    // 注意：我们不测试 Err 情况，因为它会导致无限循环

    group.finish();
}

/// 基准测试综合控制流场景
fn bench_comprehensive_control_flow(c: &mut Criterion) {
    let mut group = c.benchmark_group("comprehensive_control_flow");

    let sizes = [10, 100];

    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::new("full_workflow", size),
            size,
            |b, &size| {
                b.iter(|| {
                    // 组合多种控制流操作
                    let mut analyzer = ControlFlowAnalyzer::new();

                    // 分支
                    for i in 0..size {
                        analyzer.analyze_branch(i % 2 == 0);
                    }

                    // 循环
                    analyzer.analyze_loop(size, |i| i % 3 == 0);

                    // 匹配
                    for i in 0..size {
                        analyzer.analyze_match(Some(i));
                    }

                    // 优化操作
                    let _ = ControlFlowOptimizer::optimize_loop(size);
                    let _ = ControlFlowOptimizer::optimize_branch(42);
                    let _ = ControlFlowOptimizer::optimize_match(Some(21));

                    analyzer
                })
            },
        );
    }

    group.finish();
}

/// 基准测试控制流模式匹配器性能
fn bench_control_flow_matcher(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_matcher");
    group.throughput(Throughput::Elements(1));

    group.bench_function("match_with_guard", |b| {
        let values = vec![-5, 0, 5, 50, 200];
        b.iter(|| {
            for &value in &values {
                black_box(ControlFlowMatcher::match_with_guard(value));
            }
        })
    });

    group.bench_function("nested_match", |b| {
        let values = vec![Some(Some(21)), Some(Some(-21)), Some(None), None];
        b.iter(|| {
            for value in &values {
                black_box(ControlFlowMatcher::nested_match(*value));
            }
        })
    });

    group.bench_function("tuple_match", |b| {
        let tuples = vec![(3, 3, 3), (2, 2, 1), (1, 2, 3)];
        b.iter(|| {
            for tuple in &tuples {
                black_box(ControlFlowMatcher::tuple_match(*tuple));
            }
        })
    });

    group.bench_function("range_match", |b| {
        let values = vec![5, 42, 123, 1234, 12345];
        b.iter(|| {
            for &value in &values {
                black_box(ControlFlowMatcher::range_match(value));
            }
        })
    });

    group.finish();
}

/// 基准测试控制流组合器性能
fn bench_control_flow_combinator(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_combinator");

    let sizes = [10, 100, 1000];
    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(
            BenchmarkId::new("chain_conditions", size),
            size,
            |b, &size| {
                let values: Vec<i32> = (0..size).map(|i| (i as i32) * 10).collect();
                b.iter(|| {
                    let _ = ControlFlowCombinator::chain_conditions(&values);
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("combine_loop_and_match", size),
            size,
            |b, &size| {
                let items: Vec<Option<i32>> = (0..size).map(|i| Some(i as i32)).collect();
                b.iter(|| {
                    black_box(ControlFlowCombinator::combine_loop_and_match(&items));
                })
            },
        );
    }

    group.finish();
}

/// 基准测试控制流验证器性能
fn bench_control_flow_validator(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_validator");
    group.throughput(Throughput::Elements(1));

    group.bench_function("validate_branch", |b| {
        let values = vec![42, -1, 1001, 500];
        b.iter(|| {
            for &value in &values {
                let _ = ControlFlowValidator::validate_branch(value);
            }
        })
    });

    group.bench_function("validate_loop_termination", |b| {
        let sizes = vec![0, 100, 1000, 10000];
        b.iter(|| {
            for &size in &sizes {
                let _ = ControlFlowValidator::validate_loop_termination(size);
            }
        })
    });

    group.bench_function("validate_match_coverage", |b| {
        let values = vec![Some(42), Some(-1), None, Some(0)];
        b.iter(|| {
            for value in &values {
                let _ = ControlFlowValidator::validate_match_coverage(*value);
            }
        })
    });

    group.finish();
}

/// 基准测试控制流状态机性能
fn bench_control_flow_state_machine(c: &mut Criterion) {
    let mut group = c.benchmark_group("control_flow_state_machine");
    group.throughput(Throughput::Elements(1));

    group.bench_function("state_transitions", |b| {
        b.iter(|| {
            let mut machine = ControlFlowStateMachine::new();
            let _ = machine.transition_to(ControlFlowState::Processing);
            let _ = machine.transition_to(ControlFlowState::Validating);
            let _ = machine.transition_to(ControlFlowState::Completed);
            machine
        })
    });

    group.bench_function("execute_workflow", |b| {
        b.iter(|| {
            let mut machine = ControlFlowStateMachine::new();
            let _ = machine.execute_workflow(black_box(42));
            machine
        })
    });

    group.finish();
}

/// 基准测试迭代器控制流性能
fn bench_iterator_control_flow(c: &mut Criterion) {
    let mut group = c.benchmark_group("iterator_control_flow");

    let sizes = [10, 100, 1000];
    for size in sizes.iter() {
        group.throughput(Throughput::Elements(*size as u64));

        group.bench_with_input(
            BenchmarkId::new("filter", size),
            size,
            |b, &size| {
                let numbers: Vec<i32> = (0..size).map(|i| i as i32).collect();
                b.iter(|| {
                    black_box(IteratorControlFlow::filter_with_control_flow(
                        numbers.iter(),
                        |&x| Ok(*x % 2 == 0),
                    ))
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("map", size),
            size,
            |b, &size| {
                let numbers: Vec<i32> = (0..size).map(|i| i as i32 * 10).collect();
                b.iter(|| {
                    let _ = IteratorControlFlow::map_with_control_flow(
                        numbers.iter(),
                        |&x| control_flow_branch(x),
                    );
                })
            },
        );

        group.bench_with_input(
            BenchmarkId::new("fold", size),
            size,
            |b, &size| {
                let numbers: Vec<i32> = (0..size).map(|i| i as i32).collect();
                b.iter(|| {
                    let _ = IteratorControlFlow::fold_with_control_flow(
                        numbers.iter(),
                        0,
                        |acc, &x| Ok(acc + x),
                    );
                })
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_control_flow_check,
    bench_control_flow_branch,
    bench_control_flow_loop,
    bench_control_flow_match,
    bench_error_handling,
    bench_control_flow_analyzer,
    bench_control_flow_optimizer,
    bench_never_type_control_flow,
    bench_comprehensive_control_flow,
    bench_control_flow_matcher,
    bench_control_flow_combinator,
    bench_control_flow_validator,
    bench_control_flow_state_machine,
    bench_iterator_control_flow
);

criterion_main!(benches);
