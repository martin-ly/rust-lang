//! C03 控制流与函数模块性能基准测试（增强版）
//!
//! 测试闭包、控制流分支、模式匹配等核心语言特性的性能表现。

use criterion::{Criterion, criterion_group, criterion_main};

/// 基准测试：函数组合链性能
/// 验证函数式编程风格在高频调用下的开销
fn bench_function_composition(c: &mut Criterion) {
    use c03_control_fn::compose_functions;

    c.bench_function("function_composition", |b| {
        b.iter(|| {
            let result = compose_functions(
                |x: i32| x + 1,
                |x: i32| x * 2,
                |x: i32| x - 3,
                10,
            );
            std::hint::black_box(result);
        });
    });
}

/// 基准测试：分支预测友好 vs 不友好的代码
fn bench_branch_prediction(c: &mut Criterion) {
    use c03_control_fn::branch_predictor_friendly;

    let sorted_data: Vec<i32> = (0..1000).collect();
    let random_data: Vec<i32> = (0..1000).map(|i| i % 3).collect();

    c.bench_function("branch_predictor_friendly_sorted", |b| {
        b.iter(|| {
            let count = branch_predictor_friendly(&sorted_data);
            std::hint::black_box(count);
        });
    });

    c.bench_function("branch_predictor_friendly_random", |b| {
        b.iter(|| {
            let count = branch_predictor_friendly(&random_data);
            std::hint::black_box(count);
        });
    });
}

/// 基准测试：无分支计算
fn bench_branchless_computation(c: &mut Criterion) {
    use c03_control_fn::branchless_computation;

    let data: Vec<i32> = (-500..500).collect();

    c.bench_function("branchless_computation", |b| {
        b.iter(|| {
            let result: Vec<i32> = data.iter().map(|&x| branchless_computation(x)).collect();
            std::hint::black_box(result);
        });
    });
}

/// 基准测试：向量化的循环 vs 普通循环
fn bench_vectorizable_loop(c: &mut Criterion) {
    use c03_control_fn::vectorizable_loop;

    let data: Vec<f64> = (0..1000).map(|i| i as f64).collect();

    c.bench_function("vectorizable_loop", |b| {
        b.iter(|| {
            let result = vectorizable_loop(&data);
            std::hint::black_box(result);
        });
    });
}

/// 基准测试：状态机解析器
fn bench_state_machine_parser(c: &mut Criterion) {
    use c03_control_fn::{StateMachineParser, Token};

    let tokens: Vec<Token> = (0..100)
        .map(|i| match i % 4 {
            0 => Token::Number(i as i64),
            1 => Token::Plus,
            2 => Token::Number(i as i64),
            _ => Token::Minus,
        })
        .collect();

    c.bench_function("state_machine_parser", |b| {
        b.iter(|| {
            let mut parser = StateMachineParser::new();
            let result = parser.parse(&tokens);
            std::hint::black_box(result);
        });
    });
}

/// 基准测试：条件执行优化
fn bench_conditional_execute(c: &mut Criterion) {
    use c03_control_fn::conditional_execute;

    c.bench_function("conditional_execute", |b| {
        b.iter(|| {
            let result = conditional_execute(42, |x| x > 10, |x| x * 2, |x| x + 1);
            std::hint::black_box(result);
        });
    });
}

criterion_group!(
    benches,
    bench_function_composition,
    bench_branch_prediction,
    bench_branchless_computation,
    bench_vectorizable_loop,
    bench_state_machine_parser,
    bench_conditional_execute,
);
criterion_main!(benches);
