//! Rust 1.89 功能 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新测试请参考 `rust_192_comprehensive_tests.rs`
//!
//! ## 版本历史说明
//!
//! 本文件展示 Rust 1.89 版本的测试，当前项目已升级到 Rust 1.92.0。
//!
//! 参考:
//! - [Rust 1.92.0 Release Notes](https://releases.rs/docs/1.92.0/)
//! - [历史版本: Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)

use c03_control_fn::async_control_flow_189::AsyncControlFlowExecutor189;
use c03_control_fn::performance_optimization_189::{
    COptimizedLayout, ControlFlowOptimizer, DefaultLayout, FACTORIAL_10, PRIME_17, fast_add,
};
use c03_control_fn::rust_189_features::{
    AsyncProcessor, Collection, Matrix, TextProcessor, Type0, Type1, Type2, Type3, VecCollection,
    calculate_matrix_size as calc_size_feat, compile_time_factorial, is_prime, process_strings,
};

#[tokio::test]
async fn test_async_trait_stability() {
    let processor = TextProcessor;

    // 测试异步trait方法
    let data = b"Hello, Rust 1.89!";
    let result = processor.process(data).await;
    assert!(result.is_ok());

    let processed_data = result.unwrap();
    assert_eq!(processed_data, data);

    // 测试验证方法
    let is_valid = processor.validate("test").await;
    assert!(is_valid);

    let is_invalid = processor.validate("").await;
    assert!(!is_invalid);
}

#[tokio::test]
async fn test_async_control_flow() {
    let executor = AsyncControlFlowExecutor189;

    // 测试异步if-else
    let result = executor
        .async_if_else(true, async { "if_branch" }, async { "else_branch" })
        .await;
    assert_eq!(result, "if_branch");

    let result = executor
        .async_if_else(false, async { "if_branch" }, async { "else_branch" })
        .await;
    assert_eq!(result, "else_branch");
}

#[test]
fn test_gats_implementation() {
    let collection = VecCollection {
        items: vec![1, 2, 3, 4, 5],
    };

    let mut iter = collection.iter();
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.next(), Some(&3));
    assert_eq!(iter.next(), Some(&4));
    assert_eq!(iter.next(), Some(&5));
    assert_eq!(iter.next(), None);
}

#[test]
fn test_const_generics() {
    let matrix = Matrix::<f64, 2, 3>::new();
    assert_eq!(matrix.get(0, 0), Some(&0.0));
    assert_eq!(matrix.get(1, 2), Some(&0.0));
    assert_eq!(matrix.get(2, 0), None); // 超出边界

    let size = calc_size_feat::<2, 3>();
    assert_eq!(size, 6);
}

#[test]
fn test_performance_optimization() {
    // 测试内联优化
    let result = fast_add(10, 20);
    assert_eq!(result, 30);

    // 测试内存布局优化
    let default_size = std::mem::size_of::<DefaultLayout>();
    let optimized_size = std::mem::size_of::<COptimizedLayout>();

    // 优化后的布局应该更小或相等
    assert!(optimized_size <= default_size);

    // 测试编译时计算（使用性能模块中的常量）
    assert_eq!(FACTORIAL_10, 3628800);
    assert!(PRIME_17);
}

#[test]
fn test_control_flow_optimization() {
    // 使用0..=10范围，匹配分支预测友好处理逻辑（*2）
    let data = vec![1, 2, 0, 3, 4];
    let result = ControlFlowOptimizer::branch_prediction_friendly_process(&data);

    assert_eq!(result, vec![2, 4, 0, 6, 8]);

    // 测试无分支操作
    assert_eq!(ControlFlowOptimizer::branchless_max(10, 20), 20);
    assert_eq!(ControlFlowOptimizer::branchless_max(-10, -20), -10);

    assert_eq!(ControlFlowOptimizer::branchless_abs(10), 10);
    assert_eq!(ControlFlowOptimizer::branchless_abs(-10), 10);
}

#[tokio::test]
async fn test_async_iterator() {
    // 使用AsyncStreamProcessor模拟异步迭代处理
    use c03_control_fn::async_control_flow::AsyncStreamProcessor;
    let mut processor = AsyncStreamProcessor::new(vec![1, 2, 3, 4, 5]);
    let mut results = Vec::new();
    while let Some(val) = processor.process_next(|&x| async move { x * x }).await {
        results.push(val);
    }
    assert_eq!(results, vec![1, 4, 9, 16, 25]);
}

#[test]
fn test_lifetime_inference() {
    // 使用process_strings验证生命周期推断
    let data = vec!["a".to_string(), "bb".to_string(), "ccc".to_string()];
    let slices = process_strings(&data);
    assert_eq!(slices, vec!["a", "bb", "ccc"]);
}

#[test]
fn test_memory_layout_analysis() {
    // 简化为验证大小与对齐
    let d_size = std::mem::size_of::<DefaultLayout>();
    let c_size = std::mem::size_of::<COptimizedLayout>();
    assert!(c_size <= d_size);

    // 基本对齐大于0
    assert!(std::mem::align_of::<DefaultLayout>() > 0);
    assert!(std::mem::align_of::<COptimizedLayout>() > 0);
}

#[test]
fn test_compile_time_calculation() {
    // 测试编译时常量函数
    assert_eq!(compile_time_factorial(0), 1);
    assert_eq!(compile_time_factorial(1), 1);
    assert_eq!(compile_time_factorial(5), 120);

    // 测试素数检查
    assert!(!is_prime(0));
    assert!(!is_prime(1));
    assert!(is_prime(2));
    assert!(is_prime(3));
    assert!(!is_prime(4));
    assert!(is_prime(5));
    assert!(!is_prime(6));
    assert!(is_prime(7));
}

#[test]
fn test_type_level_programming() {
    // 测试类型级数字
    assert_eq!(Type0::VALUE, 0);
    assert_eq!(Type1::VALUE, 1);
    assert_eq!(Type2::VALUE, 2);
    assert_eq!(Type3::VALUE, 3);

    // 测试矩阵常量维度
    let size = calc_size_feat::<3, 4>();
    assert_eq!(size, 12);
}

#[test]
fn test_error_handling_improvements() {
    // 测试改进的错误类型
    let result: Result<(), Box<dyn std::error::Error + Send + Sync>> = Ok(());
    assert!(result.is_ok());

    // 测试错误传播
    let error_result: Result<(), String> = Err("test error".to_string());
    let propagated: Result<(), Box<dyn std::error::Error + Send + Sync>> =
        error_result.map_err(|e| e.into());
    assert!(propagated.is_err());
}

#[tokio::test]
async fn test_documentation_examples() {
    // 测试异步控制流示例
    let executor = AsyncControlFlowExecutor189;
    let result = executor
        .async_if_else(true, async { "if分支" }, async { "else分支" })
        .await;
    assert_eq!(result, "if分支");

    // 测试控制流优化示例
    let data = vec![1, 2, 3, 4, 5];
    let result = ControlFlowOptimizer::branch_prediction_friendly_process(&data);
    assert_eq!(result.len(), data.len());

    // 测试常量泛型示例
    let matrix = Matrix::<i32, 2, 3>::new();
    assert_eq!(matrix.get(0, 0), Some(&0));
}

#[test]
fn test_benchmark_scenarios() {
    // Web服务性能测试
    let start = std::time::Instant::now();
    for _ in 0..1000 {
        let _ = fast_add(1, 2);
    }
    let web_duration = start.elapsed();

    // 数据处理性能测试
    let start = std::time::Instant::now();
    let data = vec![1i32; 10000];
    let _ = ControlFlowOptimizer::branch_prediction_friendly_process(&data);
    let data_duration = start.elapsed();

    // 系统编程性能测试
    let start = std::time::Instant::now();
    for _ in 0..1000 {
        let _ = ControlFlowOptimizer::branchless_max(1, 2);
    }
    let system_duration = start.elapsed();

    println!("Web service performance: {:?}", web_duration);
    println!("Data processing performance: {:?}", data_duration);
    println!("System programming performance: {:?}", system_duration);

    // 性能应该在合理范围内
    assert!(web_duration.as_millis() < 1000);
    assert!(data_duration.as_millis() < 2000);
    assert!(system_duration.as_millis() < 1000);
}
