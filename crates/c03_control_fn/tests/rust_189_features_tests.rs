use c03_control_fn::rust_189_features::*;
use c03_control_fn::async_control_flow_189::*;
use c03_control_fn::performance_optimization_189::*;

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
    let executor = AsyncControlFlowExecutor;
    
    // 测试异步if-else
    let result = executor
        .async_if_else(
            true,
            async { "if_branch" },
            async { "else_branch" },
        )
        .await;
    assert_eq!(result, "if_branch");
    
    let result = executor
        .async_if_else(
            false,
            async { "if_branch" },
            async { "else_branch" },
        )
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
    
    let size = calculate_matrix_size::<2, 3>();
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
    
    // 测试编译时计算
    assert_eq!(FACTORIAL_10, 3628800);
    assert!(PRIME_17);
}

#[test]
fn test_control_flow_optimization() {
    let data = vec![1, -2, 0, 3, -4];
    let result = ControlFlowOptimizer::branch_prediction_friendly_process(&data);
    
    assert_eq!(result, vec![2, 2, 0, 6, 4]);
    
    // 测试无分支操作
    assert_eq!(ControlFlowOptimizer::branchless_max(10, 20), 20);
    assert_eq!(ControlFlowOptimizer::branchless_max(-10, -20), -10);
    
    assert_eq!(ControlFlowOptimizer::branchless_abs(10), 10);
    assert_eq!(ControlFlowOptimizer::branchless_abs(-10), 10);
}

#[tokio::test]
async fn test_async_iterator() {
    let mut iterator = AsyncNumberGenerator::new(0, 5);
    
    let mut results = Vec::new();
    while let Some(item) = iterator.next().await {
        results.push(item);
    }
    
    assert_eq!(results, vec![0, 1, 2, 3, 4]);
}

#[test]
fn test_lifetime_inference() {
    let processor = Processor {
        data: b"test data",
    };
    
    let result = processor.process("input");
    assert_eq!(result, "input");
    
    let iter = processor.create_iterator();
    let items: Vec<&i32> = iter.collect();
    assert_eq!(items.len(), 0); // 空迭代器
}

#[test]
fn test_memory_layout_analysis() {
    let analysis = MemoryLayoutOptimizer::analyze_layout::<DefaultLayout>();
    println!("Default Layout Analysis:\n{}", analysis);
    
    let analysis = MemoryLayoutOptimizer::analyze_layout::<COptimizedLayout>();
    println!("Optimized Layout Analysis:\n{}", analysis);
    
    // 验证分析结果
    assert!(analysis.size > 0);
    assert!(analysis.align > 0);
    assert!(analysis.efficiency >= 0.0 && analysis.efficiency <= 1.0);
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
    
    // 测试矩阵类型
    let matrix = Matrix::<f64, Type3, Type4>::new();
    assert_eq!(matrix.size(), 12);
}

#[test]
fn test_error_handling_improvements() {
    // 测试改进的错误类型
    let result: Result<(), Box<dyn std::error::Error + Send + Sync>> = Ok(());
    assert!(result.is_ok());
    
    // 测试错误传播
    let error_result = Err("test error".to_string());
    let propagated = error_result.map_err(|e| e.into());
    assert!(propagated.is_err());
}

#[test]
fn test_macro_improvements() {
    // 测试宏2.0改进
    let result = math_utils::power(2.0, 3);
    assert_eq!(result, 8.0);
    
    let result = math_utils::power(3.0, 2);
    assert_eq!(result, 9.0);
}

// 集成测试
#[tokio::test]
async fn test_integration_scenarios() {
    // 场景1: 异步数据处理管道
    let processor = TextProcessor;
    let executor = AsyncControlFlowExecutor;
    
    let data = b"Hello, World!";
    let processed = processor.process(data).await.unwrap();
    
    let result = executor
        .async_if_else(
            processed.len() > 10,
            async { "long_text" },
            async { "short_text" },
        )
        .await;
    
    assert_eq!(result, "long_text");
    
    // 场景2: 性能优化组合
    let matrix = Matrix::<f64, 3, 3>::new();
    let size = calculate_matrix_size::<3, 3>();
    assert_eq!(size, 9);
    
    // 场景3: 控制流优化
    let data = vec![1, -2, 3, -4, 5];
    let optimized = ControlFlowOptimizer::branch_prediction_friendly_process(&data);
    assert_eq!(optimized.len(), data.len());
}

// 性能基准测试
#[test]
fn test_performance_characteristics() {
    // 测试内联优化效果
    let start = std::time::Instant::now();
    for _ in 0..1000000 {
        let _ = fast_add(1, 2);
    }
    let duration = start.elapsed();
    
    // 内联优化应该很快
    assert!(duration.as_millis() < 100);
    
    // 测试内存布局优化
    let default_size = std::mem::size_of::<DefaultLayout>();
    let optimized_size = std::mem::size_of::<COptimizedLayout>();
    
    println!("Default layout size: {} bytes", default_size);
    println!("Optimized layout size: {} bytes", optimized_size);
    
    // 优化后的布局应该更高效
    assert!(optimized_size <= default_size);
}

// 错误处理测试
#[test]
fn test_error_handling_edge_cases() {
    // 测试边界情况
    let processor = TextProcessor;
    
    // 测试空数据
    let result = processor.validate("").await;
    assert!(!result);
    
    // 测试大数据
    let large_data = vec![0u8; 10000];
    let result = processor.process(&large_data).await;
    assert!(result.is_ok());
}

// 并发安全测试
#[tokio::test]
async fn test_concurrency_safety() {
    use std::sync::Arc;
    use tokio::sync::Mutex;
    
    let processor = Arc::new(TextProcessor);
    let mut handles = Vec::new();
    
    // 创建多个并发任务
    for i in 0..10 {
        let processor = Arc::clone(&processor);
        let handle = tokio::spawn(async move {
            let data = format!("data_{}", i).into_bytes();
            processor.process(&data).await
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        let result = handle.await.unwrap();
        assert!(result.is_ok());
    }
}

// 内存安全测试
#[test]
fn test_memory_safety() {
    // 测试生命周期推断
    let data = vec![1, 2, 3, 4, 5];
    let processor = Processor { data: &data };
    
    let result = processor.process("test");
    assert_eq!(result, "test");
    
    // 测试内存布局安全性
    let optimized = COptimizedLayout {
        a: 1,
        c: 2,
        d: 3,
        b: 4,
    };
    
    // 确保可以安全访问
    assert_eq!(optimized.a, 1);
    assert_eq!(optimized.b, 4);
    assert_eq!(optimized.c, 2);
    assert_eq!(optimized.d, 3);
}

// 编译时验证测试
#[test]
fn test_compile_time_validation() {
    // 测试编译时常量
    assert_eq!(MATRIX_SIZE, 12);
    assert!(IS_PRIME_17);
    
    // 测试类型级编程
    let matrix = Matrix::<f64, Type3, Type4>::new();
    assert_eq!(matrix.size(), 12);
    
    // 测试常量泛型约束
    let _: Matrix<f64, 2, 3> = Matrix::new();
    // 这应该编译通过
    
    // 测试编译时计算
    let factorial_5 = compile_time_factorial(5);
    assert_eq!(factorial_5, 120);
}

// 文档示例测试
#[test]
fn test_documentation_examples() {
    // 测试README中的示例
    let executor = AsyncControlFlowExecutor;
    
    // 测试异步控制流示例
    let result = executor
        .async_if_else(
            true,
            async { "if分支" },
            async { "else分支" },
        )
        .await;
    assert_eq!(result, "if分支");
    
    // 测试控制流优化示例
    let data = vec![1, 2, 3, 4, 5];
    let result = ControlFlowOptimizer::branch_prediction_friendly_process(&data);
    assert_eq!(result, vec![2, 4, 6, 8, 10]);
    
    // 测试GATs示例
    let collection = VecCollection { items: data };
    let mut iter = collection.iter();
    assert_eq!(iter.next(), Some(&1));
    
    // 测试常量泛型示例
    let matrix = Matrix::<i32, 2, 3>::new();
    assert_eq!(matrix.get(0, 0), Some(&0));
}

// 基准测试
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
    assert!(web_duration.as_millis() < 100);
    assert!(data_duration.as_millis() < 1000);
    assert!(system_duration.as_millis() < 100);
}
