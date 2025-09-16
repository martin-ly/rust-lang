// Rust 1.89 类型系统集成测试
// 文件: integration_tests.rs
// 创建日期: 2025-01-27
// 版本: 1.0

use c02_type_system::performance::*;
use c02_type_system::rust_189_enhancements::rust_189_type_composition::*;

#[test]
fn test_const_generic_array() {
    let arr = ConstGenericArray::new([1, 2, 3, 4, 5]);
    assert_eq!(arr.len(), 5);
    assert!(!arr.is_empty());

    // 测试数据访问
    assert_eq!(arr.data[0], 1);
    assert_eq!(arr.data[4], 5);
}

#[test]
fn test_lifetime_composed() {
    let data = String::from("test data");
    let metadata = "test metadata";

    let composed = LifetimeComposed::new(&data, metadata);
    assert_eq!(composed.get_data(), &data);
    assert_eq!(composed.get_metadata(), metadata);
}

#[test]
fn test_smart_pointer_composition() {
    let value = 42;
    let mut composition = SmartPointerComposition::new(value);

    assert_eq!(*composition.get(), 42);
    *composition.get_mut() = 100;
    assert_eq!(*composition.get(), 100);
}

#[test]
fn test_number_processor() {
    let processor = create_number_processor();
    assert_eq!(processor, 42);
}

#[test]
fn test_performance_analyzer() {
    let mut analyzer = PerformanceAnalyzer::new();

    let result1 = BenchmarkResult {
        name: "baseline".to_string(),
        duration: std::time::Duration::from_millis(100),
        memory_usage: 1000,
        iterations: 1000,
        throughput: 10000.0,
    };

    let result2 = BenchmarkResult {
        name: "improved".to_string(),
        duration: std::time::Duration::from_millis(50),
        memory_usage: 500,
        iterations: 1000,
        throughput: 20000.0,
    };

    analyzer.add_result(result1);
    analyzer.add_result(result2);
    analyzer.set_baseline("baseline");

    let analysis = analyzer.analyze();
    assert_eq!(analysis.comparisons.len(), 1);
    assert_eq!(analysis.comparisons[0].0, "improved");
    assert!(analysis.comparisons[0].1 > 0.0);
}

#[test]
fn test_benchmark_runner() {
    let runner = BenchmarkRunner::new(1000, 100);
    let result = runner.run("test", || {
        let _x = 1 + 1;
    });

    assert_eq!(result.name, "test");
    assert_eq!(result.iterations, 1000);
    assert!(result.throughput > 0.0);
}

#[test]
fn test_run_all_benchmarks() {
    let analysis = run_all_benchmarks();
    assert!(!analysis.comparisons.is_empty());
    assert!(!analysis.summary.is_empty());

    println!("性能测试结果:");
    println!("{}", analysis.summary);
}
