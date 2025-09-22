//! 性能分析演示程序
//!
//! 展示性能监控、分析和优化功能

use std::time::{Duration, Instant};
use std::thread;
use c13_microservice::performance::{
    PerformanceMonitor, PerformanceConfig, PerformanceBenchmark, PerformanceTestSuite,
    TestSuiteConfig, OutputFormat,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 性能分析演示程序启动");
    println!("{}", "=".repeat(50));

    // 演示性能监控
    demo_performance_monitoring().await?;
    
    // 演示基准测试
    demo_benchmarking()?;
    
    // 演示性能测试套件
    demo_test_suite()?;

    println!("\n✅ 性能分析演示完成！");
    Ok(())
}

/// 演示性能监控功能
async fn demo_performance_monitoring() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📊 演示性能监控功能");
    println!("{}", "-".repeat(30));

    // 创建性能监控器
    let config = PerformanceConfig::default();
    let mut monitor = PerformanceMonitor::new(config);

    // 开始监控
    monitor.start_monitoring()?;
    println!("✅ 开始性能监控");

    // 模拟一些工作负载
    println!("🔄 模拟工作负载...");
    
    // 模拟函数执行
    for i in 0..5 {
        let start = Instant::now();
        simulate_cpu_intensive_work();
        let duration = start.elapsed();
        
        let event = c13_microservice::performance::profiler::ProfilerEvent::new(
            format!("cpu_work_{}", i),
            "function".to_string(),
            c13_microservice::performance::profiler::ProfilerEventType::Function,
        ).with_duration(duration);
        
        monitor.record_event(event)?;
        
        println!("  完成CPU密集型任务 {} (耗时: {:.2}ms)", i + 1, duration.as_secs_f64() * 1000.0);
    }

    // 模拟内存使用
    let memory_usage = simulate_memory_usage();
    let mut metadata = std::collections::HashMap::new();
    metadata.insert("memory_bytes".to_string(), memory_usage.to_string());
    
    let event = c13_microservice::performance::profiler::ProfilerEvent::new(
        "memory_usage".to_string(),
        "memory".to_string(),
        c13_microservice::performance::profiler::ProfilerEventType::Memory,
    );
    
    monitor.record_event(event)?;
    println!("  记录内存使用: {} bytes", memory_usage);

    // 模拟网络请求
    for i in 0..3 {
        let start = Instant::now();
        simulate_network_request().await;
        let duration = start.elapsed();
        
        let mut metadata = std::collections::HashMap::new();
        metadata.insert("url".to_string(), format!("api_request_{}", i));
        metadata.insert("method".to_string(), "GET".to_string());
        metadata.insert("status_code".to_string(), "200".to_string());
        
        let event = c13_microservice::performance::profiler::ProfilerEvent::new(
            "network_request".to_string(),
            "network".to_string(),
            c13_microservice::performance::profiler::ProfilerEventType::Network,
        ).with_duration(duration);
        
        monitor.record_event(event)?;
        
        println!("  完成网络请求 {} (耗时: {:.2}ms)", i + 1, duration.as_secs_f64() * 1000.0);
    }

    // 模拟数据库查询
    for i in 0..2 {
        let start = Instant::now();
        simulate_database_query();
        let duration = start.elapsed();
        
        let mut metadata = std::collections::HashMap::new();
        metadata.insert("query".to_string(), format!("SELECT * FROM users WHERE id = {}", i));
        metadata.insert("rows_affected".to_string(), "1".to_string());
        
        let event = c13_microservice::performance::profiler::ProfilerEvent::new(
            "database_query".to_string(),
            "database".to_string(),
            c13_microservice::performance::profiler::ProfilerEventType::Database,
        ).with_duration(duration);
        
        monitor.record_event(event)?;
        
        println!("  完成数据库查询 {} (耗时: {:.2}ms)", i + 1, duration.as_secs_f64() * 1000.0);
    }

    // 停止监控并获取统计信息
    let stats = monitor.stop_monitoring()?;
    println!("✅ 停止性能监控");

    // 显示统计信息
    println!("\n📈 性能统计信息:");
    println!("  总事件数: {}", stats.total_events);
    println!("  类别数: {}", stats.categories.len());
    println!("  总执行时间: {:.2}ms", stats.timing_stats.total_duration.as_secs_f64() * 1000.0);
    println!("  平均执行时间: {:.2}ms", stats.timing_stats.average_duration.as_secs_f64() * 1000.0);
    println!("  最大执行时间: {:.2}ms", stats.timing_stats.max_duration.as_secs_f64() * 1000.0);
    println!("  平均内存使用: {} bytes", stats.memory_stats.average_memory);

    // 分析性能数据
    let report = monitor.analyze_performance()?;
    println!("\n🎯 性能分析报告:");
    println!("  整体性能分数: {:.1}/100", report.overall_score);
    println!("  性能瓶颈数: {}", report.bottlenecks.len());
    println!("  优化建议数: {}", report.recommendations.len());

    // 生成优化建议
    let suggestions = monitor.generate_optimization_suggestions()?;
    if !suggestions.is_empty() {
        println!("\n💡 优化建议:");
        for (i, suggestion) in suggestions.iter().take(3).enumerate() {
            println!("  {}. {} - {}", i + 1, suggestion.title, suggestion.description);
        }
    }

    Ok(())
}

/// 演示基准测试功能
fn demo_benchmarking() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚡ 演示基准测试功能");
    println!("{}", "-".repeat(30));

    // 创建基准测试器
    let mut benchmark = PerformanceBenchmark::new("字符串处理".to_string())
        .iterations(1000)
        .warmup_iterations(100);

    // 运行基准测试
    println!("🔄 运行基准测试...");
    let result = benchmark.run(|| {
        simulate_string_processing();
    });

    // 显示结果
    println!("✅ 基准测试完成:");
    println!("  测试名称: {}", result.name);
    println!("  迭代次数: {}", result.iterations);
    println!("  总耗时: {:.2}ms", result.total_duration.as_secs_f64() * 1000.0);
    println!("  平均耗时: {:.2}ns", result.average_duration().as_nanos());
    println!("  最小耗时: {:.2}ns", result.min_duration().as_nanos());
    println!("  最大耗时: {:.2}ns", result.max_duration().as_nanos());
    println!("  95百分位: {:.2}ns", result.percentile(95.0).as_nanos());
    println!("  99百分位: {:.2}ns", result.percentile(99.0).as_nanos());
    println!("  每秒操作数: {:.2}", result.operations_per_second());

    Ok(())
}

/// 演示性能测试套件
fn demo_test_suite() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🧪 演示性能测试套件");
    println!("{}", "-".repeat(30));

    // 创建测试套件
    let config = TestSuiteConfig {
        iterations: 500,
        warmup_iterations: 50,
        enable_statistics: true,
        output_format: OutputFormat::Text,
    };

    let mut test_suite = PerformanceTestSuite::new("微服务性能测试".to_string())
        .config(config);

    // 添加多个基准测试
    println!("🔄 运行性能测试套件...");
    
    test_suite.add_benchmark("字符串处理".to_string(), || {
        simulate_string_processing();
    });

    test_suite.add_benchmark("数学计算".to_string(), || {
        simulate_math_calculation();
    });

    test_suite.add_benchmark("数据结构操作".to_string(), || {
        simulate_data_structure_operations();
    });

    test_suite.add_benchmark("内存分配".to_string(), || {
        simulate_memory_allocation();
    });

    // 生成报告
    let report = test_suite.generate_report();
    println!("✅ 测试套件完成");
    println!("\n📊 测试报告:");
    println!("{}", report);

    Ok(())
}

/// 模拟CPU密集型工作
fn simulate_cpu_intensive_work() {
    let mut sum = 0u64;
    for i in 0..1_000_000 {
        sum = sum.wrapping_add(i);
    }
    std::hint::black_box(sum);
}

/// 模拟内存使用
fn simulate_memory_usage() -> usize {
    let data = vec![0u8; 1024 * 1024]; // 1MB
    std::hint::black_box(data);
    1024 * 1024
}

/// 模拟网络请求
async fn simulate_network_request() {
    // 模拟网络延迟
    tokio::time::sleep(Duration::from_millis(50)).await;
    
    // 模拟一些处理工作
    let mut result = String::new();
    for i in 0..1000 {
        result.push_str(&format!("response_data_{}", i));
    }
    std::hint::black_box(result);
}

/// 模拟数据库查询
fn simulate_database_query() {
    // 模拟数据库查询延迟
    thread::sleep(Duration::from_millis(20));
    
    // 模拟数据处理
    let mut users = Vec::new();
    for i in 0..100 {
        users.push(format!("user_{}", i));
    }
    std::hint::black_box(users);
}

/// 模拟字符串处理
fn simulate_string_processing() {
    let mut text = String::new();
    for i in 0..1000 {
        text.push_str(&format!("测试文本_{}", i));
    }
    let processed = text.to_uppercase();
    let reversed: String = processed.chars().rev().collect();
    std::hint::black_box(reversed);
}

/// 模拟数学计算
fn simulate_math_calculation() {
    let mut result = 0.0;
    for i in 0..10000 {
        result += (i as f64).sqrt().sin().cos();
    }
    std::hint::black_box(result);
}

/// 模拟数据结构操作
fn simulate_data_structure_operations() {
    use std::collections::HashMap;
    
    let mut map = HashMap::new();
    for i in 0..1000 {
        map.insert(i, format!("value_{}", i));
    }
    
    let mut sum = 0;
    for (key, value) in &map {
        sum += key + value.len();
    }
    std::hint::black_box(sum);
}

/// 模拟内存分配
fn simulate_memory_allocation() {
    let mut data = Vec::with_capacity(10000);
    for i in 0..10000 {
        data.push(i);
    }
    
    // 模拟一些操作
    let sum: i32 = data.iter().sum();
    std::hint::black_box(sum);
}
