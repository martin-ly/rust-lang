//! 基准测试演示示例
//! 
//! 展示如何使用c17_iot的基准测试功能来评估IoT系统性能

use c17_iot::benchmarking::{
    Benchmarker, BenchmarkConfig, BenchmarkType
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动基准测试演示...");

    // 创建基准测试器
    let benchmarker = Benchmarker::new();

    println!("📊 开始IoT系统性能基准测试...");

    // 1. 延迟基准测试
    println!("\n1️⃣ 延迟基准测试");
    run_latency_benchmark(&benchmarker).await?;

    // 2. 吞吐量基准测试
    println!("\n2️⃣ 吞吐量基准测试");
    run_throughput_benchmark(&benchmarker).await?;

    // 3. 并发基准测试
    println!("\n3️⃣ 并发基准测试");
    run_concurrency_benchmark(&benchmarker).await?;

    // 4. 内存使用基准测试
    println!("\n4️⃣ 内存使用基准测试");
    run_memory_benchmark(&benchmarker).await?;

    // 5. 稳定性基准测试
    println!("\n5️⃣ 稳定性基准测试");
    run_stability_benchmark(&benchmarker).await?;

    // 6. 压力测试
    println!("\n6️⃣ 压力测试");
    run_stress_benchmark(&benchmarker).await?;

    // 7. 结果分析和对比
    println!("\n7️⃣ 结果分析和对比");
    analyze_benchmark_results(&benchmarker).await?;

    // 8. 生成综合报告
    println!("\n8️⃣ 生成综合报告");
    generate_comprehensive_report(&benchmarker).await?;

    println!("\n✅ 基准测试演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 多种基准测试类型");
    println!("  - 性能指标收集");
    println!("  - 结果分析和对比");
    println!("  - 详细报告生成");

    Ok(())
}

/// 运行延迟基准测试
async fn run_latency_benchmark(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let config = BenchmarkConfig {
        benchmark_type: BenchmarkType::Latency,
        duration: Duration::from_secs(30),
        concurrency: 1,
        data_size: 1024,
        detailed_stats: true,
        sampling_interval: Duration::from_millis(100),
        warmup_duration: Duration::from_secs(2),
    };

    println!("  开始延迟基准测试 (30秒)...");
    benchmarker.start_benchmark("latency_test".to_string(), config).await?;

    // 模拟各种延迟的操作
    for i in 0..100 {
        let operation_latency = Duration::from_millis(50 + (i % 100)); // 50-150ms
        let success = i % 10 != 0; // 90%成功率
        let error = if success { None } else { Some("模拟错误".to_string()) };
        
        benchmarker.record_operation(operation_latency, success, error).await?;
        sleep(Duration::from_millis(300)).await;
    }

    let result = benchmarker.stop_benchmark().await?;
    println!("  延迟测试完成:");
    println!("    平均延迟: {:?}", result.avg_latency);
    println!("    最小延迟: {:?}", result.min_latency);
    println!("    最大延迟: {:?}", result.max_latency);
    println!("    95%分位延迟: {:?}", result.p95_latency);
    println!("    99%分位延迟: {:?}", result.p99_latency);

    Ok(())
}

/// 运行吞吐量基准测试
async fn run_throughput_benchmark(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let config = BenchmarkConfig {
        benchmark_type: BenchmarkType::Throughput,
        duration: Duration::from_secs(20),
        concurrency: 5,
        data_size: 512,
        detailed_stats: true,
        sampling_interval: Duration::from_millis(50),
        warmup_duration: Duration::from_secs(1),
    };

    println!("  开始吞吐量基准测试 (20秒, 5并发)...");
    benchmarker.start_benchmark("throughput_test".to_string(), config).await?;

    // 模拟高吞吐量操作
    for i in 0..200 {
        let operation_latency = Duration::from_millis(10 + (i % 20)); // 10-30ms
        let success = i % 20 != 0; // 95%成功率
        let error = if success { None } else { Some("吞吐量测试错误".to_string()) };
        
        benchmarker.record_operation(operation_latency, success, error).await?;
        sleep(Duration::from_millis(100)).await;
    }

    let result = benchmarker.stop_benchmark().await?;
    println!("  吞吐量测试完成:");
    println!("    总操作数: {}", result.total_operations);
    println!("    吞吐量: {:.2} 操作/秒", result.throughput);
    println!("    成功率: {:.1}%", (result.successful_operations as f64 / result.total_operations as f64) * 100.0);

    Ok(())
}

/// 运行并发基准测试
async fn run_concurrency_benchmark(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let config = BenchmarkConfig {
        benchmark_type: BenchmarkType::Concurrency,
        duration: Duration::from_secs(25),
        concurrency: 10,
        data_size: 256,
        detailed_stats: true,
        sampling_interval: Duration::from_millis(200),
        warmup_duration: Duration::from_secs(3),
    };

    println!("  开始并发基准测试 (25秒, 10并发)...");
    benchmarker.start_benchmark("concurrency_test".to_string(), config).await?;

    // 模拟并发操作
    for i in 0..150 {
        let operation_latency = Duration::from_millis(20 + (i % 50)); // 20-70ms
        let success = i % 15 != 0; // 93%成功率
        let error = if success { None } else { Some("并发测试错误".to_string()) };
        
        benchmarker.record_operation(operation_latency, success, error).await?;
        sleep(Duration::from_millis(150)).await;
    }

    let result = benchmarker.stop_benchmark().await?;
    println!("  并发测试完成:");
    println!("    并发数: 10");
    println!("    平均延迟: {:?}", result.avg_latency);
    println!("    吞吐量: {:.2} 操作/秒", result.throughput);
    println!("    错误率: {:.2}%", result.error_rate);

    Ok(())
}

/// 运行内存使用基准测试
async fn run_memory_benchmark(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let config = BenchmarkConfig {
        benchmark_type: BenchmarkType::MemoryUsage,
        duration: Duration::from_secs(15),
        concurrency: 3,
        data_size: 2048,
        detailed_stats: true,
        sampling_interval: Duration::from_millis(100),
        warmup_duration: Duration::from_secs(2),
    };

    println!("  开始内存使用基准测试 (15秒)...");
    benchmarker.start_benchmark("memory_test".to_string(), config).await?;

    // 模拟内存密集型操作
    for i in 0..80 {
        let operation_latency = Duration::from_millis(30 + (i % 40)); // 30-70ms
        let success = i % 12 != 0; // 92%成功率
        let error = if success { None } else { Some("内存测试错误".to_string()) };
        
        benchmarker.record_operation(operation_latency, success, error).await?;
        sleep(Duration::from_millis(180)).await;
    }

    let result = benchmarker.stop_benchmark().await?;
    println!("  内存测试完成:");
    println!("    平均内存使用: {} 字节", result.avg_memory_usage);
    println!("    峰值内存使用: {} 字节", result.peak_memory_usage);
    println!("    平均CPU使用率: {:.2}%", result.avg_cpu_usage);

    Ok(())
}

/// 运行稳定性基准测试
async fn run_stability_benchmark(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let config = BenchmarkConfig {
        benchmark_type: BenchmarkType::Stability,
        duration: Duration::from_secs(40),
        concurrency: 2,
        data_size: 1024,
        detailed_stats: true,
        sampling_interval: Duration::from_millis(500),
        warmup_duration: Duration::from_secs(5),
    };

    println!("  开始稳定性基准测试 (40秒)...");
    benchmarker.start_benchmark("stability_test".to_string(), config).await?;

    // 模拟长时间稳定运行
    for i in 0..120 {
        let operation_latency = Duration::from_millis(40 + (i % 30)); // 40-70ms
        let success = i % 25 != 0; // 96%成功率
        let error = if success { None } else { Some("稳定性测试错误".to_string()) };
        
        benchmarker.record_operation(operation_latency, success, error).await?;
        sleep(Duration::from_millis(300)).await;
    }

    let result = benchmarker.stop_benchmark().await?;
    println!("  稳定性测试完成:");
    println!("    运行时间: {:?}", result.total_duration);
    println!("    总操作数: {}", result.total_operations);
    println!("    错误率: {:.2}%", result.error_rate);
    println!("    平均延迟: {:?}", result.avg_latency);

    Ok(())
}

/// 运行压力测试
async fn run_stress_benchmark(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let config = BenchmarkConfig {
        benchmark_type: BenchmarkType::Stress,
        duration: Duration::from_secs(30),
        concurrency: 20,
        data_size: 4096,
        detailed_stats: true,
        sampling_interval: Duration::from_millis(50),
        warmup_duration: Duration::from_secs(2),
    };

    println!("  开始压力测试 (30秒, 20并发)...");
    benchmarker.start_benchmark("stress_test".to_string(), config).await?;

    // 模拟高压力操作
    for i in 0..300 {
        let operation_latency = Duration::from_millis(5 + (i % 25)); // 5-30ms
        let success = i % 8 != 0; // 87%成功率
        let error = if success { None } else { Some("压力测试错误".to_string()) };
        
        benchmarker.record_operation(operation_latency, success, error).await?;
        sleep(Duration::from_millis(100)).await;
    }

    let result = benchmarker.stop_benchmark().await?;
    println!("  压力测试完成:");
    println!("    并发数: 20");
    println!("    总操作数: {}", result.total_operations);
    println!("    吞吐量: {:.2} 操作/秒", result.throughput);
    println!("    错误率: {:.2}%", result.error_rate);
    println!("    峰值CPU使用率: {:.2}%", result.peak_cpu_usage);

    Ok(())
}

/// 分析基准测试结果
async fn analyze_benchmark_results(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let all_results = benchmarker.get_all_results().await;
    
    println!("  基准测试结果分析:");
    println!("    总测试数: {}", all_results.len());
    
    // 找出最佳性能
    let best_throughput = all_results.iter()
        .max_by(|a, b| a.throughput.partial_cmp(&b.throughput).unwrap())
        .unwrap();
    println!("    最高吞吐量: {:.2} 操作/秒 ({})", best_throughput.throughput, best_throughput.name);
    
    let lowest_latency = all_results.iter()
        .min_by(|a, b| a.avg_latency.cmp(&b.avg_latency))
        .unwrap();
    println!("    最低延迟: {:?} ({})", lowest_latency.avg_latency, lowest_latency.name);
    
    let lowest_error_rate = all_results.iter()
        .min_by(|a, b| a.error_rate.partial_cmp(&b.error_rate).unwrap())
        .unwrap();
    println!("    最低错误率: {:.2}% ({})", lowest_error_rate.error_rate, lowest_error_rate.name);

    // 性能对比
    if all_results.len() >= 2 {
        let result1 = &all_results[0];
        let result2 = &all_results[1];
        
        if let Ok(comparison) = benchmarker.compare_results(&result1.name, &result2.name).await {
            println!("  性能对比 ({} vs {}):", result1.name, result2.name);
            println!("    延迟改进: {:.1}%", comparison.latency_improvement);
            println!("    吞吐量改进: {:.1}%", comparison.throughput_improvement);
            println!("    内存使用改进: {:.1}%", comparison.memory_improvement);
            println!("    CPU使用改进: {:.1}%", comparison.cpu_improvement);
            println!("    错误率改进: {:.1}%", comparison.error_rate_improvement);
        }
    }

    Ok(())
}

/// 生成综合报告
async fn generate_comprehensive_report(benchmarker: &Benchmarker) -> Result<(), Box<dyn std::error::Error>> {
    let all_results = benchmarker.get_all_results().await;
    
    println!("  生成综合基准测试报告...");
    
    let mut report = String::new();
    report.push_str("# IoT系统基准测试综合报告\n\n");
    report.push_str(&format!("生成时间: {}\n", chrono::Utc::now().format("%Y-%m-%d %H:%M:%S UTC")));
    report.push_str(&format!("测试总数: {}\n\n", all_results.len()));

    // 总体统计
    let total_operations: u64 = all_results.iter().map(|r| r.total_operations).sum();
    let total_duration: Duration = all_results.iter().map(|r| r.total_duration).sum();
    let avg_throughput: f64 = all_results.iter().map(|r| r.throughput).sum::<f64>() / all_results.len() as f64;
    let avg_error_rate: f64 = all_results.iter().map(|r| r.error_rate).sum::<f64>() / all_results.len() as f64;

    report.push_str("## 总体统计\n\n");
    report.push_str(&format!("总操作数: {}\n", total_operations));
    report.push_str(&format!("总测试时间: {:?}\n", total_duration));
    report.push_str(&format!("平均吞吐量: {:.2} 操作/秒\n", avg_throughput));
    report.push_str(&format!("平均错误率: {:.2}%\n\n", avg_error_rate));

    // 各测试详细结果
    report.push_str("## 详细测试结果\n\n");
    for result in &all_results {
        report.push_str(&format!("### {}\n", result.name));
        report.push_str(&format!("- 测试类型: {:?}\n", result.benchmark_type));
        report.push_str(&format!("- 持续时间: {:?}\n", result.total_duration));
        report.push_str(&format!("- 总操作数: {}\n", result.total_operations));
        report.push_str(&format!("- 成功率: {:.1}%\n", (result.successful_operations as f64 / result.total_operations as f64) * 100.0));
        report.push_str(&format!("- 平均延迟: {:?}\n", result.avg_latency));
        report.push_str(&format!("- 吞吐量: {:.2} 操作/秒\n", result.throughput));
        report.push_str(&format!("- 错误率: {:.2}%\n", result.error_rate));
        report.push_str(&format!("- 平均内存使用: {} 字节\n", result.avg_memory_usage));
        report.push_str(&format!("- 平均CPU使用率: {:.2}%\n\n", result.avg_cpu_usage));
    }

    // 性能建议
    report.push_str("## 性能优化建议\n\n");
    if avg_error_rate > 5.0 {
        report.push_str("- 错误率较高，建议检查错误处理机制和系统稳定性\n");
    }
    if avg_throughput < 100.0 {
        report.push_str("- 吞吐量较低，建议优化算法和并发处理\n");
    }
    if all_results.iter().any(|r| r.avg_latency > Duration::from_millis(100)) {
        report.push_str("- 存在高延迟操作，建议优化网络通信和数据处理\n");
    }
    if all_results.iter().any(|r| r.avg_cpu_usage > 80.0) {
        report.push_str("- CPU使用率较高，建议优化计算密集型操作\n");
    }
    if all_results.iter().any(|r| r.avg_memory_usage > 100 * 1024 * 1024) {
        report.push_str("- 内存使用量较大，建议优化内存管理和数据结构\n");
    }

    println!("  综合报告已生成 ({} 字符)", report.len());
    
    // 显示报告的关键部分
    let lines: Vec<&str> = report.lines().take(30).collect();
    for line in lines {
        println!("  {}", line);
    }
    println!("  ... (报告已截断)");

    Ok(())
}
