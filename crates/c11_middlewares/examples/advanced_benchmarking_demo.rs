//! 高级基准测试演示
//! 
//! 本示例展示了如何使用 c11_middlewares 的高级基准测试功能
//! 来测试各种操作的性能，包括单线程、多线程和负载测试。

use c11_middlewares::advanced_benchmarks::*;
use c11_middlewares::{Error, Result};
use std::time::Duration;
use std::thread;

/// 模拟一个简单的计算操作
#[allow(dead_code)]
fn simple_computation() -> Result<()> {
    // 模拟一些计算工作
    let mut sum = 0;
    for i in 0..1000 {
        sum += i;
    }
    
    // 模拟偶尔的错误
    if sum % 10000 == 0 {
        Err(Error::Other("模拟错误".to_string()))
    } else {
        Ok(())
    }
}

/// 模拟一个需要等待的 I/O 操作
#[allow(dead_code)]
fn simulated_io_operation() -> Result<()> {
    // 模拟 I/O 延迟
    thread::sleep(Duration::from_millis(1));
    
    // 模拟偶尔的超时错误
    if std::process::id() % 100 == 0 {
        Err(Error::Other("I/O 超时".to_string()))
    } else {
        Ok(())
    }
}

/// 模拟一个内存密集型操作
#[allow(dead_code)]
fn memory_intensive_operation() -> Result<()> {
    // 分配一些内存
    let mut data = Vec::with_capacity(10000);
    for i in 0..10000 {
        data.push(i as f64);
    }
    
    // 进行一些计算
    let sum: f64 = data.iter().sum();
    
    // 模拟偶尔的内存不足错误
    if sum > 50000000.0 {
        Err(Error::Other("内存不足".to_string()))
    } else {
        Ok(())
    }
}

#[cfg(feature = "tokio")]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 高级基准测试演示 ===\n");
    
    let mut benchmarker = AdvancedBenchmarker::new();
    
    // 1. 单线程计算操作测试
    println!("1. 单线程计算操作测试");
    println!("------------------------");
    
    let result1 = benchmarker.run_single_threaded_benchmark(
        "简单计算操作",
        simple_computation,
        1000,
    )?;
    
    print_benchmark_result(&result1);
    
    // 2. 单线程 I/O 操作测试
    println!("\n2. 单线程 I/O 操作测试");
    println!("----------------------");
    
    let result2 = benchmarker.run_single_threaded_benchmark(
        "模拟 I/O 操作",
        simulated_io_operation,
        100,
    )?;
    
    print_benchmark_result(&result2);
    
    // 3. 单线程内存密集型操作测试
    println!("\n3. 单线程内存密集型操作测试");
    println!("---------------------------");
    
    let result3 = benchmarker.run_single_threaded_benchmark(
        "内存密集型操作",
        memory_intensive_operation,
        500,
    )?;
    
    print_benchmark_result(&result3);
    
    // 4. 多线程并发测试
    println!("\n4. 多线程并发测试");
    println!("------------------");
    
    let result4 = benchmarker.run_concurrent_benchmark(
        "多线程计算操作",
        simple_computation,
        1000,
        4, // 4个线程
    )?;
    
    print_benchmark_result(&result4);
    
    // 5. 多线程 I/O 操作测试
    println!("\n5. 多线程 I/O 操作测试");
    println!("----------------------");
    
    let result5 = benchmarker.run_concurrent_benchmark(
        "多线程 I/O 操作",
        simulated_io_operation,
        200,
        2, // 2个线程
    )?;
    
    print_benchmark_result(&result5);
    
    // 6. 生成综合报告
    println!("\n6. 综合测试报告");
    println!("================");
    
    let report = benchmarker.generate_report();
    println!("{}", report);
    
    // 7. 性能对比分析
    println!("\n7. 性能对比分析");
    println!("================");
    
    let results = benchmarker.get_results();
    
    // 找出最快的操作
    let fastest = results.iter()
        .min_by(|a, b| a.average_latency_ms.partial_cmp(&b.average_latency_ms).unwrap())
        .unwrap();
    
    println!("最快操作: {} (平均延迟: {:.2} ms)", 
             fastest.test_name, fastest.average_latency_ms);
    
    // 找出吞吐量最高的操作
    let highest_throughput = results.iter()
        .max_by(|a, b| a.throughput_ops_per_sec.partial_cmp(&b.throughput_ops_per_sec).unwrap())
        .unwrap();
    
    println!("最高吞吐量: {} ({:.2} ops/sec)", 
             highest_throughput.test_name, highest_throughput.throughput_ops_per_sec);
    
    // 找出最稳定的操作（成功率最高）
    let most_stable = results.iter()
        .max_by(|a, b| a.success_rate.partial_cmp(&b.success_rate).unwrap())
        .unwrap();
    
    println!("最稳定操作: {} (成功率: {:.2}%)", 
             most_stable.test_name, most_stable.success_rate);
    
    // 8. 资源使用分析
    println!("\n8. 资源使用分析");
    println!("================");
    
    let memory_heavy = results.iter()
        .max_by(|a, b| a.memory_usage_mb.partial_cmp(&b.memory_usage_mb).unwrap())
        .unwrap();
    
    println!("内存使用最高: {} ({:.2} MB)", 
             memory_heavy.test_name, memory_heavy.memory_usage_mb);
    
    let cpu_heavy = results.iter()
        .max_by(|a, b| a.cpu_usage_percent.partial_cmp(&b.cpu_usage_percent).unwrap())
        .unwrap();
    
    println!("CPU 使用最高: {} ({:.2}%)", 
             cpu_heavy.test_name, cpu_heavy.cpu_usage_percent);
    
    println!("\n=== 基准测试演示完成 ===");
    println!("高级基准测试功能展示了全面的性能分析能力！");
    
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("=== 高级基准测试演示 ===");
    println!("此示例需要 tokio 特性才能运行");
    println!("请使用: cargo run --example advanced_benchmarking_demo --features tokio");
    
    // 即使没有 tokio，我们也可以演示一些基本功能
    println!("\n基本功能演示:");
    
    let mut benchmarker = AdvancedBenchmarker::new();
    
    match benchmarker.run_single_threaded_benchmark(
        "基本测试",
        || Ok(()),
        100,
    ) {
        Ok(result) => {
            println!("基本测试完成:");
            println!("  操作次数: {}", result.operations_performed);
            println!("  成功率: {:.2}%", result.success_rate);
            println!("  平均延迟: {:.2} ms", result.average_latency_ms);
        }
        Err(e) => println!("测试失败: {}", e),
    }
}

/// 打印基准测试结果
#[allow(dead_code)]
fn print_benchmark_result(result: &AdvancedBenchmarkResult) {
    println!("测试名称: {}", result.test_name);
    println!("  持续时间: {:?}", result.duration);
    println!("  操作次数: {}", result.operations_performed);
    println!("  吞吐量: {:.2} ops/sec", result.throughput_ops_per_sec);
    println!("  平均延迟: {:.2} ms", result.average_latency_ms);
    println!("  P50 延迟: {:.2} ms", result.p50_latency_ms);
    println!("  P95 延迟: {:.2} ms", result.p95_latency_ms);
    println!("  P99 延迟: {:.2} ms", result.p99_latency_ms);
    println!("  内存使用: {:.2} MB", result.memory_usage_mb);
    println!("  CPU 使用: {:.2}%", result.cpu_usage_percent);
    println!("  错误数: {}", result.error_count);
    println!("  成功率: {:.2}%", result.success_rate);
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    #[allow(dead_code)]
    fn test_simple_computation() {
        let result = simple_computation();
        // 这个测试可能会成功或失败，都是正常的
        assert!(result.is_ok() || result.is_err());
    }
    
    #[test]
    fn test_memory_intensive_operation() {
        let result = memory_intensive_operation();
        // 这个测试可能会成功或失败，都是正常的
        assert!(result.is_ok() || result.is_err());
    }
    
    #[test]
    fn test_benchmarker_basic_functionality() {
        let mut benchmarker = AdvancedBenchmarker::new();
        
        let result = benchmarker.run_single_threaded_benchmark(
            "test_operation",
            || Ok(()),
            10,
        ).unwrap();
        
        assert_eq!(result.test_name, "test_operation");
        assert_eq!(result.operations_performed, 10);
        assert_eq!(result.error_count, 0);
        assert_eq!(result.success_rate, 100.0);
    }
    
    #[test]
    fn test_concurrent_benchmark() {
        let mut benchmarker = AdvancedBenchmarker::new();
        
        let result = benchmarker.run_concurrent_benchmark(
            "concurrent_test",
            || Ok(()),
            20,
            2,
        ).unwrap();
        
        assert_eq!(result.test_name, "concurrent_test");
        assert_eq!(result.operations_performed, 20);
        assert_eq!(result.error_count, 0);
    }
}
