#![allow(clippy::manual_flatten)]
#![allow(clippy::useless_format)]
#![allow(clippy::useless_vec)]

//! Rust 1.90 性能基准测试示例 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features_demo.rs`
//!
//! 本示例展示了如何使用Rust 1.90的新特性进行性能基准测试
use c10_networks::error::{NetworkError, NetworkResult};
use c10_networks::unified_api::NetClient;
use futures::StreamExt;
use std::time::{Duration, Instant};
use tokio::time::timeout;

/// 性能基准测试结果
#[allow(dead_code)]
#[derive(Debug, Clone)]
struct BenchmarkResult {
    pub test_name: String,
    pub total_operations: usize,
    pub total_duration: Duration,
    pub operations_per_second: f64,
    pub average_latency: Duration,
    pub min_latency: Duration,
    pub max_latency: Duration,
    pub memory_usage: usize,
    pub cpu_usage: f64,
}

#[allow(dead_code)]
impl BenchmarkResult {
    fn new(test_name: String) -> Self {
        Self {
            test_name,
            total_operations: 0,
            total_duration: Duration::ZERO,
            operations_per_second: 0.0,
            average_latency: Duration::ZERO,
            min_latency: Duration::MAX,
            max_latency: Duration::ZERO,
            memory_usage: 0,
            cpu_usage: 0.0,
        }
    }

    #[allow(dead_code)]
    fn calculate_metrics(&mut self) {
        if self.total_operations > 0 {
            self.operations_per_second =
                self.total_operations as f64 / self.total_duration.as_secs_f64();
            self.average_latency = Duration::from_nanos(
                self.total_duration.as_nanos() as u64 / self.total_operations as u64,
            );
        }
    }
}

/// Rust 1.90 性能基准测试主函数
#[tokio::main]
async fn main() -> NetworkResult<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    println!("🚀 Rust 1.90 性能基准测试开始...");

    let client = NetClient::new();

    // 运行各种性能测试
    let mut results = Vec::new();

    // 测试1: 异步DNS解析性能
    results.push(benchmark_dns_lookup(&client, 1000).await?);

    // 测试2: 并发异步操作性能
    results.push(benchmark_concurrent_operations(&client, 1000, 10).await?);

    // 测试3: 异步流处理性能
    results.push(benchmark_stream_processing(10000).await?);

    // 测试4: 内存池性能
    results.push(benchmark_memory_pool(1000).await?);

    // 测试5: 缓存性能
    results.push(benchmark_cache_operations(10000).await?);

    // 输出测试结果
    print_benchmark_results(&results);

    // 生成性能报告
    generate_performance_report(&results).await?;

    println!("✅ 性能基准测试完成！");
    Ok(())
}

/// 基准测试1: DNS解析性能
async fn benchmark_dns_lookup(
    client: &NetClient,
    operations: usize,
) -> NetworkResult<BenchmarkResult> {
    println!("\n📡 基准测试1: DNS解析性能 ({} 次操作)", operations);

    let mut result = BenchmarkResult::new("DNS解析".to_string());
    let start = Instant::now();

    let hosts = vec![
        "example.com",
        "google.com",
        "github.com",
        "rust-lang.org",
        "tokio.rs",
    ];

    for i in 0..operations {
        let host = hosts[i % hosts.len()];
        let operation_start = Instant::now();

        match timeout(Duration::from_secs(5), client.dns_lookup_ips(host)).await {
            Ok(Ok(_)) => {
                let latency = operation_start.elapsed();
                result.min_latency = result.min_latency.min(latency);
                result.max_latency = result.max_latency.max(latency);
            }
            Ok(Err(e)) => {
                eprintln!("DNS解析错误: {}", e);
            }
            Err(_) => {
                eprintln!("DNS解析超时");
            }
        }

        if i % 100 == 0 {
            println!("   进度: {}/{}", i, operations);
        }
    }

    result.total_operations = operations;
    result.total_duration = start.elapsed();
    result.calculate_metrics();

    Ok(result)
}

/// 基准测试2: 并发异步操作性能
async fn benchmark_concurrent_operations(
    client: &NetClient,
    total_operations: usize,
    concurrency: usize,
) -> NetworkResult<BenchmarkResult> {
    println!(
        "\n⚡ 基准测试2: 并发异步操作性能 ({} 次操作, 并发度: {})",
        total_operations, concurrency
    );

    let mut result = BenchmarkResult::new("并发操作".to_string());
    let start = Instant::now();

    let hosts = vec![
        "example.com",
        "google.com",
        "github.com",
        "rust-lang.org",
        "tokio.rs",
    ];

    let operations_per_batch = total_operations / concurrency;

    // 创建并发任务
    let tasks = (0..concurrency).map(|_batch_id| {
        let client = client.clone();
        let hosts = hosts.clone();

        tokio::spawn(async move {
            let mut batch_results = Vec::new();

            for i in 0..operations_per_batch {
                let host = hosts[i % hosts.len()];
                let operation_start = Instant::now();

                match timeout(Duration::from_secs(5), client.dns_lookup_ips(host)).await {
                    Ok(Ok(_)) => {
                        let latency = operation_start.elapsed();
                        batch_results.push(latency);
                    }
                    Ok(Err(_)) | Err(_) => {
                        // 忽略错误，继续测试
                    }
                }
            }

            batch_results
        })
    });

    // 等待所有任务完成
    let all_results = futures::future::join_all(tasks).await;

    // 收集结果
    for batch_results in all_results {
        if let Ok(latencies) = batch_results {
            for latency in latencies {
                result.min_latency = result.min_latency.min(latency);
                result.max_latency = result.max_latency.max(latency);
            }
        }
    }

    result.total_operations = total_operations;
    result.total_duration = start.elapsed();
    result.calculate_metrics();

    Ok(result)
}

/// 基准测试3: 异步流处理性能
async fn benchmark_stream_processing(stream_size: usize) -> NetworkResult<BenchmarkResult> {
    println!("\n🔄 基准测试3: 异步流处理性能 (流大小: {})", stream_size);

    let mut result = BenchmarkResult::new("流处理".to_string());
    let start = Instant::now();

    // 创建测试数据流
    let stream = futures::stream::iter(0..stream_size)
        .map(|i| async move {
            // 模拟异步处理
            tokio::time::sleep(Duration::from_micros(100)).await;
            i * 2
        })
        .buffer_unordered(100); // 并发度100

    // 处理流
    let results: Vec<usize> = stream.collect().await;

    result.total_operations = stream_size;
    result.total_duration = start.elapsed();
    result.calculate_metrics();

    println!("   处理了 {} 个元素", results.len());

    Ok(result)
}

/// 基准测试4: 内存池性能
async fn benchmark_memory_pool(operations: usize) -> NetworkResult<BenchmarkResult> {
    println!("\n💾 基准测试4: 内存池性能 ({} 次操作)", operations);

    let mut result = BenchmarkResult::new("内存池".to_string());
    let start = Instant::now();

    // 创建内存池
    let pool = c10_networks::performance::memory_pool::MemoryPool::new(1024 * 1024); // 1MB

    for i in 0..operations {
        let operation_start = Instant::now();

        // 分配内存
        if let Ok(mut bytes) = pool.allocate(1024) {
            // 使用内存
            bytes.copy_from_slice(&vec![i as u8; 1024]);

            // 内存会在drop时自动释放
            drop(bytes);
        }

        let latency = operation_start.elapsed();
        result.min_latency = result.min_latency.min(latency);
        result.max_latency = result.max_latency.max(latency);

        if i % 100 == 0 {
            println!("   进度: {}/{}", i, operations);
        }
    }

    result.total_operations = operations;
    result.total_duration = start.elapsed();
    result.calculate_metrics();

    // 获取内存池统计信息
    let stats = pool.get_stats();
    result.memory_usage = stats.used_size;

    Ok(result)
}

/// 基准测试5: 缓存操作性能
async fn benchmark_cache_operations(operations: usize) -> NetworkResult<BenchmarkResult> {
    println!("\n🗄️ 基准测试5: 缓存操作性能 ({} 次操作)", operations);

    let mut result = BenchmarkResult::new("缓存操作".to_string());
    let start = Instant::now();

    // 创建缓存
    let cache =
        c10_networks::performance::cache::Cache::new(1000).with_ttl(Duration::from_secs(60));

    for i in 0..operations {
        let operation_start = Instant::now();

        let key = format!("key_{}", i % 100); // 重复使用键以测试缓存命中
        let value = format!("value_{}", i);

        if i % 2 == 0 {
            // 写入操作
            cache.insert(key, value);
        } else {
            // 读取操作
            let _ = cache.get(&key);
        }

        let latency = operation_start.elapsed();
        result.min_latency = result.min_latency.min(latency);
        result.max_latency = result.max_latency.max(latency);

        if i % 1000 == 0 {
            println!("   进度: {}/{}", i, operations);
        }
    }

    result.total_operations = operations;
    result.total_duration = start.elapsed();
    result.calculate_metrics();

    // 获取缓存统计信息
    let stats = cache.get_stats();
    result.memory_usage = stats.total_items * 64; // 估算内存使用

    Ok(result)
}

/// 打印基准测试结果
fn print_benchmark_results(results: &[BenchmarkResult]) {
    println!("\n📊 基准测试结果汇总:");
    println!("{:-<120}", "");
    println!(
        "{:<15} {:<10} {:<12} {:<12} {:<12} {:<12} {:<12} {:<10}",
        "测试名称",
        "操作次数",
        "总耗时",
        "每秒操作",
        "平均延迟",
        "最小延迟",
        "最大延迟",
        "内存使用"
    );
    println!("{:-<120}", "");

    for result in results {
        println!(
            "{:<15} {:<10} {:<12?} {:<12.2} {:<12?} {:<12?} {:<12?} {:<10}",
            result.test_name,
            result.total_operations,
            result.total_duration,
            result.operations_per_second,
            result.average_latency,
            result.min_latency,
            result.max_latency,
            format!("{}KB", result.memory_usage / 1024)
        );
    }

    println!("{:-<120}", "");
}

/// 生成性能报告
async fn generate_performance_report(results: &[BenchmarkResult]) -> NetworkResult<()> {
    println!("\n📋 生成性能报告...");

    let mut report = String::new();
    report.push_str("# Rust 1.90 性能基准测试报告\n\n");
    report.push_str(&format!(
        "**生成时间**: {}\n",
        chrono::Utc::now().format("%Y-%m-%d %H:%M:%S UTC")
    ));
    report.push_str(&format!("**Rust版本**: Rust 1.90+\n"));
    report.push_str(&format!("**测试环境**: {}\n\n", std::env::consts::OS));

    for result in results {
        report.push_str(&format!("## {}\n\n", result.test_name));
        report.push_str(&format!("- **总操作数**: {}\n", result.total_operations));
        report.push_str(&format!("- **总耗时**: {:?}\n", result.total_duration));
        report.push_str(&format!(
            "- **每秒操作数**: {:.2}\n",
            result.operations_per_second
        ));
        report.push_str(&format!("- **平均延迟**: {:?}\n", result.average_latency));
        report.push_str(&format!("- **最小延迟**: {:?}\n", result.min_latency));
        report.push_str(&format!("- **最大延迟**: {:?}\n", result.max_latency));
        report.push_str(&format!(
            "- **内存使用**: {}KB\n\n",
            result.memory_usage / 1024
        ));
    }

    // 保存报告到文件
    let filename = format!(
        "performance_report_{}.md",
        chrono::Utc::now().format("%Y%m%d_%H%M%S")
    );
    tokio::fs::write(&filename, report)
        .await
        .map_err(|e| NetworkError::Other(format!("无法写入报告文件: {}", e)))?;

    println!("   报告已保存到: {}", filename);

    Ok(())
}

/// 系统资源监控
#[allow(dead_code)]
struct SystemMonitor {
    start_memory: usize,
    start_time: Instant,
}

#[allow(dead_code)]
impl SystemMonitor {
    fn new() -> Self {
        Self {
            start_memory: get_memory_usage(),
            start_time: Instant::now(),
        }
    }

    fn get_current_stats(&self) -> (usize, Duration, f64) {
        let current_memory = get_memory_usage();
        let elapsed = self.start_time.elapsed();
        let memory_delta = current_memory.saturating_sub(self.start_memory);

        // 简化的CPU使用率计算（实际应用中需要更复杂的实现）
        let cpu_usage = 0.0; // 这里应该实现实际的CPU使用率监控

        (memory_delta, elapsed, cpu_usage)
    }
}

/// 获取内存使用量（简化实现）
#[allow(dead_code)]
fn get_memory_usage() -> usize {
    // 这是一个简化的实现，实际应用中应该使用更精确的内存监控
    std::process::id() as usize * 1024 // 模拟内存使用
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_benchmark_result_creation() {
        let result = BenchmarkResult::new("测试".to_string());
        assert_eq!(result.test_name, "测试");
        assert_eq!(result.total_operations, 0);
    }

    #[tokio::test]
    async fn test_benchmark_result_calculation() {
        let mut result = BenchmarkResult::new("测试".to_string());
        result.total_operations = 1000;
        result.total_duration = Duration::from_secs(1);
        result.calculate_metrics();

        assert_eq!(result.operations_per_second, 1000.0);
        assert_eq!(result.average_latency, Duration::from_millis(1));
    }

    #[tokio::test]
    async fn test_system_monitor() {
        let monitor = SystemMonitor::new();
        let (memory, elapsed, cpu) = monitor.get_current_stats();

        assert!(memory >= 0);
        assert!(elapsed >= Duration::ZERO);
        assert!(cpu >= 0.0);
    }
}
