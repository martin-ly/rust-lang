use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::sleep;
use tracing::{info, warn};

/// 2025年简化异步性能基准测试套件
/// 展示实用的异步性能测试和基准测试最佳实践

/// 1. 简化基准测试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimpleBenchmarkConfig {
    pub name: String,
    pub iterations: usize,
    pub warmup_iterations: usize,
    pub timeout: Duration,
}

impl Default for SimpleBenchmarkConfig {
    fn default() -> Self {
        Self {
            name: "default_benchmark".to_string(),
            iterations: 100,
            warmup_iterations: 10,
            timeout: Duration::from_secs(30),
        }
    }
}

/// 2. 简化基准测试结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SimpleBenchmarkResult {
    pub name: String,
    pub total_iterations: usize,
    pub successful_iterations: usize,
    pub failed_iterations: usize,
    pub total_duration: Duration,
    pub min_duration: Duration,
    pub max_duration: Duration,
    pub avg_duration: Duration,
    pub throughput_ops_per_sec: f64,
}

impl SimpleBenchmarkResult {
    pub fn new(name: String, total_iterations: usize) -> Self {
        Self {
            name,
            total_iterations,
            successful_iterations: 0,
            failed_iterations: 0,
            total_duration: Duration::ZERO,
            min_duration: Duration::MAX,
            max_duration: Duration::ZERO,
            avg_duration: Duration::ZERO,
            throughput_ops_per_sec: 0.0,
        }
    }
}

/// 3. 简化异步基准测试运行器
pub struct SimpleAsyncBenchmarkRunner {
    config: SimpleBenchmarkConfig,
    results: Arc<RwLock<Vec<SimpleBenchmarkResult>>>,
}

impl SimpleAsyncBenchmarkRunner {
    pub fn new(config: SimpleBenchmarkConfig) -> Self {
        Self {
            config,
            results: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn run_benchmark<F, Fut>(
        &self,
        benchmark_name: &str,
        operation: F,
    ) -> Result<SimpleBenchmarkResult>
    where
        F: Fn() -> Fut + Send + Sync,
        Fut: std::future::Future<Output = Result<()>> + Send,
    {
        let mut result =
            SimpleBenchmarkResult::new(benchmark_name.to_string(), self.config.iterations);
        let mut durations = Vec::with_capacity(self.config.iterations);

        info!(
            "🚀 开始基准测试: {} ({} 次迭代)",
            benchmark_name, self.config.iterations
        );

        // 预热阶段
        if self.config.warmup_iterations > 0 {
            println!("🔥 预热阶段: {} 次迭代", self.config.warmup_iterations);
            info!("🔥 预热阶段: {} 次迭代", self.config.warmup_iterations);
            for i in 0..self.config.warmup_iterations {
                println!("预热迭代 {}/{}", i + 1, self.config.warmup_iterations);
                let _ = operation().await;
            }
            println!("预热阶段完成");
        }

        // 主测试阶段
        println!("🚀 开始主测试阶段: {} 次迭代", self.config.iterations);
        let start_time = Instant::now();

        for i in 0..self.config.iterations {
            if i % 10 == 0 {
                println!("主测试迭代 {}/{}", i + 1, self.config.iterations);
            }
            let iteration_start = Instant::now();
            println!("开始迭代 {} 操作", i + 1);

            match operation().await {
                Ok(_) => {
                    result.successful_iterations += 1;
                    println!("迭代 {} 成功", i + 1);
                }
                Err(_) => {
                    result.failed_iterations += 1;
                    warn!("基准测试 {} 迭代 {} 失败", benchmark_name, i);
                    println!("迭代 {} 失败", i + 1);
                }
            }

            let duration = iteration_start.elapsed();
            durations.push(duration);

            // 更新最小和最大持续时间
            if duration < result.min_duration {
                result.min_duration = duration;
            }
            if duration > result.max_duration {
                result.max_duration = duration;
            }
        }

        result.total_duration = start_time.elapsed();

        // 计算统计信息
        if !durations.is_empty() {
            let total_nanos: u64 = durations.iter().map(|d| d.as_nanos() as u64).sum();
            result.avg_duration = Duration::from_nanos(total_nanos / durations.len() as u64);
        }

        // 计算吞吐量
        result.throughput_ops_per_sec =
            result.successful_iterations as f64 / result.total_duration.as_secs_f64();

        info!("📊 基准测试 {} 完成", benchmark_name);
        info!(
            "   成功: {}, 失败: {}, 总耗时: {:?}",
            result.successful_iterations, result.failed_iterations, result.total_duration
        );
        info!(
            "   平均耗时: {:?}, 吞吐量: {:.2} ops/sec",
            result.avg_duration, result.throughput_ops_per_sec
        );

        // 保存结果
        self.results.write().await.push(result.clone());

        Ok(result)
    }

    pub async fn get_results(&self) -> Vec<SimpleBenchmarkResult> {
        self.results.read().await.clone()
    }
}

/// 4. 简化异步并发基准测试
pub struct SimpleAsyncConcurrencyBenchmark {
    semaphore: Arc<Semaphore>,
    success_count: Arc<AtomicUsize>,
    failure_count: Arc<AtomicUsize>,
}

impl SimpleAsyncConcurrencyBenchmark {
    pub fn new(max_concurrency: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrency)),
            success_count: Arc::new(AtomicUsize::new(0)),
            failure_count: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub async fn run_concurrent_benchmark(
        &self,
        iterations: usize,
    ) -> Result<SimpleBenchmarkResult> {
        let start_time = Instant::now();
        let mut handles = Vec::new();

        for _i in 0..iterations {
            let semaphore = self.semaphore.clone();
            let success_count = self.success_count.clone();
            let failure_count = self.failure_count.clone();

            let handle = tokio::spawn(async move {
                let _permit = semaphore.acquire().await.unwrap();

                // 模拟异步操作
                sleep(Duration::from_millis(5)).await;

                // 模拟偶尔失败
                let random_val = (std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
                    % 100) as f64
                    / 100.0;
                if random_val < 0.02 {
                    failure_count.fetch_add(1, Ordering::Relaxed);
                } else {
                    success_count.fetch_add(1, Ordering::Relaxed);
                }
            });

            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            let _ = handle.await;
        }

        let total_time = start_time.elapsed();
        let successful = self.success_count.load(Ordering::Relaxed);
        let failed = self.failure_count.load(Ordering::Relaxed);

        let mut result = SimpleBenchmarkResult::new("concurrent_benchmark".to_string(), iterations);
        result.successful_iterations = successful;
        result.failed_iterations = failed;
        result.total_duration = total_time;
        result.throughput_ops_per_sec = successful as f64 / total_time.as_secs_f64();

        Ok(result)
    }
}

/// 5. 简化异步内存基准测试
pub struct SimpleAsyncMemoryBenchmark {
    allocations: Arc<AtomicUsize>,
    total_bytes: Arc<AtomicU64>,
}

impl SimpleAsyncMemoryBenchmark {
    pub fn new() -> Self {
        Self {
            allocations: Arc::new(AtomicUsize::new(0)),
            total_bytes: Arc::new(AtomicU64::new(0)),
        }
    }

    pub async fn measure_memory_usage(&self) -> Result<u64> {
        let before_allocations = self.allocations.load(Ordering::Relaxed);
        let before_bytes = self.total_bytes.load(Ordering::Relaxed);

        // 模拟内存分配操作
        let mut data = Vec::with_capacity(1024);
        for i in 0..1024 {
            data.push(i as u8);
        }

        let after_allocations = self.allocations.load(Ordering::Relaxed);
        let after_bytes = self.total_bytes.load(Ordering::Relaxed);

        let memory_used = after_bytes - before_bytes;
        let allocations_made = after_allocations - before_allocations;

        info!(
            "内存使用: {} 字节, 分配次数: {}",
            memory_used, allocations_made
        );

        Ok(memory_used)
    }

    pub fn track_allocation(&self, size: usize) {
        self.allocations.fetch_add(1, Ordering::Relaxed);
        self.total_bytes.fetch_add(size as u64, Ordering::Relaxed);
    }
}

/// 6. 简化异步网络基准测试
pub struct SimpleAsyncNetworkBenchmark {
    request_count: Arc<AtomicUsize>,
    response_times: Arc<RwLock<Vec<Duration>>>,
}

impl SimpleAsyncNetworkBenchmark {
    pub fn new() -> Self {
        Self {
            request_count: Arc::new(AtomicUsize::new(0)),
            response_times: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn measure_network_latency(&self, request_id: usize) -> Result<Duration> {
        let start_time = Instant::now();
        let _request_id = self.request_count.fetch_add(1, Ordering::Relaxed);

        // 模拟网络延迟
        sleep(Duration::from_millis(20 + (request_id * 5) as u64)).await;

        let latency = start_time.elapsed();
        self.response_times.write().await.push(latency);
        info!("请求 {} 延迟: {:?}", request_id, latency);

        Ok(latency)
    }

    pub async fn get_average_latency(&self) -> Duration {
        let response_times = self.response_times.read().await;
        if response_times.is_empty() {
            Duration::ZERO
        } else {
            let total_nanos: u64 = response_times.iter().map(|d| d.as_nanos() as u64).sum();
            Duration::from_nanos(total_nanos / response_times.len() as u64)
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    println!("🚀 开始 2025 年简化异步性能基准测试套件演示");
    info!("🚀 开始 2025 年简化异步性能基准测试套件演示");

    // 1. 演示基本异步基准测试
    println!("⚡ 演示基本异步基准测试");
    info!("⚡ 演示基本异步基准测试");
    let config = SimpleBenchmarkConfig {
        name: "async_operation_benchmark".to_string(),
        iterations: 10,
        warmup_iterations: 2,
        timeout: Duration::from_secs(10),
    };

    let benchmark_runner = SimpleAsyncBenchmarkRunner::new(config);
    println!("基准测试运行器已创建");

    // 模拟异步操作
    println!("开始运行基准测试");
    let result = benchmark_runner
        .run_benchmark("async_operation", || async {
            // 模拟一些异步工作
            sleep(Duration::from_millis(1)).await;

            // 简化的操作，总是成功
            Ok(())
        })
        .await?;

    info!("📊 基准测试结果:");
    info!("   总迭代: {}", result.total_iterations);
    info!(
        "   成功: {}, 失败: {}",
        result.successful_iterations, result.failed_iterations
    );
    info!("   平均耗时: {:?}", result.avg_duration);
    info!("   吞吐量: {:.2} ops/sec", result.throughput_ops_per_sec);

    // 2. 演示并发基准测试
    info!("🔄 演示异步并发基准测试");
    let concurrency_benchmark = SimpleAsyncConcurrencyBenchmark::new(5);

    let concurrent_result = concurrency_benchmark.run_concurrent_benchmark(5).await?;

    info!("📊 并发基准测试结果:");
    info!(
        "   成功: {}, 失败: {}",
        concurrent_result.successful_iterations, concurrent_result.failed_iterations
    );
    info!(
        "   吞吐量: {:.2} ops/sec",
        concurrent_result.throughput_ops_per_sec
    );

    // 3. 演示内存基准测试
    info!("💾 演示异步内存基准测试");
    let memory_benchmark = SimpleAsyncMemoryBenchmark::new();

    let memory_usage = memory_benchmark.measure_memory_usage().await?;

    info!("📊 内存使用: {} 字节", memory_usage);

    // 4. 演示网络基准测试
    info!("🌐 演示异步网络基准测试");
    let network_benchmark = SimpleAsyncNetworkBenchmark::new();

    // 模拟网络请求
    for i in 0..3 {
        let latency = network_benchmark.measure_network_latency(i).await?;
        info!("网络请求 {} 延迟: {:?}", i, latency);
    }

    let avg_latency = network_benchmark.get_average_latency().await;
    info!("📊 平均网络延迟: {:?}", avg_latency);

    // 5. 获取所有基准测试结果
    let all_results = benchmark_runner.get_results().await;

    info!("📈 基准测试汇总:");
    info!("   总基准测试数: {}", all_results.len());

    for result in &all_results {
        info!(
            "   {}: {:.2} ops/sec",
            result.name, result.throughput_ops_per_sec
        );
    }

    info!("✅ 2025 年简化异步性能基准测试套件演示完成!");

    Ok(())
}
