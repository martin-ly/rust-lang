use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::{sleep, timeout};
use tracing::{error, info, warn};

/// 2025年异步性能基准测试套件
/// 展示最新的异步性能测试和基准测试最佳实践

/// 1. 异步基准测试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkConfig {
    pub name: String,
    pub iterations: usize,
    pub warmup_iterations: usize,
    pub timeout: Duration,
    pub concurrency: usize,
    pub batch_size: usize,
}

impl Default for BenchmarkConfig {
    fn default() -> Self {
        Self {
            name: "default_benchmark".to_string(),
            iterations: 1000,
            warmup_iterations: 100,
            timeout: Duration::from_secs(30),
            concurrency: 10,
            batch_size: 100,
        }
    }
}

/// 2. 异步基准测试结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResult {
    pub name: String,
    pub total_iterations: usize,
    pub successful_iterations: usize,
    pub failed_iterations: usize,
    pub total_duration: Duration,
    pub min_duration: Duration,
    pub max_duration: Duration,
    pub avg_duration: Duration,
    pub p50_duration: Duration,
    pub p95_duration: Duration,
    pub p99_duration: Duration,
    pub throughput_ops_per_sec: f64,
    pub memory_usage_bytes: u64,
    pub cpu_usage_percent: f64,
}

impl BenchmarkResult {
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
            p50_duration: Duration::ZERO,
            p95_duration: Duration::ZERO,
            p99_duration: Duration::ZERO,
            throughput_ops_per_sec: 0.0,
            memory_usage_bytes: 0,
            cpu_usage_percent: 0.0,
        }
    }
}

/// 3. 异步基准测试运行器
pub struct AsyncBenchmarkRunner {
    config: BenchmarkConfig,
    results: Arc<RwLock<Vec<BenchmarkResult>>>,
    metrics: Arc<RwLock<BenchmarkMetrics>>,
}

#[derive(Debug, Clone, Default)]
pub struct BenchmarkMetrics {
    pub total_benchmarks: usize,
    pub completed_benchmarks: usize,
    pub failed_benchmarks: usize,
    pub total_execution_time: Duration,
}

impl AsyncBenchmarkRunner {
    pub fn new(config: BenchmarkConfig) -> Self {
        Self {
            config,
            results: Arc::new(RwLock::new(Vec::new())),
            metrics: Arc::new(RwLock::new(BenchmarkMetrics::default())),
        }
    }

    pub async fn run_benchmark<F, Fut>(
        &self,
        benchmark_name: &str,
        operation: F,
    ) -> Result<BenchmarkResult>
    where
        F: Fn() -> Fut + Send + Sync,
        Fut: std::future::Future<Output = Result<()>> + Send,
    {
        let mut result = BenchmarkResult::new(benchmark_name.to_string(), self.config.iterations);
        let mut durations = Vec::with_capacity(self.config.iterations);

        info!(
            "🚀 开始基准测试: {} ({} 次迭代)",
            benchmark_name, self.config.iterations
        );

        // 预热阶段
        if self.config.warmup_iterations > 0 {
            info!("🔥 预热阶段: {} 次迭代", self.config.warmup_iterations);
            for _ in 0..self.config.warmup_iterations {
                let _ = operation().await;
            }
        }

        // 主测试阶段
        let start_time = Instant::now();

        for i in 0..self.config.iterations {
            let iteration_start = Instant::now();

            match timeout(self.config.timeout, operation()).await {
                Ok(Ok(_)) => {
                    result.successful_iterations += 1;
                }
                Ok(Err(_)) => {
                    result.failed_iterations += 1;
                    warn!("基准测试 {} 迭代 {} 失败", benchmark_name, i);
                }
                Err(_) => {
                    result.failed_iterations += 1;
                    warn!("基准测试 {} 迭代 {} 超时", benchmark_name, i);
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
            durations.sort();

            let total_nanos: u64 = durations.iter().map(|d| d.as_nanos() as u64).sum();
            result.avg_duration = Duration::from_nanos(total_nanos / durations.len() as u64);

            result.p50_duration = durations[durations.len() * 50 / 100];
            result.p95_duration = durations[durations.len() * 95 / 100];
            result.p99_duration = durations[durations.len() * 99 / 100];
        }

        // 计算吞吐量
        result.throughput_ops_per_sec =
            result.successful_iterations as f64 / result.total_duration.as_secs_f64();

        // 估算内存使用（简化版本）
        result.memory_usage_bytes =
            std::mem::size_of::<BenchmarkResult>() as u64 * result.successful_iterations as u64;

        // 估算CPU使用率（简化版本）
        result.cpu_usage_percent =
            (result.total_duration.as_secs_f64() / result.total_duration.as_secs_f64()) * 100.0;

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
        self.update_metrics().await;

        Ok(result)
    }

    async fn update_metrics(&self) {
        let mut metrics = self.metrics.write().await;
        metrics.completed_benchmarks += 1;
    }

    pub async fn get_results(&self) -> Vec<BenchmarkResult> {
        self.results.read().await.clone()
    }

    pub async fn get_metrics(&self) -> BenchmarkMetrics {
        self.metrics.read().await.clone()
    }
}

/// 4. 异步并发基准测试
pub struct AsyncConcurrencyBenchmark {
    semaphore: Arc<Semaphore>,
    success_count: Arc<AtomicUsize>,
    failure_count: Arc<AtomicUsize>,
    total_duration: Arc<AtomicU64>,
}

impl AsyncConcurrencyBenchmark {
    pub fn new(max_concurrency: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrency)),
            success_count: Arc::new(AtomicUsize::new(0)),
            failure_count: Arc::new(AtomicUsize::new(0)),
            total_duration: Arc::new(AtomicU64::new(0)),
        }
    }

    pub async fn run_concurrent_benchmark<F, Fut>(
        &self,
        operation: F,
        iterations: usize,
    ) -> Result<BenchmarkResult>
    where
        F: Fn() -> Fut + Send + Sync + Clone + 'static,
        Fut: std::future::Future<Output = Result<()>> + Send,
    {
        let start_time = Instant::now();
        let mut handles = Vec::new();

        for _i in 0..iterations {
            let semaphore = self.semaphore.clone();
            let success_count = self.success_count.clone();
            let failure_count = self.failure_count.clone();
            let total_duration = self.total_duration.clone();
            let operation_clone = operation.clone();

            let handle = tokio::spawn(async move {
                let _permit = semaphore.acquire().await.unwrap();
                let iteration_start = Instant::now();

                match operation_clone().await {
                    Ok(_) => {
                        success_count.fetch_add(1, Ordering::Relaxed);
                    }
                    Err(_) => {
                        failure_count.fetch_add(1, Ordering::Relaxed);
                    }
                }

                let duration = iteration_start.elapsed();
                total_duration.fetch_add(duration.as_nanos() as u64, Ordering::Relaxed);
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
        let total_duration_nanos = self.total_duration.load(Ordering::Relaxed);

        let mut result = BenchmarkResult::new("concurrent_benchmark".to_string(), iterations);
        result.successful_iterations = successful;
        result.failed_iterations = failed;
        result.total_duration = total_time;
        result.avg_duration = Duration::from_nanos(total_duration_nanos / iterations as u64);
        result.throughput_ops_per_sec = successful as f64 / total_time.as_secs_f64();

        Ok(result)
    }
}

/// 5. 异步内存基准测试
pub struct AsyncMemoryBenchmark {
    allocations: Arc<AtomicUsize>,
    total_bytes: Arc<AtomicU64>,
}

impl AsyncMemoryBenchmark {
    pub fn new() -> Self {
        Self {
            allocations: Arc::new(AtomicUsize::new(0)),
            total_bytes: Arc::new(AtomicU64::new(0)),
        }
    }

    pub async fn measure_memory_usage<F, Fut>(&self, operation: F) -> Result<u64>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<Vec<u8>>>,
    {
        let before_allocations = self.allocations.load(Ordering::Relaxed);
        let before_bytes = self.total_bytes.load(Ordering::Relaxed);

        let _result = operation().await?;

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

/// 6. 异步网络基准测试
pub struct AsyncNetworkBenchmark {
    request_count: Arc<AtomicUsize>,
    response_times: Arc<RwLock<Vec<Duration>>>,
}

impl AsyncNetworkBenchmark {
    pub fn new() -> Self {
        Self {
            request_count: Arc::new(AtomicUsize::new(0)),
            response_times: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn measure_network_latency<F, Fut>(&self, operation: F) -> Result<Duration>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<String>>,
    {
        let start_time = Instant::now();
        let request_id = self.request_count.fetch_add(1, Ordering::Relaxed);

        match operation().await {
            Ok(_response) => {
                let latency = start_time.elapsed();
                self.response_times.write().await.push(latency);
                info!("请求 {} 延迟: {:?}", request_id, latency);
                Ok(latency)
            }
            Err(e) => {
                error!("请求 {} 失败: {:?}", request_id, e);
                Err(e)
            }
        }
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

    info!("🚀 开始 2025 年异步性能基准测试套件演示");

    // 1. 演示基本异步基准测试
    info!("⚡ 演示基本异步基准测试");
    let config = BenchmarkConfig {
        name: "async_operation_benchmark".to_string(),
        iterations: 500,
        warmup_iterations: 50,
        timeout: Duration::from_secs(10),
        concurrency: 5,
        batch_size: 50,
    };

    let benchmark_runner = AsyncBenchmarkRunner::new(config);

    // 模拟异步操作
    let result = benchmark_runner
        .run_benchmark("async_operation", || async {
            // 模拟一些异步工作
            sleep(Duration::from_millis(10)).await;

            // 模拟偶尔失败（使用简单的伪随机）
            let random_val = (Instant::now().elapsed().as_nanos() % 100) as f64 / 100.0;
            if random_val < 0.05 {
                Err(anyhow::anyhow!("模拟操作失败"))
            } else {
                Ok(())
            }
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
    let concurrency_benchmark = AsyncConcurrencyBenchmark::new(10);

    let concurrent_result = concurrency_benchmark
        .run_concurrent_benchmark(
            || async {
                // 模拟并发异步操作
                sleep(Duration::from_millis(5)).await;

                let random_val = (Instant::now().elapsed().as_nanos() % 100) as f64 / 100.0;
                if random_val < 0.02 {
                    Err(anyhow::anyhow!("并发操作失败"))
                } else {
                    Ok(())
                }
            },
            200,
        )
        .await?;

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
    let memory_benchmark = AsyncMemoryBenchmark::new();

    let memory_usage = memory_benchmark
        .measure_memory_usage(|| async {
            // 模拟内存分配操作
            let mut data = Vec::with_capacity(1024);
            for i in 0..1024 {
                data.push(i as u8);
            }
            Ok(data)
        })
        .await?;

    info!("📊 内存使用: {} 字节", memory_usage);

    // 4. 演示网络基准测试
    info!("🌐 演示异步网络基准测试");
    let network_benchmark = AsyncNetworkBenchmark::new();

    // 模拟网络请求
    for i in 0..10 {
        let latency = network_benchmark
            .measure_network_latency(|| async {
                // 模拟网络延迟
                sleep(Duration::from_millis(20 + (i * 5) as u64)).await;
                Ok(format!("响应 {}", i))
            })
            .await?;

        info!("网络请求 {} 延迟: {:?}", i, latency);
    }

    let avg_latency = network_benchmark.get_average_latency().await;
    info!("📊 平均网络延迟: {:?}", avg_latency);

    // 5. 获取所有基准测试结果
    let all_results = benchmark_runner.get_results().await;
    let metrics = benchmark_runner.get_metrics().await;

    info!("📈 基准测试汇总:");
    info!("   完成的基准测试: {}", metrics.completed_benchmarks);
    info!("   总基准测试数: {}", all_results.len());

    for result in &all_results {
        info!(
            "   {}: {:.2} ops/sec",
            result.name, result.throughput_ops_per_sec
        );
    }

    info!("✅ 2025 年异步性能基准测试套件演示完成!");

    Ok(())
}
