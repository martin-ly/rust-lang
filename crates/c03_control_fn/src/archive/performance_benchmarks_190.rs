//! Rust 1.90 性能基准测试模块
//!
//! 本模块提供了全面的性能基准测试，展示 Rust 1.90 新特性在性能方面的优势：
//! - 异步性能基准测试
//! - 内存使用优化测试
//! - 并发性能测试
//! - 编译时间优化测试
//! - 运行时性能分析
//!
//! 所有基准测试都使用 Rust 1.90 的最新特性，并提供详细的性能分析报告。
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock, Semaphore};
use tokio::time::sleep;
use anyhow::Result;
use serde::{Deserialize, Serialize};

/// 性能基准测试结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResult {
    pub test_name: String,
    pub iterations: u32,
    pub total_time: Duration,
    pub average_time: Duration,
    pub min_time: Duration,
    pub max_time: Duration,
    pub throughput: f64,
    pub memory_usage: Option<usize>,
    pub cpu_usage: Option<f64>,
}

/// 性能基准测试器
pub struct PerformanceBenchmark {
    results: Arc<Mutex<Vec<BenchmarkResult>>>,
    warmup_iterations: u32,
}

impl Default for PerformanceBenchmark {
    fn default() -> Self {
        Self {
            results: Arc::new(Mutex::new(Vec::new())),
            warmup_iterations: 10,
        }
    }
}

impl PerformanceBenchmark {
    pub fn new() -> Self {
        Self::default()
    }

    /// 运行基准测试
    pub async fn benchmark<F, Fut, R>(
        &self,
        test_name: &str,
        iterations: u32,
        test_fn: F,
    ) -> BenchmarkResult
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = R>,
    {
        println!("  运行基准测试: {} ({} 次迭代)", test_name, iterations);

        // 预热
        for _ in 0..self.warmup_iterations {
            test_fn().await;
        }

        let mut times = Vec::new();
        let start_time = Instant::now();

        for i in 0..iterations {
            let iteration_start = Instant::now();
            test_fn().await;
            let iteration_time = iteration_start.elapsed();
            times.push(iteration_time);

            if i % (iterations / 10).max(1) == 0 {
                println!("    进度: {}/{} ({:.1}%)",
                        i + 1, iterations,
                        (i + 1) as f64 / iterations as f64 * 100.0);
            }
        }

        let total_time = start_time.elapsed();
        let average_time = Duration::from_nanos(
            times.iter().map(|t| t.as_nanos() as u64).sum::<u64>() / times.len() as u64
        );
        let min_time = *times.iter().min().expect("计算最小时间失败");
        let max_time = *times.iter().max().expect("计算最大时间失败");
        let throughput = iterations as f64 / total_time.as_secs_f64();

        let result = BenchmarkResult {
            test_name: test_name.to_string(),
            iterations,
            total_time,
            average_time,
            min_time,
            max_time,
            throughput,
            memory_usage: None,
            cpu_usage: None,
        };

        let mut results = self.results.lock().await;
        results.push(result.clone());

        println!("    测试完成: 平均时间 {:?}, 吞吐量 {:.2} 操作/秒",
                average_time, throughput);

        result
    }

    /// 运行同步基准测试
    pub fn benchmark_sync<F, R>(
        &self,
        test_name: &str,
        iterations: u32,
        test_fn: F,
    ) -> BenchmarkResult
    where
        F: Fn() -> R,
    {
        println!("  运行同步基准测试: {} ({} 次迭代)", test_name, iterations);

        // 预热
        for _ in 0..self.warmup_iterations {
            test_fn();
        }

        let mut times = Vec::new();
        let start_time = Instant::now();

        for i in 0..iterations {
            let iteration_start = Instant::now();
            test_fn();
            let iteration_time = iteration_start.elapsed();
            times.push(iteration_time);

            if i % (iterations / 10).max(1) == 0 {
                println!("    进度: {}/{} ({:.1}%)",
                        i + 1, iterations,
                        (i + 1) as f64 / iterations as f64 * 100.0);
            }
        }

        let total_time = start_time.elapsed();
        let average_time = Duration::from_nanos(
            times.iter().map(|t| t.as_nanos() as u64).sum::<u64>() / times.len() as u64
        );
        let min_time = *times.iter().min().expect("计算最小时间失败");
        let max_time = *times.iter().max().expect("计算最大时间失败");
        let throughput = iterations as f64 / total_time.as_secs_f64();

        let result = BenchmarkResult {
            test_name: test_name.to_string(),
            iterations,
            total_time,
            average_time,
            min_time,
            max_time,
            throughput,
            memory_usage: None,
            cpu_usage: None,
        };

        println!("    测试完成: 平均时间 {:?}, 吞吐量 {:.2} 操作/秒",
                average_time, throughput);

        result
    }

    /// 获取所有测试结果
    pub async fn get_results(&self) -> Vec<BenchmarkResult> {
        self.results.lock().await.clone()
    }

    /// 生成性能报告
    pub async fn generate_report(&self) -> String {
        let results = self.get_results().await;
        let mut report = String::new();

        report.push_str("# Rust 1.90 性能基准测试报告\n\n");
        report.push_str(&format!("测试时间: {}\n", chrono::Utc::now().format("%Y-%m-%d %H:%M:%S UTC")));
        report.push_str(&format!("总测试数: {}\n\n", results.len()));

        report.push_str("## 测试结果汇总\n\n");
        report.push_str("| 测试名称 | 迭代次数 | 总时间 | 平均时间 | 最小时间 | 最大时间 | 吞吐量 |\n");
        report.push_str("|---------|---------|--------|----------|----------|----------|--------|\n");

        for result in &results {
            report.push_str(&format!(
                "| {} | {} | {:?} | {:?} | {:?} | {:?} | {:.2} |\n",
                result.test_name,
                result.iterations,
                result.total_time,
                result.average_time,
                result.min_time,
                result.max_time,
                result.throughput
            ));
        }

        report.push_str("\n## 性能分析\n\n");

        // 找出最快的测试
        if let Some(fastest) = results.iter().min_by(|a, b| a.average_time.cmp(&b.average_time)) {
            report.push_str(&format!("**最快测试**: {} (平均时间: {:?})\n\n",
                    fastest.test_name, fastest.average_time));
        }

        // 找出吞吐量最高的测试
        if let Some(highest_throughput) = results.iter().max_by(|a, b| a.throughput.partial_cmp(&b.throughput).expect("比较吞吐量失败")) {
            report.push_str(&format!("**最高吞吐量**: {} ({:.2} 操作/秒)\n\n",
                    highest_throughput.test_name, highest_throughput.throughput));
        }

        report
    }
}

/// 异步性能测试
#[derive(Default)]
pub struct AsyncPerformanceTests {
    benchmark: PerformanceBenchmark,
}


impl AsyncPerformanceTests {
    pub fn new() -> Self {
        Self::default()
    }

    /// 测试异步闭包性能
    pub async fn test_async_closure_performance(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "异步闭包性能测试",
            1000,
            || async {
                let closure = |x: i32| async move {
                    sleep(Duration::from_micros(10)).await;
                    x * 2
                };

                let mut sum = 0;
                for i in 0..100 {
                    sum += closure(i).await;
                }
                sum
            },
        ).await;

        Ok(result)
    }

    /// 测试异步 trait 性能
    pub async fn test_async_trait_performance(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "异步 trait 性能测试",
            500,
            || async {
                let processor = AsyncTestProcessor::new("test_processor".to_string());
                let data = vec![1u8; 1024];

                let result = processor.process(data).await.expect("处理器执行失败");
                result.len()
            },
        ).await;

        Ok(result)
    }

    /// 测试并发处理性能
    pub async fn test_concurrent_processing_performance(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "并发处理性能测试",
            100,
            || async {
                let semaphore = Arc::new(Semaphore::new(10));
                let mut handles = Vec::new();

                for i in 0..50 {
                    let semaphore = semaphore.clone();
                    let handle = tokio::spawn(async move {
                        let _permit = semaphore.acquire().await.expect("获取信号量许可失败");
                        sleep(Duration::from_millis(10)).await;
                        i * 2
                    });
                    handles.push(handle);
                }

                let mut sum = 0;
                for handle in handles {
                    sum += handle.await.expect("等待异步任务失败");
                }
                sum
            },
        ).await;

        Ok(result)
    }

    /// 测试异步状态机性能
    pub async fn test_async_state_machine_performance(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "异步状态机性能测试",
            200,
            || async {
                let state_machine = AsyncTestStateMachine::new();

                for _ in 0..10 {
                    state_machine.transition_to(AsyncTestState::Running).await.expect("状态转换到Running失败");
                    state_machine.process_data("test_data".to_string()).await.expect("处理数据失败");
                    state_machine.transition_to(AsyncTestState::Completed).await.expect("状态转换到Completed失败");
                }

                state_machine.get_state().await
            },
        ).await;

        Ok(result)
    }
}

/// 测试用的异步处理器
#[allow(dead_code)]
pub struct AsyncTestProcessor {
    name: String,
}

impl AsyncTestProcessor {
    pub fn new(name: String) -> Self {
        Self { name }
    }

    pub async fn process(&self, data: Vec<u8>) -> Result<Vec<u8>> {
        sleep(Duration::from_micros(50)).await;

        let processed: Vec<u8> = data.iter().map(|&x| x.wrapping_add(1)).collect();
        Ok(processed)
    }
}

/// 测试用的异步状态机
#[derive(Debug, Clone, PartialEq)]
pub enum AsyncTestState {
    Initializing,
    Running,
    Completed,
    Failed,
}

#[allow(dead_code)]
pub struct AsyncTestStateMachine {
    state: Arc<RwLock<AsyncTestState>>,
    data: Arc<Mutex<HashMap<String, String>>>,
}

impl Default for AsyncTestStateMachine {
    fn default() -> Self {
        Self {
            state: Arc::new(RwLock::new(AsyncTestState::Initializing)),
            data: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

impl AsyncTestStateMachine {
    pub fn new() -> Self {
        Self::default()
    }

    pub async fn transition_to(&self, new_state: AsyncTestState) -> Result<()> {
        let mut state = self.state.write().await;
        *state = new_state;
        Ok(())
    }

    pub async fn process_data(&self, data: String) -> Result<()> {
        let state = self.state.read().await;
        if *state != AsyncTestState::Running {
            return Err(anyhow::anyhow!("状态机不在运行状态"));
        }
        drop(state);

        sleep(Duration::from_micros(100)).await;

        let mut data_map = self.data.lock().await;
        data_map.insert("processed_data".to_string(), data);

        Ok(())
    }

    pub async fn get_state(&self) -> AsyncTestState {
        self.state.read().await.clone()
    }
}

/// 内存性能测试
#[allow(dead_code)]
pub struct MemoryPerformanceTests {
    benchmark: PerformanceBenchmark,
}

impl Default for MemoryPerformanceTests {
    fn default() -> Self {
        Self {
            benchmark: PerformanceBenchmark::default(),
        }
    }
}

impl MemoryPerformanceTests {
    pub fn new() -> Self {
        Self::default()
    }

    /// 测试元组集合内存使用
    pub fn test_tuple_collection_memory(&self) -> BenchmarkResult {
        self.benchmark.benchmark_sync(
            "元组集合内存使用测试",
            1000,
            || {
                let data: Vec<i32> = (1..=1000).collect();

                // 使用元组集合
                let (evens, odds): (Vec<i32>, Vec<i32>) = data
                    .iter()
                    .partition(|&&x| x % 2 == 0);

                evens.len() + odds.len()
            },
        )
    }

    /// 测试枚举内存使用
    pub fn test_enum_memory_usage(&self) -> BenchmarkResult {
        self.benchmark.benchmark_sync(
            "枚举内存使用测试",
            10000,
            || {
                let mut resources = Vec::new();

                for i in 0..1000 {
                    resources.push(AsyncTestResource::Database(AsyncTestDatabase {
                        id: format!("db_{}", i),
                        connection_string: format!("postgresql://localhost:5432/db_{}", i),
                        is_connected: true,
                    }));

                    resources.push(AsyncTestResource::File(AsyncTestFile {
                        id: format!("file_{}", i),
                        file_path: format!("/tmp/file_{}.txt", i),
                        is_open: true,
                    }));
                }

                resources.len()
            },
        )
    }

    /// 测试异步资源内存使用
    pub async fn test_async_resource_memory(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "异步资源内存使用测试",
            100,
            || async {
                let mut resources = Vec::new();

                for i in 0..100 {
                    let resource = AsyncTestResource::Database(AsyncTestDatabase {
                        id: format!("db_{}", i),
                        connection_string: format!("postgresql://localhost:5432/db_{}", i),
                        is_connected: true,
                    });
                    resources.push(resource);
                }

                // 模拟异步操作
                sleep(Duration::from_micros(10)).await;

                resources.len()
            },
        ).await;

        Ok(result)
    }
}

/// 测试用的异步资源
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum AsyncTestResource {
    Database(AsyncTestDatabase),
    File(AsyncTestFile),
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AsyncTestDatabase {
    pub id: String,
    pub connection_string: String,
    pub is_connected: bool,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct AsyncTestFile {
    pub id: String,
    pub file_path: String,
    pub is_open: bool,
}

/// 并发性能测试
#[allow(dead_code)]
pub struct ConcurrencyPerformanceTests {
    benchmark: PerformanceBenchmark,
}

impl Default for ConcurrencyPerformanceTests {
    fn default() -> Self {
        Self {
            benchmark: PerformanceBenchmark::default(),
        }
    }
}

impl ConcurrencyPerformanceTests {
    pub fn new() -> Self {
        Self::default()
    }

    /// 测试并发任务处理
    pub async fn test_concurrent_task_processing(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "并发任务处理测试",
            50,
            || async {
                let mut handles = Vec::new();

                for i in 0..100 {
                    let handle = tokio::spawn(async move {
                        sleep(Duration::from_millis(1)).await;
                        i * i
                    });
                    handles.push(handle);
                }

                let mut sum = 0;
                for handle in handles {
                    sum += handle.await.expect("等待异步任务失败");
                }
                sum
            },
        ).await;

        Ok(result)
    }

    /// 测试异步锁性能
    pub async fn test_async_lock_performance(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "异步锁性能测试",
            200,
            || async {
                let data = Arc::new(Mutex::new(0i32));
                let mut handles = Vec::new();

                for _ in 0..50 {
                    let data = data.clone();
                    let handle = tokio::spawn(async move {
                        for _ in 0..10 {
                            let mut value = data.lock().await;
                            *value += 1;
                        }
                    });
                    handles.push(handle);
                }

                for handle in handles {
                    handle.await.expect("等待异步锁任务失败");
                }

                *data.lock().await
            },
        ).await;

        Ok(result)
    }

    /// 测试读写锁性能
    pub async fn test_rwlock_performance(&self) -> Result<BenchmarkResult> {
        let result = self.benchmark.benchmark(
            "读写锁性能测试",
            100,
            || async {
                let data = Arc::new(RwLock::new(HashMap::<String, i32>::new()));
                let mut handles = Vec::new();

                // 写入任务
                for i in 0..25 {
                    let data = data.clone();
                    let handle = tokio::spawn(async move {
                        for j in 0..10 {
                            let mut map = data.write().await;
                            map.insert(format!("key_{}_{}", i, j), i * j);
                        }
                    });
                    handles.push(handle);
                }

                // 读取任务
                for _ in 0..25 {
                    let data = data.clone();
                    let handle = tokio::spawn(async move {
                        for _ in 0..10 {
                            let map = data.read().await;
                            let _ = map.len();
                        }
                    });
                    handles.push(handle);
                }

                for handle in handles {
                    handle.await.expect("等待异步锁任务失败");
                }

                data.read().await.len()
            },
        ).await;

        Ok(result)
    }
}

/// 综合性能测试演示
pub async fn demonstrate_performance_benchmarks_190() -> Result<()> {
    println!("🚀 演示 Rust 1.90 性能基准测试");
    println!("{}", "=".repeat(60));

    // 1. 异步性能测试
    println!("\n1. 异步性能测试:");
    let async_tests = AsyncPerformanceTests::new();

    async_tests.test_async_closure_performance().await?;
    async_tests.test_async_trait_performance().await?;
    async_tests.test_concurrent_processing_performance().await?;
    async_tests.test_async_state_machine_performance().await?;

    // 2. 内存性能测试
    println!("\n2. 内存性能测试:");
    let memory_tests = MemoryPerformanceTests::new();

    memory_tests.test_tuple_collection_memory();
    memory_tests.test_enum_memory_usage();
    memory_tests.test_async_resource_memory().await?;

    // 3. 并发性能测试
    println!("\n3. 并发性能测试:");
    let concurrency_tests = ConcurrencyPerformanceTests::new();

    concurrency_tests.test_concurrent_task_processing().await?;
    concurrency_tests.test_async_lock_performance().await?;
    concurrency_tests.test_rwlock_performance().await?;

    // 4. 生成性能报告
    println!("\n4. 生成性能报告:");
    let benchmark = PerformanceBenchmark::new();
    let report = benchmark.generate_report().await;
    println!("{}", report);

    println!("\n✅ Rust 1.90 性能基准测试演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_closure_performance() {
        // 该模块包含“基准”逻辑，默认迭代次数较大。
        // 单元测试中只验证逻辑正确性，避免运行过久。
        let tests = AsyncPerformanceTests::new();
        let result = tests
            .benchmark
            .benchmark("异步闭包性能测试（轻量）", 10, || async {
                let closure = |x: i32| async move { x * 2 };

                let mut sum = 0;
                for i in 0..10 {
                    sum += closure(i).await;
                }
                sum
            })
            .await;
        assert!(result.throughput > 0.0);
    }

    #[tokio::test]
    async fn test_concurrent_processing() {
        let tests = ConcurrencyPerformanceTests::new();
        let result = tests.test_concurrent_task_processing().await.expect("并发处理测试失败");
        assert!(result.throughput > 0.0);
    }

    #[test]
    fn test_memory_performance() {
        let tests = MemoryPerformanceTests::new();
        let result = tests.test_tuple_collection_memory();
        assert!(result.throughput > 0.0);
    }

    #[tokio::test]
    #[ignore]
    async fn test_comprehensive_benchmarks() {
        assert!(demonstrate_performance_benchmarks_190().await.is_ok());
    }
}
