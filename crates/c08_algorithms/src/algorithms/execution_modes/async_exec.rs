//! # 异步算法执行模式
//! 
//! 本模块实现异步算法执行，充分利用 Rust 1.90 的异步特性。
//! 适用于 I/O 密集型任务和需要非阻塞执行的场景。

use super::{AsyncAlgorithm, ExecutionResult};
use std::future::Future;
use std::pin::Pin;
use std::time::Instant;
use tokio::time::{timeout, Duration};

/// 异步算法执行器
pub struct AsyncExecutor;

impl AsyncExecutor {
    /// 执行异步算法并测量性能
    pub async fn execute_with_metrics<A, T, R>(
        algorithm: A,   
        input: T,
    ) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R> + Send + Sync,
        T: Send + 'static,
        R: Send + 'static,
    {
        let start = Instant::now();
        let memory_before = get_memory_usage();
        
        let result = algorithm.execute(input).await?;
        
        let execution_time = start.elapsed();
        let memory_after = get_memory_usage();
        let memory_usage = memory_after.saturating_sub(memory_before);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count: 1,
        })
    }

    /// 带超时的异步算法执行
    pub async fn execute_with_timeout<A, T, R>(
        algorithm: A,
        input: T,
        timeout_duration: Duration,
    ) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R> + Send + Sync,
        T: Send + 'static,
        R: Send + 'static,
    {
        let start = Instant::now();
        let memory_before = get_memory_usage();
        
        let result = timeout(timeout_duration, algorithm.execute(input))
            .await
            .map_err(|_| "算法执行超时")??;
        
        let execution_time = start.elapsed();
        let memory_after = get_memory_usage();
        let memory_usage = memory_after.saturating_sub(memory_before);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count: 1,
        })
    }

    /// 批量执行异步算法
    pub async fn execute_batch<A, T, R>(
        algorithm: A,
        inputs: Vec<T>,
    ) -> Result<Vec<ExecutionResult<R>>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R> + Clone + Send + Sync + 'static,
        T: Send + 'static,
        R: Send + 'static,
    {
        let mut handles = Vec::with_capacity(inputs.len());
        
        for input in inputs {
            let algorithm_clone = algorithm.clone();
            let handle = tokio::spawn(async move {
                Self::execute_with_metrics(algorithm_clone, input).await
            });
            handles.push(handle);
        }
        
        let mut results = Vec::with_capacity(handles.len());
        for handle in handles {
            let result = handle.await??;
            results.push(result);
        }
        
        Ok(results)
    }

    /// 并发执行异步算法（限制并发数）
    pub async fn execute_concurrent<A, T, R>(
        algorithm: A,
        inputs: Vec<T>,
        max_concurrent: usize,
    ) -> Result<Vec<ExecutionResult<R>>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R> + Clone + Send + Sync + 'static,
        T: Send + 'static,
        R: Send + 'static,
    {
        use tokio::sync::Semaphore;
        use std::sync::Arc;
        
        let semaphore = Arc::new(Semaphore::new(max_concurrent));
        let mut handles = Vec::with_capacity(inputs.len());
        
        for input in inputs {
            let algorithm_clone = algorithm.clone();
            let semaphore_clone = semaphore.clone();
            
            let handle = tokio::spawn(async move {
                let _permit = semaphore_clone.acquire().await?;
                Self::execute_with_metrics(algorithm_clone, input).await
            });
            handles.push(handle);
        }
        
        let mut results = Vec::with_capacity(handles.len());
        for handle in handles {
            let result = handle.await??;
            results.push(result);
        }
        
        Ok(results)
    }

    /// 执行异步算法并返回详细统计信息
    pub async fn execute_with_stats<A, T, R>(
        algorithm: A,
        input: T,
        iterations: usize,
    ) -> Result<AsyncExecutionStats<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R> + Clone + Send + Sync + 'static,
        T: Clone + Send + 'static,
        R: Send + 'static,
    {
        let mut results = Vec::with_capacity(iterations);
        let mut total_time = Duration::ZERO;
        let mut total_memory = 0;

        for _ in 0..iterations {
            let result = Self::execute_with_metrics(algorithm.clone(), input.clone()).await?;
            total_time += result.execution_time;
            total_memory += result.memory_usage;
            results.push(result);
        }

        let avg_time = total_time / iterations as u32;
        let avg_memory = total_memory / iterations;

        // 计算标准差
        let time_variance: f64 = results
            .iter()
            .map(|r| {
                let diff = r.execution_time.as_nanos() as f64 - avg_time.as_nanos() as f64;
                diff * diff
            })
            .sum::<f64>()
            / iterations as f64;

        let time_std_dev = time_variance.sqrt();

        Ok(AsyncExecutionStats {
            results,
            average_execution_time: avg_time,
            average_memory_usage: avg_memory,
            execution_time_std_dev: Duration::from_nanos(time_std_dev as u64),
            total_iterations: iterations,
        })
    }
}

/// 异步执行统计信息
#[derive(Debug, Clone)]
pub struct AsyncExecutionStats<T> {
    pub results: Vec<ExecutionResult<T>>,
    pub average_execution_time: Duration,
    pub average_memory_usage: usize,
    pub execution_time_std_dev: Duration,
    pub total_iterations: usize,
}

impl<T> AsyncExecutionStats<T> {
    /// 获取最小执行时间
    pub fn min_execution_time(&self) -> Duration {
        self.results
            .iter()
            .map(|r| r.execution_time)
            .min()
            .unwrap_or_default()
    }

    /// 获取最大执行时间
    pub fn max_execution_time(&self) -> Duration {
        self.results
            .iter()
            .map(|r| r.execution_time)
            .max()
            .unwrap_or_default()
    }

    /// 获取最小内存使用
    pub fn min_memory_usage(&self) -> usize {
        self.results
            .iter()
            .map(|r| r.memory_usage)
            .min()
            .unwrap_or(0)
    }

    /// 获取最大内存使用
    pub fn max_memory_usage(&self) -> usize {
        self.results
            .iter()
            .map(|r| r.memory_usage)
            .max()
            .unwrap_or(0)
    }

    /// 计算性能稳定性（变异系数）
    pub fn performance_stability(&self) -> f64 {
        if self.average_execution_time.as_nanos() == 0 {
            return 0.0;
        }
        
        self.execution_time_std_dev.as_nanos() as f64 / self.average_execution_time.as_nanos() as f64
    }
}

/// 异步算法基准测试器
pub struct AsyncBenchmarker;

impl AsyncBenchmarker {
    /// 运行异步基准测试
    pub async fn benchmark<A, T, R>(
        algorithm: A,
        test_cases: Vec<AsyncBenchmarkTestCase<T>>,
    ) -> Result<AsyncBenchmarkResults<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R> + Clone + Send + Sync + 'static,
        T: Clone + Send + 'static,
        R: Send + 'static,
    {
        let mut results = Vec::with_capacity(test_cases.len());

        for test_case in test_cases {
            let stats = AsyncExecutor::execute_with_stats(
                algorithm.clone(),
                test_case.input,
                test_case.iterations,
            ).await?;

            results.push(AsyncBenchmarkResult {
                test_case: test_case.name,
                stats,
                timeout: test_case.timeout,
            });
        }

        Ok(AsyncBenchmarkResults { results })
    }

    /// 运行并发基准测试
    pub async fn benchmark_concurrent<A, T, R>(
        algorithm: A,
        test_cases: Vec<AsyncBenchmarkTestCase<T>>,
        max_concurrent: usize,
    ) -> Result<AsyncBenchmarkResults<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R> + Clone + Send + Sync + 'static,
        T: Clone + Send + 'static,
        R: Send + 'static,
    {
        let mut results = Vec::with_capacity(test_cases.len());

        for test_case in test_cases {
            let inputs = vec![test_case.input; test_case.iterations];
            let execution_results = AsyncExecutor::execute_concurrent(
                algorithm.clone(),
                inputs,
                max_concurrent,
            ).await?;

            let total_time: Duration = execution_results
                .iter()
                .map(|r| r.execution_time)
                .sum();
            let avg_time = total_time / test_case.iterations as u32;
            let avg_memory = execution_results
                .iter()
                .map(|r| r.memory_usage)
                .sum::<usize>() / test_case.iterations;

            let stats = AsyncExecutionStats {
                results: execution_results,
                average_execution_time: avg_time,
                average_memory_usage: avg_memory,
                execution_time_std_dev: Duration::ZERO, // 简化计算
                total_iterations: test_case.iterations,
            };

            results.push(AsyncBenchmarkResult {
                test_case: test_case.name,
                stats,
                timeout: test_case.timeout,
            });
        }

        Ok(AsyncBenchmarkResults { results })
    }
}

/// 异步基准测试用例
#[derive(Debug, Clone)]
pub struct AsyncBenchmarkTestCase<T> {
    pub name: String,
    pub input: T,
    pub iterations: usize,
    pub timeout: Option<Duration>,
}

/// 异步基准测试结果
#[derive(Debug, Clone)]
pub struct AsyncBenchmarkResult<T> {
    pub test_case: String,
    pub stats: AsyncExecutionStats<T>,
    pub timeout: Option<Duration>,
}

/// 异步基准测试结果集合
#[derive(Debug, Clone)]
pub struct AsyncBenchmarkResults<T> {
    pub results: Vec<AsyncBenchmarkResult<T>>,
}

impl<T> AsyncBenchmarkResults<T> {
    /// 获取最佳性能的测试用例
    pub fn best_performance(&self) -> Option<&AsyncBenchmarkResult<T>> {
        self.results
            .iter()
            .min_by_key(|r| r.stats.average_execution_time)
    }

    /// 获取最稳定性能的测试用例
    pub fn most_stable(&self) -> Option<&AsyncBenchmarkResult<T>> {
        self.results
            .iter()
            .min_by(|a, b| {
                a.stats.performance_stability()
                    .partial_cmp(&b.stats.performance_stability())
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
    }

    /// 生成异步性能报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 异步算法基准测试报告 ===\n\n");

        for result in &self.results {
            report.push_str(&format!("测试用例: {}\n", result.test_case));
            report.push_str(&format!(
                "  平均执行时间: {:?}\n",
                result.stats.average_execution_time
            ));
            report.push_str(&format!(
                "  执行时间标准差: {:?}\n",
                result.stats.execution_time_std_dev
            ));
            report.push_str(&format!(
                "  平均内存使用: {} bytes\n",
                result.stats.average_memory_usage
            ));
            report.push_str(&format!(
                "  性能稳定性: {:.4}\n",
                result.stats.performance_stability()
            ));
            if let Some(timeout) = result.timeout {
                report.push_str(&format!("  超时设置: {:?}\n", timeout));
            }
            report.push('\n');
        }

        if let Some(best) = self.best_performance() {
            report.push_str(&format!(
                "最佳性能: {} ({:?})\n",
                best.test_case, best.stats.average_execution_time
            ));
        }

        if let Some(stable) = self.most_stable() {
            report.push_str(&format!(
                "最稳定性能: {} (稳定性: {:.4})\n",
                stable.test_case,
                stable.stats.performance_stability()
            ));
        }

        report
    }
}

/// 异步算法管道
pub struct AsyncPipeline<T> {
    stages: Vec<Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = Result<T, Box<dyn std::error::Error + Send + Sync>>> + Send>> + Send + Sync>>,
}

impl<T> Default for AsyncPipeline<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> AsyncPipeline<T> {
    /// 创建新的异步管道
    pub fn new() -> Self {
        Self {
            stages: Vec::new(),
        }
    }

    /// 添加处理阶段
    pub fn add_stage<F, Fut>(&mut self, stage: F)
    where
        F: Fn(T) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<T, Box<dyn std::error::Error + Send + Sync>>> + Send + 'static,
    {
        self.stages.push(Box::new(move |input| {
            Box::pin(stage(input))
        }));
    }

    /// 执行管道
    pub async fn execute(&self, input: T) -> Result<T, Box<dyn std::error::Error + Send + Sync>>
    where
        T: Clone,
    {
        let mut current_input = input;
        
        for stage in &self.stages {
            current_input = stage(current_input).await?;
        }
        
        Ok(current_input)
    }
}

/// 获取当前内存使用量（简化实现）
fn get_memory_usage() -> usize {
    // 在实际应用中，这里应该使用更精确的内存测量方法
    std::mem::size_of::<usize>() * 1024 // 占位实现
}
