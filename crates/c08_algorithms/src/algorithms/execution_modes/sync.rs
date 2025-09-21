//! # 同步算法执行模式
//! 
//! 本模块实现同步算法执行，提供传统的单线程算法执行方式。
//! 适用于 CPU 密集型任务和需要确定性执行顺序的场景。

use super::{SyncAlgorithm, ExecutionResult};
use std::time::Instant;

/// 同步算法执行器
pub struct SyncExecutor;

impl SyncExecutor {
    /// 执行同步算法并测量性能
    pub fn execute_with_metrics<A, T, R>(
        algorithm: A,
        input: T,
    ) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: SyncAlgorithm<T, R>,
        T: Clone,
    {
        let start = Instant::now();
        let memory_before = get_memory_usage();
        
        let result = algorithm.execute(input)?;
        
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

    /// 批量执行同步算法
    pub fn execute_batch<A, T, R>(
        algorithm: A,
        inputs: Vec<T>,
    ) -> Result<Vec<ExecutionResult<R>>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: SyncAlgorithm<T, R> + Clone,
        T: Clone,
    {
        inputs
            .into_iter()
            .map(|input| Self::execute_with_metrics(algorithm.clone(), input))
            .collect()
    }

    /// 执行同步算法并返回详细统计信息
    pub fn execute_with_stats<A, T, R>(
        algorithm: A,
        input: T,
        iterations: usize,
    ) -> Result<SyncExecutionStats<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: SyncAlgorithm<T, R> + Clone,
        T: Clone,
    {
        let mut results = Vec::with_capacity(iterations);
        let mut total_time = std::time::Duration::ZERO;
        let mut total_memory = 0;

        for _ in 0..iterations {
            let result = Self::execute_with_metrics(algorithm.clone(), input.clone())?;
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

        Ok(SyncExecutionStats {
            results,
            average_execution_time: avg_time,
            average_memory_usage: avg_memory,
            execution_time_std_dev: std::time::Duration::from_nanos(time_std_dev as u64),
            total_iterations: iterations,
        })
    }
}

/// 同步执行统计信息
#[derive(Debug, Clone)]
pub struct SyncExecutionStats<T> {
    pub results: Vec<ExecutionResult<T>>,
    pub average_execution_time: std::time::Duration,
    pub average_memory_usage: usize,
    pub execution_time_std_dev: std::time::Duration,
    pub total_iterations: usize,
}

impl<T> SyncExecutionStats<T> {
    /// 获取最小执行时间
    pub fn min_execution_time(&self) -> std::time::Duration {
        self.results
            .iter()
            .map(|r| r.execution_time)
            .min()
            .unwrap_or_default()
    }

    /// 获取最大执行时间
    pub fn max_execution_time(&self) -> std::time::Duration {
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

/// 获取当前内存使用量（简化实现）
fn get_memory_usage() -> usize {
    // 在实际应用中，这里应该使用更精确的内存测量方法
    // 例如使用 `sysinfo` crate 或系统特定的 API
    std::mem::size_of::<usize>() * 1024 // 占位实现
}

/// 同步算法基准测试器
pub struct SyncBenchmarker;

impl SyncBenchmarker {
    /// 运行基准测试
    pub fn benchmark<A, T, R>(
        algorithm: A,
        test_cases: Vec<BenchmarkTestCase<T>>,
    ) -> Result<BenchmarkResults<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: SyncAlgorithm<T, R> + Clone,
        T: Clone,
    {
        let mut results = Vec::with_capacity(test_cases.len());

        for test_case in test_cases {
            let stats = SyncExecutor::execute_with_stats(
                algorithm.clone(),
                test_case.input,
                test_case.iterations,
            )?;

            results.push(BenchmarkResult {
                test_case: test_case.name,
                stats,
            });
        }

        Ok(BenchmarkResults { results })
    }
}

/// 基准测试用例
#[derive(Debug, Clone)]
pub struct BenchmarkTestCase<T> {
    pub name: String,
    pub input: T,
    pub iterations: usize,
}

/// 基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult<T> {
    pub test_case: String,
    pub stats: SyncExecutionStats<T>,
}

/// 基准测试结果集合
#[derive(Debug, Clone)]
pub struct BenchmarkResults<T> {
    pub results: Vec<BenchmarkResult<T>>,
}

impl<T> BenchmarkResults<T> {
    /// 获取最佳性能的测试用例
    pub fn best_performance(&self) -> Option<&BenchmarkResult<T>> {
        self.results
            .iter()
            .min_by_key(|r| r.stats.average_execution_time)
    }

    /// 获取最稳定性能的测试用例
    pub fn most_stable(&self) -> Option<&BenchmarkResult<T>> {
        self.results
            .iter()
            .min_by(|a, b| {
                a.stats.performance_stability()
                    .partial_cmp(&b.stats.performance_stability())
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
    }

    /// 生成性能报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 同步算法基准测试报告 ===\n\n");

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
            report.push_str(&format!(
                "  最小执行时间: {:?}\n",
                result.stats.min_execution_time()
            ));
            report.push_str(&format!(
                "  最大执行时间: {:?}\n",
                result.stats.max_execution_time()
            ));
            report.push_str("\n");
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
