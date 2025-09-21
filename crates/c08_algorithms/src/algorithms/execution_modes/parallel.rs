//! # 并行算法执行模式
//! 
//! 本模块实现并行算法执行，充分利用多核 CPU 的计算能力。
//! 基于 rayon 实现数据并行和任务并行。

use super::{ParallelAlgorithm, ExecutionResult};
use rayon::prelude::*;
use std::time::Instant;

/// 并行算法执行器
pub struct ParallelExecutor;

impl ParallelExecutor {
    /// 执行并行算法并测量性能
    pub fn execute_with_metrics<A, T, R>(
        algorithm: A,
        input: T,
    ) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R>,
        T: Clone,
    {
        let start = Instant::now();
        let memory_before = get_memory_usage();
        let thread_count = num_cpus::get();
        
        let result = algorithm.execute(input)?;
        
        let execution_time = start.elapsed();
        let memory_after = get_memory_usage();
        let memory_usage = memory_after.saturating_sub(memory_before);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count,
        })
    }

    /// 使用指定线程数执行并行算法
    pub fn execute_with_threads<A, T, R>(
        algorithm: A,
        input: T,
        thread_count: usize,
    ) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R>,
        T: Clone,
    {
        let start = Instant::now();
        let memory_before = get_memory_usage();
        
        let result = algorithm.execute_with_threads(input, thread_count)?;
        
        let execution_time = start.elapsed();
        let memory_after = get_memory_usage();
        let memory_usage = memory_after.saturating_sub(memory_before);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count,
        })
    }

    /// 批量执行并行算法
    pub fn execute_batch<A, T, R>(
        algorithm: A,
        inputs: Vec<T>,
    ) -> Result<Vec<ExecutionResult<R>>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R> + Clone + Send + Sync,
        T: Clone + Send + Sync,
        R: Send + Sync,
    {
        inputs
            .into_par_iter()
            .map(|input| Self::execute_with_metrics(algorithm.clone(), input))
            .collect()
    }

    /// 执行并行算法并返回详细统计信息
    pub fn execute_with_stats<A, T, R>(
        algorithm: A,
        input: T,
        iterations: usize,
    ) -> Result<ParallelExecutionStats<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R> + Clone,
        T: Clone,
        R: Send + Sync,
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

        Ok(ParallelExecutionStats {
            results,
            average_execution_time: avg_time,
            average_memory_usage: avg_memory,
            execution_time_std_dev: std::time::Duration::from_nanos(time_std_dev as u64),
            total_iterations: iterations,
            thread_count: num_cpus::get(),
        })
    }

    /// 测试不同线程数的性能
    pub fn benchmark_thread_scaling<A, T, R>(
        algorithm: A,
        input: T,
        thread_counts: Vec<usize>,
        iterations_per_thread: usize,
    ) -> Result<ThreadScalingResults<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R> + Clone,
        T: Clone,
        R: Send + Sync,
    {
        let mut results = Vec::with_capacity(thread_counts.len());

        for thread_count in thread_counts {
            let mut thread_results = Vec::with_capacity(iterations_per_thread);
            let mut total_time = std::time::Duration::ZERO;

            for _ in 0..iterations_per_thread {
                let result = Self::execute_with_threads(algorithm.clone(), input.clone(), thread_count)?;
                total_time += result.execution_time;
                thread_results.push(result);
            }

            let avg_time = total_time / iterations_per_thread as u32;
            let avg_memory = thread_results
                .iter()
                .map(|r| r.memory_usage)
                .sum::<usize>() / iterations_per_thread;

            results.push(ThreadScalingResult {
                thread_count,
                average_execution_time: avg_time,
                average_memory_usage: avg_memory,
                results: thread_results,
            });
        }

        Ok(ThreadScalingResults { results })
    }
}

/// 并行执行统计信息
#[derive(Debug, Clone)]
pub struct ParallelExecutionStats<T> {
    pub results: Vec<ExecutionResult<T>>,
    pub average_execution_time: std::time::Duration,
    pub average_memory_usage: usize,
    pub execution_time_std_dev: std::time::Duration,
    pub total_iterations: usize,
    pub thread_count: usize,
}

impl<T> ParallelExecutionStats<T> {
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

    /// 计算并行效率
    pub fn parallel_efficiency(&self, single_thread_time: std::time::Duration) -> f64 {
        if self.average_execution_time.as_nanos() == 0 {
            return 0.0;
        }
        
        let speedup = single_thread_time.as_nanos() as f64 / self.average_execution_time.as_nanos() as f64;
        speedup / self.thread_count as f64
    }
}

/// 线程扩展测试结果
#[derive(Debug, Clone)]
pub struct ThreadScalingResult<T> {
    pub thread_count: usize,
    pub average_execution_time: std::time::Duration,
    pub average_memory_usage: usize,
    pub results: Vec<ExecutionResult<T>>,
}

/// 线程扩展测试结果集合
#[derive(Debug, Clone)]
pub struct ThreadScalingResults<T> {
    pub results: Vec<ThreadScalingResult<T>>,
}

impl<T> ThreadScalingResults<T> {
    /// 获取最佳线程数
    pub fn optimal_thread_count(&self) -> Option<usize> {
        self.results
            .iter()
            .min_by_key(|r| r.average_execution_time)
            .map(|r| r.thread_count)
    }

    /// 计算最大加速比
    pub fn max_speedup(&self) -> Option<f64> {
        if self.results.is_empty() {
            return None;
        }

        let single_thread_time = self.results[0].average_execution_time;
        self.results
            .iter()
            .map(|r| {
                single_thread_time.as_nanos() as f64 / r.average_execution_time.as_nanos() as f64
            })
            .max_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal))
    }

    /// 生成线程扩展报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 并行算法线程扩展报告 ===\n\n");

        for result in &self.results {
            report.push_str(&format!("线程数: {}\n", result.thread_count));
            report.push_str(&format!(
                "  平均执行时间: {:?}\n",
                result.average_execution_time
            ));
            report.push_str(&format!(
                "  平均内存使用: {} bytes\n",
                result.average_memory_usage
            ));
            
            if !self.results.is_empty() {
                let speedup = self.results[0].average_execution_time.as_nanos() as f64 
                    / result.average_execution_time.as_nanos() as f64;
                report.push_str(&format!("  加速比: {:.2}x\n", speedup));
                
                let efficiency = speedup / result.thread_count as f64;
                report.push_str(&format!("  并行效率: {:.2}%\n", efficiency * 100.0));
            }
            report.push_str("\n");
        }

        if let Some(optimal) = self.optimal_thread_count() {
            report.push_str(&format!("最佳线程数: {}\n", optimal));
        }

        if let Some(max_speedup) = self.max_speedup() {
            report.push_str(&format!("最大加速比: {:.2}x\n", max_speedup));
        }

        report
    }
}

/// 并行算法基准测试器
pub struct ParallelBenchmarker;

impl ParallelBenchmarker {
    /// 运行并行基准测试
    pub fn benchmark<A, T, R>(
        algorithm: A,
        test_cases: Vec<ParallelBenchmarkTestCase<T>>,
    ) -> Result<ParallelBenchmarkResults<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R> + Clone + Send + Sync,
        T: Clone + Send + Sync,
        R: Send + Sync,
    {
        let mut results = Vec::with_capacity(test_cases.len());

        for test_case in test_cases {
            let stats = ParallelExecutor::execute_with_stats(
                algorithm.clone(),
                test_case.input,
                test_case.iterations,
            )?;

            results.push(ParallelBenchmarkResult {
                test_case: test_case.name,
                stats,
                thread_count: test_case.thread_count,
            });
        }

        Ok(ParallelBenchmarkResults { results })
    }

    /// 运行线程扩展基准测试
    pub fn benchmark_thread_scaling<A, T, R>(
        algorithm: A,
        test_cases: Vec<ThreadScalingTestCase<T>>,
    ) -> Result<Vec<ThreadScalingResults<R>>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R> + Clone,
        T: Clone,
        R: Send + Sync,
    {
        let mut results = Vec::with_capacity(test_cases.len());

        for test_case in test_cases {
            let scaling_results = ParallelExecutor::benchmark_thread_scaling(
                algorithm.clone(),
                test_case.input,
                test_case.thread_counts,
                test_case.iterations_per_thread,
            )?;

            results.push(scaling_results);
        }

        Ok(results)
    }
}

/// 并行基准测试用例
#[derive(Debug, Clone)]
pub struct ParallelBenchmarkTestCase<T> {
    pub name: String,
    pub input: T,
    pub iterations: usize,
    pub thread_count: usize,
}

/// 线程扩展测试用例
#[derive(Debug, Clone)]
pub struct ThreadScalingTestCase<T> {
    pub name: String,
    pub input: T,
    pub thread_counts: Vec<usize>,
    pub iterations_per_thread: usize,
}

/// 并行基准测试结果
#[derive(Debug, Clone)]
pub struct ParallelBenchmarkResult<T> {
    pub test_case: String,
    pub stats: ParallelExecutionStats<T>,
    pub thread_count: usize,
}

/// 并行基准测试结果集合
#[derive(Debug, Clone)]
pub struct ParallelBenchmarkResults<T> {
    pub results: Vec<ParallelBenchmarkResult<T>>,
}

impl<T> ParallelBenchmarkResults<T> {
    /// 获取最佳性能的测试用例
    pub fn best_performance(&self) -> Option<&ParallelBenchmarkResult<T>> {
        self.results
            .iter()
            .min_by_key(|r| r.stats.average_execution_time)
    }

    /// 获取最高并行效率的测试用例
    pub fn best_efficiency(&self, single_thread_time: std::time::Duration) -> Option<&ParallelBenchmarkResult<T>> {
        self.results
            .iter()
            .max_by(|a, b| {
                let eff_a = a.stats.parallel_efficiency(single_thread_time);
                let eff_b = b.stats.parallel_efficiency(single_thread_time);
                eff_a.partial_cmp(&eff_b).unwrap_or(std::cmp::Ordering::Equal)
            })
    }

    /// 生成并行性能报告
    pub fn generate_report(&self, single_thread_time: std::time::Duration) -> String {
        let mut report = String::new();
        report.push_str("=== 并行算法基准测试报告 ===\n\n");

        for result in &self.results {
            report.push_str(&format!("测试用例: {}\n", result.test_case));
            report.push_str(&format!("  线程数: {}\n", result.thread_count));
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
                "  并行效率: {:.2}%\n",
                result.stats.parallel_efficiency(single_thread_time) * 100.0
            ));
            report.push_str("\n");
        }

        if let Some(best) = self.best_performance() {
            report.push_str(&format!(
                "最佳性能: {} ({:?})\n",
                best.test_case, best.stats.average_execution_time
            ));
        }

        if let Some(efficient) = self.best_efficiency(single_thread_time) {
            report.push_str(&format!(
                "最高并行效率: {} ({:.2}%)\n",
                efficient.test_case,
                efficient.stats.parallel_efficiency(single_thread_time) * 100.0
            ));
        }

        report
    }
}

/// 并行工作池
pub struct ParallelWorkPool<T, R> {
    thread_pool: rayon::ThreadPool,
    _phantom: std::marker::PhantomData<(T, R)>,
}

impl<T, R> ParallelWorkPool<T, R> {
    /// 创建新的并行工作池
    pub fn new(thread_count: usize) -> Result<Self, Box<dyn std::error::Error + Send + Sync>> {
        let thread_pool = rayon::ThreadPoolBuilder::new()
            .num_threads(thread_count)
            .build()?;

        Ok(Self {
            thread_pool,
            _phantom: std::marker::PhantomData,
        })
    }

    /// 执行并行任务
    pub fn execute<F>(&self, tasks: Vec<T>, task_fn: F) -> Result<Vec<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        F: Fn(T) -> Result<R, Box<dyn std::error::Error + Send + Sync>> + Send + Sync,
        T: Send,
        R: Send,
    {
        self.thread_pool.install(|| {
            tasks.into_par_iter().map(task_fn).collect()
        })
    }

    /// 执行并行任务并收集结果
    pub fn execute_and_collect<F>(
        &self,
        tasks: Vec<T>,
        task_fn: F,
    ) -> Result<Vec<ExecutionResult<R>>, Box<dyn std::error::Error + Send + Sync>>
    where
        F: Fn(T) -> Result<R, Box<dyn std::error::Error + Send + Sync>> + Send + Sync,
        T: Send + Sync,
        R: Send + Sync,
    {
        self.thread_pool.install(|| {
            tasks.into_par_iter().map(|task| {
                let start = Instant::now();
                let memory_before = get_memory_usage();
                
                let result = task_fn(task)?;
                
                let execution_time = start.elapsed();
                let memory_after = get_memory_usage();
                let memory_usage = memory_after.saturating_sub(memory_before);
                
                Ok(ExecutionResult {
                    result,
                    execution_time,
                    memory_usage,
                    thread_count: self.thread_pool.current_num_threads(),
                })
            }).collect()
        })
    }
}

/// 获取当前内存使用量（简化实现）
fn get_memory_usage() -> usize {
    // 在实际应用中，这里应该使用更精确的内存测量方法
    std::mem::size_of::<usize>() * 1024 // 占位实现
}
