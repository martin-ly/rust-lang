//! 性能分析模块
//!
//! 提供性能监控、分析和优化建议功能

pub mod profiler;
pub mod analyzer;
pub mod optimizer;

pub use profiler::{
    PerformanceProfiler, ProfilerConfig, ProfilerStats, ProfilerEvent,
    ProfilerError, ProfilerResult,
};
pub use analyzer::{
    PerformanceAnalyzer, PerformanceReport, PerformanceMetrics,
    BottleneckAnalysis, OptimizationSuggestion,
};
pub use optimizer::{
    PerformanceOptimizer, OptimizationConfig, OptimizationResult,
    OptimizationStrategy,
};

use std::time::{Duration, Instant};
use std::collections::HashMap;
use serde::{Deserialize, Serialize};

/// 性能监控器
#[derive(Debug)]
pub struct PerformanceMonitor {
    profiler: PerformanceProfiler,
    analyzer: PerformanceAnalyzer,
    optimizer: PerformanceOptimizer,
    _config: PerformanceConfig,
}

impl PerformanceMonitor {
    /// 创建新的性能监控器
    pub fn new(config: PerformanceConfig) -> Self {
        Self {
            profiler: PerformanceProfiler::new(config.profiler.clone()),
            analyzer: PerformanceAnalyzer::new(),
            optimizer: PerformanceOptimizer::new(config.optimizer.clone()),
            _config: config,
        }
    }

    /// 开始性能监控
    pub fn start_monitoring(&mut self) -> ProfilerResult<()> {
        self.profiler.start()
    }

    /// 停止性能监控
    pub fn stop_monitoring(&mut self) -> ProfilerResult<ProfilerStats> {
        self.profiler.stop()
    }

    /// 记录性能事件
    pub fn record_event(&mut self, event: ProfilerEvent) -> ProfilerResult<()> {
        self.profiler.record_event(event)
    }

    /// 分析性能数据
    pub fn analyze_performance(&mut self) -> ProfilerResult<PerformanceReport> {
        let stats = self.profiler.get_stats()?;
        Ok(self.analyzer.analyze(&stats))
    }

    /// 生成优化建议
    pub fn generate_optimization_suggestions(&mut self) -> ProfilerResult<Vec<OptimizationSuggestion>> {
        let report = self.analyze_performance()?;
        Ok(self.optimizer.generate_suggestions(&report))
    }

    /// 应用优化策略
    pub fn apply_optimizations(&mut self, strategies: Vec<OptimizationStrategy>) -> ProfilerResult<OptimizationResult> {
        Ok(self.optimizer.apply_optimizations(strategies))
    }

    /// 获取性能统计信息
    pub fn get_stats(&self) -> ProfilerResult<ProfilerStats> {
        self.profiler.get_stats()
    }

    /// 重置性能监控器
    pub fn reset(&mut self) -> ProfilerResult<()> {
        self.profiler.reset()
    }
}

/// 性能配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceConfig {
    pub profiler: ProfilerConfig,
    pub optimizer: OptimizationConfig,
    pub monitoring_interval: Duration,
    pub max_events: usize,
    pub enable_auto_optimization: bool,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            profiler: ProfilerConfig::default(),
            optimizer: OptimizationConfig::default(),
            monitoring_interval: Duration::from_secs(1),
            max_events: 10000,
            enable_auto_optimization: false,
        }
    }
}

/// 性能基准测试器
#[derive(Debug)]
pub struct PerformanceBenchmark {
    name: String,
    iterations: usize,
    warmup_iterations: usize,
    results: Vec<Duration>,
}

impl PerformanceBenchmark {
    /// 创建新的基准测试器
    pub fn new(name: String) -> Self {
        Self {
            name,
            iterations: 1000,
            warmup_iterations: 100,
            results: Vec::new(),
        }
    }

    /// 设置迭代次数
    pub fn iterations(mut self, iterations: usize) -> Self {
        self.iterations = iterations;
        self
    }

    /// 设置预热迭代次数
    pub fn warmup_iterations(mut self, warmup_iterations: usize) -> Self {
        self.warmup_iterations = warmup_iterations;
        self
    }

    /// 运行基准测试
    pub fn run<F>(&mut self, mut test_function: F) -> BenchmarkResult
    where
        F: FnMut(),
    {
        // 预热
        for _ in 0..self.warmup_iterations {
            test_function();
        }

        // 运行测试
        let start_time = Instant::now();
        for _ in 0..self.iterations {
            let iteration_start = Instant::now();
            test_function();
            let iteration_duration = iteration_start.elapsed();
            self.results.push(iteration_duration);
        }
        let total_duration = start_time.elapsed();

        BenchmarkResult {
            name: self.name.clone(),
            iterations: self.iterations,
            total_duration,
            results: self.results.clone(),
        }
    }
}

/// 基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub name: String,
    pub iterations: usize,
    pub total_duration: Duration,
    pub results: Vec<Duration>,
}

impl BenchmarkResult {
    /// 计算平均执行时间
    pub fn average_duration(&self) -> Duration {
        if self.results.is_empty() {
            Duration::ZERO
        } else {
            let total_nanos: u128 = self.results.iter().map(|d| d.as_nanos()).sum();
            Duration::from_nanos((total_nanos / self.results.len() as u128) as u64)
        }
    }

    /// 计算最小执行时间
    pub fn min_duration(&self) -> Duration {
        self.results.iter().min().copied().unwrap_or(Duration::ZERO)
    }

    /// 计算最大执行时间
    pub fn max_duration(&self) -> Duration {
        self.results.iter().max().copied().unwrap_or(Duration::ZERO)
    }

    /// 计算每秒操作数
    pub fn operations_per_second(&self) -> f64 {
        if self.total_duration.as_secs_f64() > 0.0 {
            self.iterations as f64 / self.total_duration.as_secs_f64()
        } else {
            0.0
        }
    }

    /// 计算百分位数
    pub fn percentile(&self, p: f64) -> Duration {
        if self.results.is_empty() {
            return Duration::ZERO;
        }

        let mut sorted_results = self.results.clone();
        sorted_results.sort();
        
        let index = ((p / 100.0) * (sorted_results.len() - 1) as f64) as usize;
        sorted_results[index.min(sorted_results.len() - 1)]
    }
}

/// 性能比较器
#[derive(Debug)]
pub struct PerformanceComparator {
    benchmarks: HashMap<String, BenchmarkResult>,
}

impl PerformanceComparator {
    /// 创建新的性能比较器
    pub fn new() -> Self {
        Self {
            benchmarks: HashMap::new(),
        }
    }

    /// 添加基准测试结果
    pub fn add_benchmark(&mut self, result: BenchmarkResult) {
        self.benchmarks.insert(result.name.clone(), result);
    }

    /// 比较基准测试结果
    pub fn compare(&self) -> ComparisonReport {
        let mut report = ComparisonReport {
            comparisons: Vec::new(),
            summary: String::new(),
        };

        let mut benchmark_results: Vec<_> = self.benchmarks.values().collect();
        benchmark_results.sort_by(|a, b| a.average_duration().cmp(&b.average_duration()));

        // 生成比较报告
        for (i, result) in benchmark_results.iter().enumerate() {
            let comparison = BenchmarkComparison {
                name: result.name.clone(),
                rank: i + 1,
                average_duration: result.average_duration(),
                operations_per_second: result.operations_per_second(),
                percentile_95: result.percentile(95.0),
                percentile_99: result.percentile(99.0),
            };
            report.comparisons.push(comparison);
        }

        // 生成总结
        if let Some(fastest) = benchmark_results.first() {
            if let Some(slowest) = benchmark_results.last() {
                let speedup = slowest.average_duration().as_nanos() as f64 / fastest.average_duration().as_nanos() as f64;
                report.summary = format!(
                    "最快: {} ({:.2}ns), 最慢: {} ({:.2}ns), 速度差异: {:.2}x",
                    fastest.name,
                    fastest.average_duration().as_nanos(),
                    slowest.name,
                    slowest.average_duration().as_nanos(),
                    speedup
                );
            }
        }

        report
    }
}

/// 基准测试比较
#[derive(Debug, Clone)]
pub struct BenchmarkComparison {
    pub name: String,
    pub rank: usize,
    pub average_duration: Duration,
    pub operations_per_second: f64,
    pub percentile_95: Duration,
    pub percentile_99: Duration,
}

/// 比较报告
#[derive(Debug, Clone)]
pub struct ComparisonReport {
    pub comparisons: Vec<BenchmarkComparison>,
    pub summary: String,
}

/// 性能测试套件
#[derive(Debug)]
pub struct PerformanceTestSuite {
    name: String,
    benchmarks: Vec<BenchmarkResult>,
    config: TestSuiteConfig,
}

/// 测试套件配置
#[derive(Debug, Clone)]
pub struct TestSuiteConfig {
    pub iterations: usize,
    pub warmup_iterations: usize,
    pub enable_statistics: bool,
    pub output_format: OutputFormat,
}

/// 输出格式
#[derive(Debug, Clone)]
pub enum OutputFormat {
    Text,
    Json,
    Csv,
}

impl Default for TestSuiteConfig {
    fn default() -> Self {
        Self {
            iterations: 1000,
            warmup_iterations: 100,
            enable_statistics: true,
            output_format: OutputFormat::Text,
        }
    }
}

impl PerformanceTestSuite {
    /// 创建新的性能测试套件
    pub fn new(name: String) -> Self {
        Self {
            name,
            benchmarks: Vec::new(),
            config: TestSuiteConfig::default(),
        }
    }

    /// 设置配置
    pub fn config(mut self, config: TestSuiteConfig) -> Self {
        self.config = config;
        self
    }

    /// 添加基准测试
    pub fn add_benchmark<F>(&mut self, name: String, test_function: F) -> BenchmarkResult
    where
        F: FnMut(),
    {
        let mut benchmark = PerformanceBenchmark::new(name.clone())
            .iterations(self.config.iterations)
            .warmup_iterations(self.config.warmup_iterations);
        
        let result = benchmark.run(test_function);
        self.benchmarks.push(result.clone());
        result
    }

    /// 运行所有基准测试
    pub fn run_all(&mut self) -> &[BenchmarkResult] {
        &self.benchmarks
    }

    /// 生成报告
    pub fn generate_report(&self) -> String {
        let mut report = format!("性能测试套件: {}\n", self.name);
        report.push_str("=".repeat(50).as_str());
        report.push('\n');

        for result in &self.benchmarks {
            report.push_str(&format!(
                "基准测试: {}\n",
                result.name
            ));
            report.push_str(&format!(
                "  迭代次数: {}\n",
                result.iterations
            ));
            report.push_str(&format!(
                "  总耗时: {:.2}ms\n",
                result.total_duration.as_secs_f64() * 1000.0
            ));
            report.push_str(&format!(
                "  平均耗时: {:.2}ns\n",
                result.average_duration().as_nanos()
            ));
            report.push_str(&format!(
                "  最小耗时: {:.2}ns\n",
                result.min_duration().as_nanos()
            ));
            report.push_str(&format!(
                "  最大耗时: {:.2}ns\n",
                result.max_duration().as_nanos()
            ));
            report.push_str(&format!(
                "  95百分位: {:.2}ns\n",
                result.percentile(95.0).as_nanos()
            ));
            report.push_str(&format!(
                "  99百分位: {:.2}ns\n",
                result.percentile(99.0).as_nanos()
            ));
            report.push_str(&format!(
                "  每秒操作数: {:.2}\n",
                result.operations_per_second()
            ));
            report.push_str("\n");
        }

        report
    }
}
