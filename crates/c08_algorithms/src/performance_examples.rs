//! 性能优化实践示例模块
//!
//! 本模块提供四个主要性能优化领域的实践示例：
//! - 内存优化 (Memory Optimization)
//! - 并发性能优化 (Concurrency Performance Optimization)  
//! - 编译时优化 (Compile-time Optimization)
//! - 运行时性能分析 (Runtime Performance Analysis)

pub mod compile_time_optimization;
pub mod concurrency_optimization;
pub mod memory_optimization;
pub mod runtime_profiling;

use std::time::{Duration, Instant};

/// 性能基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub name: String,
    pub duration: Duration,
    pub memory_usage: Option<usize>,
    pub throughput: Option<f64>,
}

/// 性能优化基准测试器
pub struct PerformanceBenchmarker {
    results: Vec<BenchmarkResult>,
}

impl PerformanceBenchmarker {
    pub fn new() -> Self {
        Self {
            results: Vec::new(),
        }
    }

    /// 运行基准测试
    pub fn benchmark<F>(&mut self, name: &str, iterations: usize, f: F) -> BenchmarkResult
    where
        F: Fn() -> (),
    {
        let start = Instant::now();

        for _ in 0..iterations {
            f();
        }

        let duration = start.elapsed();
        let avg_duration = duration / iterations as u32;

        let result = BenchmarkResult {
            name: name.to_string(),
            duration: avg_duration,
            memory_usage: None,
            throughput: None,
        };

        self.results.push(result.clone());
        result
    }

    /// 获取所有基准测试结果
    pub fn get_results(&self) -> &[BenchmarkResult] {
        &self.results
    }

    /// 打印基准测试报告
    pub fn print_report(&self) {
        println!("=== 性能优化基准测试报告 ===");
        for result in &self.results {
            println!("{}: {:?}", result.name, result.duration);
        }
        println!("=============================");
    }
}

/// 内存使用监控器
pub struct MemoryMonitor {
    initial_usage: Option<usize>,
}

impl MemoryMonitor {
    pub fn new() -> Self {
        Self {
            initial_usage: None,
        }
    }

    /// 开始监控
    pub fn start_monitoring(&mut self) {
        // 在实际应用中，这里会调用系统API获取内存使用情况
        self.initial_usage = Some(0);
    }

    /// 获取当前内存使用
    pub fn get_current_usage(&self) -> Option<usize> {
        // 模拟内存使用监控
        Some(1024 * 1024) // 1MB
    }

    /// 计算内存增长
    pub fn calculate_growth(&self) -> Option<usize> {
        if let Some(initial) = self.initial_usage {
            self.get_current_usage().map(|current| current - initial)
        } else {
            None
        }
    }
}

/// 性能分析器
pub struct PerformanceProfiler {
    measurements: Vec<(String, Duration)>,
}

impl PerformanceProfiler {
    pub fn new() -> Self {
        Self {
            measurements: Vec::new(),
        }
    }

    /// 测量函数执行时间
    pub fn measure<F, T>(&mut self, name: &str, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        let start = Instant::now();
        let result = f();
        let duration = start.elapsed();

        self.measurements.push((name.to_string(), duration));
        result
    }

    /// 获取测量结果
    pub fn get_measurements(&self) -> &[(String, Duration)] {
        &self.measurements
    }

    /// 生成性能报告
    pub fn generate_report(&self) -> String {
        let mut report = String::from("=== 性能分析报告 ===\n");

        for (name, duration) in &self.measurements {
            report.push_str(&format!("{}: {:?}\n", name, duration));
        }

        report.push_str("=====================");
        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_benchmarker() {
        let mut benchmarker = PerformanceBenchmarker::new();

        let result = benchmarker.benchmark("test_function", 100, || {
            thread::sleep(Duration::from_millis(1));
        });

        assert!(!result.name.is_empty());
        assert!(result.duration > Duration::from_nanos(0));
    }

    #[test]
    fn test_memory_monitor() {
        let mut monitor = MemoryMonitor::new();
        monitor.start_monitoring();

        let usage = monitor.get_current_usage();
        assert!(usage.is_some());
    }

    #[test]
    fn test_profiler() {
        let mut profiler = PerformanceProfiler::new();

        let result = profiler.measure("test_measurement", || {
            thread::sleep(Duration::from_millis(10));
            42
        });

        assert_eq!(result, 42);
        assert_eq!(profiler.get_measurements().len(), 1);
    }
}
