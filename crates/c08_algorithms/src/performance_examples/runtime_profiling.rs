//! 运行时性能分析实践示例

use std::collections::HashMap;
use std::time::{Duration, Instant};

/// 简单性能分析器
pub struct SimpleProfiler {
    measurements: HashMap<String, Vec<Duration>>,
}

impl Default for SimpleProfiler {
    fn default() -> Self {
        Self::new()
    }
}

impl SimpleProfiler {
    pub fn new() -> Self {
        Self {
            measurements: HashMap::new(),
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

        self.measurements
            .entry(name.to_string())
            .or_default()
            .push(duration);

        result
    }

    /// 获取平均执行时间
    pub fn get_average_time(&self, name: &str) -> Option<Duration> {
        self.measurements.get(name).map(|durations| {
            let total: Duration = durations.iter().sum();
            total / durations.len() as u32
        })
    }

    /// 生成简单报告
    pub fn generate_report(&self) -> String {
        let mut report = String::from("=== 性能分析报告 ===\n");

        for (name, durations) in &self.measurements {
            let total: Duration = durations.iter().sum();
            let avg = total / durations.len() as u32;
            let min = durations.iter().min().unwrap();
            let max = durations.iter().max().unwrap();

            report.push_str(&format!(
                "{}: 平均={:?}, 最小={:?}, 最大={:?}, 次数={}\n",
                name,
                avg,
                min,
                max,
                durations.len()
            ));
        }

        report.push_str("=====================");
        report
    }
}

/// 内存使用监控器（简化版）
pub struct MemoryMonitor {
    initial_usage: Option<usize>,
}

impl Default for MemoryMonitor {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryMonitor {
    pub fn new() -> Self {
        Self {
            initial_usage: None,
        }
    }

    /// 开始监控
    pub fn start_monitoring(&mut self) {
        self.initial_usage = Some(0);
    }

    /// 获取当前内存使用（模拟）
    pub fn get_current_usage(&self) -> Option<usize> {
        Some(1024 * 1024) // 模拟1MB
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

/// 性能指标收集器
pub struct MetricsCollector {
    metrics: HashMap<String, f64>,
    counters: HashMap<String, u64>,
}

impl Default for MetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl MetricsCollector {
    pub fn new() -> Self {
        Self {
            metrics: HashMap::new(),
            counters: HashMap::new(),
        }
    }

    /// 记录指标
    pub fn record_metric(&mut self, name: &str, value: f64) {
        self.metrics.insert(name.to_string(), value);
    }

    /// 增加计数器
    pub fn increment_counter(&mut self, name: &str) {
        *self.counters.entry(name.to_string()).or_insert(0) += 1;
    }

    /// 获取指标
    pub fn get_metric(&self, name: &str) -> Option<f64> {
        self.metrics.get(name).copied()
    }

    /// 获取计数器值
    pub fn get_counter(&self, name: &str) -> Option<u64> {
        self.counters.get(name).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_simple_profiler() {
        let mut profiler = SimpleProfiler::new();

        profiler.measure("test_function", || {
            thread::sleep(Duration::from_millis(10));
        });

        let avg_time = profiler.get_average_time("test_function");
        assert!(avg_time.is_some());

        if let Some(avg) = avg_time {
            assert!(avg > Duration::from_millis(5));
        }
    }

    #[test]
    fn test_memory_monitor() {
        let mut monitor = MemoryMonitor::new();
        monitor.start_monitoring();

        let usage = monitor.get_current_usage();
        assert!(usage.is_some());

        let growth = monitor.calculate_growth();
        assert!(growth.is_some());
    }

    #[test]
    fn test_metrics_collector() {
        let mut collector = MetricsCollector::new();

        collector.record_metric("latency", 100.0);
        collector.increment_counter("requests");

        assert_eq!(collector.get_metric("latency"), Some(100.0));
        assert_eq!(collector.get_counter("requests"), Some(1));
    }
}
