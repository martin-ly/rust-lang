//! 性能指标收集器

// use crate::error::{NetworkError, NetworkResult}; // 暂时注释掉未使用的导入
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};

/// 性能指标
#[derive(Debug, Clone, Default)]
pub struct PerformanceMetrics {
    pub total_operations: u64,
    pub total_bytes_processed: u64,
    pub total_errors: u64,
    pub current_memory_usage: usize,
    pub peak_memory_usage: usize,
    pub average_operation_time: Duration,
    pub network_bytes_sent: u64,
    pub network_bytes_received: u64,
    pub error_counts: HashMap<String, u64>,
    pub operation_times: HashMap<String, Duration>,
    pub last_updated: Option<Instant>,
}

/// 指标收集器
pub struct MetricsCollector {
    metrics: Arc<RwLock<PerformanceMetrics>>,
    start_time: Instant,
    operation_timers: Arc<RwLock<HashMap<String, Vec<Duration>>>>,
}

impl MetricsCollector {
    /// 创建新的指标收集器
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(PerformanceMetrics::default())),
            start_time: Instant::now(),
            operation_timers: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 记录操作
    pub fn record_operation(&self) {
        let mut metrics = self.metrics.write().unwrap();
        metrics.total_operations += 1;
        metrics.last_updated = Some(Instant::now());
    }

    /// 记录操作时间
    pub fn record_operation_time(&self, operation: &str, duration: Duration) {
        let mut metrics = self.metrics.write().unwrap();
        let mut timers = self.operation_timers.write().unwrap();

        // 更新操作时间映射
        timers.entry(operation.to_string()).or_insert_with(Vec::new).push(duration);

        // 计算平均操作时间
        let total_duration: Duration = timers.values()
            .flatten()
            .sum();
        let total_count: usize = timers.values().map(|v| v.len()).sum();

        if total_count > 0 {
            metrics.average_operation_time = total_duration / total_count as u32;
        }

        metrics.last_updated = Some(Instant::now());
    }

    /// 记录内存使用
    pub fn record_memory_usage(&self, bytes: usize) {
        let mut metrics = self.metrics.write().unwrap();
        metrics.current_memory_usage = bytes;
        
        if bytes > metrics.peak_memory_usage {
            metrics.peak_memory_usage = bytes;
        }
        
        metrics.last_updated = Some(Instant::now());
    }

    /// 记录网络 I/O
    pub fn record_network_io(&self, bytes: usize, is_read: bool) {
        let mut metrics = self.metrics.write().unwrap();
        
        if is_read {
            metrics.network_bytes_received += bytes as u64;
        } else {
            metrics.network_bytes_sent += bytes as u64;
        }
        
        metrics.total_bytes_processed += bytes as u64;
        metrics.last_updated = Some(Instant::now());
    }

    /// 记录错误
    pub fn record_error(&self, error_type: &str) {
        let mut metrics = self.metrics.write().unwrap();
        metrics.total_errors += 1;
        *metrics.error_counts.entry(error_type.to_string()).or_insert(0) += 1;
        metrics.last_updated = Some(Instant::now());
    }

    /// 获取指标
    pub fn get_metrics(&self) -> PerformanceMetrics {
        self.metrics.read().unwrap().clone()
    }

    /// 重置指标
    pub fn reset(&self) {
        let mut metrics = self.metrics.write().unwrap();
        *metrics = PerformanceMetrics::default();
        metrics.last_updated = Some(Instant::now());
        
        let mut timers = self.operation_timers.write().unwrap();
        timers.clear();
    }

    /// 更新指标
    pub fn update(&self) {
        let mut metrics = self.metrics.write().unwrap();
        metrics.last_updated = Some(Instant::now());
    }

    /// 获取运行时间
    pub fn uptime(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// 获取操作统计
    pub fn get_operation_stats(&self) -> HashMap<String, OperationStats> {
        let timers = self.operation_timers.read().unwrap();
        let mut stats = HashMap::new();

        for (operation, durations) in timers.iter() {
            if !durations.is_empty() {
                let total: Duration = durations.iter().sum();
                let average = total / durations.len() as u32;
                let min = durations.iter().min().copied().unwrap_or_default();
                let max = durations.iter().max().copied().unwrap_or_default();

                stats.insert(operation.clone(), OperationStats {
                    count: durations.len(),
                    total_time: total,
                    average_time: average,
                    min_time: min,
                    max_time: max,
                });
            }
        }

        stats
    }

    /// 获取吞吐量统计
    pub fn get_throughput_stats(&self) -> ThroughputStats {
        let metrics = self.metrics.read().unwrap();
        let uptime = self.uptime();
        let uptime_secs = uptime.as_secs_f64();

        ThroughputStats {
            operations_per_second: metrics.total_operations as f64 / uptime_secs,
            bytes_per_second: metrics.total_bytes_processed as f64 / uptime_secs,
            errors_per_second: metrics.total_errors as f64 / uptime_secs,
            network_send_rate: metrics.network_bytes_sent as f64 / uptime_secs,
            network_receive_rate: metrics.network_bytes_received as f64 / uptime_secs,
        }
    }

    /// 获取内存统计
    pub fn get_memory_stats(&self) -> MemoryStats {
        let metrics = self.metrics.read().unwrap();

        MemoryStats {
            current_usage: metrics.current_memory_usage,
            peak_usage: metrics.peak_memory_usage,
            usage_percentage: if metrics.peak_memory_usage > 0 {
                metrics.current_memory_usage as f64 / metrics.peak_memory_usage as f64 * 100.0
            } else {
                0.0
            },
        }
    }

    /// 获取错误统计
    pub fn get_error_stats(&self) -> ErrorStats {
        let metrics = self.metrics.read().unwrap();

        ErrorStats {
            total_errors: metrics.total_errors,
            error_rate: if metrics.total_operations > 0 {
                metrics.total_errors as f64 / metrics.total_operations as f64 * 100.0
            } else {
                0.0
            },
            error_counts: metrics.error_counts.clone(),
        }
    }
}

/// 操作统计
#[derive(Debug, Clone)]
pub struct OperationStats {
    pub count: usize,
    pub total_time: Duration,
    pub average_time: Duration,
    pub min_time: Duration,
    pub max_time: Duration,
}

/// 吞吐量统计
#[derive(Debug, Clone)]
pub struct ThroughputStats {
    pub operations_per_second: f64,
    pub bytes_per_second: f64,
    pub errors_per_second: f64,
    pub network_send_rate: f64,
    pub network_receive_rate: f64,
}

/// 内存统计
#[derive(Debug, Clone)]
pub struct MemoryStats {
    pub current_usage: usize,
    pub peak_usage: usize,
    pub usage_percentage: f64,
}

/// 错误统计
#[derive(Debug, Clone)]
pub struct ErrorStats {
    pub total_errors: u64,
    pub error_rate: f64,
    pub error_counts: HashMap<String, u64>,
}

/// 性能报告生成器
pub struct PerformanceReporter {
    collector: Arc<MetricsCollector>,
    report_interval: Duration,
    last_report: Instant,
}

impl PerformanceReporter {
    /// 创建新的性能报告生成器
    pub fn new(collector: Arc<MetricsCollector>, report_interval: Duration) -> Self {
        Self {
            collector,
            report_interval,
            last_report: Instant::now(),
        }
    }

    /// 生成性能报告
    pub fn generate_report(&mut self) -> PerformanceReport {
        let metrics = self.collector.get_metrics();
        let operation_stats = self.collector.get_operation_stats();
        let throughput_stats = self.collector.get_throughput_stats();
        let memory_stats = self.collector.get_memory_stats();
        let error_stats = self.collector.get_error_stats();

        self.last_report = Instant::now();

        PerformanceReport {
            timestamp: self.last_report,
            uptime: self.collector.uptime(),
            metrics,
            operation_stats,
            throughput_stats,
            memory_stats,
            error_stats,
        }
    }

    /// 检查是否应该生成报告
    pub fn should_report(&self) -> bool {
        self.last_report.elapsed() >= self.report_interval
    }

    /// 生成并打印报告
    pub fn print_report(&mut self) {
        let report = self.generate_report();
        println!("=== 性能报告 ===");
        println!("时间: {:?}", report.timestamp);
        println!("运行时间: {:?}", report.uptime);
        println!("总操作数: {}", report.metrics.total_operations);
        println!("总字节数: {}", report.metrics.total_bytes_processed);
        println!("总错误数: {}", report.metrics.total_errors);
        println!("当前内存使用: {} 字节", report.memory_stats.current_usage);
        println!("峰值内存使用: {} 字节", report.memory_stats.peak_usage);
        println!("操作/秒: {:.2}", report.throughput_stats.operations_per_second);
        println!("字节/秒: {:.2}", report.throughput_stats.bytes_per_second);
        println!("错误率: {:.2}%", report.error_stats.error_rate);
        println!("================");
    }
}

/// 性能报告
#[derive(Debug, Clone)]
pub struct PerformanceReport {
    pub timestamp: Instant,
    pub uptime: Duration,
    pub metrics: PerformanceMetrics,
    pub operation_stats: HashMap<String, OperationStats>,
    pub throughput_stats: ThroughputStats,
    pub memory_stats: MemoryStats,
    pub error_stats: ErrorStats,
}

/// 性能监控器
pub struct PerformanceMonitor {
    collector: Arc<MetricsCollector>,
    reporter: PerformanceReporter,
}

impl PerformanceMonitor {
    /// 创建新的性能监控器
    pub fn new(report_interval: Duration) -> Self {
        let collector = Arc::new(MetricsCollector::new());
        let reporter = PerformanceReporter::new(collector.clone(), report_interval);

        Self {
            collector,
            reporter,
        }
    }

    /// 获取指标收集器
    pub fn collector(&self) -> Arc<MetricsCollector> {
        self.collector.clone()
    }

    /// 更新监控
    pub fn update(&mut self) {
        if self.reporter.should_report() {
            self.reporter.print_report();
        }
    }

    /// 生成最终报告
    pub fn final_report(&mut self) -> PerformanceReport {
        self.reporter.generate_report()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_metrics_collector() {
        let collector = MetricsCollector::new();
        
        // 记录一些操作
        collector.record_operation();
        collector.record_operation();
        collector.record_memory_usage(1024);
        collector.record_network_io(512, true);
        collector.record_error("test_error");
        
        let metrics = collector.get_metrics();
        assert_eq!(metrics.total_operations, 2);
        assert_eq!(metrics.current_memory_usage, 1024);
        assert_eq!(metrics.network_bytes_received, 512);
        assert_eq!(metrics.total_errors, 1);
    }

    #[test]
    fn test_operation_timing() {
        let collector = MetricsCollector::new();
        
        // 记录操作时间
        collector.record_operation_time("test_op", Duration::from_millis(100));
        collector.record_operation_time("test_op", Duration::from_millis(200));
        
        let operation_stats = collector.get_operation_stats();
        assert!(operation_stats.contains_key("test_op"));
        
        let stats = &operation_stats["test_op"];
        assert_eq!(stats.count, 2);
        assert_eq!(stats.average_time, Duration::from_millis(150));
        assert_eq!(stats.min_time, Duration::from_millis(100));
        assert_eq!(stats.max_time, Duration::from_millis(200));
    }

    #[test]
    fn test_throughput_stats() {
        let collector = MetricsCollector::new();
        
        // 记录一些操作
        for _ in 0..10 {
            collector.record_operation();
        }
        
        // 等待一小段时间
        thread::sleep(Duration::from_millis(10));
        
        let throughput = collector.get_throughput_stats();
        assert!(throughput.operations_per_second > 0.0);
    }

    #[test]
    fn test_memory_stats() {
        let collector = MetricsCollector::new();
        
        collector.record_memory_usage(1024);
        collector.record_memory_usage(2048);
        
        let memory_stats = collector.get_memory_stats();
        assert_eq!(memory_stats.current_usage, 2048);
        assert_eq!(memory_stats.peak_usage, 2048);
        assert_eq!(memory_stats.usage_percentage, 100.0);
    }

    #[test]
    fn test_error_stats() {
        let collector = MetricsCollector::new();
        
        collector.record_operation();
        collector.record_operation();
        collector.record_error("error1");
        
        let error_stats = collector.get_error_stats();
        assert_eq!(error_stats.total_errors, 1);
        assert_eq!(error_stats.error_rate, 50.0);
        assert_eq!(error_stats.error_counts["error1"], 1);
    }

    #[test]
    fn test_performance_reporter() {
        let collector = Arc::new(MetricsCollector::new());
        let mut reporter = PerformanceReporter::new(collector, Duration::from_millis(100));
        
        let report = reporter.generate_report();
        assert!(report.uptime.as_secs() < 1);
    }

    #[test]
    fn test_performance_monitor() {
        let mut monitor = PerformanceMonitor::new(Duration::from_millis(100));
        
        // 记录一些操作
        let collector = monitor.collector();
        collector.record_operation();
        collector.record_memory_usage(1024);
        
        // 更新监控
        monitor.update();
        
        // 生成最终报告
        let report = monitor.final_report();
        assert_eq!(report.metrics.total_operations, 1);
        assert_eq!(report.memory_stats.current_usage, 1024);
    }
}
