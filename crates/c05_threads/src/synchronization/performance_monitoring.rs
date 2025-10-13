//! 性能监控模块
//!
//! 本模块提供了同步原语的性能监控功能：
//! - 锁竞争监控
//! - 等待时间统计
//! - 吞吐量测量
//! - 性能分析报告

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 性能指标
#[derive(Debug)]
pub struct PerformanceMetrics {
    pub total_operations: AtomicUsize,
    pub successful_operations: AtomicUsize,
    pub failed_operations: AtomicUsize,
    pub total_wait_time: AtomicU64, // 微秒
    pub total_spin_time: AtomicU64, // 微秒
    pub contention_count: AtomicUsize,
    pub max_wait_time: AtomicU64,     // 微秒
    pub min_wait_time: AtomicU64,     // 微秒
    pub average_wait_time: AtomicU64, // 微秒
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceMetrics {
    pub fn new() -> Self {
        Self {
            total_operations: AtomicUsize::new(0),
            successful_operations: AtomicUsize::new(0),
            failed_operations: AtomicUsize::new(0),
            total_wait_time: AtomicU64::new(0),
            total_spin_time: AtomicU64::new(0),
            contention_count: AtomicUsize::new(0),
            max_wait_time: AtomicU64::new(0),
            min_wait_time: AtomicU64::new(u64::MAX),
            average_wait_time: AtomicU64::new(0),
        }
    }

    pub fn record_operation(&self, success: bool) {
        self.total_operations.fetch_add(1, Ordering::Relaxed);
        if success {
            self.successful_operations.fetch_add(1, Ordering::Relaxed);
        } else {
            self.failed_operations.fetch_add(1, Ordering::Relaxed);
        }
    }

    pub fn record_wait_time(&self, wait_time: Duration) {
        let wait_micros = wait_time.as_micros() as u64;
        self.total_wait_time
            .fetch_add(wait_micros, Ordering::Relaxed);

        // 更新最大等待时间
        let mut max_wait = self.max_wait_time.load(Ordering::Relaxed);
        while wait_micros > max_wait {
            match self.max_wait_time.compare_exchange_weak(
                max_wait,
                wait_micros,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(x) => max_wait = x,
            }
        }

        // 更新最小等待时间
        let mut min_wait = self.min_wait_time.load(Ordering::Relaxed);
        while wait_micros < min_wait {
            match self.min_wait_time.compare_exchange_weak(
                min_wait,
                wait_micros,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(x) => min_wait = x,
            }
        }

        // 更新平均等待时间
        let total_ops = self.total_operations.load(Ordering::Relaxed);
        if total_ops > 0 {
            let avg_wait = self.total_wait_time.load(Ordering::Relaxed) / total_ops as u64;
            self.average_wait_time.store(avg_wait, Ordering::Relaxed);
        }
    }

    pub fn record_spin_time(&self, spin_time: Duration) {
        let spin_micros = spin_time.as_micros() as u64;
        self.total_spin_time
            .fetch_add(spin_micros, Ordering::Relaxed);
    }

    pub fn record_contention(&self) {
        self.contention_count.fetch_add(1, Ordering::Relaxed);
    }

    pub fn get_success_rate(&self) -> f64 {
        let total = self.total_operations.load(Ordering::Relaxed);
        let successful = self.successful_operations.load(Ordering::Relaxed);

        if total == 0 {
            0.0
        } else {
            successful as f64 / total as f64
        }
    }

    pub fn get_contention_ratio(&self) -> f64 {
        // 定义为：每次成功操作是否经历过竞争，范围 [0, 1]
        let successful = self.successful_operations.load(Ordering::Relaxed);
        let contentions = self.contention_count.load(Ordering::Relaxed);
        if successful == 0 {
            if contentions > 0 { 1.0 } else { 0.0 }
        } else {
            (contentions as f64 / successful as f64).min(1.0)
        }
    }

    pub fn get_average_wait_time(&self) -> Duration {
        Duration::from_micros(self.average_wait_time.load(Ordering::Relaxed))
    }

    pub fn get_max_wait_time(&self) -> Duration {
        Duration::from_micros(self.max_wait_time.load(Ordering::Relaxed))
    }

    pub fn get_min_wait_time(&self) -> Duration {
        let min_wait = self.min_wait_time.load(Ordering::Relaxed);
        if min_wait == u64::MAX {
            Duration::ZERO
        } else {
            Duration::from_micros(min_wait)
        }
    }

    pub fn get_total_spin_time(&self) -> Duration {
        Duration::from_micros(self.total_spin_time.load(Ordering::Relaxed))
    }

    pub fn reset(&self) {
        self.total_operations.store(0, Ordering::Relaxed);
        self.successful_operations.store(0, Ordering::Relaxed);
        self.failed_operations.store(0, Ordering::Relaxed);
        self.total_wait_time.store(0, Ordering::Relaxed);
        self.total_spin_time.store(0, Ordering::Relaxed);
        self.contention_count.store(0, Ordering::Relaxed);
        self.max_wait_time.store(0, Ordering::Relaxed);
        self.min_wait_time.store(u64::MAX, Ordering::Relaxed);
        self.average_wait_time.store(0, Ordering::Relaxed);
    }
}

/// 性能监控器
pub struct PerformanceMonitor {
    metrics: Arc<PerformanceMetrics>,
    start_time: Instant,
    monitoring_enabled: AtomicBool,
}

impl Default for PerformanceMonitor {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(PerformanceMetrics::new()),
            start_time: Instant::now(),
            monitoring_enabled: AtomicBool::new(true),
        }
    }

    pub fn get_metrics(&self) -> &PerformanceMetrics {
        &self.metrics
    }

    pub fn enable_monitoring(&self, enabled: bool) {
        self.monitoring_enabled.store(enabled, Ordering::Relaxed);
    }

    pub fn is_monitoring_enabled(&self) -> bool {
        self.monitoring_enabled.load(Ordering::Relaxed)
    }

    pub fn record_operation(&self, success: bool) {
        if self.is_monitoring_enabled() {
            self.metrics.record_operation(success);
        }
    }

    pub fn record_wait_time(&self, wait_time: Duration) {
        if self.is_monitoring_enabled() {
            self.metrics.record_wait_time(wait_time);
        }
    }

    pub fn record_spin_time(&self, spin_time: Duration) {
        if self.is_monitoring_enabled() {
            self.metrics.record_spin_time(spin_time);
        }
    }

    pub fn record_contention(&self) {
        if self.is_monitoring_enabled() {
            self.metrics.record_contention();
        }
    }

    pub fn get_elapsed_time(&self) -> Duration {
        self.start_time.elapsed()
    }

    pub fn get_throughput(&self) -> f64 {
        let elapsed = self.get_elapsed_time();
        let total_ops = self.metrics.total_operations.load(Ordering::Relaxed);

        if elapsed.as_secs() > 0 {
            total_ops as f64 / elapsed.as_secs() as f64
        } else {
            0.0
        }
    }

    pub fn generate_report(&self) -> PerformanceReport {
        PerformanceReport {
            elapsed_time: self.get_elapsed_time(),
            total_operations: self.metrics.total_operations.load(Ordering::Relaxed),
            successful_operations: self.metrics.successful_operations.load(Ordering::Relaxed),
            failed_operations: self.metrics.failed_operations.load(Ordering::Relaxed),
            success_rate: self.metrics.get_success_rate(),
            contention_ratio: self.metrics.get_contention_ratio(),
            average_wait_time: self.metrics.get_average_wait_time(),
            max_wait_time: self.metrics.get_max_wait_time(),
            min_wait_time: self.metrics.get_min_wait_time(),
            total_spin_time: self.metrics.get_total_spin_time(),
            throughput: self.get_throughput(),
        }
    }

    pub fn reset(&self) {
        self.metrics.reset();
    }
}

/// 性能报告
#[derive(Debug, Clone)]
pub struct PerformanceReport {
    pub elapsed_time: Duration,
    pub total_operations: usize,
    pub successful_operations: usize,
    pub failed_operations: usize,
    pub success_rate: f64,
    pub contention_ratio: f64,
    pub average_wait_time: Duration,
    pub max_wait_time: Duration,
    pub min_wait_time: Duration,
    pub total_spin_time: Duration,
    pub throughput: f64,
}

impl PerformanceReport {
    pub fn print(&self) {
        println!("=== 性能报告 ===");
        println!("运行时间: {:?}", self.elapsed_time);
        println!("总操作数: {}", self.total_operations);
        println!("成功操作数: {}", self.successful_operations);
        println!("失败操作数: {}", self.failed_operations);
        println!("成功率: {:.2}%", self.success_rate * 100.0);
        println!("竞争比例: {:.2}%", self.contention_ratio * 100.0);
        println!("平均等待时间: {:?}", self.average_wait_time);
        println!("最大等待时间: {:?}", self.max_wait_time);
        println!("最小等待时间: {:?}", self.min_wait_time);
        println!("总自旋时间: {:?}", self.total_spin_time);
        println!("吞吐量: {:.2} ops/sec", self.throughput);
    }
}

/// 性能监控的互斥锁
pub struct MonitoredMutex<T> {
    data: Arc<Mutex<T>>,
    monitor: Arc<PerformanceMonitor>,
}

impl<T> MonitoredMutex<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            monitor: Arc::new(PerformanceMonitor::new()),
        }
    }

    pub fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let _start_time = Instant::now();

        // 尝试快速获取锁
        if let Ok(mut guard) = self.data.try_lock() {
            self.monitor.record_operation(true);
            return f(&mut guard);
        }

        // 需要等待
        self.monitor.record_contention();
        let wait_start = Instant::now();
        let mut guard = self.data.lock().unwrap();
        let wait_time = wait_start.elapsed();
        self.monitor.record_wait_time(wait_time);
        self.monitor.record_operation(true);

        f(&mut guard)
    }

    pub fn get_monitor(&self) -> &PerformanceMonitor {
        &self.monitor
    }
}

/// 性能监控的读写锁
pub struct MonitoredRwLock<T> {
    data: Arc<std::sync::RwLock<T>>,
    monitor: Arc<PerformanceMonitor>,
}

impl<T> MonitoredRwLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(std::sync::RwLock::new(data)),
            monitor: Arc::new(PerformanceMonitor::new()),
        }
    }

    pub fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let _start_time = Instant::now();

        // 尝试快速获取读锁
        if let Ok(guard) = self.data.try_read() {
            self.monitor.record_operation(true);
            return f(&guard);
        }

        // 需要等待
        self.monitor.record_contention();
        let wait_start = Instant::now();
        let guard = self.data.read().unwrap();
        let wait_time = wait_start.elapsed();
        self.monitor.record_wait_time(wait_time);
        self.monitor.record_operation(true);

        f(&guard)
    }

    pub fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let _start_time = Instant::now();

        // 尝试快速获取写锁
        if let Ok(mut guard) = self.data.try_write() {
            self.monitor.record_operation(true);
            return f(&mut guard);
        }

        // 需要等待
        self.monitor.record_contention();
        let wait_start = Instant::now();
        let mut guard = self.data.write().unwrap();
        let wait_time = wait_start.elapsed();
        self.monitor.record_wait_time(wait_time);
        self.monitor.record_operation(true);

        f(&mut guard)
    }

    pub fn get_monitor(&self) -> &PerformanceMonitor {
        &self.monitor
    }
}

/// 性能基准测试
pub struct PerformanceBenchmark {
    monitors: Vec<Arc<PerformanceMonitor>>,
    start_time: Instant,
}

impl Default for PerformanceBenchmark {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceBenchmark {
    pub fn new() -> Self {
        Self {
            monitors: Vec::new(),
            start_time: Instant::now(),
        }
    }

    pub fn add_monitor(&mut self, monitor: Arc<PerformanceMonitor>) {
        self.monitors.push(monitor);
    }

    pub fn run_benchmark<F>(&self, duration: Duration, test_fn: F)
    where
        F: Fn() + Send + Sync + 'static,
    {
        let end_time = self.start_time + duration;
        let test_fn = Arc::new(test_fn);

        let handles: Vec<_> = (0..4)
            .map(|_| {
                let test_fn = test_fn.clone();
                thread::spawn(move || {
                    while Instant::now() < end_time {
                        test_fn();
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }
    }

    pub fn generate_comparison_report(&self) -> ComparisonReport {
        let mut reports = Vec::new();

        for monitor in &self.monitors {
            reports.push(monitor.generate_report());
        }

        ComparisonReport { reports }
    }
}

/// 比较报告
#[derive(Debug, Clone)]
pub struct ComparisonReport {
    reports: Vec<PerformanceReport>,
}

impl ComparisonReport {
    pub fn print(&self) {
        println!("=== 性能比较报告 ===");

        for (i, report) in self.reports.iter().enumerate() {
            println!("监控器 {}:", i + 1);
            report.print();
            println!();
        }

        // 找出最佳性能
        if let Some(best_throughput) = self
            .reports
            .iter()
            .max_by(|a, b| a.throughput.partial_cmp(&b.throughput).unwrap())
        {
            println!("最佳吞吐量: {:.2} ops/sec", best_throughput.throughput);
        }

        if let Some(best_wait_time) = self
            .reports
            .iter()
            .min_by(|a, b| a.average_wait_time.cmp(&b.average_wait_time))
        {
            println!("最佳平均等待时间: {:?}", best_wait_time.average_wait_time);
        }
    }
}

/// 运行所有性能监控示例
pub fn demonstrate_performance_monitoring() {
    println!("=== 性能监控演示 ===");

    // 测试监控互斥锁
    let mutex = Arc::new(MonitoredMutex::new(0));
    let handles: Vec<_> = (0..4)
        .map(|_i| {
            let mutex = mutex.clone();
            thread::spawn(move || {
                for _ in 0..1000 {
                    mutex.lock(|data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    let report = mutex.get_monitor().generate_report();
    report.print();

    // 测试监控读写锁
    let rwlock = Arc::new(MonitoredRwLock::new(0));
    let read_handles: Vec<_> = (0..4)
        .map(|_i| {
            let rwlock = rwlock.clone();
            thread::spawn(move || {
                for _ in 0..1000 {
                    rwlock.read(|data| {
                        let _ = *data;
                    });
                }
            })
        })
        .collect();

    let write_handles: Vec<_> = (0..2)
        .map(|_i| {
            let rwlock = rwlock.clone();
            thread::spawn(move || {
                for _ in 0..500 {
                    rwlock.write(|data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();

    for handle in read_handles {
        handle.join().unwrap();
    }

    for handle in write_handles {
        handle.join().unwrap();
    }

    let report = rwlock.get_monitor().generate_report();
    report.print();

    // 测试性能基准
    let mut benchmark = PerformanceBenchmark::new();
    let monitor1 = Arc::new(PerformanceMonitor::new());
    let monitor2 = Arc::new(PerformanceMonitor::new());

    benchmark.add_monitor(monitor1.clone());
    benchmark.add_monitor(monitor2.clone());

    benchmark.run_benchmark(Duration::from_secs(1), || {
        // 模拟工作负载
        thread::sleep(Duration::from_micros(1));
    });

    let comparison_report = benchmark.generate_comparison_report();
    comparison_report.print();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_performance_metrics() {
        let metrics = PerformanceMetrics::new();

        metrics.record_operation(true);
        metrics.record_wait_time(Duration::from_millis(1));
        metrics.record_operation(false);
        metrics.record_contention();

        assert_eq!(metrics.get_success_rate(), 0.5);
        assert_eq!(metrics.get_contention_ratio(), 1.0);
        assert_eq!(metrics.get_average_wait_time(), Duration::from_millis(1));
    }

    #[test]
    #[ignore]
    fn test_performance_monitor() {
        let monitor = PerformanceMonitor::new();

        monitor.record_operation(true);
        monitor.record_wait_time(Duration::from_millis(1));
        monitor.record_contention();

        let report = monitor.generate_report();
        assert_eq!(report.success_rate, 1.0);
        assert_eq!(report.contention_ratio, 1.0);
    }

    #[test]
    fn test_monitored_mutex() {
        let mutex = MonitoredMutex::new(0);

        mutex.lock(|data| {
            *data = 42;
        });

        let value = mutex.lock(|data| *data);
        assert_eq!(value, 42);

        let report = mutex.get_monitor().generate_report();
        assert_eq!(report.total_operations, 2);
    }

    #[test]
    #[ignore]
    fn test_monitored_rwlock() {
        let rwlock = MonitoredRwLock::new(0);

        rwlock.write(|data| {
            *data = 42;
        });

        let value = rwlock.read(|data| *data);
        assert_eq!(value, 42);

        let report = rwlock.get_monitor().generate_report();
        assert_eq!(report.total_operations, 2);
    }
}
