//! 线程资源监控
//! 
//! 本模块提供了线程资源监控功能：
//! - CPU使用率监控
//! - 内存使用监控
//! - 系统调用统计
//! - 性能分析

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};
use std::collections::HashMap;

/// 线程资源使用统计
#[derive(Debug, Clone)]
pub struct ThreadResourceStats {
    pub thread_id: usize,
    pub cpu_usage: f64,
    pub memory_usage: usize,
    pub virtual_memory: usize,
    pub page_faults: usize,
    pub context_switches: usize,
    pub system_calls: usize,
    pub io_operations: usize,
    pub last_updated: Instant,
}

impl ThreadResourceStats {
    pub fn new(thread_id: usize) -> Self {
        Self {
            thread_id,
            cpu_usage: 0.0,
            memory_usage: 0,
            virtual_memory: 0,
            page_faults: 0,
            context_switches: 0,
            system_calls: 0,
            io_operations: 0,
            last_updated: Instant::now(),
        }
    }
    
    pub fn update_cpu_usage(&mut self, usage: f64) {
        self.cpu_usage = usage;
        self.last_updated = Instant::now();
    }
    
    pub fn update_memory_usage(&mut self, usage: usize) {
        self.memory_usage = usage;
        self.last_updated = Instant::now();
    }
    
    pub fn increment_page_faults(&mut self) {
        self.page_faults += 1;
    }
    
    pub fn increment_context_switches(&mut self) {
        self.context_switches += 1;
    }
    
    pub fn increment_system_calls(&mut self) {
        self.system_calls += 1;
    }
    
    pub fn increment_io_operations(&mut self) {
        self.io_operations += 1;
    }
}

/// 系统资源监控器
pub struct SystemResourceMonitor {
    thread_stats: Arc<Mutex<HashMap<usize, ThreadResourceStats>>>,
    system_stats: Arc<Mutex<SystemStats>>,
    monitoring_enabled: AtomicBool,
    monitoring_interval: Duration,
}

#[derive(Debug, Clone)]
pub struct SystemStats {
    pub total_cpu_usage: f64,
    pub total_memory_usage: usize,
    pub total_virtual_memory: usize,
    pub total_page_faults: usize,
    pub total_context_switches: usize,
    pub total_system_calls: usize,
    pub total_io_operations: usize,
    pub last_updated: Instant,
}

impl SystemResourceMonitor {
    pub fn new() -> Self {
        Self {
            thread_stats: Arc::new(Mutex::new(HashMap::new())),
            system_stats: Arc::new(Mutex::new(SystemStats {
                total_cpu_usage: 0.0,
                total_memory_usage: 0,
                total_virtual_memory: 0,
                total_page_faults: 0,
                total_context_switches: 0,
                total_system_calls: 0,
                total_io_operations: 0,
                last_updated: Instant::now(),
            })),
            monitoring_enabled: AtomicBool::new(true),
            monitoring_interval: Duration::from_millis(100),
        }
    }
    
    pub fn register_thread(&self, thread_id: usize) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        thread_stats.insert(thread_id, ThreadResourceStats::new(thread_id));
    }
    
    pub fn unregister_thread(&self, thread_id: usize) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        thread_stats.remove(&thread_id);
    }
    
    pub fn update_thread_cpu_usage(&self, thread_id: usize, usage: f64) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        if let Some(stats) = thread_stats.get_mut(&thread_id) {
            stats.update_cpu_usage(usage);
        }
    }
    
    pub fn update_thread_memory_usage(&self, thread_id: usize, usage: usize) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        if let Some(stats) = thread_stats.get_mut(&thread_id) {
            stats.update_memory_usage(usage);
        }
    }
    
    pub fn record_page_fault(&self, thread_id: usize) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        if let Some(stats) = thread_stats.get_mut(&thread_id) {
            stats.increment_page_faults();
        }
    }
    
    pub fn record_context_switch(&self, thread_id: usize) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        if let Some(stats) = thread_stats.get_mut(&thread_id) {
            stats.increment_context_switches();
        }
    }
    
    pub fn record_system_call(&self, thread_id: usize) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        if let Some(stats) = thread_stats.get_mut(&thread_id) {
            stats.increment_system_calls();
        }
    }
    
    pub fn record_io_operation(&self, thread_id: usize) {
        let mut thread_stats = self.thread_stats.lock().unwrap();
        if let Some(stats) = thread_stats.get_mut(&thread_id) {
            stats.increment_io_operations();
        }
    }
    
    pub fn get_thread_stats(&self, thread_id: usize) -> Option<ThreadResourceStats> {
        let thread_stats = self.thread_stats.lock().unwrap();
        thread_stats.get(&thread_id).cloned()
    }
    
    pub fn get_all_thread_stats(&self) -> Vec<ThreadResourceStats> {
        let thread_stats = self.thread_stats.lock().unwrap();
        thread_stats.values().cloned().collect()
    }
    
    pub fn get_system_stats(&self) -> SystemStats {
        let system_stats = self.system_stats.lock().unwrap();
        system_stats.clone()
    }
    
    pub fn enable_monitoring(&self, enabled: bool) {
        self.monitoring_enabled.store(enabled, Ordering::Relaxed);
    }
    
    pub fn set_monitoring_interval(&mut self, interval: Duration) {
        self.monitoring_interval = interval;
    }
    
    pub fn start_monitoring(&self) {
        let monitor = self.clone();
        let interval = self.monitoring_interval;
        
        thread::spawn(move || {
            while monitor.monitoring_enabled.load(Ordering::Relaxed) {
                monitor.collect_system_stats();
                thread::sleep(interval);
            }
        });
    }
    
    fn collect_system_stats(&self) {
        let mut system_stats = self.system_stats.lock().unwrap();
        let thread_stats = self.thread_stats.lock().unwrap();
        
        // 计算系统总统计
        system_stats.total_cpu_usage = thread_stats.values().map(|s| s.cpu_usage).sum();
        system_stats.total_memory_usage = thread_stats.values().map(|s| s.memory_usage).sum();
        system_stats.total_virtual_memory = thread_stats.values().map(|s| s.virtual_memory).sum();
        system_stats.total_page_faults = thread_stats.values().map(|s| s.page_faults).sum();
        system_stats.total_context_switches = thread_stats.values().map(|s| s.context_switches).sum();
        system_stats.total_system_calls = thread_stats.values().map(|s| s.system_calls).sum();
        system_stats.total_io_operations = thread_stats.values().map(|s| s.io_operations).sum();
        system_stats.last_updated = Instant::now();
    }
}

impl Clone for SystemResourceMonitor {
    fn clone(&self) -> Self {
        Self {
            thread_stats: self.thread_stats.clone(),
            system_stats: self.system_stats.clone(),
            monitoring_enabled: AtomicBool::new(self.monitoring_enabled.load(Ordering::Relaxed)),
            monitoring_interval: self.monitoring_interval,
        }
    }
}

/// 性能分析器
#[allow(dead_code)]
pub struct PerformanceProfiler {
    monitor: Arc<SystemResourceMonitor>,
    profile_data: Arc<Mutex<HashMap<usize, ProfileData>>>,
    profiling_enabled: AtomicBool,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ProfileData {
    pub thread_id: usize,
    pub function_calls: HashMap<String, usize>,
    pub execution_times: HashMap<String, Duration>,
    pub memory_allocations: HashMap<String, usize>,
    pub cache_misses: usize,
    pub branch_mispredictions: usize,
}

impl PerformanceProfiler {
    pub fn new(monitor: Arc<SystemResourceMonitor>) -> Self {
        Self {
            monitor,
            profile_data: Arc::new(Mutex::new(HashMap::new())),
            profiling_enabled: AtomicBool::new(true),
        }
    }
    
    pub fn start_profiling(&self, thread_id: usize) {
        let mut profile_data = self.profile_data.lock().unwrap();
        profile_data.insert(thread_id, ProfileData {
            thread_id,
            function_calls: HashMap::new(),
            execution_times: HashMap::new(),
            memory_allocations: HashMap::new(),
            cache_misses: 0,
            branch_mispredictions: 0,
        });
    }
    
    pub fn stop_profiling(&self, thread_id: usize) {
        let mut profile_data = self.profile_data.lock().unwrap();
        profile_data.remove(&thread_id);
    }
    
    pub fn record_function_call(&self, thread_id: usize, function_name: String, execution_time: Duration) {
        if !self.profiling_enabled.load(Ordering::Relaxed) {
            return;
        }
        
        let mut profile_data = self.profile_data.lock().unwrap();
        if let Some(data) = profile_data.get_mut(&thread_id) {
            *data.function_calls.entry(function_name.clone()).or_insert(0) += 1;
            *data.execution_times.entry(function_name).or_insert(Duration::ZERO) += execution_time;
        }
    }
    
    pub fn record_memory_allocation(&self, thread_id: usize, allocation_type: String, size: usize) {
        if !self.profiling_enabled.load(Ordering::Relaxed) {
            return;
        }
        
        let mut profile_data = self.profile_data.lock().unwrap();
        if let Some(data) = profile_data.get_mut(&thread_id) {
            *data.memory_allocations.entry(allocation_type).or_insert(0) += size;
        }
    }
    
    pub fn record_cache_miss(&self, thread_id: usize) {
        if !self.profiling_enabled.load(Ordering::Relaxed) {
            return;
        }
        
        let mut profile_data = self.profile_data.lock().unwrap();
        if let Some(data) = profile_data.get_mut(&thread_id) {
            data.cache_misses += 1;
        }
    }
    
    pub fn record_branch_misprediction(&self, thread_id: usize) {
        if !self.profiling_enabled.load(Ordering::Relaxed) {
            return;
        }
        
        let mut profile_data = self.profile_data.lock().unwrap();
        if let Some(data) = profile_data.get_mut(&thread_id) {
            data.branch_mispredictions += 1;
        }
    }
    
    pub fn get_profile_data(&self, thread_id: usize) -> Option<ProfileData> {
        let profile_data = self.profile_data.lock().unwrap();
        profile_data.get(&thread_id).cloned()
    }
    
    pub fn generate_profile_report(&self, thread_id: usize) -> Option<ProfileReport> {
        let profile_data = self.profile_data.lock().unwrap();
        if let Some(data) = profile_data.get(&thread_id) {
            Some(ProfileReport {
                thread_id: data.thread_id,
                total_function_calls: data.function_calls.values().sum(),
                total_execution_time: data.execution_times.values().sum(),
                total_memory_allocations: data.memory_allocations.values().sum(),
                cache_misses: data.cache_misses,
                branch_mispredictions: data.branch_mispredictions,
                function_calls: data.function_calls.clone(),
                execution_times: data.execution_times.clone(),
                memory_allocations: data.memory_allocations.clone(),
            })
        } else {
            None
        }
    }
    
    pub fn enable_profiling(&self, enabled: bool) {
        self.profiling_enabled.store(enabled, Ordering::Relaxed);
    }
}

#[derive(Debug, Clone)]
pub struct ProfileReport {
    pub thread_id: usize,
    pub total_function_calls: usize,
    pub total_execution_time: Duration,
    pub total_memory_allocations: usize,
    pub cache_misses: usize,
    pub branch_mispredictions: usize,
    pub function_calls: HashMap<String, usize>,
    pub execution_times: HashMap<String, Duration>,
    pub memory_allocations: HashMap<String, usize>,
}

impl ProfileReport {
    pub fn print(&self) {
        println!("=== 线程 {} 性能分析报告 ===", self.thread_id);
        println!("总函数调用次数: {}", self.total_function_calls);
        println!("总执行时间: {:?}", self.total_execution_time);
        println!("总内存分配: {} 字节", self.total_memory_allocations);
        println!("缓存未命中: {}", self.cache_misses);
        println!("分支预测错误: {}", self.branch_mispredictions);
        
        println!("\n函数调用统计:");
        for (function, count) in &self.function_calls {
            println!("  {}: {} 次", function, count);
        }
        
        println!("\n执行时间统计:");
        for (function, time) in &self.execution_times {
            println!("  {}: {:?}", function, time);
        }
        
        println!("\n内存分配统计:");
        for (allocation_type, size) in &self.memory_allocations {
            println!("  {}: {} 字节", allocation_type, size);
        }
    }
}

/// 运行所有资源监控示例
pub fn demonstrate_resource_monitoring() {
    println!("=== 线程资源监控演示 ===");
    
    let monitor = Arc::new(SystemResourceMonitor::new());
    let profiler = Arc::new(PerformanceProfiler::new(monitor.clone()));
    
    // 启动监控
    monitor.start_monitoring();
    
    // 创建测试线程
    let handles: Vec<_> = (0..3)
        .map(|thread_id| {
            let monitor = monitor.clone();
            let profiler = profiler.clone();
            thread::spawn(move || {
                // 注册线程
                monitor.register_thread(thread_id);
                profiler.start_profiling(thread_id);
                
                for i in 0..100 {
                    let start_time = Instant::now();
                    
                    // 模拟工作负载
                    let _ = (0..1000).fold(0, |acc, x| acc + x);
                    
                    let execution_time = start_time.elapsed();
                    
                    // 记录性能数据
                    profiler.record_function_call(thread_id, "compute".to_string(), execution_time);
                    profiler.record_memory_allocation(thread_id, "heap".to_string(), 1024);
                    
                    if i % 10 == 0 {
                        profiler.record_cache_miss(thread_id);
                    }
                    
                    if i % 20 == 0 {
                        profiler.record_branch_misprediction(thread_id);
                    }
                    
                    // 更新资源使用统计
                    monitor.update_thread_cpu_usage(thread_id, 0.8);
                    monitor.update_thread_memory_usage(thread_id, 1024 * (i + 1));
                    monitor.record_system_call(thread_id);
                    
                    if i % 5 == 0 {
                        monitor.record_io_operation(thread_id);
                    }
                    
                    thread::sleep(Duration::from_millis(1));
                }
                
                // 停止性能分析
                profiler.stop_profiling(thread_id);
                monitor.unregister_thread(thread_id);
            })
        })
        .collect();
    
    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 显示系统统计
    let system_stats = monitor.get_system_stats();
    println!("系统总统计:");
    println!("  总CPU使用率: {:.2}%", system_stats.total_cpu_usage * 100.0);
    println!("  总内存使用: {} 字节", system_stats.total_memory_usage);
    println!("  总虚拟内存: {} 字节", system_stats.total_virtual_memory);
    println!("  总页面错误: {}", system_stats.total_page_faults);
    println!("  总上下文切换: {}", system_stats.total_context_switches);
    println!("  总系统调用: {}", system_stats.total_system_calls);
    println!("  总I/O操作: {}", system_stats.total_io_operations);
    
    // 显示线程统计
    for thread_id in 0..3 {
        if let Some(stats) = monitor.get_thread_stats(thread_id) {
            println!("线程 {} 统计:", thread_id);
            println!("  CPU使用率: {:.2}%", stats.cpu_usage * 100.0);
            println!("  内存使用: {} 字节", stats.memory_usage);
            println!("  虚拟内存: {} 字节", stats.virtual_memory);
            println!("  页面错误: {}", stats.page_faults);
            println!("  上下文切换: {}", stats.context_switches);
            println!("  系统调用: {}", stats.system_calls);
            println!("  I/O操作: {}", stats.io_operations);
        }
    }
    
    // 显示性能分析报告
    for thread_id in 0..3 {
        if let Some(report) = profiler.generate_profile_report(thread_id) {
            report.print();
        }
    }
    
    // 停止监控
    monitor.enable_monitoring(false);
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_system_resource_monitor() {
        let monitor = SystemResourceMonitor::new();
        
        monitor.register_thread(1);
        monitor.update_thread_cpu_usage(1, 0.8);
        monitor.update_thread_memory_usage(1, 1024);
        
        let stats = monitor.get_thread_stats(1).unwrap();
        assert_eq!(stats.cpu_usage, 0.8);
        assert_eq!(stats.memory_usage, 1024);
    }
    
    #[test]
    fn test_performance_profiler() {
        let monitor = Arc::new(SystemResourceMonitor::new());
        let profiler = PerformanceProfiler::new(monitor);
        
        profiler.start_profiling(1);
        profiler.record_function_call(1, "test".to_string(), Duration::from_millis(1));
        profiler.record_memory_allocation(1, "heap".to_string(), 1024);
        
        let report = profiler.generate_profile_report(1).unwrap();
        assert_eq!(report.total_function_calls, 1);
        assert_eq!(report.total_memory_allocations, 1024);
    }
    
    #[test]
    fn test_thread_resource_stats() {
        let mut stats = ThreadResourceStats::new(1);
        
        stats.update_cpu_usage(0.8);
        stats.update_memory_usage(1024);
        stats.increment_page_faults();
        stats.increment_context_switches();
        
        assert_eq!(stats.cpu_usage, 0.8);
        assert_eq!(stats.memory_usage, 1024);
        assert_eq!(stats.page_faults, 1);
        assert_eq!(stats.context_switches, 1);
    }
}
