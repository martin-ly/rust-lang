//! 线程亲和性管理
//! 
//! 本模块提供了线程亲和性管理功能：
//! - CPU核心绑定
//! - NUMA节点绑定
//! - 动态亲和性调整
//! - 亲和性监控

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;
use std::collections::HashMap;
use num_cpus;

/// 线程亲和性配置
#[derive(Debug, Clone, PartialEq)]
pub struct ThreadAffinityConfig {
    pub cpu_mask: Vec<usize>,
    pub numa_node: Option<usize>,
    pub dynamic_adjustment: bool,
    pub migration_threshold: f64,
}

impl Default for ThreadAffinityConfig {
    fn default() -> Self {
        Self {
            cpu_mask: (0..num_cpus::get()).collect(),
            numa_node: None,
            dynamic_adjustment: false,
            migration_threshold: 0.8,
        }
    }
}

/// 线程亲和性管理器
pub struct ThreadAffinityManager {
    config: Arc<Mutex<ThreadAffinityConfig>>,
    thread_affinities: Arc<Mutex<HashMap<usize, ThreadAffinityConfig>>>,
    performance_stats: Arc<Mutex<HashMap<usize, PerformanceStats>>>,
    migration_enabled: AtomicBool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PerformanceStats {
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub cache_misses: usize,
    pub context_switches: usize,
    pub last_updated: std::time::Instant,
}

impl ThreadAffinityManager {
    pub fn new() -> Self {
        Self {
            config: Arc::new(Mutex::new(ThreadAffinityConfig::default())),
            thread_affinities: Arc::new(Mutex::new(HashMap::new())),
            performance_stats: Arc::new(Mutex::new(HashMap::new())),
            migration_enabled: AtomicBool::new(true),
        }
    }
    
    pub fn set_thread_affinity(&self, thread_id: usize, config: ThreadAffinityConfig) -> Result<(), String> {
        // 验证CPU掩码
        let total_cpus = num_cpus::get();
        for &cpu_id in &config.cpu_mask {
            if cpu_id >= total_cpus {
                return Err(format!("无效的CPU ID: {}", cpu_id));
            }
        }
        
        // 设置线程亲和性
        self.set_cpu_affinity(thread_id, &config.cpu_mask)?;
        
        // 设置NUMA节点亲和性
        if let Some(numa_node) = config.numa_node {
            self.set_numa_affinity(thread_id, numa_node)?;
        }
        
        // 记录配置
        let mut affinities = self.thread_affinities.lock().unwrap();
        affinities.insert(thread_id, config);
        
        Ok(())
    }
    
    fn set_cpu_affinity(&self, thread_id: usize, cpu_mask: &[usize]) -> Result<(), String> {
        // 这里应该调用操作系统特定的API来设置CPU亲和性
        // 由于Rust标准库不直接支持，这里使用模拟实现
        
        #[cfg(target_os = "linux")]
        {
            // Linux: 使用sched_setaffinity
            self.set_linux_cpu_affinity(thread_id, cpu_mask)?;
        }
        
        #[cfg(target_os = "windows")]
        {
            // Windows: 使用SetThreadAffinityMask
            self.set_windows_cpu_affinity(thread_id, cpu_mask)?;
        }
        
        #[cfg(target_os = "macos")]
        {
            // macOS: 使用thread_policy_set
            self.set_macos_cpu_affinity(thread_id, cpu_mask)?;
        }
        
        Ok(())
    }
    
    #[cfg(target_os = "linux")]
    fn set_linux_cpu_affinity(&self, thread_id: usize, cpu_mask: &[usize]) -> Result<(), String> {
        // 模拟Linux CPU亲和性设置
        println!("设置Linux线程 {} 的CPU亲和性: {:?}", thread_id, cpu_mask);
        Ok(())
    }
    
    #[cfg(target_os = "windows")]
    fn set_windows_cpu_affinity(&self, thread_id: usize, cpu_mask: &[usize]) -> Result<(), String> {
        // 模拟Windows CPU亲和性设置
        println!("设置Windows线程 {} 的CPU亲和性: {:?}", thread_id, cpu_mask);
        Ok(())
    }
    
    #[cfg(target_os = "macos")]
    fn set_macos_cpu_affinity(&self, thread_id: usize, cpu_mask: &[usize]) -> Result<(), String> {
        // 模拟macOS CPU亲和性设置
        println!("设置macOS线程 {} 的CPU亲和性: {:?}", thread_id, cpu_mask);
        Ok(())
    }
    
    fn set_numa_affinity(&self, thread_id: usize, numa_node: usize) -> Result<(), String> {
        // 模拟NUMA节点亲和性设置
        println!("设置线程 {} 的NUMA节点亲和性: {}", thread_id, numa_node);
        Ok(())
    }
    
    pub fn get_thread_affinity(&self, thread_id: usize) -> Option<ThreadAffinityConfig> {
        let affinities = self.thread_affinities.lock().unwrap();
        affinities.get(&thread_id).cloned()
    }
    
    pub fn update_performance_stats(&self, thread_id: usize, stats: PerformanceStats) {
        let mut performance_stats = self.performance_stats.lock().unwrap();
        performance_stats.insert(thread_id, stats);
    }
    
    pub fn get_performance_stats(&self, thread_id: usize) -> Option<PerformanceStats> {
        let performance_stats = self.performance_stats.lock().unwrap();
        performance_stats.get(&thread_id).cloned()
    }
    
    pub fn enable_migration(&self, enabled: bool) {
        self.migration_enabled.store(enabled, Ordering::Relaxed);
    }
    
    pub fn is_migration_enabled(&self) -> bool {
        self.migration_enabled.load(Ordering::Relaxed)
    }
    
    pub fn check_and_migrate(&self) -> Result<(), String> {
        if !self.is_migration_enabled() {
            return Ok(());
        }
        
        let config = self.config.lock().unwrap();
        if !config.dynamic_adjustment {
            return Ok(());
        }
        
        let performance_stats = self.performance_stats.lock().unwrap();
        let affinities = self.thread_affinities.lock().unwrap();
        
        for (thread_id, stats) in performance_stats.iter() {
            if stats.cpu_usage > config.migration_threshold {
                // 高CPU使用率，考虑迁移到其他核心
                if let Some(current_affinity) = affinities.get(thread_id) {
                    let new_cpu_mask = self.find_better_cpu_mask(&current_affinity.cpu_mask);
                    if new_cpu_mask != current_affinity.cpu_mask {
                        let new_config = ThreadAffinityConfig {
                            cpu_mask: new_cpu_mask,
                            numa_node: current_affinity.numa_node,
                            dynamic_adjustment: current_affinity.dynamic_adjustment,
                            migration_threshold: current_affinity.migration_threshold,
                        };
                        
                        self.set_thread_affinity(*thread_id, new_config)?;
                    }
                }
            }
        }
        
        Ok(())
    }
    
    fn find_better_cpu_mask(&self, current_mask: &[usize]) -> Vec<usize> {
        let total_cpus = num_cpus::get();
        let mut available_cpus: Vec<usize> = (0..total_cpus).collect();
        
        // 移除当前使用的CPU
        for &cpu in current_mask {
            available_cpus.retain(|&x| x != cpu);
        }
        
        // 选择负载较轻的CPU
        if available_cpus.is_empty() {
            current_mask.to_vec()
        } else {
            vec![available_cpus[0]]
        }
    }
    
    pub fn get_optimal_affinity(&self, workload_type: WorkloadType) -> ThreadAffinityConfig {
        match workload_type {
            WorkloadType::CpuIntensive => {
                // CPU密集型任务：绑定到特定核心
                ThreadAffinityConfig {
                    cpu_mask: vec![0],
                    numa_node: Some(0),
                    dynamic_adjustment: false,
                    migration_threshold: 0.9,
                }
            }
            WorkloadType::MemoryIntensive => {
                // 内存密集型任务：绑定到NUMA节点
                ThreadAffinityConfig {
                    cpu_mask: (0..num_cpus::get()).collect(),
                    numa_node: Some(0),
                    dynamic_adjustment: true,
                    migration_threshold: 0.7,
                }
            }
            WorkloadType::IoIntensive => {
                // I/O密集型任务：允许动态迁移
                ThreadAffinityConfig {
                    cpu_mask: (0..num_cpus::get()).collect(),
                    numa_node: None,
                    dynamic_adjustment: true,
                    migration_threshold: 0.5,
                }
            }
            WorkloadType::Mixed => {
                // 混合工作负载：平衡配置
                ThreadAffinityConfig {
                    cpu_mask: (0..num_cpus::get()).collect(),
                    numa_node: None,
                    dynamic_adjustment: true,
                    migration_threshold: 0.8,
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum WorkloadType {
    CpuIntensive,
    MemoryIntensive,
    IoIntensive,
    Mixed,
}

/// 线程亲和性监控器
pub struct ThreadAffinityMonitor {
    manager: Arc<ThreadAffinityManager>,
    monitoring_enabled: AtomicBool,
    monitoring_interval: Duration,
}

impl ThreadAffinityMonitor {
    pub fn new(manager: Arc<ThreadAffinityManager>) -> Self {
        Self {
            manager,
            monitoring_enabled: AtomicBool::new(true),
            monitoring_interval: Duration::from_secs(1),
        }
    }
    
    pub fn start_monitoring(&self) {
        let manager = self.manager.clone();
        let monitoring_enabled = Arc::new(self.monitoring_enabled.load(Ordering::Relaxed));
        let interval = self.monitoring_interval;
        
        thread::spawn(move || {
            while *monitoring_enabled {
                // 收集性能统计
                manager.collect_performance_stats();
                
                // 检查并执行迁移
                if let Err(e) = manager.check_and_migrate() {
                    eprintln!("线程迁移失败: {}", e);
                }
                
                thread::sleep(interval);
            }
        });
    }
    
    pub fn stop_monitoring(&self) {
        self.monitoring_enabled.store(false, Ordering::Relaxed);
    }
    
    pub fn set_monitoring_interval(&mut self, interval: Duration) {
        self.monitoring_interval = interval;
    }
}

impl ThreadAffinityManager {
    fn collect_performance_stats(&self) {
        // 模拟收集性能统计
        let mut performance_stats = self.performance_stats.lock().unwrap();
        
        for (_thread_id, stats) in performance_stats.iter_mut() {
            // 模拟更新CPU使用率
            stats.cpu_usage = (stats.cpu_usage + 0.1) % 1.0;
            stats.memory_usage = (stats.memory_usage + 0.05) % 1.0;
            stats.cache_misses += 1;
            stats.context_switches += 1;
            stats.last_updated = std::time::Instant::now();
        }
    }
}

/// 运行所有线程亲和性示例
pub fn demonstrate_thread_affinity() {
    println!("=== 线程亲和性演示 ===");
    
    let manager = Arc::new(ThreadAffinityManager::new());
    
    // 设置不同工作负载的亲和性
    let cpu_intensive_config = manager.get_optimal_affinity(WorkloadType::CpuIntensive);
    let memory_intensive_config = manager.get_optimal_affinity(WorkloadType::MemoryIntensive);
    let io_intensive_config = manager.get_optimal_affinity(WorkloadType::IoIntensive);
    
    // 创建线程并设置亲和性
    let handles: Vec<_> = vec![
        (0, cpu_intensive_config),
        (1, memory_intensive_config),
        (2, io_intensive_config),
    ]
    .into_iter()
    .map(|(thread_id, config)| {
        let manager = manager.clone();
        thread::spawn(move || {
            // 设置线程亲和性
            if let Err(e) = manager.set_thread_affinity(thread_id, config) {
                eprintln!("设置线程亲和性失败: {}", e);
                return;
            }
            
            // 模拟工作负载
            for i in 0..1000 {
                // 模拟CPU密集型工作
                let _ = (0..1000).fold(0, |acc, x| acc + x);
                
                // 更新性能统计
                let stats = PerformanceStats {
                    cpu_usage: 0.8,
                    memory_usage: 0.3,
                    cache_misses: i,
                    context_switches: i / 10,
                    last_updated: std::time::Instant::now(),
                };
                manager.update_performance_stats(thread_id, stats);
                
                if i % 100 == 0 {
                    println!("线程 {} 完成 {} 次迭代", thread_id, i);
                }
            }
        })
    })
    .collect();
    
    // 启动监控
    let monitor = ThreadAffinityMonitor::new(manager.clone());
    monitor.start_monitoring();
    
    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }
    
    // 停止监控
    monitor.stop_monitoring();
    
    // 显示最终统计
    for thread_id in 0..3 {
        if let Some(stats) = manager.get_performance_stats(thread_id) {
            println!("线程 {} 最终统计:", thread_id);
            println!("  CPU使用率: {:.2}%", stats.cpu_usage * 100.0);
            println!("  内存使用率: {:.2}%", stats.memory_usage * 100.0);
            println!("  缓存未命中: {}", stats.cache_misses);
            println!("  上下文切换: {}", stats.context_switches);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_thread_affinity_manager() {
        let manager = ThreadAffinityManager::new();
        let config = ThreadAffinityConfig::default();
        
        assert!(manager.set_thread_affinity(1, config.clone()).is_ok());
        assert_eq!(manager.get_thread_affinity(1), Some(config));
    }
    
    #[test]
    fn test_workload_affinity() {
        let manager = ThreadAffinityManager::new();
        
        let cpu_config = manager.get_optimal_affinity(WorkloadType::CpuIntensive);
        assert_eq!(cpu_config.cpu_mask.len(), 1);
        assert!(cpu_config.numa_node.is_some());
        
        let io_config = manager.get_optimal_affinity(WorkloadType::IoIntensive);
        assert!(io_config.dynamic_adjustment);
        assert!(io_config.numa_node.is_none());
    }
    
    #[test]
    fn test_performance_stats() {
        let manager = ThreadAffinityManager::new();
        let stats = PerformanceStats {
            cpu_usage: 0.8,
            memory_usage: 0.3,
            cache_misses: 100,
            context_switches: 10,
            last_updated: std::time::Instant::now(),
        };
        
        manager.update_performance_stats(1, stats.clone());
        assert_eq!(manager.get_performance_stats(1), Some(stats));
    }
}
