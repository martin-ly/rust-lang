use crate::error::ProcessResult;
use crate::types::{ProcessInfo, SystemResources};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};

/// 进程监控器
pub struct ProcessMonitor {
    processes: Arc<Mutex<HashMap<u32, ProcessInfo>>>,
    resources: Arc<Mutex<SystemResources>>,
    last_update: Arc<Mutex<SystemTime>>,
    performance_metrics: Arc<Mutex<PerformanceMetrics>>,
}

/// 性能指标
#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub cpu_usage_history: Vec<(SystemTime, f64)>,
    pub memory_usage_history: Vec<(SystemTime, u64)>,
    pub disk_io_history: Vec<(SystemTime, DiskIOStats)>,
    pub network_io_history: Vec<(SystemTime, NetworkIOStats)>,
    pub max_history_size: usize,
}

/// 磁盘IO统计
#[derive(Debug, Clone)]
#[derive(Default)]
pub struct DiskIOStats {
    pub read_bytes: u64,
    pub write_bytes: u64,
    pub read_operations: u64,
    pub write_operations: u64,
}

/// 网络IO统计
#[derive(Debug, Clone)]
#[derive(Default)]
pub struct NetworkIOStats {
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub packets_sent: u64,
    pub packets_received: u64,
}

impl ProcessMonitor {
    /// 创建新的进程监控器
    pub fn new() -> Self {
        Self {
            processes: Arc::new(Mutex::new(HashMap::new())),
            resources: Arc::new(Mutex::new(SystemResources {
                total_memory: 0,
                available_memory: 0,
                cpu_cores: 0,
                cpu_usage: 0.0,
                total_disk: 0,
                available_disk: 0,
                timestamp: SystemTime::now(),
            })),
            last_update: Arc::new(Mutex::new(SystemTime::now())),
            performance_metrics: Arc::new(Mutex::new(PerformanceMetrics {
                cpu_usage_history: Vec::new(),
                memory_usage_history: Vec::new(),
                disk_io_history: Vec::new(),
                network_io_history: Vec::new(),
                max_history_size: 1000,
            })),
        }
    }

    /// 添加进程到监控
    pub fn add_process(&self, info: ProcessInfo) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        processes.insert(info.pid, info);
        Ok(())
    }

    /// 移除进程监控
    pub fn remove_process(&self, pid: u32) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        processes.remove(&pid);
        Ok(())
    }

    /// 更新进程信息
    pub fn update_process(&self, info: ProcessInfo) -> ProcessResult<()> {
        let mut processes = self.processes.lock().unwrap();
        processes.insert(info.pid, info);
        Ok(())
    }

    /// 获取所有监控的进程
    pub fn get_processes(&self) -> Vec<ProcessInfo> {
        let processes = self.processes.lock().unwrap();
        processes.values().cloned().collect()
    }

    /// 获取特定进程信息
    pub fn get_process(&self, pid: u32) -> Option<ProcessInfo> {
        let processes = self.processes.lock().unwrap();
        processes.get(&pid).cloned()
    }

    /// 更新系统资源信息
    pub fn update_resources(&self, resources: SystemResources) {
        let mut current_resources = self.resources.lock().unwrap();
        *current_resources = resources.clone();

        // 更新性能指标历史
        self.update_performance_metrics(&resources);

        let mut last_update = self.last_update.lock().unwrap();
        *last_update = SystemTime::now();
    }

    /// 获取系统资源信息
    pub fn get_resources(&self) -> SystemResources {
        let resources = self.resources.lock().unwrap();
        resources.clone()
    }

    /// 获取最后更新时间
    pub fn last_update(&self) -> SystemTime {
        let last_update = self.last_update.lock().unwrap();
        *last_update
    }

    /// 检查是否需要更新
    pub fn needs_update(&self, interval: Duration) -> bool {
        let last_update = self.last_update.lock().unwrap();
        last_update.elapsed().unwrap_or(Duration::ZERO) >= interval
    }

    /// 获取进程统计信息
    pub fn get_stats(&self) -> ProcessStats {
        let processes = self.processes.lock().unwrap();
        let total = processes.len();
        let running = processes
            .values()
            .filter(|p| p.status == crate::types::ProcessStatus::Running)
            .count();
        let sleeping = processes
            .values()
            .filter(|p| p.status == crate::types::ProcessStatus::Sleeping)
            .count();
        let stopped = processes
            .values()
            .filter(|p| p.status == crate::types::ProcessStatus::Stopped)
            .count();

        let last_update = self.last_update.lock().unwrap();
        ProcessStats {
            total,
            running,
            sleeping,
            stopped,
            timestamp: *last_update,
        }
    }

    /// 更新性能指标
    fn update_performance_metrics(&self, resources: &SystemResources) {
        let mut metrics = self.performance_metrics.lock().unwrap();
        let now = SystemTime::now();

        // 更新CPU使用率历史
        metrics.cpu_usage_history.push((now, resources.cpu_usage));
        if metrics.cpu_usage_history.len() > metrics.max_history_size {
            metrics.cpu_usage_history.remove(0);
        }

        // 更新内存使用率历史
        let memory_usage = resources.total_memory - resources.available_memory;
        metrics.memory_usage_history.push((now, memory_usage));
        if metrics.memory_usage_history.len() > metrics.max_history_size {
            metrics.memory_usage_history.remove(0);
        }
    }

    /// 获取性能指标
    pub fn get_performance_metrics(&self) -> PerformanceMetrics {
        let metrics = self.performance_metrics.lock().unwrap();
        metrics.clone()
    }

    /// 获取CPU使用率趋势
    pub fn get_cpu_trend(&self, duration: Duration) -> Vec<(SystemTime, f64)> {
        let metrics = self.performance_metrics.lock().unwrap();
        let cutoff = SystemTime::now() - duration;

        metrics
            .cpu_usage_history
            .iter()
            .filter(|(timestamp, _)| *timestamp >= cutoff)
            .cloned()
            .collect()
    }

    /// 获取内存使用率趋势
    pub fn get_memory_trend(&self, duration: Duration) -> Vec<(SystemTime, u64)> {
        let metrics = self.performance_metrics.lock().unwrap();
        let cutoff = SystemTime::now() - duration;

        metrics
            .memory_usage_history
            .iter()
            .filter(|(timestamp, _)| *timestamp >= cutoff)
            .cloned()
            .collect()
    }

    /// 清理旧的历史数据
    pub fn cleanup_old_data(&self, max_age: Duration) {
        let mut metrics = self.performance_metrics.lock().unwrap();
        let cutoff = SystemTime::now() - max_age;

        metrics
            .cpu_usage_history
            .retain(|(timestamp, _)| *timestamp >= cutoff);
        metrics
            .memory_usage_history
            .retain(|(timestamp, _)| *timestamp >= cutoff);
        metrics
            .disk_io_history
            .retain(|(timestamp, _)| *timestamp >= cutoff);
        metrics
            .network_io_history
            .retain(|(timestamp, _)| *timestamp >= cutoff);
    }
}

/// 进程统计信息
#[derive(Debug, Clone)]
pub struct ProcessStats {
    pub total: usize,
    pub running: usize,
    pub sleeping: usize,
    pub stopped: usize,
    pub timestamp: SystemTime,
}

impl Default for ProcessMonitor {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self {
            cpu_usage_history: Vec::new(),
            memory_usage_history: Vec::new(),
            disk_io_history: Vec::new(),
            network_io_history: Vec::new(),
            max_history_size: 1000,
        }
    }
}


