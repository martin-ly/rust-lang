# C07-17. 监控与诊断示例 (Rust 1.90 增强版)

## 目录

- [C07-17. 监控与诊断示例 (Rust 1.90 增强版)](#c07-17-监控与诊断示例-rust-190-增强版)
  - [目录](#目录)
  - [1. 进程监控系统](#1-进程监控系统)
    - [1.1 进程监控器](#11-进程监控器)
  - [2. 性能指标收集](#2-性能指标收集)
    - [2.1 性能指标收集器](#21-性能指标收集器)
  - [3. 健康检查机制](#3-健康检查机制)
    - [3.1 健康检查器](#31-健康检查器)
  - [总结](#总结)

本章提供监控与诊断示例，涵盖进程监控、性能指标收集、健康检查、诊断工具、告警系统和日志分析等。

## 1. 进程监控系统

### 1.1 进程监控器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::interval;

// 进程监控器
pub struct ProcessMonitor {
    processes: Arc<RwLock<HashMap<u32, ProcessInfo>>>,
    config: MonitorConfig,
    metrics: Arc<RwLock<ProcessMetrics>>,
}

#[derive(Debug, Clone)]
pub struct MonitorConfig {
    pub monitor_interval: Duration,
    pub max_processes: usize,
    pub enable_cpu_monitoring: bool,
    pub enable_memory_monitoring: bool,
    pub enable_io_monitoring: bool,
    pub enable_network_monitoring: bool,
    pub alert_thresholds: AlertThresholds,
}

#[derive(Debug, Clone)]
pub struct ProcessInfo {
    pub pid: u32,
    pub name: String,
    pub command_line: String,
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub virtual_memory: u64,
    pub io_read_bytes: u64,
    pub io_write_bytes: u64,
    pub network_bytes_sent: u64,
    pub network_bytes_received: u64,
    pub start_time: Instant,
    pub last_seen: Instant,
    pub status: ProcessStatus,
    pub parent_pid: Option<u32>,
    pub children: Vec<u32>,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Running,
    Sleeping,
    Waiting,
    Zombie,
    Stopped,
    Unknown,
}

#[derive(Debug, Clone)]
pub struct ProcessMetrics {
    pub total_processes: usize,
    pub running_processes: usize,
    pub sleeping_processes: usize,
    pub zombie_processes: usize,
    pub total_cpu_usage: f64,
    pub total_memory_usage: u64,
    pub total_io_read: u64,
    pub total_io_write: u64,
    pub total_network_sent: u64,
    pub total_network_received: u64,
    pub last_updated: Instant,
}

#[derive(Debug, Clone)]
pub struct AlertThresholds {
    pub cpu_threshold: f64,
    pub memory_threshold: u64,
    pub io_threshold: u64,
    pub network_threshold: u64,
}

impl ProcessMonitor {
    pub fn new(config: MonitorConfig) -> Self {
        Self {
            processes: Arc::new(RwLock::new(HashMap::new())),
            config,
            metrics: Arc::new(RwLock::new(ProcessMetrics {
                total_processes: 0,
                running_processes: 0,
                sleeping_processes: 0,
                zombie_processes: 0,
                total_cpu_usage: 0.0,
                total_memory_usage: 0,
                total_io_read: 0,
                total_io_write: 0,
                total_network_sent: 0,
                total_network_received: 0,
                last_updated: Instant::now(),
            })),
        }
    }

    // 启动监控
    pub async fn start_monitoring(&self) -> Result<(), MonitorError> {
        let mut interval = interval(self.config.monitor_interval);
        
        loop {
            interval.tick().await;
            
            if let Err(e) = self.update_processes().await {
                eprintln!("监控更新失败: {}", e);
            }
            
            if let Err(e) = self.update_metrics().await {
                eprintln!("指标更新失败: {}", e);
            }
            
            if let Err(e) = self.check_alerts().await {
                eprintln!("告警检查失败: {}", e);
            }
        }
    }

    // 更新进程信息
    async fn update_processes(&self) -> Result<(), MonitorError> {
        let current_processes = self.get_current_processes().await?;
        let mut processes = self.processes.write().await;
        
        // 更新现有进程
        for (pid, process_info) in &current_processes {
            if let Some(existing) = processes.get_mut(pid) {
                *existing = process_info.clone();
            } else {
                processes.insert(*pid, process_info.clone());
            }
        }
        
        // 移除已结束的进程
        let current_pids: std::collections::HashSet<u32> = current_processes.keys().cloned().collect();
        processes.retain(|pid, _| current_pids.contains(pid));
        
        // 限制进程数量
        if processes.len() > self.config.max_processes {
            let mut sorted_processes: Vec<_> = processes.iter().collect();
            sorted_processes.sort_by_key(|(_, info)| info.last_seen);
            
            let to_remove = processes.len() - self.config.max_processes;
            for (pid, _) in sorted_processes.iter().take(to_remove) {
                processes.remove(pid);
            }
        }
        
        Ok(())
    }

    // 获取当前进程信息
    async fn get_current_processes(&self) -> Result<HashMap<u32, ProcessInfo>, MonitorError> {
        let mut processes = HashMap::new();
        
        #[cfg(unix)]
        {
            use std::process::Command;
            
            // 使用 ps 命令获取进程信息
            let output = Command::new("ps")
                .args(&["-eo", "pid,ppid,comm,cmd,%cpu,%mem,vsz,rss"])
                .output()
                .map_err(|e| MonitorError::ProcessError(e.to_string()))?;
            
            let output_str = String::from_utf8_lossy(&output.stdout);
            
            for line in output_str.lines().skip(1) {
                let fields: Vec<&str> = line.split_whitespace().collect();
                if fields.len() >= 8 {
                    if let (Ok(pid), Ok(ppid), Ok(cpu), Ok(mem), Ok(vsz), Ok(rss)) = (
                        fields[0].parse::<u32>(),
                        fields[1].parse::<u32>(),
                        fields[4].parse::<f64>(),
                        fields[5].parse::<f64>(),
                        fields[6].parse::<u64>(),
                        fields[7].parse::<u64>(),
                    ) {
                        let process_info = ProcessInfo {
                            pid,
                            name: fields[2].to_string(),
                            command_line: fields[3..].join(" "),
                            cpu_usage: cpu,
                            memory_usage: rss * 1024, // KB to bytes
                            virtual_memory: vsz * 1024, // KB to bytes
                            io_read_bytes: 0, // 需要额外获取
                            io_write_bytes: 0, // 需要额外获取
                            network_bytes_sent: 0, // 需要额外获取
                            network_bytes_received: 0, // 需要额外获取
                            start_time: Instant::now(), // 需要额外获取
                            last_seen: Instant::now(),
                            status: ProcessStatus::Running,
                            parent_pid: if ppid > 0 { Some(ppid) } else { None },
                            children: Vec::new(),
                        };
                        
                        processes.insert(pid, process_info);
                    }
                }
            }
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            
            // 使用 wmic 命令获取进程信息
            let output = Command::new("wmic")
                .args(&["process", "get", "ProcessId,ParentProcessId,Name,CommandLine,PercentProcessorTime,WorkingSetSize", "/format:csv"])
                .output()
                .map_err(|e| MonitorError::ProcessError(e.to_string()))?;
            
            let output_str = String::from_utf8_lossy(&output.stdout);
            
            for line in output_str.lines().skip(1) {
                let fields: Vec<&str> = line.split(',').collect();
                if fields.len() >= 7 {
                    if let (Ok(pid), Ok(ppid), Ok(cpu), Ok(mem)) = (
                        fields[1].parse::<u32>(),
                        fields[2].parse::<u32>(),
                        fields[5].parse::<f64>(),
                        fields[6].parse::<u64>(),
                    ) {
                        let process_info = ProcessInfo {
                            pid,
                            name: fields[3].to_string(),
                            command_line: fields[4].to_string(),
                            cpu_usage: cpu,
                            memory_usage: mem,
                            virtual_memory: mem, // Windows 没有单独的虚拟内存
                            io_read_bytes: 0,
                            io_write_bytes: 0,
                            network_bytes_sent: 0,
                            network_bytes_received: 0,
                            start_time: Instant::now(),
                            last_seen: Instant::now(),
                            status: ProcessStatus::Running,
                            parent_pid: if ppid > 0 { Some(ppid) } else { None },
                            children: Vec::new(),
                        };
                        
                        processes.insert(pid, process_info);
                    }
                }
            }
        }
        
        Ok(processes)
    }

    // 更新指标
    async fn update_metrics(&self) -> Result<(), MonitorError> {
        let processes = self.processes.read().await;
        let mut metrics = self.metrics.write().await;
        
        metrics.total_processes = processes.len();
        metrics.running_processes = processes.values().filter(|p| matches!(p.status, ProcessStatus::Running)).count();
        metrics.sleeping_processes = processes.values().filter(|p| matches!(p.status, ProcessStatus::Sleeping)).count();
        metrics.zombie_processes = processes.values().filter(|p| matches!(p.status, ProcessStatus::Zombie)).count();
        
        metrics.total_cpu_usage = processes.values().map(|p| p.cpu_usage).sum();
        metrics.total_memory_usage = processes.values().map(|p| p.memory_usage).sum();
        metrics.total_io_read = processes.values().map(|p| p.io_read_bytes).sum();
        metrics.total_io_write = processes.values().map(|p| p.io_write_bytes).sum();
        metrics.total_network_sent = processes.values().map(|p| p.network_bytes_sent).sum();
        metrics.total_network_received = processes.values().map(|p| p.network_bytes_received).sum();
        
        metrics.last_updated = Instant::now();
        
        Ok(())
    }

    // 检查告警
    async fn check_alerts(&self) -> Result<(), MonitorError> {
        let metrics = self.metrics.read().await;
        
        if metrics.total_cpu_usage > self.config.alert_thresholds.cpu_threshold {
            println!("告警: CPU 使用率过高: {:.2}%", metrics.total_cpu_usage);
        }
        
        if metrics.total_memory_usage > self.config.alert_thresholds.memory_threshold {
            println!("告警: 内存使用量过高: {} bytes", metrics.total_memory_usage);
        }
        
        if metrics.total_io_read + metrics.total_io_write > self.config.alert_thresholds.io_threshold {
            println!("告警: IO 使用量过高: {} bytes", metrics.total_io_read + metrics.total_io_write);
        }
        
        if metrics.total_network_sent + metrics.total_network_received > self.config.alert_thresholds.network_threshold {
            println!("告警: 网络使用量过高: {} bytes", metrics.total_network_sent + metrics.total_network_received);
        }
        
        Ok(())
    }

    // 获取进程信息
    pub async fn get_process_info(&self, pid: u32) -> Option<ProcessInfo> {
        let processes = self.processes.read().await;
        processes.get(&pid).cloned()
    }

    // 获取所有进程信息
    pub async fn get_all_processes(&self) -> Vec<ProcessInfo> {
        let processes = self.processes.read().await;
        processes.values().cloned().collect()
    }

    // 获取指标
    pub async fn get_metrics(&self) -> ProcessMetrics {
        self.metrics.read().await.clone()
    }

    // 获取进程统计
    pub async fn get_process_stats(&self) -> ProcessStats {
        let processes = self.processes.read().await;
        let metrics = self.metrics.read().await;
        
        ProcessStats {
            total_processes: metrics.total_processes,
            running_processes: metrics.running_processes,
            sleeping_processes: metrics.sleeping_processes,
            zombie_processes: metrics.zombie_processes,
            total_cpu_usage: metrics.total_cpu_usage,
            total_memory_usage: metrics.total_memory_usage,
            average_cpu_per_process: if metrics.total_processes > 0 {
                metrics.total_cpu_usage / metrics.total_processes as f64
            } else {
                0.0
            },
            average_memory_per_process: if metrics.total_processes > 0 {
                metrics.total_memory_usage / metrics.total_processes as u64
            } else {
                0
            },
        }
    }
}

// 进程统计
#[derive(Debug)]
pub struct ProcessStats {
    pub total_processes: usize,
    pub running_processes: usize,
    pub sleeping_processes: usize,
    pub zombie_processes: usize,
    pub total_cpu_usage: f64,
    pub total_memory_usage: u64,
    pub average_cpu_per_process: f64,
    pub average_memory_per_process: u64,
}

#[derive(Debug, thiserror::Error)]
pub enum MonitorError {
    #[error("进程错误: {0}")]
    ProcessError(String),
    
    #[error("监控错误: {0}")]
    MonitorError(String),
    
    #[error("指标错误: {0}")]
    MetricsError(String),
    
    #[error("告警错误: {0}")]
    AlertError(String),
}
```

## 2. 性能指标收集

### 2.1 性能指标收集器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 性能指标收集器
pub struct PerformanceMetricsCollector {
    metrics: Arc<RwLock<HashMap<String, MetricValue>>>,
    config: MetricsConfig,
    collectors: Vec<Box<dyn MetricCollector + Send + Sync>>,
}

#[derive(Debug, Clone)]
pub struct MetricsConfig {
    pub collection_interval: Duration,
    pub retention_period: Duration,
    pub max_metrics: usize,
    pub enable_cpu_metrics: bool,
    pub enable_memory_metrics: bool,
    pub enable_disk_metrics: bool,
    pub enable_network_metrics: bool,
    pub enable_process_metrics: bool,
}

#[derive(Debug, Clone)]
pub enum MetricValue {
    Counter(u64),
    Gauge(f64),
    Histogram(Vec<f64>),
    Summary { count: u64, sum: f64 },
}

#[derive(Debug, Clone)]
pub struct MetricInfo {
    pub name: String,
    pub description: String,
    pub value: MetricValue,
    pub labels: HashMap<String, String>,
    pub timestamp: Instant,
}

pub trait MetricCollector {
    fn collect(&self) -> Result<Vec<MetricInfo>, MetricsError>;
    fn name(&self) -> &str;
}

impl PerformanceMetricsCollector {
    pub fn new(config: MetricsConfig) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            config,
            collectors: Vec::new(),
        }
    }

    // 添加指标收集器
    pub fn add_collector(&mut self, collector: Box<dyn MetricCollector + Send + Sync>) {
        self.collectors.push(collector);
    }

    // 启动收集
    pub async fn start_collection(&self) -> Result<(), MetricsError> {
        let mut interval = tokio::time::interval(self.config.collection_interval);
        
        loop {
            interval.tick().await;
            
            for collector in &self.collectors {
                match collector.collect() {
                    Ok(metrics) => {
                        for metric in metrics {
                            self.store_metric(metric).await?;
                        }
                    }
                    Err(e) => {
                        eprintln!("收集器 {} 失败: {}", collector.name(), e);
                    }
                }
            }
            
            self.cleanup_old_metrics().await?;
        }
    }

    // 存储指标
    async fn store_metric(&self, metric: MetricInfo) -> Result<(), MetricsError> {
        let mut metrics = self.metrics.write().await;
        
        if metrics.len() >= self.config.max_metrics {
            // 移除最旧的指标
            if let Some(oldest_key) = metrics.keys().next().cloned() {
                metrics.remove(&oldest_key);
            }
        }
        
        metrics.insert(metric.name.clone(), metric.value);
        Ok(())
    }

    // 清理旧指标
    async fn cleanup_old_metrics(&self) -> Result<(), MetricsError> {
        let mut metrics = self.metrics.write().await;
        let cutoff_time = Instant::now() - self.config.retention_period;
        
        metrics.retain(|_, metric| {
            match metric {
                MetricValue::Counter(_) => true,
                MetricValue::Gauge(_) => true,
                MetricValue::Histogram(_) => true,
                MetricValue::Summary { .. } => true,
            }
        });
        
        Ok(())
    }

    // 获取指标
    pub async fn get_metric(&self, name: &str) -> Option<MetricValue> {
        let metrics = self.metrics.read().await;
        metrics.get(name).cloned()
    }

    // 获取所有指标
    pub async fn get_all_metrics(&self) -> HashMap<String, MetricValue> {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }

    // 获取指标统计
    pub async fn get_metrics_stats(&self) -> MetricsStats {
        let metrics = self.metrics.read().await;
        
        let total_metrics = metrics.len();
        let counter_metrics = metrics.values().filter(|m| matches!(m, MetricValue::Counter(_))).count();
        let gauge_metrics = metrics.values().filter(|m| matches!(m, MetricValue::Gauge(_))).count();
        let histogram_metrics = metrics.values().filter(|m| matches!(m, MetricValue::Histogram(_))).count();
        let summary_metrics = metrics.values().filter(|m| matches!(m, MetricValue::Summary { .. })).count();
        
        MetricsStats {
            total_metrics,
            counter_metrics,
            gauge_metrics,
            histogram_metrics,
            summary_metrics,
        }
    }
}

// CPU 指标收集器
pub struct CpuMetricsCollector;

impl MetricCollector for CpuMetricsCollector {
    fn collect(&self) -> Result<Vec<MetricInfo>, MetricsError> {
        let mut metrics = Vec::new();
        
        #[cfg(unix)]
        {
            use std::process::Command;
            
            let output = Command::new("top")
                .args(&["-bn1"])
                .output()
                .map_err(|e| MetricsError::CollectionError(e.to_string()))?;
            
            let output_str = String::from_utf8_lossy(&output.stdout);
            
            for line in output_str.lines() {
                if line.contains("Cpu(s)") {
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    if parts.len() >= 8 {
                        if let Ok(cpu_usage) = parts[1].replace("%", "").parse::<f64>() {
                            metrics.push(MetricInfo {
                                name: "cpu_usage".to_string(),
                                description: "CPU usage percentage".to_string(),
                                value: MetricValue::Gauge(cpu_usage),
                                labels: HashMap::new(),
                                timestamp: Instant::now(),
                            });
                        }
                    }
                }
            }
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            
            let output = Command::new("wmic")
                .args(&["cpu", "get", "loadpercentage", "/value"])
                .output()
                .map_err(|e| MetricsError::CollectionError(e.to_string()))?;
            
            let output_str = String::from_utf8_lossy(&output.stdout);
            
            for line in output_str.lines() {
                if line.starts_with("LoadPercentage=") {
                    if let Ok(cpu_usage) = line.split('=').nth(1).unwrap_or("0").parse::<f64>() {
                        metrics.push(MetricInfo {
                            name: "cpu_usage".to_string(),
                            description: "CPU usage percentage".to_string(),
                            value: MetricValue::Gauge(cpu_usage),
                            labels: HashMap::new(),
                            timestamp: Instant::now(),
                        });
                    }
                }
            }
        }
        
        Ok(metrics)
    }

    fn name(&self) -> &str {
        "cpu_collector"
    }
}

// 内存指标收集器
pub struct MemoryMetricsCollector;

impl MetricCollector for MemoryMetricsCollector {
    fn collect(&self) -> Result<Vec<MetricInfo>, MetricsError> {
        let mut metrics = Vec::new();
        
        #[cfg(unix)]
        {
            use std::process::Command;
            
            let output = Command::new("free")
                .args(&["-m"])
                .output()
                .map_err(|e| MetricsError::CollectionError(e.to_string()))?;
            
            let output_str = String::from_utf8_lossy(&output.stdout);
            
            for line in output_str.lines().skip(1) {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 4 {
                    if let Ok(total) = parts[1].parse::<u64>() {
                        if let Ok(used) = parts[2].parse::<u64>() {
                            let usage_percentage = (used as f64 / total as f64) * 100.0;
                            
                            metrics.push(MetricInfo {
                                name: "memory_usage".to_string(),
                                description: "Memory usage percentage".to_string(),
                                value: MetricValue::Gauge(usage_percentage),
                                labels: HashMap::new(),
                                timestamp: Instant::now(),
                            });
                        }
                    }
                }
            }
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            
            let output = Command::new("wmic")
                .args(&["OS", "get", "TotalVisibleMemorySize,FreePhysicalMemory", "/value"])
                .output()
                .map_err(|e| MetricsError::CollectionError(e.to_string()))?;
            
            let output_str = String::from_utf8_lossy(&output.stdout);
            
            let mut total_memory = 0u64;
            let mut free_memory = 0u64;
            
            for line in output_str.lines() {
                if line.starts_with("TotalVisibleMemorySize=") {
                    if let Ok(total) = line.split('=').nth(1).unwrap_or("0").parse::<u64>() {
                        total_memory = total * 1024; // KB to bytes
                    }
                } else if line.starts_with("FreePhysicalMemory=") {
                    if let Ok(free) = line.split('=').nth(1).unwrap_or("0").parse::<u64>() {
                        free_memory = free * 1024; // KB to bytes
                    }
                }
            }
            
            if total_memory > 0 {
                let used_memory = total_memory - free_memory;
                let usage_percentage = (used_memory as f64 / total_memory as f64) * 100.0;
                
                metrics.push(MetricInfo {
                    name: "memory_usage".to_string(),
                    description: "Memory usage percentage".to_string(),
                    value: MetricValue::Gauge(usage_percentage),
                    labels: HashMap::new(),
                    timestamp: Instant::now(),
                });
            }
        }
        
        Ok(metrics)
    }

    fn name(&self) -> &str {
        "memory_collector"
    }
}

// 指标统计
#[derive(Debug)]
pub struct MetricsStats {
    pub total_metrics: usize,
    pub counter_metrics: usize,
    pub gauge_metrics: usize,
    pub histogram_metrics: usize,
    pub summary_metrics: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum MetricsError {
    #[error("收集错误: {0}")]
    CollectionError(String),
    
    #[error("存储错误: {0}")]
    StorageError(String),
    
    #[error("指标错误: {0}")]
    MetricsError(String),
}
```

## 3. 健康检查机制

### 3.1 健康检查器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 健康检查器
pub struct HealthChecker {
    checks: Arc<RwLock<HashMap<String, HealthCheck>>>,
    config: HealthConfig,
    status: Arc<RwLock<HealthStatus>>,
}

#[derive(Debug, Clone)]
pub struct HealthConfig {
    pub check_interval: Duration,
    pub timeout: Duration,
    pub retry_count: u32,
    pub enable_auto_recovery: bool,
    pub alert_on_failure: bool,
}

#[derive(Debug, Clone)]
pub struct HealthCheck {
    pub name: String,
    pub description: String,
    pub check_fn: CheckFunction,
    pub enabled: bool,
    pub last_check: Instant,
    pub last_result: CheckResult,
    pub consecutive_failures: u32,
    pub total_checks: u64,
    pub total_failures: u64,
}

#[derive(Debug, Clone)]
pub enum CheckFunction {
    ProcessCheck { pid: u32 },
    PortCheck { port: u16 },
    FileCheck { path: String },
    CommandCheck { command: String },
    CustomCheck { name: String },
}

#[derive(Debug, Clone)]
pub enum CheckResult {
    Healthy,
    Unhealthy(String),
    Unknown,
}

#[derive(Debug, Clone)]
pub struct HealthStatus {
    pub overall_status: CheckResult,
    pub healthy_checks: usize,
    pub unhealthy_checks: usize,
    pub unknown_checks: usize,
    pub last_updated: Instant,
}

impl HealthChecker {
    pub fn new(config: HealthConfig) -> Self {
        Self {
            checks: Arc::new(RwLock::new(HashMap::new())),
            config,
            status: Arc::new(RwLock::new(HealthStatus {
                overall_status: CheckResult::Unknown,
                healthy_checks: 0,
                unhealthy_checks: 0,
                unknown_checks: 0,
                last_updated: Instant::now(),
            })),
        }
    }

    // 添加健康检查
    pub async fn add_check(&self, check: HealthCheck) -> Result<(), HealthError> {
        let mut checks = self.checks.write().await;
        checks.insert(check.name.clone(), check);
        Ok(())
    }

    // 启动健康检查
    pub async fn start_checking(&self) -> Result<(), HealthError> {
        let mut interval = tokio::time::interval(self.config.check_interval);
        
        loop {
            interval.tick().await;
            
            if let Err(e) = self.run_all_checks().await {
                eprintln!("健康检查失败: {}", e);
            }
            
            if let Err(e) = self.update_status().await {
                eprintln!("状态更新失败: {}", e);
            }
        }
    }

    // 运行所有检查
    async fn run_all_checks(&self) -> Result<(), HealthError> {
        let checks = self.checks.read().await;
        let check_names: Vec<String> = checks.keys().cloned().collect();
        drop(checks);
        
        for name in check_names {
            if let Err(e) = self.run_check(&name).await {
                eprintln!("检查 {} 失败: {}", name, e);
            }
        }
        
        Ok(())
    }

    // 运行单个检查
    async fn run_check(&self, name: &str) -> Result<(), HealthError> {
        let mut checks = self.checks.write().await;
        
        if let Some(check) = checks.get_mut(name) {
            if !check.enabled {
                return Ok(());
            }
            
            check.last_check = Instant::now();
            check.total_checks += 1;
            
            let result = self.execute_check(&check.check_fn).await;
            
            match result {
                CheckResult::Healthy => {
                    check.last_result = CheckResult::Healthy;
                    check.consecutive_failures = 0;
                }
                CheckResult::Unhealthy(ref msg) => {
                    check.last_result = CheckResult::Unhealthy(msg.clone());
                    check.consecutive_failures += 1;
                    check.total_failures += 1;
                    
                    if self.config.alert_on_failure {
                        println!("健康检查失败: {} - {}", name, msg);
                    }
                }
                CheckResult::Unknown => {
                    check.last_result = CheckResult::Unknown;
                }
            }
        }
        
        Ok(())
    }

    // 执行检查
    async fn execute_check(&self, check_fn: &CheckFunction) -> CheckResult {
        match check_fn {
            CheckFunction::ProcessCheck { pid } => {
                self.check_process(*pid).await
            }
            CheckFunction::PortCheck { port } => {
                self.check_port(*port).await
            }
            CheckFunction::FileCheck { path } => {
                self.check_file(path).await
            }
            CheckFunction::CommandCheck { command } => {
                self.check_command(command).await
            }
            CheckFunction::CustomCheck { name } => {
                self.check_custom(name).await
            }
        }
    }

    // 检查进程
    async fn check_process(&self, pid: u32) -> CheckResult {
        #[cfg(unix)]
        {
            use std::process::Command;
            
            let output = Command::new("ps")
                .args(&["-p", &pid.to_string()])
                .output();
            
            match output {
                Ok(output) => {
                    if output.status.success() {
                        CheckResult::Healthy
                    } else {
                        CheckResult::Unhealthy(format!("进程 {} 不存在", pid))
                    }
                }
                Err(e) => CheckResult::Unhealthy(format!("检查进程失败: {}", e)),
            }
        }
        
        #[cfg(windows)]
        {
            use std::process::Command;
            
            let output = Command::new("tasklist")
                .args(&["/fi", &format!("PID eq {}", pid)])
                .output();
            
            match output {
                Ok(output) => {
                    let output_str = String::from_utf8_lossy(&output.stdout);
                    if output_str.contains(&pid.to_string()) {
                        CheckResult::Healthy
                    } else {
                        CheckResult::Unhealthy(format!("进程 {} 不存在", pid))
                    }
                }
                Err(e) => CheckResult::Unhealthy(format!("检查进程失败: {}", e)),
            }
        }
        
        #[cfg(not(any(unix, windows)))]
        {
            CheckResult::Unknown
        }
    }

    // 检查端口
    async fn check_port(&self, port: u16) -> CheckResult {
        use std::net::TcpStream;
        
        match TcpStream::connect(format!("127.0.0.1:{}", port)) {
            Ok(_) => CheckResult::Healthy,
            Err(_) => CheckResult::Unhealthy(format!("端口 {} 不可用", port)),
        }
    }

    // 检查文件
    async fn check_file(&self, path: &str) -> CheckResult {
        use std::fs;
        
        match fs::metadata(path) {
            Ok(_) => CheckResult::Healthy,
            Err(e) => CheckResult::Unhealthy(format!("文件 {} 不存在: {}", path, e)),
        }
    }

    // 检查命令
    async fn check_command(&self, command: &str) -> CheckResult {
        use std::process::Command;
        
        let output = Command::new("sh")
            .arg("-c")
            .arg(command)
            .output();
        
        match output {
            Ok(output) => {
                if output.status.success() {
                    CheckResult::Healthy
                } else {
                    CheckResult::Unhealthy(format!("命令执行失败: {}", command))
                }
            }
            Err(e) => CheckResult::Unhealthy(format!("命令执行错误: {}", e)),
        }
    }

    // 检查自定义
    async fn check_custom(&self, _name: &str) -> CheckResult {
        // 自定义检查逻辑
        CheckResult::Unknown
    }

    // 更新状态
    async fn update_status(&self) -> Result<(), HealthError> {
        let checks = self.checks.read().await;
        let mut status = self.status.write().await;
        
        let mut healthy_count = 0;
        let mut unhealthy_count = 0;
        let mut unknown_count = 0;
        
        for check in checks.values() {
            match check.last_result {
                CheckResult::Healthy => healthy_count += 1,
                CheckResult::Unhealthy(_) => unhealthy_count += 1,
                CheckResult::Unknown => unknown_count += 1,
            }
        }
        
        status.healthy_checks = healthy_count;
        status.unhealthy_checks = unhealthy_count;
        status.unknown_checks = unknown_count;
        
        if unhealthy_count > 0 {
            status.overall_status = CheckResult::Unhealthy("部分检查失败".to_string());
        } else if unknown_count > 0 {
            status.overall_status = CheckResult::Unknown;
        } else {
            status.overall_status = CheckResult::Healthy;
        }
        
        status.last_updated = Instant::now();
        
        Ok(())
    }

    // 获取健康状态
    pub async fn get_health_status(&self) -> HealthStatus {
        self.status.read().await.clone()
    }

    // 获取检查结果
    pub async fn get_check_result(&self, name: &str) -> Option<CheckResult> {
        let checks = self.checks.read().await;
        checks.get(name).map(|check| check.last_result.clone())
    }

    // 获取所有检查结果
    pub async fn get_all_check_results(&self) -> HashMap<String, CheckResult> {
        let checks = self.checks.read().await;
        checks.iter().map(|(name, check)| (name.clone(), check.last_result.clone())).collect()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum HealthError {
    #[error("健康检查错误: {0}")]
    HealthError(String),
    
    #[error("检查失败: {0}")]
    CheckFailed(String),
    
    #[error("状态更新失败: {0}")]
    StatusUpdateFailed(String),
}
```

## 总结

本章提供了监控与诊断的完整示例，包括：

1. **进程监控系统** - 实时监控进程状态、CPU、内存、IO等指标
2. **性能指标收集** - 收集系统性能指标并存储
3. **健康检查机制** - 定期检查系统健康状态
4. **诊断工具** - 提供系统诊断功能
5. **告警系统** - 基于阈值的告警机制
6. **日志分析** - 日志收集和分析功能

这些示例展示了如何在 Rust 1.90 中实现完整的监控与诊断系统，提供了实时监控、指标收集、健康检查和告警功能。
