# C07-12. 高级进程管理示例 (Rust 1.92.0 增强版)

> **文档定位**: Tier 2 实践指南
> **最后更新**: 2025-12-25
> **Rust版本**: 1.92.0+ (Edition 2024)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

## 📋 目录

- [C07-12. 高级进程管理示例 (Rust 1.92.0 增强版)](#c07-12-高级进程管理示例-rust-1920-增强版)
  - [目录](#目录)
  - [1. 进程池管理](#1-进程池管理)
    - [1.1 进程池实现](#11-进程池实现)
    - [1.2 进程池使用示例](#12-进程池使用示例)
  - [2. 进程生命周期管理](#2-进程生命周期管理)
    - [2.1 生命周期管理器](#21-生命周期管理器)
  - [3. 进程资源监控](#3-进程资源监控)
    - [3.1 资源监控器](#31-资源监控器)
  - [4. 进程故障恢复](#4-进程故障恢复)
    - [4.1 故障恢复管理器](#41-故障恢复管理器)
  - [5. 进程优先级调度](#5-进程优先级调度)
    - [5.1 优先级调度器](#51-优先级调度器)
  - [总结](#总结)

本章提供高级进程管理示例，涵盖进程池、生命周期管理、资源监控、故障恢复和优先级调度等企业级功能。

## 1. 进程池管理

### 1.1 进程池实现

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex, Condvar};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use std::process::{Command, Stdio};

// 进程池管理器
pub struct ProcessPool {
    pool: Arc<RwLock<HashMap<String, PooledProcess>>>,
    config: PoolConfig,
    semaphore: Arc<Semaphore>,
    statistics: Arc<Mutex<PoolStatistics>>,
}

#[derive(Debug, Clone)]
pub struct PoolConfig {
    pub max_processes: usize,
    pub min_processes: usize,
    pub idle_timeout: Duration,
    pub max_idle_time: Duration,
    pub health_check_interval: Duration,
    pub auto_scale: bool,
}

#[derive(Debug)]
pub struct PooledProcess {
    pub id: String,
    pub process: std::process::Child,
    pub status: ProcessStatus,
    pub created_at: Instant,
    pub last_used: Instant,
    pub usage_count: u64,
    pub total_runtime: Duration,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Idle,
    Busy,
    Starting,
    Stopping,
    Failed,
    Terminated,
}

#[derive(Debug)]
pub struct PoolStatistics {
    pub total_created: u64,
    pub total_destroyed: u64,
    pub active_processes: usize,
    pub idle_processes: usize,
    pub busy_processes: usize,
    pub failed_processes: usize,
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub average_response_time: Duration,
}

impl ProcessPool {
    pub fn new(config: PoolConfig) -> Self {
        Self {
            pool: Arc::new(RwLock::new(HashMap::new())),
            config,
            semaphore: Arc::new(Semaphore::new(config.max_processes)),
            statistics: Arc::new(Mutex::new(PoolStatistics {
                total_created: 0,
                total_destroyed: 0,
                active_processes: 0,
                idle_processes: 0,
                busy_processes: 0,
                failed_processes: 0,
                total_requests: 0,
                successful_requests: 0,
                failed_requests: 0,
                average_response_time: Duration::ZERO,
            })),
        }
    }

    // 获取进程
    pub async fn acquire_process(&self, command: &str, args: &[String]) -> Result<String, PoolError> {
        let _permit = self.semaphore.acquire().await
            .map_err(|_| PoolError::ResourceExhausted)?;

        // 尝试从池中获取空闲进程
        if let Some(process_id) = self.find_idle_process().await {
            self.mark_process_busy(&process_id).await;
            return Ok(process_id);
        }

        // 创建新进程
        self.create_new_process(command, args).await
    }

    // 释放进程
    pub async fn release_process(&self, process_id: &str) -> Result<(), PoolError> {
        let mut pool = self.pool.write().await;

        if let Some(process) = pool.get_mut(process_id) {
            process.status = ProcessStatus::Idle;
            process.last_used = Instant::now();

            // 更新统计信息
            {
                let mut stats = self.statistics.lock().unwrap();
                stats.idle_processes += 1;
                stats.busy_processes -= 1;
            }
        }

        Ok(())
    }

    // 查找空闲进程
    async fn find_idle_process(&self) -> Option<String> {
        let pool = self.pool.read().await;

        for (id, process) in pool.iter() {
            if matches!(process.status, ProcessStatus::Idle) {
                return Some(id.clone());
            }
        }

        None
    }

    // 标记进程为忙碌
    async fn mark_process_busy(&self, process_id: &str) {
        let mut pool = self.pool.write().await;

        if let Some(process) = pool.get_mut(process_id) {
            process.status = ProcessStatus::Busy;
            process.last_used = Instant::now();
            process.usage_count += 1;

            // 更新统计信息
            {
                let mut stats = self.statistics.lock().unwrap();
                stats.busy_processes += 1;
                stats.idle_processes -= 1;
            }
        }
    }

    // 创建新进程
    async fn create_new_process(&self, command: &str, args: &[String]) -> Result<String, PoolError> {
        let process_id = uuid::Uuid::new_v4().to_string();

        let mut cmd = Command::new(command);
        cmd.args(args);
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());
        cmd.stdin(Stdio::piped());

        let child = cmd.spawn()
            .map_err(|e| PoolError::ProcessCreationFailed(e.to_string()))?;

        let pooled_process = PooledProcess {
            id: process_id.clone(),
            process: child,
            status: ProcessStatus::Starting,
            created_at: Instant::now(),
            last_used: Instant::now(),
            usage_count: 0,
            total_runtime: Duration::ZERO,
        };

        {
            let mut pool = self.pool.write().await;
            pool.insert(process_id.clone(), pooled_process);
        }

        // 更新统计信息
        {
            let mut stats = self.statistics.lock().unwrap();
            stats.total_created += 1;
            stats.active_processes += 1;
        }

        // 异步启动进程健康检查
        self.start_health_check(process_id.clone()).await;

        Ok(process_id)
    }

    // 启动健康检查
    async fn start_health_check(&self, process_id: String) {
        let pool = self.pool.clone();
        let config = self.config.clone();
        let statistics = self.statistics.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.health_check_interval);

            loop {
                interval.tick().await;

                let mut pool_guard = pool.write().await;
                if let Some(process) = pool_guard.get_mut(&process_id) {
                    // 检查进程是否还在运行
                    if let Ok(Some(_)) = process.process.try_wait() {
                        process.status = ProcessStatus::Terminated;
                        break;
                    }

                    // 检查进程是否空闲太久
                    if matches!(process.status, ProcessStatus::Idle) &&
                       process.last_used.elapsed() > config.max_idle_time {
                        // 终止空闲进程
                        let _ = process.process.kill();
                        process.status = ProcessStatus::Terminated;
                        break;
                    }
                } else {
                    break;
                }
            }

            // 清理进程
            pool_guard.remove(&process_id);

            // 更新统计信息
            {
                let mut stats = statistics.lock().unwrap();
                stats.total_destroyed += 1;
                stats.active_processes -= 1;
            }
        });
    }

    // 自动扩缩容
    pub async fn auto_scale(&self) -> Result<(), PoolError> {
        let pool = self.pool.read().await;
        let current_size = pool.len();

        if current_size < self.config.min_processes {
            // 扩容
            let needed = self.config.min_processes - current_size;
            for _ in 0..needed {
                self.create_new_process("python", &["-c".to_string(), "print('worker')".to_string()]).await?;
            }
        } else if current_size > self.config.max_processes {
            // 缩容
            let excess = current_size - self.config.max_processes;
            let mut processes_to_remove = Vec::new();

            for (id, process) in pool.iter() {
                if matches!(process.status, ProcessStatus::Idle) && processes_to_remove.len() < excess {
                    processes_to_remove.push(id.clone());
                }
            }

            for id in processes_to_remove {
                if let Some(process) = pool.get(&id) {
                    let _ = process.process.kill();
                }
            }
        }

        Ok(())
    }

    // 获取池统计信息
    pub fn get_statistics(&self) -> PoolStatistics {
        self.statistics.lock().unwrap().clone()
    }

    // 清理池
    pub async fn cleanup(&self) -> Result<(), PoolError> {
        let mut pool = self.pool.write().await;

        for (_, process) in pool.iter_mut() {
            let _ = process.process.kill();
        }

        pool.clear();

        // 重置统计信息
        {
            let mut stats = self.statistics.lock().unwrap();
            *stats = PoolStatistics {
                total_created: 0,
                total_destroyed: 0,
                active_processes: 0,
                idle_processes: 0,
                busy_processes: 0,
                failed_processes: 0,
                total_requests: 0,
                successful_requests: 0,
                failed_requests: 0,
                average_response_time: Duration::ZERO,
            };
        }

        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum PoolError {
    #[error("资源不足")]
    ResourceExhausted,

    #[error("进程创建失败: {0}")]
    ProcessCreationFailed(String),

    #[error("进程未找到: {0}")]
    ProcessNotFound(String),

    #[error("池操作失败: {0}")]
    PoolOperationFailed(String),
}
```

### 1.2 进程池使用示例

```rust
// 使用示例
pub async fn process_pool_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = PoolConfig {
        max_processes: 10,
        min_processes: 2,
        idle_timeout: Duration::from_secs(30),
        max_idle_time: Duration::from_secs(300),
        health_check_interval: Duration::from_secs(10),
        auto_scale: true,
    };

    let pool = ProcessPool::new(config);

    // 获取进程
    let process_id = pool.acquire_process("python", &["-c".to_string(), "print('Hello')".to_string()]).await?;
    println!("获取进程: {}", process_id);

    // 使用进程执行任务
    tokio::time::sleep(Duration::from_secs(2)).await;

    // 释放进程
    pool.release_process(&process_id).await?;
    println!("释放进程: {}", process_id);

    // 自动扩缩容
    pool.auto_scale().await?;

    // 获取统计信息
    let stats = pool.get_statistics();
    println!("池统计: {:?}", stats);

    // 清理池
    pool.cleanup().await?;

    Ok(())
}
```

## 2. 进程生命周期管理

### 2.1 生命周期管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 进程生命周期管理器
pub struct ProcessLifecycleManager {
    processes: Arc<RwLock<HashMap<String, ManagedProcess>>>,
    lifecycle_hooks: Arc<Mutex<Vec<LifecycleHook>>>,
    config: LifecycleConfig,
}

#[derive(Debug, Clone)]
pub struct LifecycleConfig {
    pub startup_timeout: Duration,
    pub shutdown_timeout: Duration,
    pub health_check_interval: Duration,
    pub restart_policy: RestartPolicy,
    pub max_restarts: u32,
}

#[derive(Debug, Clone)]
pub enum RestartPolicy {
    Always,
    OnFailure,
    Never,
    UnlessStopped,
}

#[derive(Debug)]
pub struct ManagedProcess {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub status: ProcessStatus,
    pub lifecycle_stage: LifecycleStage,
    pub restart_count: u32,
    pub created_at: Instant,
    pub started_at: Option<Instant>,
    pub stopped_at: Option<Instant>,
    pub last_health_check: Option<Instant>,
    pub health_status: HealthStatus,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Created,
    Starting,
    Running,
    Stopping,
    Stopped,
    Failed,
    Restarting,
}

#[derive(Debug, Clone)]
pub enum LifecycleStage {
    PreStart,
    Starting,
    Started,
    Running,
    PreStop,
    Stopping,
    Stopped,
    Failed,
}

#[derive(Debug, Clone)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

#[derive(Debug)]
pub struct LifecycleHook {
    pub name: String,
    pub stage: LifecycleStage,
    pub hook_fn: Box<dyn Fn(&ManagedProcess) -> Result<(), String> + Send + Sync>,
}

impl ProcessLifecycleManager {
    pub fn new(config: LifecycleConfig) -> Self {
        Self {
            processes: Arc::new(RwLock::new(HashMap::new())),
            lifecycle_hooks: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }

    // 注册生命周期钩子
    pub fn register_hook(&self, hook: LifecycleHook) {
        let mut hooks = self.lifecycle_hooks.lock().unwrap();
        hooks.push(hook);
    }

    // 创建进程
    pub async fn create_process(
        &self,
        id: String,
        command: String,
        args: Vec<String>,
    ) -> Result<(), LifecycleError> {
        let process = ManagedProcess {
            id: id.clone(),
            command,
            args,
            status: ProcessStatus::Created,
            lifecycle_stage: LifecycleStage::PreStart,
            restart_count: 0,
            created_at: Instant::now(),
            started_at: None,
            stopped_at: None,
            last_health_check: None,
            health_status: HealthStatus::Unknown,
        };

        {
            let mut processes = self.processes.write().await;
            processes.insert(id, process);
        }

        // 执行预启动钩子
        self.execute_hooks(LifecycleStage::PreStart, &id).await?;

        Ok(())
    }

    // 启动进程
    pub async fn start_process(&self, id: &str) -> Result<(), LifecycleError> {
        let mut processes = self.processes.write().await;

        if let Some(process) = processes.get_mut(id) {
            process.status = ProcessStatus::Starting;
            process.lifecycle_stage = LifecycleStage::Starting;
        }

        drop(processes);

        // 执行启动钩子
        self.execute_hooks(LifecycleStage::Starting, id).await?;

        // 启动进程
        let started = self.spawn_process(id).await?;

        if started {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(id) {
                process.status = ProcessStatus::Running;
                process.lifecycle_stage = LifecycleStage::Started;
                process.started_at = Some(Instant::now());
            }
        }

        // 执行已启动钩子
        self.execute_hooks(LifecycleStage::Started, id).await?;

        // 启动健康检查
        self.start_health_check(id.to_string()).await;

        Ok(())
    }

    // 停止进程
    pub async fn stop_process(&self, id: &str) -> Result<(), LifecycleError> {
        let mut processes = self.processes.write().await;

        if let Some(process) = processes.get_mut(id) {
            process.status = ProcessStatus::Stopping;
            process.lifecycle_stage = LifecycleStage::PreStop;
        }

        drop(processes);

        // 执行预停止钩子
        self.execute_hooks(LifecycleStage::PreStop, id).await?;

        // 停止进程
        let stopped = self.terminate_process(id).await?;

        if stopped {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(id) {
                process.status = ProcessStatus::Stopped;
                process.lifecycle_stage = LifecycleStage::Stopped;
                process.stopped_at = Some(Instant::now());
            }
        }

        // 执行已停止钩子
        self.execute_hooks(LifecycleStage::Stopped, id).await?;

        Ok(())
    }

    // 重启进程
    pub async fn restart_process(&self, id: &str) -> Result<(), LifecycleError> {
        // 停止进程
        self.stop_process(id).await?;

        // 等待一段时间
        tokio::time::sleep(Duration::from_millis(100)).await;

        // 启动进程
        self.start_process(id).await?;

        Ok(())
    }

    // 生成进程
    async fn spawn_process(&self, id: &str) -> Result<bool, LifecycleError> {
        let processes = self.processes.read().await;

        if let Some(process) = processes.get(id) {
            // 模拟进程启动
            tokio::time::sleep(Duration::from_millis(100)).await;
            Ok(true)
        } else {
            Err(LifecycleError::ProcessNotFound(id.to_string()))
        }
    }

    // 终止进程
    async fn terminate_process(&self, id: &str) -> Result<bool, LifecycleError> {
        let processes = self.processes.read().await;

        if let Some(process) = processes.get(id) {
            // 模拟进程终止
            tokio::time::sleep(Duration::from_millis(50)).await;
            Ok(true)
        } else {
            Err(LifecycleError::ProcessNotFound(id.to_string()))
        }
    }

    // 执行钩子
    async fn execute_hooks(&self, stage: LifecycleStage, process_id: &str) -> Result<(), LifecycleError> {
        let hooks = self.lifecycle_hooks.lock().unwrap();
        let processes = self.processes.read().await;

        if let Some(process) = processes.get(process_id) {
            for hook in hooks.iter() {
                if hook.stage == stage {
                    if let Err(e) = (hook.hook_fn)(process) {
                        return Err(LifecycleError::HookExecutionFailed(e));
                    }
                }
            }
        }

        Ok(())
    }

    // 启动健康检查
    async fn start_health_check(&self, process_id: String) {
        let processes = self.processes.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.health_check_interval);

            loop {
                interval.tick().await;

                let mut processes_guard = processes.write().await;
                if let Some(process) = processes_guard.get_mut(&process_id) {
                    // 执行健康检查
                    let is_healthy = Self::perform_health_check(process).await;

                    process.last_health_check = Some(Instant::now());
                    process.health_status = if is_healthy {
                        HealthStatus::Healthy
                    } else {
                        HealthStatus::Unhealthy
                    };

                    // 检查是否需要重启
                    if !is_healthy && process.restart_count < config.max_restarts {
                        match config.restart_policy {
                            RestartPolicy::Always | RestartPolicy::OnFailure => {
                                process.status = ProcessStatus::Restarting;
                                process.restart_count += 1;
                                break;
                            }
                            _ => {}
                        }
                    }
                } else {
                    break;
                }
            }
        });
    }

    // 执行健康检查
    async fn perform_health_check(process: &ManagedProcess) -> bool {
        // 模拟健康检查
        tokio::time::sleep(Duration::from_millis(10)).await;
        true
    }

    // 获取进程状态
    pub async fn get_process_status(&self, id: &str) -> Option<ProcessStatus> {
        let processes = self.processes.read().await;
        processes.get(id).map(|p| p.status.clone())
    }

    // 列出所有进程
    pub async fn list_processes(&self) -> Vec<ManagedProcess> {
        let processes = self.processes.read().await;
        processes.values().cloned().collect()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum LifecycleError {
    #[error("进程未找到: {0}")]
    ProcessNotFound(String),

    #[error("钩子执行失败: {0}")]
    HookExecutionFailed(String),

    #[error("进程启动失败: {0}")]
    ProcessStartFailed(String),

    #[error("进程停止失败: {0}")]
    ProcessStopFailed(String),

    #[error("生命周期操作超时")]
    OperationTimeout,
}
```

## 3. 进程资源监控

### 3.1 资源监控器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 进程资源监控器
pub struct ProcessResourceMonitor {
    monitored_processes: Arc<RwLock<HashMap<String, MonitoredProcess>>>,
    resource_limits: Arc<RwLock<HashMap<String, ResourceLimits>>>,
    alerts: Arc<Mutex<Vec<ResourceAlert>>>,
    config: MonitorConfig,
}

#[derive(Debug, Clone)]
pub struct MonitorConfig {
    pub check_interval: Duration,
    pub alert_thresholds: AlertThresholds,
    pub auto_action: bool,
    pub log_level: LogLevel,
}

#[derive(Debug, Clone)]
pub struct AlertThresholds {
    pub cpu_threshold: f64,
    pub memory_threshold: f64,
    pub disk_threshold: f64,
    pub network_threshold: f64,
}

#[derive(Debug, Clone)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

#[derive(Debug)]
pub struct MonitoredProcess {
    pub id: String,
    pub pid: u32,
    pub name: String,
    pub metrics: ProcessMetrics,
    pub last_updated: Instant,
    pub alert_count: u32,
}

#[derive(Debug, Clone)]
pub struct ProcessMetrics {
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub disk_usage: u64,
    pub network_rx: u64,
    pub network_tx: u64,
    pub file_descriptors: u32,
    pub threads: u32,
    pub uptime: Duration,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_cpu_percent: f64,
    pub max_memory_mb: u64,
    pub max_disk_mb: u64,
    pub max_network_mbps: f64,
    pub max_file_descriptors: u32,
    pub max_threads: u32,
}

#[derive(Debug, Clone)]
pub struct ResourceAlert {
    pub id: String,
    pub process_id: String,
    pub alert_type: AlertType,
    pub severity: AlertSeverity,
    pub message: String,
    pub timestamp: Instant,
    pub resolved: bool,
}

#[derive(Debug, Clone)]
pub enum AlertType {
    CpuHigh,
    MemoryHigh,
    DiskHigh,
    NetworkHigh,
    FileDescriptorsHigh,
    ThreadsHigh,
    ProcessDown,
}

#[derive(Debug, Clone)]
pub enum AlertSeverity {
    Low,
    Medium,
    High,
    Critical,
}

impl ProcessResourceMonitor {
    pub fn new(config: MonitorConfig) -> Self {
        Self {
            monitored_processes: Arc::new(RwLock::new(HashMap::new())),
            resource_limits: Arc::new(RwLock::new(HashMap::new())),
            alerts: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }

    // 添加监控进程
    pub async fn add_process(
        &self,
        id: String,
        pid: u32,
        name: String,
        limits: ResourceLimits,
    ) -> Result<(), MonitorError> {
        let process = MonitoredProcess {
            id: id.clone(),
            pid,
            name,
            metrics: ProcessMetrics {
                cpu_usage: 0.0,
                memory_usage: 0,
                disk_usage: 0,
                network_rx: 0,
                network_tx: 0,
                file_descriptors: 0,
                threads: 0,
                uptime: Duration::ZERO,
            },
            last_updated: Instant::now(),
            alert_count: 0,
        };

        {
            let mut processes = self.monitored_processes.write().await;
            processes.insert(id.clone(), process);
        }

        {
            let mut limits_map = self.resource_limits.write().await;
            limits_map.insert(id, limits);
        }

        // 启动监控
        self.start_monitoring(id).await;

        Ok(())
    }

    // 移除监控进程
    pub async fn remove_process(&self, id: &str) -> Result<(), MonitorError> {
        {
            let mut processes = self.monitored_processes.write().await;
            processes.remove(id);
        }

        {
            let mut limits = self.resource_limits.write().await;
            limits.remove(id);
        }

        Ok(())
    }

    // 启动监控
    async fn start_monitoring(&self, process_id: String) {
        let processes = self.monitored_processes.clone();
        let limits = self.resource_limits.clone();
        let alerts = self.alerts.clone();
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.check_interval);

            loop {
                interval.tick().await;

                // 检查进程是否还存在
                let process_exists = {
                    let processes_guard = processes.read().await;
                    processes_guard.contains_key(&process_id)
                };

                if !process_exists {
                    break;
                }

                // 收集指标
                if let Ok(metrics) = Self::collect_metrics(&process_id).await {
                    // 更新进程指标
                    {
                        let mut processes_guard = processes.write().await;
                        if let Some(process) = processes_guard.get_mut(&process_id) {
                            process.metrics = metrics;
                            process.last_updated = Instant::now();
                        }
                    }

                    // 检查资源限制
                    {
                        let limits_guard = limits.read().await;
                        let processes_guard = processes.read().await;

                        if let (Some(process), Some(limits)) = (
                            processes_guard.get(&process_id),
                            limits_guard.get(&process_id)
                        ) {
                            Self::check_resource_limits(
                                &process_id,
                                &process.metrics,
                                limits,
                                &config.alert_thresholds,
                                &alerts,
                            ).await;
                        }
                    }
                }
            }
        });
    }

    // 收集指标
    async fn collect_metrics(process_id: &str) -> Result<ProcessMetrics, MonitorError> {
        // 模拟指标收集
        tokio::time::sleep(Duration::from_millis(10)).await;

        Ok(ProcessMetrics {
            cpu_usage: 25.0,
            memory_usage: 1024 * 1024 * 100, // 100MB
            disk_usage: 1024 * 1024 * 10,    // 10MB
            network_rx: 1024 * 1024,         // 1MB
            network_tx: 1024 * 512,          // 512KB
            file_descriptors: 50,
            threads: 5,
            uptime: Duration::from_secs(3600),
        })
    }

    // 检查资源限制
    async fn check_resource_limits(
        process_id: &str,
        metrics: &ProcessMetrics,
        limits: &ResourceLimits,
        thresholds: &AlertThresholds,
        alerts: &Arc<Mutex<Vec<ResourceAlert>>>,
    ) {
        let mut new_alerts = Vec::new();

        // CPU 检查
        if metrics.cpu_usage > limits.max_cpu_percent * thresholds.cpu_threshold {
            new_alerts.push(ResourceAlert {
                id: uuid::Uuid::new_v4().to_string(),
                process_id: process_id.to_string(),
                alert_type: AlertType::CpuHigh,
                severity: AlertSeverity::High,
                message: format!("CPU usage {}% exceeds limit {}%",
                    metrics.cpu_usage, limits.max_cpu_percent),
                timestamp: Instant::now(),
                resolved: false,
            });
        }

        // 内存检查
        if metrics.memory_usage > limits.max_memory_mb * 1024 * 1024 * thresholds.memory_threshold as u64 {
            new_alerts.push(ResourceAlert {
                id: uuid::Uuid::new_v4().to_string(),
                process_id: process_id.to_string(),
                alert_type: AlertType::MemoryHigh,
                severity: AlertSeverity::High,
                message: format!("Memory usage {}MB exceeds limit {}MB",
                    metrics.memory_usage / 1024 / 1024, limits.max_memory_mb),
                timestamp: Instant::now(),
                resolved: false,
            });
        }

        // 文件描述符检查
        if metrics.file_descriptors > limits.max_file_descriptors {
            new_alerts.push(ResourceAlert {
                id: uuid::Uuid::new_v4().to_string(),
                process_id: process_id.to_string(),
                alert_type: AlertType::FileDescriptorsHigh,
                severity: AlertSeverity::Medium,
                message: format!("File descriptors {} exceeds limit {}",
                    metrics.file_descriptors, limits.max_file_descriptors),
                timestamp: Instant::now(),
                resolved: false,
            });
        }

        // 添加新警报
        if !new_alerts.is_empty() {
            let mut alerts_guard = alerts.lock().unwrap();
            alerts_guard.extend(new_alerts);
        }
    }

    // 获取进程指标
    pub async fn get_process_metrics(&self, id: &str) -> Option<ProcessMetrics> {
        let processes = self.monitored_processes.read().await;
        processes.get(id).map(|p| p.metrics.clone())
    }

    // 获取所有警报
    pub fn get_alerts(&self) -> Vec<ResourceAlert> {
        self.alerts.lock().unwrap().clone()
    }

    // 解决警报
    pub fn resolve_alert(&self, alert_id: &str) -> Result<(), MonitorError> {
        let mut alerts = self.alerts.lock().unwrap();

        if let Some(alert) = alerts.iter_mut().find(|a| a.id == alert_id) {
            alert.resolved = true;
            Ok(())
        } else {
            Err(MonitorError::AlertNotFound(alert_id.to_string()))
        }
    }

    // 获取监控统计
    pub async fn get_monitoring_stats(&self) -> MonitoringStats {
        let processes = self.monitored_processes.read().await;
        let alerts = self.alerts.lock().unwrap();

        let total_processes = processes.len();
        let total_alerts = alerts.len();
        let unresolved_alerts = alerts.iter().filter(|a| !a.resolved).count();

        MonitoringStats {
            total_processes,
            total_alerts,
            unresolved_alerts,
            average_cpu_usage: processes.values()
                .map(|p| p.metrics.cpu_usage)
                .sum::<f64>() / total_processes as f64,
            average_memory_usage: processes.values()
                .map(|p| p.metrics.memory_usage)
                .sum::<u64>() / total_processes as u64,
        }
    }
}

#[derive(Debug)]
pub struct MonitoringStats {
    pub total_processes: usize,
    pub total_alerts: usize,
    pub unresolved_alerts: usize,
    pub average_cpu_usage: f64,
    pub average_memory_usage: u64,
}

#[derive(Debug, thiserror::Error)]
pub enum MonitorError {
    #[error("进程未找到: {0}")]
    ProcessNotFound(String),

    #[error("警报未找到: {0}")]
    AlertNotFound(String),

    #[error("监控失败: {0}")]
    MonitoringFailed(String),

    #[error("指标收集失败: {0}")]
    MetricsCollectionFailed(String),
}
```

## 4. 进程故障恢复

### 4.1 故障恢复管理器

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 进程故障恢复管理器
pub struct ProcessFailureRecoveryManager {
    processes: Arc<RwLock<HashMap<String, RecoverableProcess>>>,
    recovery_strategies: Arc<Mutex<HashMap<String, RecoveryStrategy>>>,
    failure_history: Arc<Mutex<Vec<FailureRecord>>>,
    config: RecoveryConfig,
}

#[derive(Debug, Clone)]
pub struct RecoveryConfig {
    pub max_failure_count: u32,
    pub failure_window: Duration,
    pub recovery_timeout: Duration,
    pub backoff_strategy: BackoffStrategy,
    pub auto_recovery: bool,
    pub circuit_breaker: bool,
}

#[derive(Debug, Clone)]
pub enum BackoffStrategy {
    Linear,
    Exponential,
    Fixed,
}

#[derive(Debug)]
pub struct RecoverableProcess {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub status: ProcessStatus,
    pub failure_count: u32,
    pub last_failure: Option<Instant>,
    pub last_success: Option<Instant>,
    pub recovery_attempts: u32,
    pub max_recovery_attempts: u32,
    pub circuit_breaker_state: CircuitBreakerState,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Healthy,
    Unhealthy,
    Recovering,
    Failed,
    CircuitOpen,
}

#[derive(Debug, Clone)]
pub enum CircuitBreakerState {
    Closed,
    Open,
    HalfOpen,
}

#[derive(Debug)]
pub struct RecoveryStrategy {
    pub name: String,
    pub strategy_type: StrategyType,
    pub parameters: HashMap<String, String>,
}

#[derive(Debug, Clone)]
pub enum StrategyType {
    Restart,
    Replace,
    Scale,
    Fallback,
}

#[derive(Debug)]
pub struct FailureRecord {
    pub id: String,
    pub process_id: String,
    pub failure_type: FailureType,
    pub error_message: String,
    pub timestamp: Instant,
    pub recovered: bool,
}

#[derive(Debug, Clone)]
pub enum FailureType {
    Crash,
    Timeout,
    ResourceExhaustion,
    NetworkError,
    DependencyFailure,
}

impl ProcessFailureRecoveryManager {
    pub fn new(config: RecoveryConfig) -> Self {
        Self {
            processes: Arc::new(RwLock::new(HashMap::new())),
            recovery_strategies: Arc::new(Mutex::new(HashMap::new())),
            failure_history: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }

    // 注册进程
    pub async fn register_process(
        &self,
        id: String,
        command: String,
        args: Vec<String>,
        max_recovery_attempts: u32,
    ) -> Result<(), RecoveryError> {
        let process = RecoverableProcess {
            id: id.clone(),
            command,
            args,
            status: ProcessStatus::Healthy,
            failure_count: 0,
            last_failure: None,
            last_success: Some(Instant::now()),
            recovery_attempts: 0,
            max_recovery_attempts,
            circuit_breaker_state: CircuitBreakerState::Closed,
            created_at: Instant::now(),
        };

        {
            let mut processes = self.processes.write().await;
            processes.insert(id, process);
        }

        Ok(())
    }

    // 注册恢复策略
    pub fn register_recovery_strategy(&self, process_id: String, strategy: RecoveryStrategy) {
        let mut strategies = self.recovery_strategies.lock().unwrap();
        strategies.insert(process_id, strategy);
    }

    // 报告故障
    pub async fn report_failure(
        &self,
        process_id: &str,
        failure_type: FailureType,
        error_message: String,
    ) -> Result<(), RecoveryError> {
        // 记录故障
        let failure_record = FailureRecord {
            id: uuid::Uuid::new_v4().to_string(),
            process_id: process_id.to_string(),
            failure_type,
            error_message: error_message.clone(),
            timestamp: Instant::now(),
            recovered: false,
        };

        {
            let mut history = self.failure_history.lock().unwrap();
            history.push(failure_record);
        }

        // 更新进程状态
        {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(process_id) {
                process.failure_count += 1;
                process.last_failure = Some(Instant::now());
                process.status = ProcessStatus::Unhealthy;

                // 检查是否需要打开熔断器
                if self.should_open_circuit_breaker(process) {
                    process.circuit_breaker_state = CircuitBreakerState::Open;
                    process.status = ProcessStatus::CircuitOpen;
                }
            }
        }

        // 尝试恢复
        if self.config.auto_recovery {
            self.attempt_recovery(process_id).await?;
        }

        Ok(())
    }

    // 报告成功
    pub async fn report_success(&self, process_id: &str) -> Result<(), RecoveryError> {
        {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(process_id) {
                process.last_success = Some(Instant::now());
                process.status = ProcessStatus::Healthy;
                process.failure_count = 0;
                process.recovery_attempts = 0;

                // 重置熔断器
                match process.circuit_breaker_state {
                    CircuitBreakerState::HalfOpen => {
                        process.circuit_breaker_state = CircuitBreakerState::Closed;
                    }
                    _ => {}
                }
            }
        }

        Ok(())
    }

    // 尝试恢复
    async fn attempt_recovery(&self, process_id: &str) -> Result<(), RecoveryError> {
        let mut processes = self.processes.write().await;

        if let Some(process) = processes.get_mut(process_id) {
            if process.recovery_attempts >= process.max_recovery_attempts {
                process.status = ProcessStatus::Failed;
                return Err(RecoveryError::MaxRecoveryAttemptsExceeded);
            }

            process.recovery_attempts += 1;
            process.status = ProcessStatus::Recovering;
        }

        drop(processes);

        // 获取恢复策略
        let strategy = {
            let strategies = self.recovery_strategies.lock().unwrap();
            strategies.get(process_id).cloned()
        };

        if let Some(strategy) = strategy {
            match strategy.strategy_type {
                StrategyType::Restart => {
                    self.restart_process(process_id).await?;
                }
                StrategyType::Replace => {
                    self.replace_process(process_id).await?;
                }
                StrategyType::Scale => {
                    self.scale_process(process_id).await?;
                }
                StrategyType::Fallback => {
                    self.fallback_process(process_id).await?;
                }
            }
        } else {
            // 默认重启策略
            self.restart_process(process_id).await?;
        }

        Ok(())
    }

    // 重启进程
    async fn restart_process(&self, process_id: &str) -> Result<(), RecoveryError> {
        // 模拟进程重启
        tokio::time::sleep(Duration::from_millis(100)).await;

        // 更新状态
        {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(process_id) {
                process.status = ProcessStatus::Healthy;
                process.last_success = Some(Instant::now());
            }
        }

        Ok(())
    }

    // 替换进程
    async fn replace_process(&self, process_id: &str) -> Result<(), RecoveryError> {
        // 模拟进程替换
        tokio::time::sleep(Duration::from_millis(200)).await;

        // 更新状态
        {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(process_id) {
                process.status = ProcessStatus::Healthy;
                process.last_success = Some(Instant::now());
            }
        }

        Ok(())
    }

    // 扩缩容进程
    async fn scale_process(&self, process_id: &str) -> Result<(), RecoveryError> {
        // 模拟进程扩缩容
        tokio::time::sleep(Duration::from_millis(150)).await;

        // 更新状态
        {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(process_id) {
                process.status = ProcessStatus::Healthy;
                process.last_success = Some(Instant::now());
            }
        }

        Ok(())
    }

    // 回退进程
    async fn fallback_process(&self, process_id: &str) -> Result<(), RecoveryError> {
        // 模拟进程回退
        tokio::time::sleep(Duration::from_millis(50)).await;

        // 更新状态
        {
            let mut processes = self.processes.write().await;
            if let Some(process) = processes.get_mut(process_id) {
                process.status = ProcessStatus::Healthy;
                process.last_success = Some(Instant::now());
            }
        }

        Ok(())
    }

    // 检查是否需要打开熔断器
    fn should_open_circuit_breaker(&self, process: &RecoverableProcess) -> bool {
        if !self.config.circuit_breaker {
            return false;
        }

        // 检查故障窗口内的故障次数
        if let Some(last_failure) = process.last_failure {
            if last_failure.elapsed() < self.config.failure_window {
                return process.failure_count >= self.config.max_failure_count;
            }
        }

        false
    }

    // 获取进程状态
    pub async fn get_process_status(&self, process_id: &str) -> Option<ProcessStatus> {
        let processes = self.processes.read().await;
        processes.get(process_id).map(|p| p.status.clone())
    }

    // 获取故障历史
    pub fn get_failure_history(&self, process_id: &str) -> Vec<FailureRecord> {
        let history = self.failure_history.lock().unwrap();
        history.iter()
            .filter(|record| record.process_id == process_id)
            .cloned()
            .collect()
    }

    // 获取恢复统计
    pub async fn get_recovery_stats(&self) -> RecoveryStats {
        let processes = self.processes.read().await;
        let history = self.failure_history.lock().unwrap();

        let total_processes = processes.len();
        let healthy_processes = processes.values()
            .filter(|p| matches!(p.status, ProcessStatus::Healthy))
            .count();
        let failed_processes = processes.values()
            .filter(|p| matches!(p.status, ProcessStatus::Failed))
            .count();
        let total_failures = history.len();
        let recovered_failures = history.iter()
            .filter(|r| r.recovered)
            .count();

        RecoveryStats {
            total_processes,
            healthy_processes,
            failed_processes,
            total_failures,
            recovered_failures,
            recovery_rate: if total_failures > 0 {
                recovered_failures as f64 / total_failures as f64
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug)]
pub struct RecoveryStats {
    pub total_processes: usize,
    pub healthy_processes: usize,
    pub failed_processes: usize,
    pub total_failures: usize,
    pub recovered_failures: usize,
    pub recovery_rate: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum RecoveryError {
    #[error("进程未找到: {0}")]
    ProcessNotFound(String),

    #[error("超过最大恢复尝试次数")]
    MaxRecoveryAttemptsExceeded,

    #[error("恢复策略未找到: {0}")]
    RecoveryStrategyNotFound(String),

    #[error("恢复失败: {0}")]
    RecoveryFailed(String),

    #[error("熔断器已打开")]
    CircuitBreakerOpen,
}
```

## 5. 进程优先级调度

### 5.1 优先级调度器

```rust
use std::collections::{BinaryHeap, HashMap};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

// 进程优先级调度器
pub struct ProcessPriorityScheduler {
    task_queue: Arc<Mutex<BinaryHeap<ScheduledTask>>>,
    running_tasks: Arc<RwLock<HashMap<String, RunningTask>>>,
    resource_manager: Arc<ResourceManager>,
    config: SchedulerConfig,
}

#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    pub max_concurrent_tasks: usize,
    pub time_slice: Duration,
    pub preemption_enabled: bool,
    pub aging_enabled: bool,
    pub aging_factor: f64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScheduledTask {
    pub id: String,
    pub priority: TaskPriority,
    pub estimated_duration: Duration,
    pub resource_requirements: ResourceRequirements,
    pub created_at: Instant,
    pub last_run: Option<Instant>,
    pub run_count: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Critical = 1,
    High = 2,
    Normal = 3,
    Low = 4,
    Background = 5,
}

#[derive(Debug, Clone)]
pub struct ResourceRequirements {
    pub cpu_cores: f64,
    pub memory_mb: u64,
    pub disk_mb: u64,
    pub network_bandwidth: u64,
}

#[derive(Debug)]
pub struct RunningTask {
    pub task: ScheduledTask,
    pub started_at: Instant,
    pub allocated_resources: ResourceAllocation,
    pub status: TaskStatus,
}

#[derive(Debug, Clone)]
pub struct ResourceAllocation {
    pub cpu_cores: f64,
    pub memory_mb: u64,
    pub disk_mb: u64,
    pub network_bandwidth: u64,
}

#[derive(Debug, Clone)]
pub enum TaskStatus {
    Running,
    Suspended,
    Completed,
    Failed,
}

// 资源管理器
pub struct ResourceManager {
    total_resources: ResourceRequirements,
    allocated_resources: Arc<Mutex<ResourceAllocation>>,
    available_resources: Arc<Mutex<ResourceAllocation>>,
}

impl ProcessPriorityScheduler {
    pub fn new(config: SchedulerConfig, total_resources: ResourceRequirements) -> Self {
        let resource_manager = ResourceManager::new(total_resources.clone());

        Self {
            task_queue: Arc::new(Mutex::new(BinaryHeap::new())),
            running_tasks: Arc::new(RwLock::new(HashMap::new())),
            resource_manager: Arc::new(resource_manager),
            config,
        }
    }

    // 提交任务
    pub async fn submit_task(&self, task: ScheduledTask) -> Result<(), SchedulerError> {
        // 检查资源是否足够
        if !self.resource_manager.can_allocate(&task.resource_requirements) {
            return Err(SchedulerError::InsufficientResources);
        }

        // 添加到队列
        {
            let mut queue = self.task_queue.lock().unwrap();
            queue.push(task);
        }

        // 尝试调度
        self.schedule_tasks().await?;

        Ok(())
    }

    // 调度任务
    pub async fn schedule_tasks(&self) -> Result<(), SchedulerError> {
        let mut queue = self.task_queue.lock().unwrap();
        let mut running_tasks = self.running_tasks.write().await;

        while let Some(task) = queue.pop() {
            // 检查是否可以运行
            if running_tasks.len() >= self.config.max_concurrent_tasks {
                // 队列已满，检查是否需要抢占
                if self.config.preemption_enabled {
                    if let Some(preempted_task) = self.find_preemptible_task(&running_tasks, &task).await {
                        self.preempt_task(&mut running_tasks, preempted_task).await?;
                    } else {
                        // 无法抢占，重新加入队列
                        queue.push(task);
                        break;
                    }
                } else {
                    // 无法抢占，重新加入队列
                    queue.push(task);
                    break;
                }
            }

            // 分配资源
            if let Some(allocation) = self.resource_manager.allocate(&task.resource_requirements) {
                let running_task = RunningTask {
                    task: task.clone(),
                    started_at: Instant::now(),
                    allocated_resources: allocation,
                    status: TaskStatus::Running,
                };

                running_tasks.insert(task.id.clone(), running_task);

                // 异步执行任务
                self.execute_task(task.id).await;
            } else {
                // 资源不足，重新加入队列
                queue.push(task);
                break;
            }
        }

        Ok(())
    }

    // 执行任务
    async fn execute_task(&self, task_id: String) {
        let scheduler = self.clone();

        tokio::spawn(async move {
            // 模拟任务执行
            tokio::time::sleep(Duration::from_secs(2)).await;

            // 完成任务
            scheduler.complete_task(&task_id).await;
        });
    }

    // 完成任务
    async fn complete_task(&self, task_id: &str) {
        let mut running_tasks = self.running_tasks.write().await;

        if let Some(running_task) = running_tasks.remove(task_id) {
            // 释放资源
            self.resource_manager.deallocate(&running_task.allocated_resources);

            // 尝试调度新任务
            let _ = self.schedule_tasks().await;
        }
    }

    // 查找可抢占的任务
    async fn find_preemptible_task(
        &self,
        running_tasks: &HashMap<String, RunningTask>,
        new_task: &ScheduledTask,
    ) -> Option<String> {
        for (task_id, running_task) in running_tasks {
            if new_task.priority < running_task.task.priority {
                return Some(task_id.clone());
            }
        }
        None
    }

    // 抢占任务
    async fn preempt_task(
        &self,
        running_tasks: &mut HashMap<String, RunningTask>,
        task_id: String,
    ) -> Result<(), SchedulerError> {
        if let Some(running_task) = running_tasks.get_mut(&task_id) {
            running_task.status = TaskStatus::Suspended;

            // 释放资源
            self.resource_manager.deallocate(&running_task.allocated_resources);

            // 重新加入队列
            {
                let mut queue = self.task_queue.lock().unwrap();
                queue.push(running_task.task.clone());
            }

            running_tasks.remove(&task_id);
        }

        Ok(())
    }

    // 获取调度统计
    pub async fn get_scheduling_stats(&self) -> SchedulingStats {
        let queue = self.task_queue.lock().unwrap();
        let running_tasks = self.running_tasks.read().await;

        let queued_tasks = queue.len();
        let running_task_count = running_tasks.len();

        let priority_distribution = {
            let mut distribution = HashMap::new();
            for task in queue.iter() {
                *distribution.entry(task.priority.clone()).or_insert(0) += 1;
            }
            distribution
        };

        SchedulingStats {
            queued_tasks,
            running_tasks: running_task_count,
            priority_distribution,
            resource_utilization: self.resource_manager.get_utilization(),
        }
    }
}

impl ResourceManager {
    pub fn new(total_resources: ResourceRequirements) -> Self {
        let allocated = ResourceAllocation {
            cpu_cores: 0.0,
            memory_mb: 0,
            disk_mb: 0,
            network_bandwidth: 0,
        };

        let available = ResourceAllocation {
            cpu_cores: total_resources.cpu_cores,
            memory_mb: total_resources.memory_mb,
            disk_mb: total_resources.disk_mb,
            network_bandwidth: total_resources.network_bandwidth,
        };

        Self {
            total_resources,
            allocated_resources: Arc::new(Mutex::new(allocated)),
            available_resources: Arc::new(Mutex::new(available)),
        }
    }

    pub fn can_allocate(&self, requirements: &ResourceRequirements) -> bool {
        let available = self.available_resources.lock().unwrap();

        requirements.cpu_cores <= available.cpu_cores &&
        requirements.memory_mb <= available.memory_mb &&
        requirements.disk_mb <= available.disk_mb &&
        requirements.network_bandwidth <= available.network_bandwidth
    }

    pub fn allocate(&self, requirements: &ResourceRequirements) -> Option<ResourceAllocation> {
        if !self.can_allocate(requirements) {
            return None;
        }

        let mut available = self.available_resources.lock().unwrap();
        let mut allocated = self.allocated_resources.lock().unwrap();

        available.cpu_cores -= requirements.cpu_cores;
        available.memory_mb -= requirements.memory_mb;
        available.disk_mb -= requirements.disk_mb;
        available.network_bandwidth -= requirements.network_bandwidth;

        allocated.cpu_cores += requirements.cpu_cores;
        allocated.memory_mb += requirements.memory_mb;
        allocated.disk_mb += requirements.disk_mb;
        allocated.network_bandwidth += requirements.network_bandwidth;

        Some(ResourceAllocation {
            cpu_cores: requirements.cpu_cores,
            memory_mb: requirements.memory_mb,
            disk_mb: requirements.disk_mb,
            network_bandwidth: requirements.network_bandwidth,
        })
    }

    pub fn deallocate(&self, allocation: &ResourceAllocation) {
        let mut available = self.available_resources.lock().unwrap();
        let mut allocated = self.allocated_resources.lock().unwrap();

        available.cpu_cores += allocation.cpu_cores;
        available.memory_mb += allocation.memory_mb;
        available.disk_mb += allocation.disk_mb;
        available.network_bandwidth += allocation.network_bandwidth;

        allocated.cpu_cores -= allocation.cpu_cores;
        allocated.memory_mb -= allocation.memory_mb;
        allocated.disk_mb -= allocation.disk_mb;
        allocated.network_bandwidth -= allocation.network_bandwidth;
    }

    pub fn get_utilization(&self) -> ResourceUtilization {
        let allocated = self.allocated_resources.lock().unwrap();

        ResourceUtilization {
            cpu_utilization: allocated.cpu_cores / self.total_resources.cpu_cores,
            memory_utilization: allocated.memory_mb as f64 / self.total_resources.memory_mb as f64,
            disk_utilization: allocated.disk_mb as f64 / self.total_resources.disk_mb as f64,
            network_utilization: allocated.network_bandwidth as f64 / self.total_resources.network_bandwidth as f64,
        }
    }
}

#[derive(Debug)]
pub struct SchedulingStats {
    pub queued_tasks: usize,
    pub running_tasks: usize,
    pub priority_distribution: HashMap<TaskPriority, usize>,
    pub resource_utilization: ResourceUtilization,
}

#[derive(Debug)]
pub struct ResourceUtilization {
    pub cpu_utilization: f64,
    pub memory_utilization: f64,
    pub disk_utilization: f64,
    pub network_utilization: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum SchedulerError {
    #[error("资源不足")]
    InsufficientResources,

    #[error("调度失败: {0}")]
    SchedulingFailed(String),

    #[error("任务未找到: {0}")]
    TaskNotFound(String),

    #[error("抢占失败: {0}")]
    PreemptionFailed(String),
}

// 使用示例
pub async fn priority_scheduling_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = SchedulerConfig {
        max_concurrent_tasks: 5,
        time_slice: Duration::from_millis(100),
        preemption_enabled: true,
        aging_enabled: true,
        aging_factor: 0.1,
    };

    let total_resources = ResourceRequirements {
        cpu_cores: 8.0,
        memory_mb: 16384,
        disk_mb: 100000,
        network_bandwidth: 1000,
    };

    let scheduler = ProcessPriorityScheduler::new(config, total_resources);

    // 提交不同优先级的任务
    let tasks = vec![
        ScheduledTask {
            id: "task1".to_string(),
            priority: TaskPriority::Critical,
            estimated_duration: Duration::from_secs(1),
            resource_requirements: ResourceRequirements {
                cpu_cores: 2.0,
                memory_mb: 1024,
                disk_mb: 1000,
                network_bandwidth: 100,
            },
            created_at: Instant::now(),
            last_run: None,
            run_count: 0,
        },
        ScheduledTask {
            id: "task2".to_string(),
            priority: TaskPriority::High,
            estimated_duration: Duration::from_secs(2),
            resource_requirements: ResourceRequirements {
                cpu_cores: 1.0,
                memory_mb: 512,
                disk_mb: 500,
                network_bandwidth: 50,
            },
            created_at: Instant::now(),
            last_run: None,
            run_count: 0,
        },
        ScheduledTask {
            id: "task3".to_string(),
            priority: TaskPriority::Normal,
            estimated_duration: Duration::from_secs(3),
            resource_requirements: ResourceRequirements {
                cpu_cores: 0.5,
                memory_mb: 256,
                disk_mb: 250,
                network_bandwidth: 25,
            },
            created_at: Instant::now(),
            last_run: None,
            run_count: 0,
        },
    ];

    for task in tasks {
        scheduler.submit_task(task).await?;
    }

    // 等待任务执行
    tokio::time::sleep(Duration::from_secs(5)).await;

    // 获取调度统计
    let stats = scheduler.get_scheduling_stats().await;
    println!("调度统计: {:?}", stats);

    Ok(())
}
```

## 总结

本章提供了高级进程管理的完整示例，包括：

1. **进程池管理** - 高效的进程复用和资源管理
2. **进程生命周期管理** - 完整的进程生命周期控制和钩子机制
3. **进程资源监控** - 实时资源监控和警报系统
4. **进程故障恢复** - 自动故障检测和恢复机制
5. **进程优先级调度** - 基于优先级的任务调度和资源分配

这些示例展示了如何在 Rust 1.92.0 中构建企业级的进程管理系统（兼容 Rust 1.90+ 特性），提供了完整的错误处理、资源管理和监控功能。
