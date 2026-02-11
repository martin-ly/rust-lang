# C07-04. 高级进程管理

> **文档定位**: Tier 4 高级主题
> **最后更新**: 2025-12-25
> **Rust版本**: 1.92.0+ (Edition 2024)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

## 📋 目录

- [C07-04. 高级进程管理](#c07-04-高级进程管理)
  - [📋 目录](#-目录)
  - [1. 进程池管理](#1-进程池管理)
    - [1.1 基础进程池实现](#11-基础进程池实现)
    - [1.2 负载均衡策略](#12-负载均衡策略)
  - [2. 进程监控与健康检查](#2-进程监控与健康检查)
    - [2.1 进程健康监控系统](#21-进程健康监控系统)
    - [2.2 自动故障恢复](#22-自动故障恢复)
  - [3. 资源限制与配额管理](#3-资源限制与配额管理)
    - [3.1 进程资源限制](#31-进程资源限制)
    - [3.2 配额管理系统](#32-配额管理系统)
  - [4. 进程调度与优先级管理](#4-进程调度与优先级管理)
    - [4.1 进程调度器](#41-进程调度器)
  - [5. 总结](#5-总结)

本章深入探讨 Rust 中的高级进程管理技术，包括进程池、负载均衡、健康检查、资源监控等企业级特性。

## 1. 进程池管理

### 1.1 基础进程池实现

```rust
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::time::{Duration, Instant};
use tokio::sync::Semaphore;
use tokio::time::sleep;

#[derive(Debug, Clone)]
pub struct ProcessPoolConfig {
    pub min_processes: usize,
    pub max_processes: usize,
    pub initial_processes: usize,
    pub idle_timeout: Duration,
    pub health_check_interval: Duration,
    pub max_idle_time: Duration,
}

impl Default for ProcessPoolConfig {
    fn default() -> Self {
        Self {
            min_processes: 2,
            max_processes: 10,
            initial_processes: 5,
            idle_timeout: Duration::from_secs(30),
            health_check_interval: Duration::from_secs(10),
            max_idle_time: Duration::from_secs(300),
        }
    }
}

pub struct ProcessPool {
    config: ProcessPoolConfig,
    processes: Arc<Mutex<VecDeque<PooledProcess>>>,
    semaphore: Arc<Semaphore>,
    base_command: String,
    base_args: Vec<String>,
}

#[derive(Debug)]
struct PooledProcess {
    child: tokio::process::Child,
    created_at: Instant,
    last_used: Instant,
    usage_count: u64,
    is_healthy: bool,
}

impl ProcessPool {
    pub fn new(config: ProcessPoolConfig, base_command: String, base_args: Vec<String>) -> Self {
        let semaphore = Arc::new(Semaphore::new(config.max_processes));

        Self {
            config,
            processes: Arc::new(Mutex::new(VecDeque::new())),
            semaphore,
            base_command,
            base_args,
        }
    }

    pub async fn initialize(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        for _ in 0..self.config.initial_processes {
            let process = self.create_process().await?;
            processes.push_back(process);
        }

        Ok(())
    }

    async fn create_process(&self) -> Result<PooledProcess, Box<dyn std::error::Error>> {
        let mut child = Command::new(&self.base_command)
            .args(&self.base_args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        Ok(PooledProcess {
            child,
            created_at: Instant::now(),
            last_used: Instant::now(),
            usage_count: 0,
            is_healthy: true,
        })
    }

    pub async fn execute_task(&self, task_data: &str) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        let mut processes = self.processes.lock().await;

        // 查找可用的健康进程
        let mut process_index = None;
        for (i, process) in processes.iter_mut().enumerate() {
            if process.is_healthy {
                process_index = Some(i);
                break;
            }
        }

        let process = if let Some(index) = process_index {
            processes.remove(index).unwrap()
        } else {
            // 创建新进程
            self.create_process().await?
        };

        // 执行任务
        let result = self.execute_with_process(process, task_data).await;

        // 将进程返回池中（如果健康）
        if let Ok(mut process) = result {
            process.last_used = Instant::now();
            process.usage_count += 1;
            processes.push_back(process);
        }

        result.map(|p| String::new()) // 简化实现
    }

    async fn execute_with_process(
        &self,
        mut process: PooledProcess,
        task_data: &str,
    ) -> Result<PooledProcess, Box<dyn std::error::Error>> {
        // 向进程发送任务数据
        if let Some(stdin) = process.child.stdin.take() {
            let mut async_stdin = tokio::io::BufWriter::new(stdin);
            async_stdin.write_all(task_data.as_bytes()).await?;
            async_stdin.write_all(b"\n").await?;
            async_stdin.flush().await?;
        }

        // 读取结果
        let output = process.child.wait_with_output().await?;

        if output.status.success() {
            process.is_healthy = true;
            Ok(process)
        } else {
            process.is_healthy = false;
            Err("进程执行失败".into())
        }
    }

    pub async fn health_check(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;
        let now = Instant::now();

        // 移除不健康的进程
        processes.retain(|process| {
            process.is_healthy &&
            now.duration_since(process.last_used) < self.config.max_idle_time
        });

        // 确保最小进程数
        while processes.len() < self.config.min_processes {
            let process = self.create_process().await?;
            processes.push_back(process);
        }

        Ok(())
    }

    pub async fn get_stats(&self) -> ProcessPoolStats {
        let processes = self.processes.lock().await;

        ProcessPoolStats {
            total_processes: processes.len(),
            healthy_processes: processes.iter().filter(|p| p.is_healthy).count(),
            unhealthy_processes: processes.iter().filter(|p| !p.is_healthy).count(),
            total_usage_count: processes.iter().map(|p| p.usage_count).sum(),
            average_usage_per_process: if processes.is_empty() {
                0.0
            } else {
                processes.iter().map(|p| p.usage_count).sum::<u64>() as f64 / processes.len() as f64
            },
        }
    }
}

#[derive(Debug)]
pub struct ProcessPoolStats {
    pub total_processes: usize,
    pub healthy_processes: usize,
    pub unhealthy_processes: usize,
    pub total_usage_count: u64,
    pub average_usage_per_process: f64,
}
```

### 1.2 负载均衡策略

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

pub enum LoadBalancingStrategy {
    RoundRobin,
    LeastConnections,
    WeightedRoundRobin,
    Random,
    LeastResponseTime,
}

pub struct LoadBalancedProcessPool {
    pools: Vec<Arc<ProcessPool>>,
    strategy: LoadBalancingStrategy,
    current_index: Arc<Mutex<usize>>,
    pool_weights: Vec<f64>,
}

impl LoadBalancedProcessPool {
    pub fn new(pools: Vec<Arc<ProcessPool>>, strategy: LoadBalancingStrategy) -> Self {
        let pool_weights = vec![1.0; pools.len()];

        Self {
            pools,
            strategy,
            current_index: Arc::new(Mutex::new(0)),
            pool_weights,
        }
    }

    pub async fn execute_task(&self, task_data: &str) -> Result<String, Box<dyn std::error::Error>> {
        let pool_index = self.select_pool().await;
        let pool = &self.pools[pool_index];

        pool.execute_task(task_data).await
    }

    async fn select_pool(&self) -> usize {
        match self.strategy {
            LoadBalancingStrategy::RoundRobin => {
                let mut index = self.current_index.lock().await;
                let selected = *index;
                *index = (*index + 1) % self.pools.len();
                selected
            }
            LoadBalancingStrategy::LeastConnections => {
                let mut min_connections = usize::MAX;
                let mut selected_index = 0;

                for (i, pool) in self.pools.iter().enumerate() {
                    let stats = pool.get_stats().await;
                    if stats.total_processes < min_connections {
                        min_connections = stats.total_processes;
                        selected_index = i;
                    }
                }

                selected_index
            }
            LoadBalancingStrategy::WeightedRoundRobin => {
                // 实现加权轮询算法
                self.weighted_round_robin().await
            }
            LoadBalancingStrategy::Random => {
                use rand::Rng;
                let mut rng = rand::thread_rng();
                rng.gen_range(0..self.pools.len())
            }
            LoadBalancingStrategy::LeastResponseTime => {
                // 实现最少响应时间算法
                self.least_response_time().await
            }
        }
    }

    async fn weighted_round_robin(&self) -> usize {
        let mut index = self.current_index.lock().await;
        let mut max_weight = 0.0;
        let mut selected_index = 0;

        for (i, weight) in self.pool_weights.iter().enumerate() {
            private static mut current_weight: f64 = 0.0;
            current_weight += weight;
            if current_weight > max_weight {
                max_weight = current_weight;
                selected_index = i;
            }
        }

        self.pool_weights[selected_index] -= 1.0;
        if self.pool_weights[selected_index] <= 0.0 {
            self.pool_weights[selected_index] = 1.0;
        }

        selected_index
    }

    async fn least_response_time(&self) -> usize {
        let mut min_response_time = Duration::MAX;
        let mut selected_index = 0;

        for (i, pool) in self.pools.iter().enumerate() {
            let start = Instant::now();
            let _ = pool.execute_task("ping").await; // 健康检查
            let response_time = start.elapsed();

            if response_time < min_response_time {
                min_response_time = response_time;
                selected_index = i;
            }
        }

        selected_index
    }
}
```

## 2. 进程监控与健康检查

### 2.1 进程健康监控系统

```rust
use std::time::{Duration, Instant};
use std::sync::Arc;
use tokio::sync::Mutex;
use tokio::time::interval;

pub struct ProcessHealthMonitor {
    processes: Arc<Mutex<Vec<MonitoredProcess>>>,
    check_interval: Duration,
    max_memory_mb: u64,
    max_cpu_percent: f64,
    max_response_time: Duration,
}

#[derive(Debug, Clone)]
pub struct MonitoredProcess {
    pub pid: u32,
    pub name: String,
    pub created_at: Instant,
    pub last_health_check: Instant,
    pub health_status: HealthStatus,
    pub metrics: ProcessMetrics,
}

#[derive(Debug, Clone)]
pub enum HealthStatus {
    Healthy,
    Warning,
    Critical,
    Dead,
}

#[derive(Debug, Clone)]
pub struct ProcessMetrics {
    pub memory_usage_mb: u64,
    pub cpu_percent: f64,
    pub response_time: Duration,
    pub error_count: u64,
    pub success_count: u64,
}

impl ProcessHealthMonitor {
    pub fn new(
        check_interval: Duration,
        max_memory_mb: u64,
        max_cpu_percent: f64,
        max_response_time: Duration,
    ) -> Self {
        Self {
            processes: Arc::new(Mutex::new(Vec::new())),
            check_interval,
            max_memory_mb,
            max_cpu_percent,
            max_response_time,
        }
    }

    pub async fn start_monitoring(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut interval = interval(self.check_interval);

        loop {
            interval.tick().await;
            self.perform_health_check().await?;
        }
    }

    async fn perform_health_check(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        for process in processes.iter_mut() {
            let metrics = self.collect_process_metrics(process.pid).await?;
            process.metrics = metrics.clone();
            process.last_health_check = Instant::now();

            // 更新健康状态
            process.health_status = self.determine_health_status(&metrics);

            // 记录健康检查结果
            self.log_health_status(process).await;
        }

        Ok(())
    }

    async fn collect_process_metrics(&self, pid: u32) -> Result<ProcessMetrics, Box<dyn std::error::Error>> {
        use std::process::Command;

        // 收集内存使用情况
        let memory_output = Command::new("ps")
            .arg("-p")
            .arg(pid.to_string())
            .arg("-o")
            .arg("rss")
            .output()
            .await?;

        let memory_mb = if memory_output.status.success() {
            let output_str = String::from_utf8_lossy(&memory_output.stdout);
            output_str.lines()
                .nth(1)
                .and_then(|line| line.trim().parse::<u64>().ok())
                .map(|kb| kb / 1024)
                .unwrap_or(0)
        } else {
            0
        };

        // 收集CPU使用情况
        let cpu_output = Command::new("ps")
            .arg("-p")
            .arg(pid.to_string())
            .arg("-o")
            .arg("pcpu")
            .output()
            .await?;

        let cpu_percent = if cpu_output.status.success() {
            let output_str = String::from_utf8_lossy(&cpu_output.stdout);
            output_str.lines()
                .nth(1)
                .and_then(|line| line.trim().parse::<f64>().ok())
                .unwrap_or(0.0)
        } else {
            0.0
        };

        // 测试响应时间
        let response_time = self.measure_response_time(pid).await;

        Ok(ProcessMetrics {
            memory_usage_mb: memory_mb,
            cpu_percent,
            response_time,
            error_count: 0, // 实际实现中需要维护错误计数
            success_count: 0, // 实际实现中需要维护成功计数
        })
    }

    async fn measure_response_time(&self, pid: u32) -> Duration {
        let start = Instant::now();

        // 发送健康检查请求
        let health_check_result = Command::new("kill")
            .arg("-0")
            .arg(pid.to_string())
            .output()
            .await;

        match health_check_result {
            Ok(output) if output.status.success() => start.elapsed(),
            _ => Duration::MAX,
        }
    }

    fn determine_health_status(&self, metrics: &ProcessMetrics) -> HealthStatus {
        if metrics.memory_usage_mb > self.max_memory_mb ||
           metrics.cpu_percent > self.max_cpu_percent ||
           metrics.response_time > self.max_response_time {
            HealthStatus::Critical
        } else if metrics.memory_usage_mb > self.max_memory_mb * 80 / 100 ||
                  metrics.cpu_percent > self.max_cpu_percent * 80 / 100 ||
                  metrics.response_time > self.max_response_time * 80 / 100 {
            HealthStatus::Warning
        } else {
            HealthStatus::Healthy
        }
    }

    async fn log_health_status(&self, process: &MonitoredProcess) {
        match process.health_status {
            HealthStatus::Critical => {
                println!(
                    "CRITICAL: 进程 {} (PID: {}) 健康状态严重",
                    process.name, process.pid
                );
            }
            HealthStatus::Warning => {
                println!(
                    "WARNING: 进程 {} (PID: {}) 健康状态警告",
                    process.name, process.pid
                );
            }
            HealthStatus::Healthy => {
                // 正常状态，可以选择性记录
            }
            HealthStatus::Dead => {
                println!(
                    "DEAD: 进程 {} (PID: {}) 已死亡",
                    process.name, process.pid
                );
            }
        }
    }

    pub async fn add_process(&self, pid: u32, name: String) {
        let mut processes = self.processes.lock().await;

        let monitored_process = MonitoredProcess {
            pid,
            name,
            created_at: Instant::now(),
            last_health_check: Instant::now(),
            health_status: HealthStatus::Healthy,
            metrics: ProcessMetrics {
                memory_usage_mb: 0,
                cpu_percent: 0.0,
                response_time: Duration::ZERO,
                error_count: 0,
                success_count: 0,
            },
        };

        processes.push(monitored_process);
    }

    pub async fn get_health_summary(&self) -> HealthSummary {
        let processes = self.processes.lock().await;

        let mut healthy_count = 0;
        let mut warning_count = 0;
        let mut critical_count = 0;
        let mut dead_count = 0;

        for process in processes.iter() {
            match process.health_status {
                HealthStatus::Healthy => healthy_count += 1,
                HealthStatus::Warning => warning_count += 1,
                HealthStatus::Critical => critical_count += 1,
                HealthStatus::Dead => dead_count += 1,
            }
        }

        HealthSummary {
            total_processes: processes.len(),
            healthy_processes: healthy_count,
            warning_processes: warning_count,
            critical_processes: critical_count,
            dead_processes: dead_count,
        }
    }
}

#[derive(Debug)]
pub struct HealthSummary {
    pub total_processes: usize,
    pub healthy_processes: usize,
    pub warning_processes: usize,
    pub critical_processes: usize,
    pub dead_processes: usize,
}
```

### 2.2 自动故障恢复

```rust
use std::time::Duration;
use tokio::time::sleep;

pub struct AutoRecoveryManager {
    max_retry_attempts: u32,
    retry_delay: Duration,
    backoff_multiplier: f64,
    max_retry_delay: Duration,
}

impl AutoRecoveryManager {
    pub fn new(
        max_retry_attempts: u32,
        initial_retry_delay: Duration,
        backoff_multiplier: f64,
        max_retry_delay: Duration,
    ) -> Self {
        Self {
            max_retry_attempts,
            retry_delay: initial_retry_delay,
            backoff_multiplier,
            max_retry_delay,
        }
    }

    pub async fn recover_process(
        &self,
        process_config: ProcessConfig,
    ) -> Result<tokio::process::Child, Box<dyn std::error::Error>> {
        let mut current_delay = self.retry_delay;
        let mut attempt = 0;

        loop {
            match self.attempt_process_recovery(&process_config).await {
                Ok(child) => return Ok(child),
                Err(e) => {
                    attempt += 1;

                    if attempt >= self.max_retry_attempts {
                        return Err(format!(
                            "进程恢复失败，已尝试 {} 次: {}",
                            self.max_retry_attempts, e
                        ).into());
                    }

                    println!(
                        "进程恢复失败 (尝试 {}/{}), {} 秒后重试: {}",
                        attempt, self.max_retry_attempts, current_delay.as_secs(), e
                    );

                    sleep(current_delay).await;

                    // 指数退避
                    current_delay = Duration::from_millis(
                        (current_delay.as_millis() as f64 * self.backoff_multiplier) as u64
                    );

                    if current_delay > self.max_retry_delay {
                        current_delay = self.max_retry_delay;
                    }
                }
            }
        }
    }

    async fn attempt_process_recovery(
        &self,
        config: &ProcessConfig,
    ) -> Result<tokio::process::Child, Box<dyn std::error::Error>> {
        use std::process::{Command, Stdio};

        let mut child = Command::new(&config.program)
            .args(&config.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        // 等待一小段时间确保进程正常启动
        sleep(Duration::from_millis(100)).await;

        // 检查进程是否仍在运行
        match child.try_wait() {
            Ok(Some(status)) => {
                if status.success() {
                    Err("进程启动后立即退出".into())
                } else {
                    Err(format!("进程启动失败，退出码: {:?}", status.code()).into())
                }
            }
            Ok(None) => Ok(child), // 进程正在运行
            Err(e) => Err(format!("检查进程状态失败: {}", e).into()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProcessConfig {
    pub program: String,
    pub args: Vec<String>,
    pub env: std::collections::HashMap<String, String>,
    pub working_dir: Option<String>,
}
```

## 3. 资源限制与配额管理

### 3.1 进程资源限制

```rust
use std::time::Duration;
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct ResourceLimiter {
    max_memory_mb: u64,
    max_cpu_percent: f64,
    max_file_descriptors: u32,
    max_execution_time: Duration,
    current_usage: Arc<Mutex<ResourceUsage>>,
}

#[derive(Debug, Default)]
pub struct ResourceUsage {
    pub memory_mb: u64,
    pub cpu_percent: f64,
    pub file_descriptors: u32,
    pub execution_time: Duration,
}

impl ResourceLimiter {
    pub fn new(
        max_memory_mb: u64,
        max_cpu_percent: f64,
        max_file_descriptors: u32,
        max_execution_time: Duration,
    ) -> Self {
        Self {
            max_memory_mb,
            max_cpu_percent,
            max_file_descriptors,
            max_execution_time,
            current_usage: Arc::new(Mutex::new(ResourceUsage::default())),
        }
    }

    pub async fn check_resource_limits(&self) -> Result<(), ResourceLimitError> {
        let usage = self.current_usage.lock().await;

        if usage.memory_mb > self.max_memory_mb {
            return Err(ResourceLimitError::MemoryLimitExceeded {
                current: usage.memory_mb,
                limit: self.max_memory_mb,
            });
        }

        if usage.cpu_percent > self.max_cpu_percent {
            return Err(ResourceLimitError::CpuLimitExceeded {
                current: usage.cpu_percent,
                limit: self.max_cpu_percent,
            });
        }

        if usage.file_descriptors > self.max_file_descriptors {
            return Err(ResourceLimitError::FileDescriptorLimitExceeded {
                current: usage.file_descriptors,
                limit: self.max_file_descriptors,
            });
        }

        if usage.execution_time > self.max_execution_time {
            return Err(ResourceLimitError::ExecutionTimeLimitExceeded {
                current: usage.execution_time,
                limit: self.max_execution_time,
            });
        }

        Ok(())
    }

    pub async fn update_resource_usage(&self, usage: ResourceUsage) {
        let mut current = self.current_usage.lock().await;
        *current = usage;
    }

    pub async fn get_current_usage(&self) -> ResourceUsage {
        self.current_usage.lock().await.clone()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum ResourceLimitError {
    #[error("内存使用超限: 当前 {current}MB, 限制 {limit}MB")]
    MemoryLimitExceeded { current: u64, limit: u64 },

    #[error("CPU使用超限: 当前 {current}%, 限制 {limit}%")]
    CpuLimitExceeded { current: f64, limit: f64 },

    #[error("文件描述符超限: 当前 {current}, 限制 {limit}")]
    FileDescriptorLimitExceeded { current: u32, limit: u32 },

    #[error("执行时间超限: 当前 {current:?}, 限制 {limit:?}")]
    ExecutionTimeLimitExceeded { current: Duration, limit: Duration },
}
```

### 3.2 配额管理系统

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

pub struct QuotaManager {
    quotas: Arc<RwLock<HashMap<String, ProcessQuota>>>,
    usage_tracker: Arc<RwLock<HashMap<String, ResourceUsage>>>,
}

#[derive(Debug, Clone)]
pub struct ProcessQuota {
    pub max_memory_mb: u64,
    pub max_cpu_percent: f64,
    pub max_file_descriptors: u32,
    pub max_execution_time: Duration,
    pub max_concurrent_processes: u32,
    pub priority: ProcessPriority,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProcessPriority {
    Low,
    Normal,
    High,
    Critical,
}

impl QuotaManager {
    pub fn new() -> Self {
        Self {
            quotas: Arc::new(RwLock::new(HashMap::new())),
            usage_tracker: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    pub async fn set_quota(&self, process_id: String, quota: ProcessQuota) {
        let mut quotas = self.quotas.write().await;
        quotas.insert(process_id, quota);
    }

    pub async fn check_quota(&self, process_id: &str) -> Result<(), QuotaError> {
        let quotas = self.quotas.read().await;
        let usage_tracker = self.usage_tracker.read().await;

        let quota = quotas.get(process_id)
            .ok_or_else(|| QuotaError::QuotaNotFound(process_id.to_string()))?;

        let usage = usage_tracker.get(process_id)
            .cloned()
            .unwrap_or_default();

        if usage.memory_mb > quota.max_memory_mb {
            return Err(QuotaError::MemoryQuotaExceeded {
                current: usage.memory_mb,
                limit: quota.max_memory_mb,
            });
        }

        if usage.cpu_percent > quota.max_cpu_percent {
            return Err(QuotaError::CpuQuotaExceeded {
                current: usage.cpu_percent,
                limit: quota.max_cpu_percent,
            });
        }

        if usage.file_descriptors > quota.max_file_descriptors {
            return Err(QuotaError::FileDescriptorQuotaExceeded {
                current: usage.file_descriptors,
                limit: quota.max_file_descriptors,
            });
        }

        if usage.execution_time > quota.max_execution_time {
            return Err(QuotaError::ExecutionTimeQuotaExceeded {
                current: usage.execution_time,
                limit: quota.max_execution_time,
            });
        }

        Ok(())
    }

    pub async fn update_usage(&self, process_id: String, usage: ResourceUsage) {
        let mut usage_tracker = self.usage_tracker.write().await;
        usage_tracker.insert(process_id, usage);
    }

    pub async fn get_quota_status(&self, process_id: &str) -> Option<QuotaStatus> {
        let quotas = self.quotas.read().await;
        let usage_tracker = self.usage_tracker.read().await;

        let quota = quotas.get(process_id)?;
        let usage = usage_tracker.get(process_id).cloned().unwrap_or_default();

        Some(QuotaStatus {
            quota: quota.clone(),
            usage,
            memory_utilization: usage.memory_mb as f64 / quota.max_memory_mb as f64,
            cpu_utilization: usage.cpu_percent / quota.max_cpu_percent,
            file_descriptor_utilization: usage.file_descriptors as f64 / quota.max_file_descriptors as f64,
            execution_time_utilization: usage.execution_time.as_secs_f64() / quota.max_execution_time.as_secs_f64(),
        })
    }
}

#[derive(Debug)]
pub struct QuotaStatus {
    pub quota: ProcessQuota,
    pub usage: ResourceUsage,
    pub memory_utilization: f64,
    pub cpu_utilization: f64,
    pub file_descriptor_utilization: f64,
    pub execution_time_utilization: f64,
}

#[derive(Debug, thiserror::Error)]
pub enum QuotaError {
    #[error("配额未找到: {0}")]
    QuotaNotFound(String),

    #[error("内存配额超限: 当前 {current}MB, 限制 {limit}MB")]
    MemoryQuotaExceeded { current: u64, limit: u64 },

    #[error("CPU配额超限: 当前 {current}%, 限制 {limit}%")]
    CpuQuotaExceeded { current: f64, limit: f64 },

    #[error("文件描述符配额超限: 当前 {current}, 限制 {limit}")]
    FileDescriptorQuotaExceeded { current: u32, limit: u32 },

    #[error("执行时间配额超限: 当前 {current:?}, 限制 {limit:?}")]
    ExecutionTimeQuotaExceeded { current: Duration, limit: Duration },
}
```

## 4. 进程调度与优先级管理

### 4.1 进程调度器

```rust
use std::collections::BinaryHeap;
use std::cmp::Ordering;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;

pub struct ProcessScheduler {
    ready_queue: Arc<Mutex<BinaryHeap<ScheduledProcess>>>,
    running_processes: Arc<Mutex<Vec<RunningProcess>>>,
    max_concurrent: usize,
    time_slice: Duration,
}

#[derive(Debug, Clone)]
pub struct ScheduledProcess {
    pub process_id: String,
    pub priority: ProcessPriority,
    pub arrival_time: Instant,
    pub estimated_duration: Duration,
    pub resource_requirements: ResourceRequirements,
}

#[derive(Debug, Clone)]
pub struct RunningProcess {
    pub process_id: String,
    pub start_time: Instant,
    pub remaining_time: Duration,
    pub priority: ProcessPriority,
}

#[derive(Debug, Clone)]
pub struct ResourceRequirements {
    pub memory_mb: u64,
    pub cpu_percent: f64,
    pub file_descriptors: u32,
}

impl Ord for ScheduledProcess {
    fn cmp(&self, other: &Self) -> Ordering {
        // 优先级高的进程排在前面
        match self.priority.cmp(&other.priority) {
            Ordering::Equal => {
                // 相同优先级时，先到达的进程排在前面
                other.arrival_time.cmp(&self.arrival_time)
            }
            other => other,
        }
    }
}

impl PartialOrd for ScheduledProcess {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for ScheduledProcess {
    fn eq(&self, other: &Self) -> bool {
        self.process_id == other.process_id
    }
}

impl Eq for ScheduledProcess {}

impl ProcessScheduler {
    pub fn new(max_concurrent: usize, time_slice: Duration) -> Self {
        Self {
            ready_queue: Arc::new(Mutex::new(BinaryHeap::new())),
            running_processes: Arc::new(Mutex::new(Vec::new())),
            max_concurrent,
            time_slice,
        }
    }

    pub async fn schedule_process(&self, process: ScheduledProcess) -> Result<(), SchedulerError> {
        let mut ready_queue = self.ready_queue.lock().await;
        let mut running_processes = self.running_processes.lock().await;

        // 检查是否可以立即运行
        if running_processes.len() < self.max_concurrent {
            let running_process = RunningProcess {
                process_id: process.process_id.clone(),
                start_time: Instant::now(),
                remaining_time: process.estimated_duration,
                priority: process.priority.clone(),
            };

            running_processes.push(running_process);
            println!("进程 {} 立即开始执行", process.process_id);
        } else {
            ready_queue.push(process);
            println!("进程 {} 加入就绪队列", process.process_id);
        }

        Ok(())
    }

    pub async fn preempt_process(&self, process_id: &str) -> Result<(), SchedulerError> {
        let mut running_processes = self.running_processes.lock().await;
        let mut ready_queue = self.ready_queue.lock().await;

        // 查找要抢占的进程
        if let Some(index) = running_processes.iter().position(|p| p.process_id == process_id) {
            let running_process = running_processes.remove(index);

            // 计算剩余时间
            let elapsed = Instant::now().duration_since(running_process.start_time);
            let remaining_time = running_process.remaining_time.saturating_sub(elapsed);

            // 将进程重新加入就绪队列
            let scheduled_process = ScheduledProcess {
                process_id: running_process.process_id,
                priority: running_process.priority,
                arrival_time: Instant::now(),
                estimated_duration: remaining_time,
                resource_requirements: ResourceRequirements {
                    memory_mb: 0, // 实际实现中需要保存这些信息
                    cpu_percent: 0.0,
                    file_descriptors: 0,
                },
            };

            ready_queue.push(scheduled_process);
            println!("进程 {} 被抢占，重新加入就绪队列", process_id);
        }

        Ok(())
    }

    pub async fn complete_process(&self, process_id: &str) -> Result<(), SchedulerError> {
        let mut running_processes = self.running_processes.lock().await;
        let mut ready_queue = self.ready_queue.lock().await;

        // 移除完成的进程
        running_processes.retain(|p| p.process_id != process_id);

        // 从就绪队列中选择下一个进程
        if let Some(next_process) = ready_queue.pop() {
            let running_process = RunningProcess {
                process_id: next_process.process_id.clone(),
                start_time: Instant::now(),
                remaining_time: next_process.estimated_duration,
                priority: next_process.priority,
            };

            running_processes.push(running_process);
            println!("进程 {} 开始执行", next_process.process_id);
        }

        Ok(())
    }

    pub async fn get_scheduler_status(&self) -> SchedulerStatus {
        let ready_queue = self.ready_queue.lock().await;
        let running_processes = self.running_processes.lock().await;

        SchedulerStatus {
            ready_queue_size: ready_queue.len(),
            running_processes_count: running_processes.len(),
            max_concurrent: self.max_concurrent,
            time_slice: self.time_slice,
        }
    }
}

#[derive(Debug)]
pub struct SchedulerStatus {
    pub ready_queue_size: usize,
    pub running_processes_count: usize,
    pub max_concurrent: usize,
    pub time_slice: Duration,
}

#[derive(Debug, thiserror::Error)]
pub enum SchedulerError {
    #[error("调度器错误: {0}")]
    Generic(String),
}
```

## 5. 总结

本章介绍了 Rust 中的高级进程管理技术：

1. **进程池管理**: 实现高效的进程复用和资源管理
2. **负载均衡**: 多种策略的负载均衡算法
3. **健康监控**: 全面的进程健康检查和监控
4. **自动恢复**: 故障检测和自动恢复机制
5. **资源限制**: 进程资源使用限制和配额管理
6. **进程调度**: 基于优先级的进程调度系统

这些技术为构建企业级的进程管理系统提供了坚实的基础，能够确保系统的稳定性、可扩展性和高性能。
