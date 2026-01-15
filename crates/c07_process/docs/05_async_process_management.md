# C07-05. 异步进程管理

> **文档定位**: Tier 4 高级主题
> **最后更新**: 2025-12-25
> **Rust版本**: 1.92.0+ (Edition 2024)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

## 📋 目录

- [C07-05. 异步进程管理](#c07-05-异步进程管理)
  - [目录](#目录)
  - [1. 异步进程基础](#1-异步进程基础)
    - [1.1 异步进程创建与管理](#11-异步进程创建与管理)
    - [1.2 异步进程通信](#12-异步进程通信)
  - [2. 异步进程池](#2-异步进程池)
    - [2.1 高级异步进程池](#21-高级异步进程池)
    - [2.2 异步任务调度器](#22-异步任务调度器)
  - [3. 异步进程监控](#3-异步进程监控)
    - [3.1 实时进程监控](#31-实时进程监控)
  - [4. 错误处理与恢复](#4-错误处理与恢复)
    - [4.1 异步错误处理](#41-异步错误处理)
  - [5. 总结](#5-总结)

本章深入探讨 Rust 中的异步进程管理，包括异步进程创建、监控、通信和错误处理，以及与现代异步运行时的集成。

## 1. 异步进程基础

### 1.1 异步进程创建与管理

```rust
use std::process::{Command, Stdio};
use tokio::process::Command as AsyncCommand;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use std::time::Duration;

pub struct AsyncProcessManager {
    processes: std::sync::Arc<tokio::sync::Mutex<Vec<AsyncProcess>>>,
    max_concurrent: usize,
}

#[derive(Debug)]
pub struct AsyncProcess {
    pub id: String,
    pub child: tokio::process::Child,
    pub created_at: std::time::Instant,
    pub status: ProcessStatus,
    pub metadata: ProcessMetadata,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Starting,
    Running,
    Completed,
    Failed,
    Terminated,
}

#[derive(Debug, Clone)]
pub struct ProcessMetadata {
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub env_vars: std::collections::HashMap<String, String>,
}

impl AsyncProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            processes: std::sync::Arc::new(tokio::sync::Mutex::new(Vec::new())),
            max_concurrent,
        }
    }

    pub async fn spawn_process(
        &self,
        config: ProcessConfig,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        if processes.len() >= self.max_concurrent {
            return Err("已达到最大并发进程数限制".into());
        }

        let process_id = uuid::Uuid::new_v4().to_string();

        let mut async_cmd = AsyncCommand::new(&config.command);
        async_cmd.args(&config.args);

        if let Some(working_dir) = &config.working_dir {
            async_cmd.current_dir(working_dir);
        }

        for (key, value) in &config.env_vars {
            async_cmd.env(key, value);
        }

        async_cmd
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());

        let child = async_cmd.spawn()?;

        let async_process = AsyncProcess {
            id: process_id.clone(),
            child,
            created_at: std::time::Instant::now(),
            status: ProcessStatus::Starting,
            metadata: ProcessMetadata {
                command: config.command,
                args: config.args,
                working_dir: config.working_dir,
                env_vars: config.env_vars,
            },
        };

        processes.push(async_process);

        Ok(process_id)
    }

    pub async fn wait_for_process(
        &self,
        process_id: &str,
    ) -> Result<ProcessResult, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id) {
            let output = process.child.wait_with_output().await?;

            let result = ProcessResult {
                process_id: process_id.to_string(),
                exit_code: output.status.code(),
                stdout: output.stdout,
                stderr: output.stderr,
                execution_time: std::time::Instant::now().duration_since(process.created_at),
            };

            process.status = if output.status.success() {
                ProcessStatus::Completed
            } else {
                ProcessStatus::Failed
            };

            Ok(result)
        } else {
            Err("进程未找到".into())
        }
    }

    pub async fn terminate_process(
        &self,
        process_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id) {
            process.child.kill().await?;
            process.status = ProcessStatus::Terminated;
            Ok(())
        } else {
            Err("进程未找到".into())
        }
    }

    pub async fn get_process_status(&self, process_id: &str) -> Option<ProcessStatus> {
        let processes = self.processes.lock().await;
        processes.iter()
            .find(|p| p.id == process_id)
            .map(|p| p.status.clone())
    }

    pub async fn list_processes(&self) -> Vec<ProcessInfo> {
        let processes = self.processes.lock().await;
        processes.iter().map(|p| ProcessInfo {
            id: p.id.clone(),
            status: p.status.clone(),
            created_at: p.created_at,
            metadata: p.metadata.clone(),
        }).collect()
    }
}

#[derive(Debug, Clone)]
pub struct ProcessConfig {
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub env_vars: std::collections::HashMap<String, String>,
}

#[derive(Debug)]
pub struct ProcessResult {
    pub process_id: String,
    pub exit_code: Option<i32>,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub execution_time: Duration,
}

#[derive(Debug, Clone)]
pub struct ProcessInfo {
    pub id: String,
    pub status: ProcessStatus,
    pub created_at: std::time::Instant,
    pub metadata: ProcessMetadata,
}
```

### 1.2 异步进程通信

```rust
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use tokio::sync::mpsc;
use std::time::Duration;

pub struct AsyncProcessCommunicator {
    stdin_tx: mpsc::UnboundedSender<Vec<u8>>,
    stdout_rx: mpsc::UnboundedReceiver<Vec<u8>>,
    stderr_rx: mpsc::UnboundedReceiver<Vec<u8>>,
}

impl AsyncProcessCommunicator {
    pub fn new(child: &mut tokio::process::Child) -> Self {
        let (stdin_tx, mut stdin_rx) = mpsc::unbounded_channel();
        let (stdout_tx, stdout_rx) = mpsc::unbounded_channel();
        let (stderr_tx, stderr_rx) = mpsc::unbounded_channel();

        // 处理标准输入
        if let Some(stdin) = child.stdin.take() {
            let stdin_tx_clone = stdin_tx.clone();
            tokio::spawn(async move {
                let mut async_stdin = tokio::io::BufWriter::new(stdin);

                while let Some(data) = stdin_rx.recv().await {
                    if let Err(e) = async_stdin.write_all(&data).await {
                        eprintln!("写入标准输入失败: {}", e);
                        break;
                    }
                    if let Err(e) = async_stdin.flush().await {
                        eprintln!("刷新标准输入失败: {}", e);
                        break;
                    }
                }
            });
        }

        // 处理标准输出
        if let Some(stdout) = child.stdout.take() {
            let stdout_tx_clone = stdout_tx.clone();
            tokio::spawn(async move {
                let mut async_stdout = tokio::io::BufReader::new(stdout);
                let mut buffer = String::new();

                while let Ok(n) = async_stdout.read_line(&mut buffer).await {
                    if n == 0 {
                        break;
                    }

                    if let Err(_) = stdout_tx_clone.send(buffer.as_bytes().to_vec()) {
                        break;
                    }

                    buffer.clear();
                }
            });
        }

        // 处理标准错误
        if let Some(stderr) = child.stderr.take() {
            let stderr_tx_clone = stderr_tx.clone();
            tokio::spawn(async move {
                let mut async_stderr = tokio::io::BufReader::new(stderr);
                let mut buffer = String::new();

                while let Ok(n) = async_stderr.read_line(&mut buffer).await {
                    if n == 0 {
                        break;
                    }

                    if let Err(_) = stderr_tx_clone.send(buffer.as_bytes().to_vec()) {
                        break;
                    }

                    buffer.clear();
                }
            });
        }

        Self {
            stdin_tx,
            stdout_rx,
            stderr_rx,
        }
    }

    pub async fn send_input(&self, data: Vec<u8>) -> Result<(), mpsc::error::SendError<Vec<u8>>> {
        self.stdin_tx.send(data)
    }

    pub async fn receive_output(&mut self) -> Option<Vec<u8>> {
        self.stdout_rx.recv().await
    }

    pub async fn receive_error(&mut self) -> Option<Vec<u8>> {
        self.stderr_rx.recv().await
    }

    pub async fn send_line(&self, line: &str) -> Result<(), mpsc::error::SendError<Vec<u8>>> {
        let data = format!("{}\n", line).into_bytes();
        self.stdin_tx.send(data)
    }
}
```

## 2. 异步进程池

### 2.1 高级异步进程池

```rust
use std::sync::Arc;
use tokio::sync::{Mutex, Semaphore, RwLock};
use std::collections::VecDeque;
use std::time::{Duration, Instant};

pub struct AsyncProcessPool {
    config: ProcessPoolConfig,
    processes: Arc<RwLock<VecDeque<PooledAsyncProcess>>>,
    semaphore: Arc<Semaphore>,
    task_queue: Arc<Mutex<VecDeque<Task>>>,
    metrics: Arc<RwLock<PoolMetrics>>,
}

#[derive(Debug, Clone)]
pub struct ProcessPoolConfig {
    pub min_processes: usize,
    pub max_processes: usize,
    pub initial_processes: usize,
    pub idle_timeout: Duration,
    pub health_check_interval: Duration,
    pub task_timeout: Duration,
    pub max_retries: u32,
    pub retry_delay: Duration,
}

#[derive(Debug)]
struct PooledAsyncProcess {
    id: String,
    child: tokio::process::Child,
    created_at: Instant,
    last_used: Instant,
    usage_count: u64,
    is_healthy: bool,
    current_task: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Task {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub input_data: Option<Vec<u8>>,
    pub timeout: Duration,
    pub priority: TaskPriority,
    pub retry_count: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

#[derive(Debug, Default)]
pub struct PoolMetrics {
    pub total_tasks_completed: u64,
    pub total_tasks_failed: u64,
    pub average_execution_time: Duration,
    pub total_processes_created: u64,
    pub total_processes_destroyed: u64,
    pub current_active_processes: usize,
    pub current_queued_tasks: usize,
}

impl AsyncProcessPool {
    pub fn new(config: ProcessPoolConfig) -> Self {
        let semaphore = Arc::new(Semaphore::new(config.max_processes));

        Self {
            config,
            processes: Arc::new(RwLock::new(VecDeque::new())),
            semaphore,
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
            metrics: Arc::new(RwLock::new(PoolMetrics::default())),
        }
    }

    pub async fn initialize(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.write().await;

        for i in 0..self.config.initial_processes {
            let process = self.create_process().await?;
            processes.push_back(process);
        }

        let mut metrics = self.metrics.write().await;
        metrics.total_processes_created = self.config.initial_processes as u64;
        metrics.current_active_processes = self.config.initial_processes;

        Ok(())
    }

    async fn create_process(&self) -> Result<PooledAsyncProcess, Box<dyn std::error::Error>> {
        let process_id = uuid::Uuid::new_v4().to_string();

        let mut child = tokio::process::Command::new("sh")
            .arg("-c")
            .arg("cat") // 默认命令，实际使用中应该可配置
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()?;

        Ok(PooledAsyncProcess {
            id: process_id,
            child,
            created_at: Instant::now(),
            last_used: Instant::now(),
            usage_count: 0,
            is_healthy: true,
            current_task: None,
        })
    }

    pub async fn submit_task(&self, task: Task) -> Result<String, Box<dyn std::error::Error>> {
        let task_id = task.id.clone();

        // 将任务加入队列
        {
            let mut queue = self.task_queue.lock().await;
            queue.push_back(task);
        }

        // 尝试立即执行任务
        self.try_execute_next_task().await;

        Ok(task_id)
    }

    async fn try_execute_next_task(&self) {
        let _permit = self.semaphore.acquire().await.unwrap();

        let mut processes = self.processes.write().await;
        let mut queue = self.task_queue.lock().await;

        // 查找可用的健康进程
        let mut process_index = None;
        for (i, process) in processes.iter_mut().enumerate() {
            if process.is_healthy && process.current_task.is_none() {
                process_index = Some(i);
                break;
            }
        }

        if let Some(index) = process_index {
            if let Some(task) = queue.pop_front() {
                let process = processes.get_mut(index).unwrap();
                process.current_task = Some(task.id.clone());
                process.last_used = Instant::now();

                // 异步执行任务
                let process_id = process.id.clone();
                let task_clone = task.clone();
                let processes_clone = self.processes.clone();
                let metrics_clone = self.metrics.clone();

                tokio::spawn(async move {
                    let result = Self::execute_task_with_process(
                        process_id,
                        task_clone,
                        processes_clone,
                        metrics_clone,
                    ).await;

                    match result {
                        Ok(_) => println!("任务 {} 执行成功", task.id),
                        Err(e) => println!("任务 {} 执行失败: {}", task.id, e),
                    }
                });
            }
        }
    }

    async fn execute_task_with_process(
        process_id: String,
        task: Task,
        processes: Arc<RwLock<VecDeque<PooledAsyncProcess>>>,
        metrics: Arc<RwLock<PoolMetrics>>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let start_time = Instant::now();

        // 获取进程
        let mut processes_guard = processes.write().await;
        let process = processes_guard.iter_mut()
            .find(|p| p.id == process_id)
            .ok_or("进程未找到")?;

        // 执行任务
        let result = Self::run_task_on_process(process, &task).await;

        // 更新进程状态
        process.current_task = None;
        process.usage_count += 1;

        // 更新指标
        let execution_time = start_time.elapsed();
        let mut metrics_guard = metrics.write().await;

        if result.is_ok() {
            metrics_guard.total_tasks_completed += 1;
        } else {
            metrics_guard.total_tasks_failed += 1;
        }

        // 更新平均执行时间
        let total_completed = metrics_guard.total_tasks_completed;
        if total_completed > 0 {
            metrics_guard.average_execution_time = Duration::from_millis(
                (metrics_guard.average_execution_time.as_millis() * (total_completed - 1) as u128
                 + execution_time.as_millis()) / total_completed as u128
            );
        }

        result
    }

    async fn run_task_on_process(
        process: &mut PooledAsyncProcess,
        task: &Task,
    ) -> Result<(), Box<dyn std::error::Error>> {
        use tokio::time::timeout;

        // 设置超时
        let execution_future = async {
            // 向进程发送输入数据
            if let Some(stdin) = process.child.stdin.as_mut() {
                if let Some(input_data) = &task.input_data {
                    stdin.write_all(input_data).await?;
                }
                stdin.write_all(b"\n").await?;
                stdin.flush().await?;
            }

            // 等待进程完成
            let output = process.child.wait_with_output().await?;

            if output.status.success() {
                println!("任务 {} 输出: {}", task.id, String::from_utf8_lossy(&output.stdout));
                Ok(())
            } else {
                Err(format!("进程执行失败: {}", String::from_utf8_lossy(&output.stderr)).into())
            }
        };

        timeout(task.timeout, execution_future).await
            .map_err(|_| "任务执行超时".into())?
    }

    pub async fn get_metrics(&self) -> PoolMetrics {
        let metrics = self.metrics.read().await;
        let processes = self.processes.read().await;
        let queue = self.task_queue.lock().await;

        PoolMetrics {
            total_tasks_completed: metrics.total_tasks_completed,
            total_tasks_failed: metrics.total_tasks_failed,
            average_execution_time: metrics.average_execution_time,
            total_processes_created: metrics.total_processes_created,
            total_processes_destroyed: metrics.total_processes_destroyed,
            current_active_processes: processes.len(),
            current_queued_tasks: queue.len(),
        }
    }

    pub async fn health_check(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.write().await;
        let now = Instant::now();

        // 移除不健康的进程
        let mut removed_count = 0;
        processes.retain(|process| {
            let is_healthy = process.is_healthy &&
                now.duration_since(process.last_used) < self.config.idle_timeout;

            if !is_healthy {
                removed_count += 1;
            }

            is_healthy
        });

        // 确保最小进程数
        while processes.len() < self.config.min_processes {
            let process = self.create_process().await?;
            processes.push_back(process);
        }

        // 更新指标
        let mut metrics = self.metrics.write().await;
        metrics.total_processes_destroyed += removed_count;
        metrics.current_active_processes = processes.len();

        Ok(())
    }
}
```

### 2.2 异步任务调度器

```rust
use std::collections::BinaryHeap;
use std::cmp::Ordering;
use tokio::sync::{Mutex, RwLock};
use std::time::{Duration, Instant};

pub struct AsyncTaskScheduler {
    task_queue: Arc<Mutex<BinaryHeap<ScheduledTask>>>,
    running_tasks: Arc<RwLock<Vec<RunningTask>>>,
    max_concurrent: usize,
    scheduler_config: SchedulerConfig,
}

#[derive(Debug, Clone)]
pub struct ScheduledTask {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub priority: TaskPriority,
    pub scheduled_time: Instant,
    pub estimated_duration: Duration,
    pub retry_count: u32,
    pub max_retries: u32,
}

#[derive(Debug)]
pub struct RunningTask {
    pub id: String,
    pub start_time: Instant,
    pub process_id: Option<String>,
    pub priority: TaskPriority,
}

#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    pub max_concurrent_tasks: usize,
    pub default_timeout: Duration,
    pub retry_delay: Duration,
    pub max_retry_delay: Duration,
    pub backoff_multiplier: f64,
}

impl Ord for ScheduledTask {
    fn cmp(&self, other: &Self) -> Ordering {
        // 优先级高的任务排在前面
        match self.priority.cmp(&other.priority) {
            Ordering::Equal => {
                // 相同优先级时，调度时间早的任务排在前面
                other.scheduled_time.cmp(&self.scheduled_time)
            }
            other => other,
        }
    }
}

impl PartialOrd for ScheduledTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for ScheduledTask {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for ScheduledTask {}

impl AsyncTaskScheduler {
    pub fn new(config: SchedulerConfig) -> Self {
        Self {
            task_queue: Arc::new(Mutex::new(BinaryHeap::new())),
            running_tasks: Arc::new(RwLock::new(Vec::new())),
            max_concurrent: config.max_concurrent_tasks,
            scheduler_config: config,
        }
    }

    pub async fn schedule_task(&self, task: ScheduledTask) -> Result<(), SchedulerError> {
        let mut queue = self.task_queue.lock().await;
        queue.push(task);

        // 尝试立即调度任务
        self.try_schedule_next_task().await;

        Ok(())
    }

    async fn try_schedule_next_task(&self) {
        let mut queue = self.task_queue.lock().await;
        let mut running_tasks = self.running_tasks.write().await;

        // 检查是否可以调度新任务
        if running_tasks.len() >= self.max_concurrent {
            return;
        }

        // 查找可以立即执行的任务
        if let Some(task) = queue.pop() {
            let now = Instant::now();

            if task.scheduled_time <= now {
                let running_task = RunningTask {
                    id: task.id.clone(),
                    start_time: now,
                    process_id: None,
                    priority: task.priority,
                };

                running_tasks.push(running_task);

                // 异步执行任务
                let task_clone = task.clone();
                let queue_clone = self.task_queue.clone();
                let running_tasks_clone = self.running_tasks.clone();
                let config = self.scheduler_config.clone();

                tokio::spawn(async move {
                    Self::execute_scheduled_task(
                        task_clone,
                        queue_clone,
                        running_tasks_clone,
                        config,
                    ).await;
                });
            } else {
                // 任务还未到执行时间，重新加入队列
                queue.push(task);
            }
        }
    }

    async fn execute_scheduled_task(
        task: ScheduledTask,
        queue: Arc<Mutex<BinaryHeap<ScheduledTask>>>,
        running_tasks: Arc<RwLock<Vec<RunningTask>>>,
        config: SchedulerConfig,
    ) {
        let start_time = Instant::now();

        // 执行任务
        let result = Self::run_task(&task).await;

        // 移除运行中的任务
        {
            let mut running_tasks_guard = running_tasks.write().await;
            running_tasks_guard.retain(|t| t.id != task.id);
        }

        match result {
            Ok(_) => {
                println!("任务 {} 执行成功", task.id);
            }
            Err(e) => {
                println!("任务 {} 执行失败: {}", task.id, e);

                // 检查是否需要重试
                if task.retry_count < task.max_retries {
                    let mut new_task = task.clone();
                    new_task.retry_count += 1;

                    // 计算退避延迟
                    let delay = Duration::from_millis(
                        (config.retry_delay.as_millis() as f64 *
                         config.backoff_multiplier.powi(new_task.retry_count as i32)) as u64
                    );

                    new_task.scheduled_time = Instant::now() + delay;

                    // 重新调度任务
                    let queue_clone = queue.clone();
                    tokio::spawn(async move {
                        let mut queue_guard = queue_clone.lock().await;
                        queue_guard.push(new_task);
                    });
                }
            }
        }
    }

    async fn run_task(task: &ScheduledTask) -> Result<(), Box<dyn std::error::Error>> {
        use tokio::process::Command;
        use tokio::time::timeout;

        let mut cmd = Command::new(&task.command);
        cmd.args(&task.args);

        let execution_future = async {
            let output = cmd.output().await?;

            if output.status.success() {
                println!("任务 {} 输出: {}", task.id, String::from_utf8_lossy(&output.stdout));
                Ok(())
            } else {
                Err(format!("任务执行失败: {}", String::from_utf8_lossy(&output.stderr)).into())
            }
        };

        timeout(task.estimated_duration, execution_future).await
            .map_err(|_| "任务执行超时".into())?
    }

    pub async fn get_scheduler_status(&self) -> SchedulerStatus {
        let queue = self.task_queue.lock().await;
        let running_tasks = self.running_tasks.read().await;

        SchedulerStatus {
            queued_tasks: queue.len(),
            running_tasks: running_tasks.len(),
            max_concurrent: self.max_concurrent,
            next_scheduled_time: queue.peek().map(|t| t.scheduled_time),
        }
    }
}

#[derive(Debug)]
pub struct SchedulerStatus {
    pub queued_tasks: usize,
    pub running_tasks: usize,
    pub max_concurrent: usize,
    pub next_scheduled_time: Option<Instant>,
}

#[derive(Debug, thiserror::Error)]
pub enum SchedulerError {
    #[error("调度器错误: {0}")]
    Generic(String),
}
```

## 3. 异步进程监控

### 3.1 实时进程监控

```rust
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use tokio::time::{interval, Duration};
use std::collections::HashMap;

pub struct AsyncProcessMonitor {
    monitored_processes: Arc<RwLock<HashMap<String, MonitoredProcess>>>,
    check_interval: Duration,
    alert_thresholds: AlertThresholds,
    alert_callbacks: Arc<Mutex<Vec<AlertCallback>>>,
}

#[derive(Debug, Clone)]
pub struct MonitoredProcess {
    pub id: String,
    pub pid: u32,
    pub name: String,
    pub created_at: std::time::Instant,
    pub last_check: std::time::Instant,
    pub status: ProcessStatus,
    pub metrics: ProcessMetrics,
    pub alert_history: Vec<Alert>,
}

#[derive(Debug, Clone)]
pub struct ProcessMetrics {
    pub memory_usage_mb: u64,
    pub cpu_percent: f64,
    pub file_descriptors: u32,
    pub response_time: Duration,
    pub error_count: u64,
    pub success_count: u64,
    pub throughput: f64,
}

#[derive(Debug, Clone)]
pub struct Alert {
    pub id: String,
    pub process_id: String,
    pub alert_type: AlertType,
    pub severity: AlertSeverity,
    pub message: String,
    pub timestamp: std::time::Instant,
    pub resolved: bool,
}

#[derive(Debug, Clone)]
pub enum AlertType {
    MemoryUsage,
    CpuUsage,
    ResponseTime,
    ErrorRate,
    ProcessDown,
    ProcessHung,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AlertSeverity {
    Info,
    Warning,
    Critical,
    Emergency,
}

#[derive(Debug, Clone)]
pub struct AlertThresholds {
    pub max_memory_mb: u64,
    pub max_cpu_percent: f64,
    pub max_response_time: Duration,
    pub max_error_rate: f64,
    pub max_idle_time: Duration,
}

pub type AlertCallback = Box<dyn Fn(Alert) + Send + Sync>;

impl AsyncProcessMonitor {
    pub fn new(check_interval: Duration, thresholds: AlertThresholds) -> Self {
        Self {
            monitored_processes: Arc::new(RwLock::new(HashMap::new())),
            check_interval,
            alert_thresholds: thresholds,
            alert_callbacks: Arc::new(Mutex::new(Vec::new())),
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
        let mut processes = self.monitored_processes.write().await;

        for (process_id, process) in processes.iter_mut() {
            let metrics = self.collect_process_metrics(process.pid).await?;
            process.metrics = metrics.clone();
            process.last_check = std::time::Instant::now();

            // 检查警报条件
            self.check_alerts(process, &metrics).await;
        }

        Ok(())
    }

    async fn collect_process_metrics(&self, pid: u32) -> Result<ProcessMetrics, Box<dyn std::error::Error>> {
        use tokio::process::Command;

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
            file_descriptors: 0, // 实际实现中需要收集
            response_time,
            error_count: 0, // 实际实现中需要维护
            success_count: 0, // 实际实现中需要维护
            throughput: 0.0, // 实际实现中需要计算
        })
    }

    async fn measure_response_time(&self, pid: u32) -> Duration {
        let start = std::time::Instant::now();

        let health_check_result = tokio::process::Command::new("kill")
            .arg("-0")
            .arg(pid.to_string())
            .output()
            .await;

        match health_check_result {
            Ok(output) if output.status.success() => start.elapsed(),
            _ => Duration::MAX,
        }
    }

    async fn check_alerts(&self, process: &mut MonitoredProcess, metrics: &ProcessMetrics) {
        let mut new_alerts = Vec::new();

        // 检查内存使用
        if metrics.memory_usage_mb > self.alert_thresholds.max_memory_mb {
            let alert = Alert {
                id: uuid::Uuid::new_v4().to_string(),
                process_id: process.id.clone(),
                alert_type: AlertType::MemoryUsage,
                severity: AlertSeverity::Critical,
                message: format!(
                    "进程 {} 内存使用过高: {} MB (限制: {} MB)",
                    process.name, metrics.memory_usage_mb, self.alert_thresholds.max_memory_mb
                ),
                timestamp: std::time::Instant::now(),
                resolved: false,
            };
            new_alerts.push(alert);
        }

        // 检查CPU使用
        if metrics.cpu_percent > self.alert_thresholds.max_cpu_percent {
            let alert = Alert {
                id: uuid::Uuid::new_v4().to_string(),
                process_id: process.id.clone(),
                alert_type: AlertType::CpuUsage,
                severity: AlertSeverity::Warning,
                message: format!(
                    "进程 {} CPU使用过高: {:.2}% (限制: {:.2}%)",
                    process.name, metrics.cpu_percent, self.alert_thresholds.max_cpu_percent
                ),
                timestamp: std::time::Instant::now(),
                resolved: false,
            };
            new_alerts.push(alert);
        }

        // 检查响应时间
        if metrics.response_time > self.alert_thresholds.max_response_time {
            let alert = Alert {
                id: uuid::Uuid::new_v4().to_string(),
                process_id: process.id.clone(),
                alert_type: AlertType::ResponseTime,
                severity: AlertSeverity::Warning,
                message: format!(
                    "进程 {} 响应时间过长: {:?} (限制: {:?})",
                    process.name, metrics.response_time, self.alert_thresholds.max_response_time
                ),
                timestamp: std::time::Instant::now(),
                resolved: false,
            };
            new_alerts.push(alert);
        }

        // 触发警报回调
        for alert in new_alerts {
            process.alert_history.push(alert.clone());
            self.trigger_alert_callbacks(alert).await;
        }
    }

    async fn trigger_alert_callbacks(&self, alert: Alert) {
        let callbacks = self.alert_callbacks.lock().await;
        for callback in callbacks.iter() {
            callback(alert.clone());
        }
    }

    pub async fn add_alert_callback(&self, callback: AlertCallback) {
        let mut callbacks = self.alert_callbacks.lock().await;
        callbacks.push(callback);
    }

    pub async fn add_process(&self, process_id: String, pid: u32, name: String) {
        let mut processes = self.monitored_processes.write().await;

        let monitored_process = MonitoredProcess {
            id: process_id,
            pid,
            name,
            created_at: std::time::Instant::now(),
            last_check: std::time::Instant::now(),
            status: ProcessStatus::Starting,
            metrics: ProcessMetrics {
                memory_usage_mb: 0,
                cpu_percent: 0.0,
                file_descriptors: 0,
                response_time: Duration::ZERO,
                error_count: 0,
                success_count: 0,
                throughput: 0.0,
            },
            alert_history: Vec::new(),
        };

        processes.insert(monitored_process.id.clone(), monitored_process);
    }

    pub async fn get_process_status(&self, process_id: &str) -> Option<MonitoredProcess> {
        let processes = self.monitored_processes.read().await;
        processes.get(process_id).cloned()
    }

    pub async fn get_all_processes(&self) -> Vec<MonitoredProcess> {
        let processes = self.monitored_processes.read().await;
        processes.values().cloned().collect()
    }
}
```

## 4. 错误处理与恢复

### 4.1 异步错误处理

```rust
use std::time::Duration;
use tokio::time::{timeout, sleep};
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct AsyncErrorHandler {
    retry_policies: Arc<Mutex<HashMap<String, RetryPolicy>>>,
    error_callbacks: Arc<Mutex<Vec<ErrorCallback>>>,
    recovery_strategies: Arc<Mutex<HashMap<String, RecoveryStrategy>>>,
}

#[derive(Debug, Clone)]
pub struct RetryPolicy {
    pub max_retries: u32,
    pub initial_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
    pub jitter: bool,
}

#[derive(Debug, Clone)]
pub enum RecoveryStrategy {
    RestartProcess,
    ReplaceProcess,
    ScaleUp,
    ScaleDown,
    NotifyAdmin,
    DoNothing,
}

pub type ErrorCallback = Box<dyn Fn(ProcessError) + Send + Sync>;

#[derive(Debug, thiserror::Error)]
pub enum ProcessError {
    #[error("进程启动失败: {0}")]
    StartupFailed(String),

    #[error("进程执行超时: {0}")]
    ExecutionTimeout(Duration),

    #[error("进程崩溃: {0}")]
    ProcessCrashed(String),

    #[error("资源不足: {0}")]
    ResourceExhausted(String),

    #[error("通信错误: {0}")]
    CommunicationError(String),

    #[error("权限错误: {0}")]
    PermissionError(String),
}

impl AsyncErrorHandler {
    pub fn new() -> Self {
        Self {
            retry_policies: Arc::new(Mutex::new(HashMap::new())),
            error_callbacks: Arc::new(Mutex::new(Vec::new())),
            recovery_strategies: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub async fn set_retry_policy(&self, process_id: String, policy: RetryPolicy) {
        let mut policies = self.retry_policies.lock().await;
        policies.insert(process_id, policy);
    }

    pub async fn set_recovery_strategy(&self, process_id: String, strategy: RecoveryStrategy) {
        let mut strategies = self.recovery_strategies.lock().await;
        strategies.insert(process_id, strategy);
    }

    pub async fn add_error_callback(&self, callback: ErrorCallback) {
        let mut callbacks = self.error_callbacks.lock().await;
        callbacks.push(callback);
    }

    pub async fn handle_error(
        &self,
        process_id: &str,
        error: ProcessError,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 触发错误回调
        self.trigger_error_callbacks(error.clone()).await;

        // 获取重试策略
        let retry_policy = {
            let policies = self.retry_policies.lock().await;
            policies.get(process_id).cloned()
        };

        if let Some(policy) = retry_policy {
            return self.retry_with_policy(process_id, error, policy).await;
        }

        // 获取恢复策略
        let recovery_strategy = {
            let strategies = self.recovery_strategies.lock().await;
            strategies.get(process_id).cloned()
        };

        if let Some(strategy) = recovery_strategy {
            return self.execute_recovery_strategy(process_id, error, strategy).await;
        }

        Err("没有配置错误处理策略".into())
    }

    async fn retry_with_policy(
        &self,
        process_id: &str,
        error: ProcessError,
        policy: RetryPolicy,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut current_delay = policy.initial_delay;
        let mut attempt = 0;

        while attempt < policy.max_retries {
            attempt += 1;

            println!(
                "重试进程 {} (尝试 {}/{}): {}",
                process_id, attempt, policy.max_retries, error
            );

            // 等待重试延迟
            if policy.jitter {
                let jitter = Duration::from_millis(
                    (current_delay.as_millis() as f64 * 0.1 * rand::random::<f64>()) as u64
                );
                sleep(current_delay + jitter).await;
            } else {
                sleep(current_delay).await;
            }

            // 尝试恢复进程
            match self.attempt_process_recovery(process_id).await {
                Ok(_) => {
                    println!("进程 {} 恢复成功", process_id);
                    return Ok(());
                }
                Err(e) => {
                    println!("进程 {} 恢复失败: {}", process_id, e);

                    // 计算下次延迟
                    current_delay = Duration::from_millis(
                        (current_delay.as_millis() as f64 * policy.backoff_multiplier) as u64
                    );

                    if current_delay > policy.max_delay {
                        current_delay = policy.max_delay;
                    }
                }
            }
        }

        Err(format!("进程 {} 重试 {} 次后仍然失败", process_id, policy.max_retries).into())
    }

    async fn attempt_process_recovery(
        &self,
        process_id: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 实际实现中，这里应该包含具体的恢复逻辑
        // 例如：重启进程、替换进程、清理资源等

        // 模拟恢复过程
        sleep(Duration::from_millis(100)).await;

        // 模拟恢复成功/失败
        if rand::random::<f64>() > 0.3 {
            Ok(())
        } else {
            Err("恢复失败".into())
        }
    }

    async fn execute_recovery_strategy(
        &self,
        process_id: &str,
        error: ProcessError,
        strategy: RecoveryStrategy,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match strategy {
            RecoveryStrategy::RestartProcess => {
                println!("重启进程 {}", process_id);
                self.restart_process(process_id).await
            }
            RecoveryStrategy::ReplaceProcess => {
                println!("替换进程 {}", process_id);
                self.replace_process(process_id).await
            }
            RecoveryStrategy::ScaleUp => {
                println!("扩展进程池 {}", process_id);
                self.scale_up_processes(process_id).await
            }
            RecoveryStrategy::ScaleDown => {
                println!("缩减进程池 {}", process_id);
                self.scale_down_processes(process_id).await
            }
            RecoveryStrategy::NotifyAdmin => {
                println!("通知管理员: 进程 {} 发生错误: {}", process_id, error);
                Ok(())
            }
            RecoveryStrategy::DoNothing => {
                println!("忽略错误: 进程 {} 发生错误: {}", process_id, error);
                Ok(())
            }
        }
    }

    async fn restart_process(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 实际实现中应该包含重启逻辑
        sleep(Duration::from_millis(500)).await;
        Ok(())
    }

    async fn replace_process(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 实际实现中应该包含替换逻辑
        sleep(Duration::from_millis(1000)).await;
        Ok(())
    }

    async fn scale_up_processes(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 实际实现中应该包含扩展逻辑
        sleep(Duration::from_millis(2000)).await;
        Ok(())
    }

    async fn scale_down_processes(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        // 实际实现中应该包含缩减逻辑
        sleep(Duration::from_millis(1000)).await;
        Ok(())
    }

    async fn trigger_error_callbacks(&self, error: ProcessError) {
        let callbacks = self.error_callbacks.lock().await;
        for callback in callbacks.iter() {
            callback(error.clone());
        }
    }
}
```

## 5. 总结

本章详细介绍了 Rust 中的异步进程管理：

1. **异步进程基础**: 异步进程创建、管理和通信
2. **异步进程池**: 高效的进程复用和任务调度
3. **异步任务调度**: 基于优先级的任务调度系统
4. **异步进程监控**: 实时监控和警报系统
5. **错误处理与恢复**: 完善的错误处理和自动恢复机制

这些技术为构建高性能、高可用的异步进程管理系统提供了坚实的基础，能够充分利用 Rust 的异步特性和现代运行时。
