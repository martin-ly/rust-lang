# C07-11. 实用案例与代码示例 (Rust 1.90 增强版)

## 目录

- [C07-11. 实用案例与代码示例 (Rust 1.90 增强版)](#c07-11-实用案例与代码示例-rust-190-增强版)
  - [目录](#目录)
  - [1. Rust 1.90 新特性应用示例](#1-rust-190-新特性应用示例)
    - [1.1 异步闭包进程管理](#11-异步闭包进程管理)
    - [1.2 改进模式匹配错误处理](#12-改进模式匹配错误处理)
    - [1.3 增强迭代器进程处理](#13-增强迭代器进程处理)
  - [2. 现代库集成示例](#2-现代库集成示例)
    - [2.1 Tokio 异步进程管理](#21-tokio-异步进程管理)
    - [2.2 Async-Std 进程处理](#22-async-std-进程处理)
    - [2.3 Duct 链式命令执行](#23-duct-链式命令执行)
    - [2.4 Subprocess 高级进程控制](#24-subprocess-高级进程控制)
  - [3. 企业级应用场景](#3-企业级应用场景)
    - [3.1 微服务编排系统](#31-微服务编排系统)
    - [3.2 分布式任务调度](#32-分布式任务调度)

本章提供基于 Rust 1.90 的丰富实用案例和代码示例，涵盖从基础到企业级的各种应用场景，展示现代 Rust 进程管理的最佳实践。

## 1. Rust 1.90 新特性应用示例

### 1.1 异步闭包进程管理

Rust 1.90 引入了异步闭包，为进程管理提供了更强大的异步编程能力：

```rust
use std::process::{Command, Stdio};
use std::time::Duration;
use tokio::time::timeout;
use std::sync::Arc;
use tokio::sync::Mutex;

// 异步闭包进程执行器
pub struct AsyncClosureProcessExecutor {
    processes: Arc<Mutex<Vec<AsyncProcess>>>,
    max_concurrent: usize,
}

#[derive(Debug)]
pub struct AsyncProcess {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub status: ProcessStatus,
    pub created_at: std::time::Instant,
    pub metadata: ProcessMetadata,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Timeout,
}

#[derive(Debug, Clone)]
pub struct ProcessMetadata {
    pub timeout: Duration,
    pub retry_count: u32,
    pub max_retries: u32,
    pub priority: ProcessPriority,
}

#[derive(Debug, Clone)]
pub enum ProcessPriority {
    Low,
    Normal,
    High,
    Critical,
}

impl AsyncClosureProcessExecutor {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            processes: Arc::new(Mutex::new(Vec::new())),
            max_concurrent,
        }
    }

    // 使用异步闭包执行进程
    pub async fn execute_with_async_closure<F, Fut>(
        &self,
        command: String,
        args: Vec<String>,
        metadata: ProcessMetadata,
        async_handler: F,
    ) -> Result<String, ProcessError>
    where
        F: FnOnce(&AsyncProcess) -> Fut,
        Fut: std::future::Future<Output = Result<String, ProcessError>>,
    {
        let process_id = uuid::Uuid::new_v4().to_string();
        
        let process = AsyncProcess {
            id: process_id.clone(),
            command: command.clone(),
            args: args.clone(),
            status: ProcessStatus::Pending,
            created_at: std::time::Instant::now(),
            metadata: metadata.clone(),
        };

        // 添加到进程列表
        {
            let mut processes = self.processes.lock().await;
            processes.push(process.clone());
        }

        // 更新状态为运行中
        {
            let mut processes = self.processes.lock().await;
            if let Some(p) = processes.iter_mut().find(|p| p.id == process_id) {
                p.status = ProcessStatus::Running;
            }
        }

        // 执行异步闭包处理
        let result = async_handler(&process).await;

        // 更新最终状态
        {
            let mut processes = self.processes.lock().await;
            if let Some(p) = processes.iter_mut().find(|p| p.id == process_id) {
                p.status = match &result {
                    Ok(_) => ProcessStatus::Completed,
                    Err(_) => ProcessStatus::Failed,
                };
            }
        }

        result
    }

    // 批量执行异步闭包
    pub async fn execute_batch_with_closure<F, Fut>(
        &self,
        commands: Vec<(String, Vec<String>, ProcessMetadata)>,
        batch_handler: F,
    ) -> Result<Vec<Result<String, ProcessError>>, ProcessError>
    where
        F: Fn(Vec<AsyncProcess>) -> Fut,
        Fut: std::future::Future<Output = Result<Vec<Result<String, ProcessError>>, ProcessError>>,
    {
        let mut processes = Vec::new();
        
        for (command, args, metadata) in commands {
            let process_id = uuid::Uuid::new_v4().to_string();
            let process = AsyncProcess {
                id: process_id,
                command,
                args,
                status: ProcessStatus::Pending,
                created_at: std::time::Instant::now(),
                metadata,
            };
            processes.push(process);
        }

        // 添加到进程列表
        {
            let mut process_list = self.processes.lock().await;
            process_list.extend(processes.clone());
        }

        // 执行批量处理
        batch_handler(processes).await
    }

    // 带超时的异步闭包执行
    pub async fn execute_with_timeout_closure<F, Fut>(
        &self,
        command: String,
        args: Vec<String>,
        timeout_duration: Duration,
        timeout_handler: F,
    ) -> Result<String, ProcessError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<String, ProcessError>>,
    {
        match timeout(timeout_duration, async {
            let mut cmd = Command::new(&command);
            cmd.args(&args);
            cmd.output()
        }).await {
            Ok(output_result) => {
                match output_result {
                    Ok(output) => {
                        if output.status.success() {
                            Ok(String::from_utf8_lossy(&output.stdout).to_string())
                        } else {
                            Err(ProcessError::ExecutionFailed(format!(
                                "Command failed: {}",
                                String::from_utf8_lossy(&output.stderr)
                            )))
                        }
                    }
                    Err(e) => Err(ProcessError::SpawnFailed(e.to_string())),
                }
            }
            Err(_) => {
                // 超时处理
                timeout_handler().await
            }
        }
    }

    // 获取进程统计信息
    pub async fn get_process_stats(&self) -> ProcessStats {
        let processes = self.processes.lock().await;
        
        let total = processes.len();
        let running = processes.iter().filter(|p| matches!(p.status, ProcessStatus::Running)).count();
        let completed = processes.iter().filter(|p| matches!(p.status, ProcessStatus::Completed)).count();
        let failed = processes.iter().filter(|p| matches!(p.status, ProcessStatus::Failed)).count();
        
        ProcessStats {
            total_processes: total,
            running_processes: running,
            completed_processes: completed,
            failed_processes: failed,
        }
    }
}

#[derive(Debug)]
pub struct ProcessStats {
    pub total_processes: usize,
    pub running_processes: usize,
    pub completed_processes: usize,
    pub failed_processes: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum ProcessError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(String),
    
    #[error("进程执行失败: {0}")]
    ExecutionFailed(String),
    
    #[error("进程超时")]
    Timeout,
    
    #[error("未知错误: {0}")]
    Unknown(String),
}

// 使用示例
pub async fn async_closure_example() -> Result<(), Box<dyn std::error::Error>> {
    let executor = AsyncClosureProcessExecutor::new(10);
    
    // 单个进程执行
    let metadata = ProcessMetadata {
        timeout: Duration::from_secs(30),
        retry_count: 0,
        max_retries: 3,
        priority: ProcessPriority::Normal,
    };
    
    let result = executor.execute_with_async_closure(
        "echo".to_string(),
        vec!["Hello, Async Closure!".to_string()],
        metadata,
        |process| async move {
            println!("处理进程: {:?}", process);
            Ok("执行成功".to_string())
        },
    ).await?;
    
    println!("执行结果: {}", result);
    
    // 批量执行
    let commands = vec![
        ("echo".to_string(), vec!["Batch 1".to_string()], metadata.clone()),
        ("echo".to_string(), vec!["Batch 2".to_string()], metadata.clone()),
        ("echo".to_string(), vec!["Batch 3".to_string()], metadata.clone()),
    ];
    
    let batch_results = executor.execute_batch_with_closure(
        commands,
        |processes| async move {
            println!("批量处理 {} 个进程", processes.len());
            Ok(vec![Ok("成功".to_string()); processes.len()])
        },
    ).await?;
    
    println!("批量执行结果: {:?}", batch_results);
    
    // 带超时的执行
    let timeout_result = executor.execute_with_timeout_closure(
        "sleep".to_string(),
        vec!["2".to_string()],
        Duration::from_secs(1),
        || async move {
            println!("进程执行超时，执行超时处理逻辑");
            Ok("超时处理完成".to_string())
        },
    ).await?;
    
    println!("超时处理结果: {}", timeout_result);
    
    // 获取统计信息
    let stats = executor.get_process_stats().await;
    println!("进程统计: {:?}", stats);
    
    Ok(())
}
```

### 1.2 改进模式匹配错误处理

Rust 1.90 改进了模式匹配，使错误处理更加精确和优雅：

```rust
use std::process::{Command, Stdio};
use std::io::{self, ErrorKind};
use thiserror::Error;

// 增强的错误类型
#[derive(Error, Debug)]
pub enum EnhancedProcessError {
    #[error("进程启动失败: {command} - {source}")]
    SpawnFailed { 
        command: String, 
        source: std::io::Error,
    },
    
    #[error("进程执行超时: {command} (超时时间: {timeout:?})")]
    Timeout { 
        command: String, 
        timeout: std::time::Duration,
    },
    
    #[error("进程执行失败: {command} (退出码: {exit_code})")]
    ExecutionFailed { 
        command: String, 
        exit_code: Option<i32>,
    },
    
    #[error("资源不足: {resource}")]
    ResourceExhausted { 
        resource: String,
    },
    
    #[error("权限不足: {operation}")]
    PermissionDenied { 
        operation: String,
    },
    
    #[error("配置错误: {config}")]
    ConfigurationError { 
        config: String,
    },
}

// 增强的进程执行器
pub struct EnhancedProcessExecutor {
    config: ProcessConfig,
    resource_monitor: ResourceMonitor,
}

#[derive(Debug, Clone)]
pub struct ProcessConfig {
    pub max_concurrent_processes: usize,
    pub default_timeout: std::time::Duration,
    pub retry_attempts: u32,
    pub resource_limits: ResourceLimits,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_percent: f64,
    pub max_file_descriptors: u32,
}

pub struct ResourceMonitor {
    current_processes: std::sync::Arc<std::sync::Mutex<usize>>,
    memory_usage: std::sync::Arc<std::sync::Mutex<u64>>,
}

impl EnhancedProcessExecutor {
    pub fn new(config: ProcessConfig) -> Self {
        Self {
            config,
            resource_monitor: ResourceMonitor::new(),
        }
    }
    
    // 检查资源可用性
    async fn check_resources(&self) -> Result<(), EnhancedProcessError> {
        let current_processes = self.resource_monitor.current_processes.lock().unwrap();
        
        if *current_processes >= self.config.max_concurrent_processes {
            return Err(EnhancedProcessError::ResourceExhausted {
                resource: "并发进程数".to_string(),
            });
        }
        
        Ok(())
    }
    
    // 启动进程并等待
    async fn spawn_and_wait(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<std::process::Output, EnhancedProcessError> {
        // 检查资源
        self.check_resources().await?;
        
        // 启动进程
        let mut cmd = Command::new(command);
        cmd.args(args);
        cmd.stdout(Stdio::piped());
        cmd.stderr(Stdio::piped());
        
        let output = cmd.output().map_err(|e| {
            // 使用改进的模式匹配处理不同的错误类型
            match e.kind() {
                ErrorKind::NotFound => EnhancedProcessError::SpawnFailed {
                    command: command.to_string(),
                    source: e,
                },
                ErrorKind::PermissionDenied => EnhancedProcessError::PermissionDenied {
                    operation: format!("执行命令: {}", command),
                },
                ErrorKind::ResourceUnavailable => EnhancedProcessError::ResourceExhausted {
                    resource: "系统资源".to_string(),
                },
                _ => EnhancedProcessError::SpawnFailed {
                    command: command.to_string(),
                    source: e,
                },
            }
        })?;
        
        Ok(output)
    }
    
    // 执行进程并处理错误
    pub async fn execute_with_enhanced_error_handling(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, EnhancedProcessError> {
        let output = self.spawn_and_wait(command, args).await?;
        
        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(EnhancedProcessError::ExecutionFailed {
                command: command.to_string(),
                exit_code: output.status.code(),
            })
        }
    }
    
    // 带重试的执行
    pub async fn execute_with_recovery(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, EnhancedProcessError> {
        let mut last_error = None;
        
        for attempt in 0..=self.config.retry_attempts {
            match self.execute_with_enhanced_error_handling(command, args).await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);
                    
                    if attempt < self.config.retry_attempts {
                        // 等待一段时间后重试
                        tokio::time::sleep(std::time::Duration::from_millis(100 * (attempt + 1) as u64)).await;
                    }
                }
            }
        }
        
        Err(last_error.unwrap())
    }
}

impl ResourceMonitor {
    pub fn new() -> Self {
        Self {
            current_processes: std::sync::Arc::new(std::sync::Mutex::new(0)),
            memory_usage: std::sync::Arc::new(std::sync::Mutex::new(0)),
        }
    }
}

// 使用示例
pub async fn enhanced_error_handling_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = ProcessConfig {
        max_concurrent_processes: 10,
        default_timeout: std::time::Duration::from_secs(30),
        retry_attempts: 3,
        resource_limits: ResourceLimits {
            max_memory_mb: 1024,
            max_cpu_percent: 80.0,
            max_file_descriptors: 1000,
        },
    };
    
    let executor = EnhancedProcessExecutor::new(config);
    
    // 正常执行
    let result = executor.execute_with_enhanced_error_handling(
        "echo",
        &["Hello, Enhanced Error Handling!".to_string()],
    ).await?;
    
    println!("执行结果: {}", result);
    
    // 带重试的执行
    let retry_result = executor.execute_with_recovery(
        "ls",
        &["-la".to_string()],
    ).await?;
    
    println!("重试执行结果: {}", retry_result);
    
    // 错误处理示例
    match executor.execute_with_enhanced_error_handling(
        "nonexistent_command",
        &[],
    ).await {
        Ok(result) => println!("意外成功: {}", result),
        Err(EnhancedProcessError::SpawnFailed { command, source }) => {
            println!("进程启动失败: {} - {}", command, source);
        }
        Err(EnhancedProcessError::PermissionDenied { operation }) => {
            println!("权限不足: {}", operation);
        }
        Err(EnhancedProcessError::ResourceExhausted { resource }) => {
            println!("资源不足: {}", resource);
        }
        Err(e) => println!("其他错误: {}", e),
    }
    
    Ok(())
}
```

### 1.3 增强迭代器进程处理

Rust 1.90 增强了迭代器功能，使进程批处理更加高效：

```rust
use std::process::Command;
use std::time::Duration;
use std::collections::HashMap;

// 进程批处理器
pub struct ProcessBatchProcessor {
    processes: Vec<ProcessTask>,
    batch_size: usize,
    timeout: Duration,
}

#[derive(Debug, Clone)]
pub struct ProcessTask {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub priority: TaskPriority,
    pub dependencies: Vec<String>,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

#[derive(Debug)]
pub struct ProcessResult {
    pub task_id: String,
    pub success: bool,
    pub output: String,
    pub error: Option<String>,
    pub duration: Duration,
    pub exit_code: Option<i32>,
}

impl ProcessBatchProcessor {
    pub fn new(batch_size: usize, timeout: Duration) -> Self {
        Self {
            processes: Vec::new(),
            batch_size,
            timeout,
        }
    }
    
    // 添加任务
    pub fn add_task(&mut self, task: ProcessTask) {
        self.processes.push(task);
    }
    
    // 批量处理进程
    pub async fn process_batch(&mut self) -> Result<Vec<ProcessResult>, ProcessError> {
        // 按优先级排序
        self.processes.sort_by(|a, b| b.priority.cmp(&a.priority));
        
        // 检查依赖关系
        self.validate_dependencies()?;
        
        // 分批处理
        let mut results = Vec::new();
        let chunks: Vec<_> = self.processes.chunks(self.batch_size).collect();
        
        for chunk in chunks {
            let chunk_results = self.process_batch_chunk(chunk).await?;
            results.extend(chunk_results);
        }
        
        Ok(results)
    }
    
    // 处理单个批次
    async fn process_batch_chunk(&self, batch: &[ProcessTask]) -> Result<Vec<ProcessResult>, ProcessError> {
        let mut handles = Vec::new();
        
        for task in batch {
            let task_clone = task.clone();
            let handle = tokio::spawn(async move {
                Self::execute_task(&task_clone).await
            });
            handles.push(handle);
        }
        
        let mut results = Vec::new();
        for handle in handles {
            match handle.await {
                Ok(result) => results.push(result),
                Err(e) => {
                    return Err(ProcessError::TaskExecutionFailed(e.to_string()));
                }
            }
        }
        
        Ok(results)
    }
    
    // 执行单个任务
    async fn execute_task(task: &ProcessTask) -> ProcessResult {
        let start_time = std::time::Instant::now();
        
        let mut cmd = Command::new(&task.command);
        cmd.args(&task.args);
        
        match cmd.output() {
            Ok(output) => {
                let duration = start_time.elapsed();
                let success = output.status.success();
                
                ProcessResult {
                    task_id: task.id.clone(),
                    success,
                    output: String::from_utf8_lossy(&output.stdout).to_string(),
                    error: if success {
                        None
                    } else {
                        Some(String::from_utf8_lossy(&output.stderr).to_string())
                    },
                    duration,
                    exit_code: output.status.code(),
                }
            }
            Err(e) => {
                let duration = start_time.elapsed();
                ProcessResult {
                    task_id: task.id.clone(),
                    success: false,
                    output: String::new(),
                    error: Some(e.to_string()),
                    duration,
                    exit_code: None,
                }
            }
        }
    }
    
    // 验证依赖关系
    fn validate_dependencies(&self) -> Result<(), ProcessError> {
        let task_ids: std::collections::HashSet<_> = self.processes.iter().map(|t| &t.id).collect();
        
        for task in &self.processes {
            for dep in &task.dependencies {
                if !task_ids.contains(dep) {
                    return Err(ProcessError::DependencyNotFound {
                        task_id: task.id.clone(),
                        dependency: dep.clone(),
                    });
                }
            }
        }
        
        Ok(())
    }
    
    // 分析结果
    pub fn analyze_results(&self, results: &[ProcessResult]) -> ProcessAnalysis {
        let total = results.len();
        let successful = results.iter().filter(|r| r.success).count();
        let failed = total - successful;
        
        let total_duration: Duration = results.iter().map(|r| r.duration).sum();
        let avg_duration = if total > 0 {
            Duration::from_nanos(total_duration.as_nanos() as u64 / total as u64)
        } else {
            Duration::ZERO
        };
        
        let mut error_counts = HashMap::new();
        for result in results {
            if let Some(error) = &result.error {
                let count = error_counts.entry(error.clone()).or_insert(0);
                *count += 1;
            }
        }
        
        ProcessAnalysis {
            total_tasks: total,
            successful_tasks: successful,
            failed_tasks: failed,
            success_rate: if total > 0 { successful as f64 / total as f64 } else { 0.0 },
            total_duration,
            average_duration: avg_duration,
            common_errors: error_counts,
        }
    }
    
    // 优化批次大小
    pub fn optimize_batch_size(&self, results: &[ProcessResult]) -> usize {
        let analysis = self.analyze_results(results);
        
        // 基于成功率调整批次大小
        if analysis.success_rate > 0.9 {
            // 高成功率，可以增加批次大小
            (self.batch_size * 2).min(50)
        } else if analysis.success_rate < 0.7 {
            // 低成功率，减少批次大小
            (self.batch_size / 2).max(1)
        } else {
            // 中等成功率，保持当前批次大小
            self.batch_size
        }
    }
}

#[derive(Debug)]
pub struct ProcessAnalysis {
    pub total_tasks: usize,
    pub successful_tasks: usize,
    pub failed_tasks: usize,
    pub success_rate: f64,
    pub total_duration: Duration,
    pub average_duration: Duration,
    pub common_errors: HashMap<String, u32>,
}

#[derive(Debug, thiserror::Error)]
pub enum ProcessError {
    #[error("任务执行失败: {0}")]
    TaskExecutionFailed(String),
    
    #[error("依赖未找到: 任务 {task_id} 依赖 {dependency}")]
    DependencyNotFound { 
        task_id: String, 
        dependency: String,
    },
    
    #[error("批次处理超时")]
    BatchTimeout,
}

// 使用示例
pub async fn enhanced_iterator_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut processor = ProcessBatchProcessor::new(3, Duration::from_secs(30));
    
    // 添加任务
    processor.add_task(ProcessTask {
        id: "task1".to_string(),
        command: "echo".to_string(),
        args: vec!["Task 1".to_string()],
        priority: TaskPriority::High,
        dependencies: Vec::new(),
        metadata: HashMap::new(),
    });
    
    processor.add_task(ProcessTask {
        id: "task2".to_string(),
        command: "echo".to_string(),
        args: vec!["Task 2".to_string()],
        priority: TaskPriority::Normal,
        dependencies: vec!["task1".to_string()],
        metadata: HashMap::new(),
    });
    
    processor.add_task(ProcessTask {
        id: "task3".to_string(),
        command: "echo".to_string(),
        args: vec!["Task 3".to_string()],
        priority: TaskPriority::Low,
        dependencies: Vec::new(),
        metadata: HashMap::new(),
    });
    
    // 批量处理
    let results = processor.process_batch().await?;
    
    // 分析结果
    let analysis = processor.analyze_results(&results);
    println!("处理分析: {:?}", analysis);
    
    // 优化批次大小
    let optimized_size = processor.optimize_batch_size(&results);
    println!("优化后的批次大小: {}", optimized_size);
    
    // 显示结果
    for result in results {
        println!("任务 {}: {} ({:?})", 
            result.task_id, 
            if result.success { "成功" } else { "失败" },
            result.duration
        );
    }
    
    Ok(())
}
```

## 2. 现代库集成示例

### 2.1 Tokio 异步进程管理

使用 Tokio 进行异步进程管理：

```rust
use tokio::process::{Command as TokioCommand, Child};
use tokio::sync::{Mutex, Semaphore};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};

// Tokio 异步进程管理器
pub struct TokioProcessManager {
    active_processes: Arc<Mutex<HashMap<String, TokioProcess>>>,
    process_semaphore: Arc<Semaphore>,
    config: TokioProcessConfig,
}

#[derive(Debug, Clone)]
pub struct TokioProcessConfig {
    pub max_concurrent_processes: usize,
    pub default_timeout: Duration,
    pub health_check_interval: Duration,
    pub auto_cleanup: bool,
}

#[derive(Debug)]
pub struct TokioProcess {
    pub id: String,
    pub child: Child,
    pub status: TokioProcessStatus,
    pub metadata: TokioProcessMetadata,
    pub created_at: Instant,
}

#[derive(Debug, Clone)]
pub enum TokioProcessStatus {
    Starting,
    Running,
    Completed,
    Failed,
    Timeout,
    Terminated,
}

#[derive(Debug, Clone)]
pub struct TokioProcessMetadata {
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub environment: HashMap<String, String>,
    pub priority: ProcessPriority,
    pub resource_limits: ResourceLimits,
}

#[derive(Debug, Clone)]
pub enum ProcessPriority {
    Low,
    Normal,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_percent: f64,
    pub max_file_descriptors: u32,
}

impl TokioProcessManager {
    pub fn new(config: TokioProcessConfig) -> Self {
        Self {
            active_processes: Arc::new(Mutex::new(HashMap::new())),
            process_semaphore: Arc::new(Semaphore::new(config.max_concurrent_processes)),
            config,
        }
    }
    
    // 启动进程
    pub async fn spawn_process(
        &self,
        command: String,
        args: Vec<String>,
        metadata: TokioProcessMetadata,
    ) -> Result<String, TokioProcessError> {
        let _permit = self.process_semaphore.acquire().await
            .map_err(|_| TokioProcessError::ResourceExhausted)?;
        
        let process_id = uuid::Uuid::new_v4().to_string();
        
        let mut cmd = TokioCommand::new(&command);
        cmd.args(&args);
        
        if let Some(working_dir) = &metadata.working_dir {
            cmd.current_dir(working_dir);
        }
        
        for (key, value) in &metadata.environment {
            cmd.env(key, value);
        }
        
        let child = cmd.spawn()
            .map_err(|e| TokioProcessError::SpawnFailed(e.to_string()))?;
        
        let process = TokioProcess {
            id: process_id.clone(),
            child,
            status: TokioProcessStatus::Starting,
            metadata,
            created_at: Instant::now(),
        };
        
        {
            let mut processes = self.active_processes.lock().await;
            processes.insert(process_id.clone(), process);
        }
        
        // 异步监控进程
        self.monitor_process(process_id.clone()).await;
        
        Ok(process_id)
    }
    
    // 与进程通信
    pub async fn communicate_with_process(
        &self,
        process_id: &str,
        input: &str,
    ) -> Result<String, TokioProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        if let Some(process) = processes.get_mut(process_id) {
            if let Some(stdin) = process.child.stdin.as_mut() {
                use tokio::io::AsyncWriteExt;
                stdin.write_all(input.as_bytes()).await
                    .map_err(|e| TokioProcessError::CommunicationFailed(e.to_string()))?;
                stdin.flush().await
                    .map_err(|e| TokioProcessError::CommunicationFailed(e.to_string()))?;
            }
            
            if let Some(stdout) = process.child.stdout.as_mut() {
                use tokio::io::AsyncReadExt;
                let mut buffer = Vec::new();
                stdout.read_to_end(&mut buffer).await
                    .map_err(|e| TokioProcessError::CommunicationFailed(e.to_string()))?;
                
                return Ok(String::from_utf8_lossy(&buffer).to_string());
            }
        }
        
        Err(TokioProcessError::ProcessNotFound(process_id.to_string()))
    }
    
    // 等待进程完成
    pub async fn wait_for_process(
        &self,
        process_id: &str,
    ) -> Result<tokio::process::ExitStatus, TokioProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        if let Some(process) = processes.get_mut(process_id) {
            let status = process.child.wait().await
                .map_err(|e| TokioProcessError::WaitFailed(e.to_string()))?;
            
            process.status = TokioProcessStatus::Completed;
            
            Ok(status)
        } else {
            Err(TokioProcessError::ProcessNotFound(process_id.to_string()))
        }
    }
    
    // 终止进程
    pub async fn terminate_process(
        &self,
        process_id: &str,
    ) -> Result<(), TokioProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        if let Some(process) = processes.get_mut(process_id) {
            process.child.kill().await
                .map_err(|e| TokioProcessError::TerminationFailed(e.to_string()))?;
            
            process.status = TokioProcessStatus::Terminated;
        }
        
        Ok(())
    }
    
    // 监控进程
    async fn monitor_process(&self, process_id: String) {
        let processes = self.active_processes.clone();
        let config = self.config.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.health_check_interval);
            
            loop {
                interval.tick().await;
                
                let mut processes_guard = processes.lock().await;
                if let Some(process) = processes_guard.get_mut(&process_id) {
                    // 检查进程是否还在运行
                    if let Ok(Some(_)) = process.child.try_wait() {
                        process.status = TokioProcessStatus::Completed;
                        break;
                    }
                    
                    // 检查超时
                    if process.created_at.elapsed() > config.default_timeout {
                        process.status = TokioProcessStatus::Timeout;
                        let _ = process.child.kill().await;
                        break;
                    }
                } else {
                    break;
                }
            }
        });
    }
    
    // 健康检查
    pub async fn health_check(&self) -> Result<(), TokioProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        for (process_id, process) in processes.iter_mut() {
            if let Ok(Some(status)) = process.child.try_wait() {
                if status.success() {
                    process.status = TokioProcessStatus::Completed;
                } else {
                    process.status = TokioProcessStatus::Failed;
                }
            }
        }
        
        Ok(())
    }
    
    // 自动清理
    pub async fn auto_cleanup(&self) -> Result<(), TokioProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        processes.retain(|_, process| {
            matches!(process.status, TokioProcessStatus::Running | TokioProcessStatus::Starting)
        });
        
        Ok(())
    }
    
    // 获取进程统计
    pub async fn get_process_stats(&self) -> TokioProcessStats {
        let processes = self.active_processes.lock().await;
        
        let total = processes.len();
        let running = processes.values().filter(|p| matches!(p.status, TokioProcessStatus::Running)).count();
        let completed = processes.values().filter(|p| matches!(p.status, TokioProcessStatus::Completed)).count();
        let failed = processes.values().filter(|p| matches!(p.status, TokioProcessStatus::Failed)).count();
        
        TokioProcessStats {
            total_processes: total,
            running_processes: running,
            completed_processes: completed,
            failed_processes: failed,
        }
    }
}

#[derive(Debug)]
pub struct TokioProcessStats {
    pub total_processes: usize,
    pub running_processes: usize,
    pub completed_processes: usize,
    pub failed_processes: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum TokioProcessError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(String),
    
    #[error("进程未找到: {0}")]
    ProcessNotFound(String),
    
    #[error("进程通信失败: {0}")]
    CommunicationFailed(String),
    
    #[error("等待进程失败: {0}")]
    WaitFailed(String),
    
    #[error("终止进程失败: {0}")]
    TerminationFailed(String),
    
    #[error("资源不足")]
    ResourceExhausted,
}

// 使用示例
pub async fn tokio_process_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = TokioProcessConfig {
        max_concurrent_processes: 10,
        default_timeout: Duration::from_secs(30),
        health_check_interval: Duration::from_secs(5),
        auto_cleanup: true,
    };
    
    let manager = TokioProcessManager::new(config);
    
    // 启动进程
    let metadata = TokioProcessMetadata {
        command: "echo".to_string(),
        args: vec!["Hello, Tokio!".to_string()],
        working_dir: None,
        environment: HashMap::new(),
        priority: ProcessPriority::Normal,
        resource_limits: ResourceLimits {
            max_memory_mb: 512,
            max_cpu_percent: 80.0,
            max_file_descriptors: 1000,
        },
    };
    
    let process_id = manager.spawn_process(
        "echo".to_string(),
        vec!["Hello, Tokio!".to_string()],
        metadata,
    ).await?;
    
    println!("进程启动成功，ID: {}", process_id);
    
    // 等待进程完成
    let status = manager.wait_for_process(&process_id).await?;
    println!("进程完成，状态: {:?}", status);
    
    // 获取统计信息
    let stats = manager.get_process_stats().await;
    println!("进程统计: {:?}", stats);
    
    // 健康检查
    manager.health_check().await?;
    
    // 自动清理
    manager.auto_cleanup().await?;
    
    Ok(())
}
```

### 2.2 Async-Std 进程处理

使用 Async-Std 进行异步进程管理：

```rust
use async_std::process::{Command as AsyncStdCommand, Stdio};
use async_std::sync::{Arc, Mutex};
use std::collections::HashMap;
use std::time::{Duration, Instant};

// Async-Std 进程管理器
pub struct AsyncStdProcessManager {
    active_processes: Arc<Mutex<Vec<AsyncStdProcess>>>,
    config: AsyncStdProcessConfig,
}

#[derive(Debug, Clone)]
pub struct AsyncStdProcessConfig {
    pub max_concurrent_processes: usize,
    pub default_timeout: Duration,
    pub restart_policy: RestartPolicy,
    pub health_check_interval: Duration,
}

#[derive(Debug, Clone)]
pub enum RestartPolicy {
    Never,
    Always,
    OnFailure,
    OnExit,
}

#[derive(Debug)]
pub struct AsyncStdProcess {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub status: AsyncStdProcessStatus,
    pub restart_count: u32,
    pub max_restarts: u32,
    pub created_at: Instant,
    pub last_restart: Option<Instant>,
}

#[derive(Debug, Clone)]
pub enum AsyncStdProcessStatus {
    Starting,
    Running,
    Stopped,
    Failed,
    Restarting,
}

impl AsyncStdProcessManager {
    pub fn new(config: AsyncStdProcessConfig) -> Self {
        Self {
            active_processes: Arc::new(Mutex::new(Vec::new())),
            config,
        }
    }
    
    // 启动进程
    pub async fn spawn_process(
        &self,
        command: String,
        args: Vec<String>,
        max_restarts: u32,
    ) -> Result<String, AsyncStdProcessError> {
        let process_id = uuid::Uuid::new_v4().to_string();
        
        let process = AsyncStdProcess {
            id: process_id.clone(),
            command: command.clone(),
            args: args.clone(),
            status: AsyncStdProcessStatus::Starting,
            restart_count: 0,
            max_restarts,
            created_at: Instant::now(),
            last_restart: None,
        };
        
        {
            let mut processes = self.active_processes.lock().await;
            processes.push(process);
        }
        
        // 异步启动进程
        self.start_process(&process_id).await?;
        
        Ok(process_id)
    }
    
    // 启动单个进程
    async fn start_process(&self, process_id: &str) -> Result<(), AsyncStdProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        if let Some(process) = processes.iter_mut().find(|p| p.id == *process_id) {
            let mut cmd = AsyncStdCommand::new(&process.command);
            cmd.args(&process.args);
            cmd.stdout(Stdio::piped());
            cmd.stderr(Stdio::piped());
            
            match cmd.spawn() {
                Ok(child) => {
                    process.status = AsyncStdProcessStatus::Running;
                    
                    // 异步监控进程
                    let process_id_clone = process_id.to_string();
                    let processes_clone = self.active_processes.clone();
                    let config = self.config.clone();
                    
                    async_std::task::spawn(async move {
                        let output = child.output().await;
                        
                        let mut processes = processes_clone.lock().await;
                        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id_clone) {
                            match output {
                                Ok(output) => {
                                    if output.status.success() {
                                        process.status = AsyncStdProcessStatus::Stopped;
                                    } else {
                                        process.status = AsyncStdProcessStatus::Failed;
                                    }
                                }
                                Err(_) => {
                                    process.status = AsyncStdProcessStatus::Failed;
                                }
                            }
                        }
                    });
                }
                Err(e) => {
                    process.status = AsyncStdProcessStatus::Failed;
                    return Err(AsyncStdProcessError::SpawnFailed(e.to_string()));
                }
            }
        }
        
        Ok(())
    }
    
    // 重启进程
    pub async fn restart_process(&self, process_id: &str) -> Result<(), AsyncStdProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        if let Some(process) = processes.iter_mut().find(|p| p.id == *process_id) {
            if process.restart_count >= process.max_restarts {
                return Err(AsyncStdProcessError::MaxRestartsExceeded);
            }
            
            process.status = AsyncStdProcessStatus::Restarting;
            process.restart_count += 1;
            process.last_restart = Some(Instant::now());
        }
        
        drop(processes);
        
        // 重新启动进程
        self.start_process(process_id).await?;
        
        Ok(())
    }
    
    // 终止进程
    pub async fn terminate_process(&self, process_id: &str) -> Result<(), AsyncStdProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        if let Some(process) = processes.iter_mut().find(|p| p.id == *process_id) {
            process.status = AsyncStdProcessStatus::Stopped;
        }
        
        Ok(())
    }
    
    // 监控进程
    pub async fn monitor_processes(&self) -> Result<(), AsyncStdProcessError> {
        let mut processes = self.active_processes.lock().await;
        
        for process in processes.iter_mut() {
            match process.status {
                AsyncStdProcessStatus::Failed => {
                    // 根据重启策略决定是否重启
                    match self.config.restart_policy {
                        RestartPolicy::Always => {
                            if process.restart_count < process.max_restarts {
                                process.status = AsyncStdProcessStatus::Restarting;
                                process.restart_count += 1;
                                process.last_restart = Some(Instant::now());
                            }
                        }
                        RestartPolicy::OnFailure => {
                            if process.restart_count < process.max_restarts {
                                process.status = AsyncStdProcessStatus::Restarting;
                                process.restart_count += 1;
                                process.last_restart = Some(Instant::now());
                            }
                        }
                        _ => {}
                    }
                }
                AsyncStdProcessStatus::Restarting => {
                    // 重启进程
                    drop(processes);
                    self.start_process(&process.id).await?;
                    processes = self.active_processes.lock().await;
                }
                _ => {}
            }
        }
        
        Ok(())
    }
    
    // 获取进程状态
    pub async fn get_process_status(&self, process_id: &str) -> Option<AsyncStdProcessStatus> {
        let processes = self.active_processes.lock().await;
        processes.iter().find(|p| p.id == *process_id).map(|p| p.status.clone())
    }
    
    // 获取所有进程状态
    pub async fn get_all_process_status(&self) -> Vec<(String, AsyncStdProcessStatus)> {
        let processes = self.active_processes.lock().await;
        processes.iter().map(|p| (p.id.clone(), p.status.clone())).collect()
    }
    
    // 清理已完成的进程
    pub async fn cleanup_completed_processes(&self) -> Result<(), AsyncStdProcessError> {
        let mut processes = self.active_processes.lock().await;
        processes.retain(|p| matches!(p.status, AsyncStdProcessStatus::Running | AsyncStdProcessStatus::Starting));
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum AsyncStdProcessError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(String),
    
    #[error("进程未找到: {0}")]
    ProcessNotFound(String),
    
    #[error("超过最大重启次数")]
    MaxRestartsExceeded,
    
    #[error("进程终止失败: {0}")]
    TerminationFailed(String),
}

// 使用示例
pub async fn async_std_process_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = AsyncStdProcessConfig {
        max_concurrent_processes: 10,
        default_timeout: Duration::from_secs(30),
        restart_policy: RestartPolicy::OnFailure,
        health_check_interval: Duration::from_secs(5),
    };
    
    let manager = AsyncStdProcessManager::new(config);
    
    // 启动进程
    let process_id = manager.spawn_process(
        "echo".to_string(),
        vec!["Hello, Async-Std!".to_string()],
        3,
    ).await?;
    
    println!("进程启动成功，ID: {}", process_id);
    
    // 等待一段时间
    async_std::task::sleep(Duration::from_secs(2)).await;
    
    // 获取进程状态
    if let Some(status) = manager.get_process_status(&process_id).await {
        println!("进程状态: {:?}", status);
    }
    
    // 获取所有进程状态
    let all_status = manager.get_all_process_status().await;
    println!("所有进程状态: {:?}", all_status);
    
    // 监控进程
    manager.monitor_processes().await?;
    
    // 清理已完成的进程
    manager.cleanup_completed_processes().await?;
    
    Ok(())
}
```

### 2.3 Duct 链式命令执行

使用 Duct 进行链式命令执行：

```rust
use duct::cmd;
use std::collections::HashMap;
use std::time::{Duration, Instant};

// Duct 链式命令执行器
pub struct DuctCommandExecutor {
    command_chains: Vec<CommandChain>,
    config: DuctConfig,
}

#[derive(Debug, Clone)]
pub struct CommandChain {
    pub id: String,
    pub name: String,
    pub commands: Vec<DuctCommand>,
    pub parallel: bool,
    pub timeout: Duration,
    pub retry_count: u32,
    pub max_retries: u32,
}

#[derive(Debug, Clone)]
pub struct DuctCommand {
    pub name: String,
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub environment: HashMap<String, String>,
    pub timeout: Duration,
    pub retry_on_failure: bool,
}

#[derive(Debug, Clone)]
pub struct DuctConfig {
    pub max_concurrent_chains: usize,
    pub default_timeout: Duration,
    pub retry_delay: Duration,
    pub auto_cleanup: bool,
}

impl DuctCommandExecutor {
    pub fn new(config: DuctConfig) -> Self {
        Self {
            command_chains: Vec::new(),
            config,
        }
    }
    
    // 添加命令链
    pub fn add_command_chain(&mut self, chain: CommandChain) {
        self.command_chains.push(chain);
    }
    
    // 执行单个命令
    pub async fn execute_single_command(&self, command: &DuctCommand) -> Result<String, DuctError> {
        let mut cmd = cmd(&command.command, &command.args);
        
        if let Some(working_dir) = &command.working_dir {
            cmd = cmd.dir(working_dir);
        }
        
        for (key, value) in &command.environment {
            cmd = cmd.env(key, value);
        }
        
        let output = cmd.read()
            .map_err(|e| DuctError::ExecutionFailed(e.to_string()))?;
        
        Ok(output)
    }
    
    // 执行命令链
    pub async fn execute_command_chain(&self, chain: &CommandChain) -> Result<Vec<String>, DuctError> {
        let mut results = Vec::new();
        
        if chain.parallel {
            // 并行执行
            let mut handles = Vec::new();
            
            for command in &chain.commands {
                let command_clone = command.clone();
                let handle = tokio::spawn(async move {
                    Self::execute_command_with_retry(&command_clone).await
                });
                handles.push(handle);
            }
            
            for handle in handles {
                let result = handle.await
                    .map_err(|e| DuctError::TaskExecutionFailed(e.to_string()))?;
                results.push(result?);
            }
        } else {
            // 顺序执行
            for command in &chain.commands {
                let result = Self::execute_command_with_retry(command).await?;
                results.push(result);
            }
        }
        
        Ok(results)
    }
    
    // 执行并行命令链
    pub async fn execute_parallel_chains(&self) -> Result<Vec<ChainResult>, DuctError> {
        let mut handles = Vec::new();
        
        for chain in &self.command_chains {
            let chain_clone = chain.clone();
            let handle = tokio::spawn(async move {
                Self::execute_command_chain(&chain_clone).await
            });
            handles.push(handle);
        }
        
        let mut results = Vec::new();
        for handle in handles {
            let result = handle.await
                .map_err(|e| DuctError::TaskExecutionFailed(e.to_string()))?;
            
            results.push(ChainResult {
                success: result.is_ok(),
                output: result.unwrap_or_default(),
                error: result.err().map(|e| e.to_string()),
            });
        }
        
        Ok(results)
    }
    
    // 执行管道命令
    pub async fn execute_pipeline(&self, commands: Vec<DuctCommand>) -> Result<String, DuctError> {
        if commands.is_empty() {
            return Err(DuctError::EmptyCommandList);
        }
        
        let mut pipeline = cmd(&commands[0].command, &commands[0].args);
        
        for command in commands.iter().skip(1) {
            pipeline = pipeline.pipe(cmd(&command.command, &command.args));
        }
        
        let output = pipeline.read()
            .map_err(|e| DuctError::ExecutionFailed(e.to_string()))?;
        
        Ok(output)
    }
    
    // 执行条件命令链
    pub async fn execute_conditional_chain(
        &self,
        condition: &DuctCommand,
        success_chain: &[DuctCommand],
        failure_chain: &[DuctCommand],
    ) -> Result<Vec<String>, DuctError> {
        // 执行条件命令
        let condition_result = Self::execute_command_with_retry(condition).await?;
        
        // 根据条件结果选择执行链
        let chain_to_execute = if condition_result.trim().is_empty() {
            failure_chain
        } else {
            success_chain
        };
        
        let mut results = Vec::new();
        for command in chain_to_execute {
            let result = Self::execute_command_with_retry(command).await?;
            results.push(result);
        }
        
        Ok(results)
    }
    
    // 带重试的命令执行
    async fn execute_command_with_retry(command: &DuctCommand) -> Result<String, DuctError> {
        let mut last_error = None;
        
        for attempt in 0..=command.max_retries {
            match Self::execute_single_command_static(command).await {
                Ok(result) => return Ok(result),
                Err(e) => {
                    last_error = Some(e);
                    
                    if attempt < command.max_retries && command.retry_on_failure {
                        tokio::time::sleep(Duration::from_millis(100 * (attempt + 1) as u64)).await;
                    }
                }
            }
        }
        
        Err(last_error.unwrap())
    }
    
    // 静态方法执行单个命令
    async fn execute_single_command_static(command: &DuctCommand) -> Result<String, DuctError> {
        let mut cmd = cmd(&command.command, &command.args);
        
        if let Some(working_dir) = &command.working_dir {
            cmd = cmd.dir(working_dir);
        }
        
        for (key, value) in &command.environment {
            cmd = cmd.env(key, value);
        }
        
        let output = cmd.read()
            .map_err(|e| DuctError::ExecutionFailed(e.to_string()))?;
        
        Ok(output)
    }
    
    // 获取执行统计
    pub fn get_execution_stats(&self) -> DuctExecutionStats {
        let total_chains = self.command_chains.len();
        let total_commands: usize = self.command_chains.iter().map(|c| c.commands.len()).sum();
        
        DuctExecutionStats {
            total_chains,
            total_commands,
            parallel_chains: self.command_chains.iter().filter(|c| c.parallel).count(),
            sequential_chains: self.command_chains.iter().filter(|c| !c.parallel).count(),
        }
    }
}

#[derive(Debug)]
pub struct ChainResult {
    pub success: bool,
    pub output: Vec<String>,
    pub error: Option<String>,
}

#[derive(Debug)]
pub struct DuctExecutionStats {
    pub total_chains: usize,
    pub total_commands: usize,
    pub parallel_chains: usize,
    pub sequential_chains: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum DuctError {
    #[error("命令执行失败: {0}")]
    ExecutionFailed(String),
    
    #[error("任务执行失败: {0}")]
    TaskExecutionFailed(String),
    
    #[error("空命令列表")]
    EmptyCommandList,
    
    #[error("超时错误")]
    Timeout,
    
    #[error("重试次数超限")]
    MaxRetriesExceeded,
}

// 使用示例
pub async fn duct_command_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = DuctConfig {
        max_concurrent_chains: 5,
        default_timeout: Duration::from_secs(30),
        retry_delay: Duration::from_millis(100),
        auto_cleanup: true,
    };
    
    let mut executor = DuctCommandExecutor::new(config);
    
    // 创建命令链
    let chain = CommandChain {
        id: "test_chain".to_string(),
        name: "测试命令链".to_string(),
        commands: vec![
            DuctCommand {
                name: "echo1".to_string(),
                command: "echo".to_string(),
                args: vec!["Hello".to_string()],
                working_dir: None,
                environment: HashMap::new(),
                timeout: Duration::from_secs(5),
                retry_on_failure: true,
                max_retries: 3,
            },
            DuctCommand {
                name: "echo2".to_string(),
                command: "echo".to_string(),
                args: vec!["World".to_string()],
                working_dir: None,
                environment: HashMap::new(),
                timeout: Duration::from_secs(5),
                retry_on_failure: true,
                max_retries: 3,
            },
        ],
        parallel: false,
        timeout: Duration::from_secs(10),
        retry_count: 0,
        max_retries: 2,
    };
    
    executor.add_command_chain(chain);
    
    // 执行命令链
    let results = executor.execute_command_chain(&executor.command_chains[0]).await?;
    println!("命令链执行结果: {:?}", results);
    
    // 执行管道命令
    let pipeline_commands = vec![
        DuctCommand {
            name: "ls".to_string(),
            command: "ls".to_string(),
            args: vec!["-la".to_string()],
            working_dir: None,
            environment: HashMap::new(),
            timeout: Duration::from_secs(5),
            retry_on_failure: false,
            max_retries: 0,
        },
        DuctCommand {
            name: "grep".to_string(),
            command: "grep".to_string(),
            args: vec!["txt".to_string()],
            working_dir: None,
            environment: HashMap::new(),
            timeout: Duration::from_secs(5),
            retry_on_failure: false,
            max_retries: 0,
        },
    ];
    
    let pipeline_result = executor.execute_pipeline(pipeline_commands).await?;
    println!("管道执行结果: {}", pipeline_result);
    
    // 获取执行统计
    let stats = executor.get_execution_stats();
    println!("执行统计: {:?}", stats);
    
    Ok(())
}
```

### 2.4 Subprocess 高级进程控制

使用 Subprocess 进行高级进程控制：

```rust
use subprocess::{Popen, PopenConfig, Redirection};
use std::collections::HashMap;
use std::time::{Duration, Instant};

// Subprocess 高级进程控制器
pub struct SubprocessController {
    active_processes: HashMap<String, ControlledProcess>,
    config: SubprocessConfig,
}

#[derive(Debug, Clone)]
pub struct SubprocessConfig {
    pub max_concurrent_processes: usize,
    pub default_timeout: Duration,
    pub auto_cleanup: bool,
    pub capture_output: bool,
    pub capture_stderr: bool,
}

#[derive(Debug)]
pub struct ControlledProcess {
    pub id: String,
    pub popen: Popen,
    pub status: ProcessStatus,
    pub metadata: ProcessMetadata,
    pub created_at: Instant,
    pub last_activity: Instant,
}

#[derive(Debug, Clone)]
pub enum ProcessStatus {
    Starting,
    Running,
    Completed,
    Failed,
    Timeout,
    Terminated,
}

#[derive(Debug, Clone)]
pub struct ProcessMetadata {
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub environment: HashMap<String, String>,
    pub priority: ProcessPriority,
    pub resource_limits: ResourceLimits,
}

#[derive(Debug, Clone)]
pub enum ProcessPriority {
    Low,
    Normal,
    High,
    Critical,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_percent: f64,
    pub max_file_descriptors: u32,
}

impl SubprocessController {
    pub fn new(config: SubprocessConfig) -> Self {
        Self {
            active_processes: HashMap::new(),
            config,
        }
    }
    
    // 启动进程
    pub fn spawn_process(
        &mut self,
        command: String,
        args: Vec<String>,
        metadata: ProcessMetadata,
    ) -> Result<String, SubprocessError> {
        let process_id = uuid::Uuid::new_v4().to_string();
        
        let mut config = PopenConfig {
            stdout: if self.config.capture_output {
                Redirection::Pipe
            } else {
                Redirection::None
            },
            stderr: if self.config.capture_stderr {
                Redirection::Pipe
            } else {
                Redirection::None
            },
            stdin: Redirection::Pipe,
            ..Default::default()
        };
        
        if let Some(working_dir) = &metadata.working_dir {
            config.cwd = Some(working_dir.clone());
        }
        
        for (key, value) in &metadata.environment {
            config.env = Some({
                let mut env = std::env::vars().collect::<HashMap<_, _>>();
                env.insert(key.clone(), value.clone());
                env
            });
        }
        
        let popen = Popen::create(&[&command], config)
            .map_err(|e| SubprocessError::SpawnFailed(e.to_string()))?;
        
        let controlled_process = ControlledProcess {
            id: process_id.clone(),
            popen,
            status: ProcessStatus::Starting,
            metadata,
            created_at: Instant::now(),
            last_activity: Instant::now(),
        };
        
        self.active_processes.insert(process_id.clone(), controlled_process);
        
        Ok(process_id)
    }
    
    // 与进程通信
    pub fn communicate_with_process(
        &mut self,
        process_id: &str,
        input: &str,
    ) -> Result<String, SubprocessError> {
        if let Some(process) = self.active_processes.get_mut(process_id) {
            if let Some(stdin) = &mut process.popen.stdin {
                use std::io::Write;
                stdin.write_all(input.as_bytes())
                    .map_err(|e| SubprocessError::CommunicationFailed(e.to_string()))?;
                stdin.flush()
                    .map_err(|e| SubprocessError::CommunicationFailed(e.to_string()))?;
            }
            
            if let Some(stdout) = &mut process.popen.stdout {
                use std::io::Read;
                let mut buffer = String::new();
                stdout.read_to_string(&mut buffer)
                    .map_err(|e| SubprocessError::CommunicationFailed(e.to_string()))?;
                
                process.last_activity = Instant::now();
                return Ok(buffer);
            }
        }
        
        Err(SubprocessError::ProcessNotFound(process_id.to_string()))
    }
    
    // 等待进程完成
    pub fn wait_for_process(&mut self, process_id: &str) -> Result<i32, SubprocessError> {
        if let Some(process) = self.active_processes.get_mut(process_id) {
            let exit_status = process.popen.wait()
                .map_err(|e| SubprocessError::WaitFailed(e.to_string()))?;
            
            process.status = ProcessStatus::Completed;
            process.last_activity = Instant::now();
            
            Ok(exit_status.code().unwrap_or(-1))
        } else {
            Err(SubprocessError::ProcessNotFound(process_id.to_string()))
        }
    }
    
    // 终止进程
    pub fn terminate_process(&mut self, process_id: &str) -> Result<(), SubprocessError> {
        if let Some(process) = self.active_processes.get_mut(process_id) {
            process.popen.terminate()
                .map_err(|e| SubprocessError::TerminationFailed(e.to_string()))?;
            
            process.status = ProcessStatus::Terminated;
            process.last_activity = Instant::now();
        }
        
        Ok(())
    }
    
    // 强制终止进程
    pub fn kill_process(&mut self, process_id: &str) -> Result<(), SubprocessError> {
        if let Some(process) = self.active_processes.get_mut(process_id) {
            process.popen.kill()
                .map_err(|e| SubprocessError::TerminationFailed(e.to_string()))?;
            
            process.status = ProcessStatus::Terminated;
            process.last_activity = Instant::now();
        }
        
        Ok(())
    }
    
    // 检查进程状态
    pub fn check_process_status(&mut self, process_id: &str) -> Result<ProcessStatus, SubprocessError> {
        if let Some(process) = self.active_processes.get_mut(process_id) {
            if let Some(exit_status) = process.popen.poll() {
                process.status = if exit_status.success() {
                    ProcessStatus::Completed
                } else {
                    ProcessStatus::Failed
                };
                process.last_activity = Instant::now();
            }
            
            Ok(process.status.clone())
        } else {
            Err(SubprocessError::ProcessNotFound(process_id.to_string()))
        }
    }
    
    // 监控所有进程
    pub fn monitor_all_processes(&mut self) -> Result<(), SubprocessError> {
        for (process_id, process) in self.active_processes.iter_mut() {
            if let Some(exit_status) = process.popen.poll() {
                process.status = if exit_status.success() {
                    ProcessStatus::Completed
                } else {
                    ProcessStatus::Failed
                };
                process.last_activity = Instant::now();
            }
            
            // 检查超时
            if process.created_at.elapsed() > self.config.default_timeout {
                process.status = ProcessStatus::Timeout;
                let _ = process.popen.terminate();
            }
        }
        
        Ok(())
    }
    
    // 清理已完成的进程
    pub fn cleanup_completed_processes(&mut self) -> Result<(), SubprocessError> {
        self.active_processes.retain(|_, process| {
            matches!(process.status, ProcessStatus::Running | ProcessStatus::Starting)
        });
        
        Ok(())
    }
    
    // 获取进程统计
    pub fn get_process_stats(&self) -> SubprocessStats {
        let total = self.active_processes.len();
        let running = self.active_processes.values().filter(|p| matches!(p.status, ProcessStatus::Running)).count();
        let completed = self.active_processes.values().filter(|p| matches!(p.status, ProcessStatus::Completed)).count();
        let failed = self.active_processes.values().filter(|p| matches!(p.status, ProcessStatus::Failed)).count();
        
        SubprocessStats {
            total_processes: total,
            running_processes: running,
            completed_processes: completed,
            failed_processes: failed,
        }
    }
}

#[derive(Debug)]
pub struct SubprocessStats {
    pub total_processes: usize,
    pub running_processes: usize,
    pub completed_processes: usize,
    pub failed_processes: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum SubprocessError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(String),
    
    #[error("进程未找到: {0}")]
    ProcessNotFound(String),
    
    #[error("进程通信失败: {0}")]
    CommunicationFailed(String),
    
    #[error("等待进程失败: {0}")]
    WaitFailed(String),
    
    #[error("终止进程失败: {0}")]
    TerminationFailed(String),
    
    #[error("超时错误")]
    Timeout,
}

// 使用示例
pub fn subprocess_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = SubprocessConfig {
        max_concurrent_processes: 10,
        default_timeout: Duration::from_secs(30),
        auto_cleanup: true,
        capture_output: true,
        capture_stderr: true,
    };
    
    let mut controller = SubprocessController::new(config);
    
    // 启动进程
    let metadata = ProcessMetadata {
        command: "python".to_string(),
        args: vec!["-c".to_string(), "print('Hello, Subprocess!')".to_string()],
        working_dir: None,
        environment: HashMap::new(),
        priority: ProcessPriority::Normal,
        resource_limits: ResourceLimits {
            max_memory_mb: 512,
            max_cpu_percent: 80.0,
            max_file_descriptors: 1000,
        },
    };
    
    let process_id = controller.spawn_process(
        "python".to_string(),
        vec!["-c".to_string(), "print('Hello, Subprocess!')".to_string()],
        metadata,
    )?;
    
    println!("进程启动成功，ID: {}", process_id);
    
    // 等待进程完成
    let exit_code = controller.wait_for_process(&process_id)?;
    println!("进程完成，退出码: {}", exit_code);
    
    // 获取进程统计
    let stats = controller.get_process_stats();
    println!("进程统计: {:?}", stats);
    
    // 监控进程
    controller.monitor_all_processes()?;
    
    // 清理已完成的进程
    controller.cleanup_completed_processes()?;
    
    Ok(())
}
```

## 3. 企业级应用场景

### 3.1 微服务编排系统

构建企业级微服务编排系统：

```rust
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};
use tokio::sync::Mutex;
use serde::{Deserialize, Serialize};

// 微服务编排器
pub struct MicroserviceOrchestrator {
    services: Arc<RwLock<HashMap<String, Microservice>>>,
    deployments: Arc<RwLock<Vec<Deployment>>>,
    config: OrchestratorConfig,
    health_checker: Arc<HealthChecker>,
    load_balancer: Arc<LoadBalancer>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Microservice {
    pub id: String,
    pub name: String,
    pub version: String,
    pub image: String,
    pub replicas: u32,
    pub instances: Vec<ServiceInstance>,
    pub config: ServiceConfig,
    pub status: ServiceStatus,
    pub created_at: Instant,
    pub updated_at: Instant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub service_id: String,
    pub instance_index: u32,
    pub container_id: Option<String>,
    pub status: InstanceStatus,
    pub metrics: InstanceMetrics,
    pub created_at: Instant,
    pub started_at: Option<Instant>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceConfig {
    pub cpu_limit: f64,
    pub memory_limit: u64,
    pub port: u16,
    pub environment: HashMap<String, String>,
    pub volumes: Vec<VolumeMount>,
    pub restart_policy: RestartPolicy,
    pub health_check: HealthCheckConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VolumeMount {
    pub name: String,
    pub path: String,
    pub read_only: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RestartPolicy {
    Always,
    OnFailure,
    Never,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckConfig {
    pub path: String,
    pub interval: Duration,
    pub timeout: Duration,
    pub retries: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Deployment {
    pub id: String,
    pub service_id: String,
    pub version: String,
    pub strategy: DeploymentStrategy,
    pub status: DeploymentStatus,
    pub created_at: Instant,
    pub completed_at: Option<Instant>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ServiceStatus {
    Creating,
    Running,
    Updating,
    Stopping,
    Stopped,
    Failed,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum InstanceStatus {
    Starting,
    Running,
    Stopping,
    Stopped,
    Failed,
    Unhealthy,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeploymentStatus {
    Pending,
    InProgress,
    Completed,
    Failed,
    RolledBack,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeploymentStrategy {
    Rolling,
    BlueGreen,
    Canary,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstanceMetrics {
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub network_rx: u64,
    pub network_tx: u64,
    pub request_count: u64,
    pub error_count: u64,
    pub response_time_avg: Duration,
}

#[derive(Debug, Clone)]
pub struct OrchestratorConfig {
    pub max_services: usize,
    pub max_instances_per_service: u32,
    pub default_cpu_limit: f64,
    pub default_memory_limit: u64,
    pub health_check_interval: Duration,
    pub auto_scaling: bool,
}

impl MicroserviceOrchestrator {
    pub fn new(config: OrchestratorConfig) -> Self {
        Self {
            services: Arc::new(RwLock::new(HashMap::new())),
            deployments: Arc::new(RwLock::new(Vec::new())),
            config,
            health_checker: Arc::new(HealthChecker::new()),
            load_balancer: Arc::new(LoadBalancer::new()),
        }
    }
    
    // 部署服务
    pub async fn deploy_service(
        &self,
        service_def: MicroserviceDefinition,
    ) -> Result<String, OrchestratorError> {
        let service_id = uuid::Uuid::new_v4().to_string();
        
        let mut service = Microservice {
            id: service_id.clone(),
            name: service_def.name,
            version: service_def.version,
            image: service_def.image,
            replicas: service_def.replicas,
            instances: Vec::new(),
            config: service_def.config,
            status: ServiceStatus::Creating,
            created_at: Instant::now(),
            updated_at: Instant::now(),
        };
        
        // 创建服务实例
        for i in 0..service_def.replicas {
            let instance = self.create_service_instance(&service_id, i).await?;
            service.instances.push(instance);
        }
        
        // 保存服务
        {
            let mut services = self.services.write().await;
            services.insert(service_id.clone(), service);
        }
        
        // 异步执行部署
        let orchestrator = self.clone();
        let service_id_clone = service_id.clone();
        tokio::spawn(async move {
            orchestrator.execute_deployment(&service_id_clone).await;
        });
        
        Ok(service_id)
    }
    
    // 创建服务实例
    async fn create_service_instance(
        &self,
        service_id: &str,
        instance_index: u32,
    ) -> Result<ServiceInstance, OrchestratorError> {
        let instance_id = uuid::Uuid::new_v4().to_string();
        
        // 启动容器
        let container_id = self.start_container(service_id, instance_index).await?;
        
        let instance = ServiceInstance {
            id: instance_id,
            service_id: service_id.to_string(),
            instance_index,
            container_id: Some(container_id),
            status: InstanceStatus::Starting,
            metrics: InstanceMetrics {
                cpu_usage: 0.0,
                memory_usage: 0,
                network_rx: 0,
                network_tx: 0,
                request_count: 0,
                error_count: 0,
                response_time_avg: Duration::ZERO,
            },
            created_at: Instant::now(),
            started_at: None,
        };
        
        Ok(instance)
    }
    
    // 启动容器
    async fn start_container(
        &self,
        service_id: &str,
        instance_index: u32,
    ) -> Result<String, OrchestratorError> {
        // 模拟容器启动
        let container_id = format!("{}-{}", service_id, instance_index);
        
        // 在实际实现中，这里会调用容器运行时 API
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        Ok(container_id)
    }
    
    // 执行部署
    async fn execute_deployment(&self, service_id: &str) {
        // 更新服务状态为运行中
        {
            let mut services = self.services.write().await;
            if let Some(service) = services.get_mut(service_id) {
                service.status = ServiceStatus::Running;
                service.updated_at = Instant::now();
                
                // 更新实例状态
                for instance in &mut service.instances {
                    instance.status = InstanceStatus::Running;
                    instance.started_at = Some(Instant::now());
                }
            }
        }
        
        // 创建部署记录
        let deployment = Deployment {
            id: uuid::Uuid::new_v4().to_string(),
            service_id: service_id.to_string(),
            version: "1.0.0".to_string(),
            strategy: DeploymentStrategy::Rolling,
            status: DeploymentStatus::InProgress,
            created_at: Instant::now(),
            completed_at: None,
        };
        
        {
            let mut deployments = self.deployments.write().await;
            deployments.push(deployment);
        }
        
        // 执行健康检查
        self.health_check_service(service_id).await;
        
        // 更新部署状态
        {
            let mut deployments = self.deployments.write().await;
            if let Some(deployment) = deployments.iter_mut().find(|d| d.service_id == service_id) {
                deployment.status = DeploymentStatus::Completed;
                deployment.completed_at = Some(Instant::now());
            }
        }
    }
    
    // 健康检查服务
    async fn health_check_service(&self, service_id: &str) {
        let services = self.services.read().await;
        if let Some(service) = services.get(service_id) {
            for instance in &service.instances {
                // 执行健康检查
                let is_healthy = self.health_checker.check_instance(instance).await;
                
                if !is_healthy {
                    // 标记实例为不健康
                    // 在实际实现中，这里会触发重启或替换
                }
            }
        }
    }
    
    // 扩缩容服务
    pub async fn scale_service(
        &self,
        service_id: &str,
        target_replicas: u32,
    ) -> Result<(), OrchestratorError> {
        let mut services = self.services.write().await;
        
        if let Some(service) = services.get_mut(service_id) {
            let current_replicas = service.instances.len() as u32;
            
            if target_replicas > current_replicas {
                // 扩容
                for i in current_replicas..target_replicas {
                    let instance = self.create_service_instance(service_id, i).await?;
                    service.instances.push(instance);
                }
            } else if target_replicas < current_replicas {
                // 缩容
                let instances_to_remove = current_replicas - target_replicas;
                for _ in 0..instances_to_remove {
                    if let Some(instance) = service.instances.pop() {
                        self.stop_instance(&instance).await?;
                    }
                }
            }
            
            service.replicas = target_replicas;
            service.updated_at = Instant::now();
        }
        
        Ok(())
    }
    
    // 停止实例
    async fn stop_instance(&self, instance: &ServiceInstance) -> Result<(), OrchestratorError> {
        if let Some(container_id) = &instance.container_id {
            // 在实际实现中，这里会调用容器运行时 API 停止容器
            println!("停止容器: {}", container_id);
        }
        
        Ok(())
    }
    
    // 获取服务状态
    pub async fn get_service_status(&self, service_id: &str) -> Option<ServiceStatus> {
        let services = self.services.read().await;
        services.get(service_id).map(|s| s.status.clone())
    }
    
    // 列出所有服务
    pub async fn list_services(&self) -> Vec<Microservice> {
        let services = self.services.read().await;
        services.values().cloned().collect()
    }
    
    // 获取部署历史
    pub async fn get_deployment_history(&self, service_id: &str) -> Vec<Deployment> {
        let deployments = self.deployments.read().await;
        deployments.iter()
            .filter(|d| d.service_id == service_id)
            .cloned()
            .collect()
    }
}

// 服务定义
#[derive(Debug, Clone)]
pub struct MicroserviceDefinition {
    pub name: String,
    pub version: String,
    pub image: String,
    pub replicas: u32,
    pub config: ServiceConfig,
}

// 健康检查器
pub struct HealthChecker {
    // 健康检查器实现
}

impl HealthChecker {
    pub fn new() -> Self {
        Self {}
    }
    
    pub async fn check_instance(&self, instance: &ServiceInstance) -> bool {
        // 模拟健康检查
        tokio::time::sleep(Duration::from_millis(10)).await;
        true
    }
}

// 负载均衡器
pub struct LoadBalancer {
    // 负载均衡器实现
}

impl LoadBalancer {
    pub fn new() -> Self {
        Self {}
    }
}

#[derive(Debug, thiserror::Error)]
pub enum OrchestratorError {
    #[error("服务部署失败: {0}")]
    DeploymentFailed(String),
    
    #[error("容器启动失败: {0}")]
    ContainerStartFailed(String),
    
    #[error("服务未找到: {0}")]
    ServiceNotFound(String),
    
    #[error("实例创建失败: {0}")]
    InstanceCreationFailed(String),
    
    #[error("资源不足")]
    ResourceExhausted,
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
}

// 使用示例
pub async fn microservice_orchestration_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OrchestratorConfig {
        max_services: 100,
        max_instances_per_service: 10,
        default_cpu_limit: 1.0,
        default_memory_limit: 512,
        health_check_interval: Duration::from_secs(30),
        auto_scaling: true,
    };
    
    let orchestrator = MicroserviceOrchestrator::new(config);
    
    // 定义服务
    let service_def = MicroserviceDefinition {
        name: "web-service".to_string(),
        version: "1.0.0".to_string(),
        image: "nginx:latest".to_string(),
        replicas: 3,
        config: ServiceConfig {
            cpu_limit: 1.0,
            memory_limit: 512,
            port: 80,
            environment: HashMap::new(),
            volumes: Vec::new(),
            restart_policy: RestartPolicy::Always,
            health_check: HealthCheckConfig {
                path: "/health".to_string(),
                interval: Duration::from_secs(10),
                timeout: Duration::from_secs(5),
                retries: 3,
            },
        },
    };
    
    // 部署服务
    let service_id = orchestrator.deploy_service(service_def).await?;
    println!("服务部署成功，ID: {}", service_id);
    
    // 等待部署完成
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 获取服务状态
    if let Some(status) = orchestrator.get_service_status(&service_id).await {
        println!("服务状态: {:?}", status);
    }
    
    // 扩缩容服务
    orchestrator.scale_service(&service_id, 5).await?;
    println!("服务扩容到 5 个实例");
    
    // 列出所有服务
    let services = orchestrator.list_services().await;
    println!("所有服务: {:?}", services);
    
    // 获取部署历史
    let deployments = orchestrator.get_deployment_history(&service_id).await;
    println!("部署历史: {:?}", deployments);
    
    Ok(())
}
```

### 3.2 分布式任务调度

构建分布式任务调度系统：

```rust
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};
use tokio::sync::RwLock as TokioRwLock;
use serde::{Deserialize, Serialize};

// 分布式任务调度器
pub struct DistributedTaskScheduler {
    tasks: Arc<TokioRwLock<HashMap<String, Task>>>,
    workers: Arc<TokioRwLock<HashMap<String, Worker>>>,
    task_queue: Arc<Mutex<VecDeque<Task>>>,
    scheduler: Arc<TaskScheduler>,
    config: SchedulerConfig,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Task {
    pub id: String,
    pub name: String,
    pub description: String,
    pub command: String,
    pub args: Vec<String>,
    pub metadata: TaskMetadata,
    pub status: TaskStatus,
    pub priority: TaskPriority,
    pub created_at: Instant,
    pub scheduled_at: Option<Instant>,
    pub started_at: Option<Instant>,
    pub completed_at: Option<Instant>,
    pub assigned_worker: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskMetadata {
    pub timeout: Duration,
    pub retry_count: u32,
    pub max_retries: u32,
    pub dependencies: Vec<String>,
    pub resource_requirements: ResourceRequirements,
    pub scheduling_constraints: SchedulingConstraints,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceRequirements {
    pub cpu_cores: f64,
    pub memory_mb: u64,
    pub disk_gb: u64,
    pub network_bandwidth: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SchedulingConstraints {
    pub preferred_workers: Vec<String>,
    pub excluded_workers: Vec<String>,
    pub time_window: Option<TimeWindow>,
    pub affinity_rules: Vec<AffinityRule>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeWindow {
    pub start: Instant,
    pub end: Instant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AffinityRule {
    pub rule_type: AffinityRuleType,
    pub target: String,
    pub weight: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AffinityRuleType {
    NodeAffinity,
    PodAffinity,
    ServiceAffinity,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Worker {
    pub id: String,
    pub name: String,
    pub address: String,
    pub status: WorkerStatus,
    pub capabilities: WorkerCapabilities,
    pub metrics: WorkerMetrics,
    pub last_heartbeat: Instant,
    pub created_at: Instant,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkerCapabilities {
    pub cpu_cores: f64,
    pub memory_mb: u64,
    pub disk_gb: u64,
    pub network_bandwidth: u64,
    pub supported_commands: Vec<String>,
    pub max_concurrent_tasks: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkerMetrics {
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub disk_usage: u64,
    pub network_rx: u64,
    pub network_tx: u64,
    pub active_tasks: u32,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TaskStatus {
    Pending,
    Scheduled,
    Running,
    Completed,
    Failed,
    Cancelled,
    Timeout,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TaskPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum WorkerStatus {
    Online,
    Offline,
    Busy,
    Maintenance,
}

#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    pub max_concurrent_tasks: usize,
    pub task_timeout: Duration,
    pub worker_timeout: Duration,
    pub heartbeat_interval: Duration,
    pub scheduling_algorithm: SchedulingAlgorithm,
}

#[derive(Debug, Clone)]
pub enum SchedulingAlgorithm {
    RoundRobin,
    LeastLoaded,
    PriorityBased,
    AffinityBased,
}

impl DistributedTaskScheduler {
    pub fn new(config: SchedulerConfig) -> Self {
        Self {
            tasks: Arc::new(TokioRwLock::new(HashMap::new())),
            workers: Arc::new(TokioRwLock::new(HashMap::new())),
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
            scheduler: Arc::new(TaskScheduler::new()),
            config,
        }
    }
    
    // 提交任务
    pub async fn submit_task(&self, task_def: TaskDefinition) -> Result<String, SchedulerError> {
        let task_id = uuid::Uuid::new_v4().to_string();
        
        let task = Task {
            id: task_id.clone(),
            name: task_def.name,
            description: task_def.description,
            command: task_def.command,
            args: task_def.args,
            metadata: task_def.metadata,
            status: TaskStatus::Pending,
            priority: task_def.priority,
            created_at: Instant::now(),
            scheduled_at: None,
            started_at: None,
            completed_at: None,
            assigned_worker: None,
        };
        
        // 保存任务
        {
            let mut tasks = self.tasks.write().await;
            tasks.insert(task_id.clone(), task.clone());
        }
        
        // 添加到任务队列
        {
            let mut queue = self.task_queue.lock().unwrap();
            queue.push_back(task);
        }
        
        // 异步调度任务
        let scheduler = self.clone();
        tokio::spawn(async move {
            scheduler.schedule_tasks().await;
        });
        
        Ok(task_id)
    }
    
    // 注册工作节点
    pub async fn register_worker(&self, worker_def: WorkerDefinition) -> Result<String, SchedulerError> {
        let worker_id = uuid::Uuid::new_v4().to_string();
        
        let worker = Worker {
            id: worker_id.clone(),
            name: worker_def.name,
            address: worker_def.address,
            status: WorkerStatus::Online,
            capabilities: worker_def.capabilities,
            metrics: WorkerMetrics {
                cpu_usage: 0.0,
                memory_usage: 0,
                disk_usage: 0,
                network_rx: 0,
                network_tx: 0,
                active_tasks: 0,
                completed_tasks: 0,
                failed_tasks: 0,
            },
            last_heartbeat: Instant::now(),
            created_at: Instant::now(),
        };
        
        // 保存工作节点
        {
            let mut workers = self.workers.write().await;
            workers.insert(worker_id.clone(), worker);
        }
        
        Ok(worker_id)
    }
    
    // 调度任务
    pub async fn schedule_tasks(&self) -> Result<(), SchedulerError> {
        let mut queue = self.task_queue.lock().unwrap();
        let workers = self.workers.read().await;
        let mut tasks = self.tasks.write().await;
        
        while let Some(mut task) = queue.pop_front() {
            // 检查依赖关系
            if !self.check_dependencies(&task.metadata.dependencies, &tasks).await {
                // 依赖未满足，重新加入队列
                queue.push_back(task);
                continue;
            }
            
            // 选择工作节点
            if let Some(worker_id) = self.scheduler.select_worker(&task, &workers) {
                // 分配任务
                task.status = TaskStatus::Scheduled;
                task.scheduled_at = Some(Instant::now());
                task.assigned_worker = Some(worker_id.clone());
                
                // 更新任务状态
                tasks.insert(task.id.clone(), task.clone());
                
                // 异步执行任务
                let scheduler = self.clone();
                let task_id = task.id.clone();
                tokio::spawn(async move {
                    scheduler.execute_task(&task_id).await;
                });
            } else {
                // 没有可用工作节点，重新加入队列
                queue.push_back(task);
            }
        }
        
        Ok(())
    }
    
    // 执行任务
    async fn execute_task(&self, task_id: &str) {
        let mut tasks = self.tasks.write().await;
        let mut workers = self.workers.write().await;
        
        if let Some(task) = tasks.get_mut(task_id) {
            task.status = TaskStatus::Running;
            task.started_at = Some(Instant::now());
            
            if let Some(worker_id) = &task.assigned_worker {
                if let Some(worker) = workers.get_mut(worker_id) {
                    worker.metrics.active_tasks += 1;
                }
            }
        }
        
        drop(tasks);
        drop(workers);
        
        // 模拟任务执行
        tokio::time::sleep(Duration::from_secs(2)).await;
        
        // 更新任务状态
        let mut tasks = self.tasks.write().await;
        let mut workers = self.workers.write().await;
        
        if let Some(task) = tasks.get_mut(task_id) {
            task.status = TaskStatus::Completed;
            task.completed_at = Some(Instant::now());
            
            if let Some(worker_id) = &task.assigned_worker {
                if let Some(worker) = workers.get_mut(worker_id) {
                    worker.metrics.active_tasks -= 1;
                    worker.metrics.completed_tasks += 1;
                }
            }
        }
    }
    
    // 检查依赖关系
    async fn check_dependencies(
        &self,
        dependencies: &[String],
        tasks: &HashMap<String, Task>,
    ) -> bool {
        for dep_id in dependencies {
            if let Some(dep_task) = tasks.get(dep_id) {
                if !matches!(dep_task.status, TaskStatus::Completed) {
                    return false;
                }
            } else {
                return false;
            }
        }
        true
    }
    
    // 获取任务状态
    pub async fn get_task_status(&self, task_id: &str) -> Option<TaskStatus> {
        let tasks = self.tasks.read().await;
        tasks.get(task_id).map(|t| t.status.clone())
    }
    
    // 获取工作节点状态
    pub async fn get_worker_status(&self, worker_id: &str) -> Option<WorkerStatus> {
        let workers = self.workers.read().await;
        workers.get(worker_id).map(|w| w.status.clone())
    }
    
    // 获取调度器统计
    pub async fn get_scheduler_stats(&self) -> SchedulerStats {
        let tasks = self.tasks.read().await;
        let workers = self.workers.read().await;
        
        let total_tasks = tasks.len();
        let pending_tasks = tasks.values().filter(|t| matches!(t.status, TaskStatus::Pending)).count();
        let running_tasks = tasks.values().filter(|t| matches!(t.status, TaskStatus::Running)).count();
        let completed_tasks = tasks.values().filter(|t| matches!(t.status, TaskStatus::Completed)).count();
        let failed_tasks = tasks.values().filter(|t| matches!(t.status, TaskStatus::Failed)).count();
        
        let total_workers = workers.len();
        let online_workers = workers.values().filter(|w| matches!(w.status, WorkerStatus::Online)).count();
        let busy_workers = workers.values().filter(|w| matches!(w.status, WorkerStatus::Busy)).count();
        
        SchedulerStats {
            total_tasks,
            pending_tasks,
            running_tasks,
            completed_tasks,
            failed_tasks,
            total_workers,
            online_workers,
            busy_workers,
        }
    }
}

// 任务调度器
pub struct TaskScheduler {
    // 调度器实现
}

impl TaskScheduler {
    pub fn new() -> Self {
        Self {}
    }
    
    pub fn select_worker(&self, task: &Task, workers: &HashMap<String, Worker>) -> Option<String> {
        // 简单的调度算法：选择第一个可用的工作节点
        for (worker_id, worker) in workers {
            if matches!(worker.status, WorkerStatus::Online) && 
               worker.metrics.active_tasks < worker.capabilities.max_concurrent_tasks {
                return Some(worker_id.clone());
            }
        }
        None
    }
}

// 任务定义
#[derive(Debug, Clone)]
pub struct TaskDefinition {
    pub name: String,
    pub description: String,
    pub command: String,
    pub args: Vec<String>,
    pub metadata: TaskMetadata,
    pub priority: TaskPriority,
}

// 工作节点定义
#[derive(Debug, Clone)]
pub struct WorkerDefinition {
    pub name: String,
    pub address: String,
    pub capabilities: WorkerCapabilities,
}

#[derive(Debug)]
pub struct SchedulerStats {
    pub total_tasks: usize,
    pub pending_tasks: usize,
    pub running_tasks: usize,
    pub completed_tasks: usize,
    pub failed_tasks: usize,
    pub total_workers: usize,
    pub online_workers: usize,
    pub busy_workers: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum SchedulerError {
    #[error("任务提交失败: {0}")]
    TaskSubmissionFailed(String),
    
    #[error("工作节点注册失败: {0}")]
    WorkerRegistrationFailed(String),
    
    #[error("任务调度失败: {0}")]
    TaskSchedulingFailed(String),
    
    #[error("任务执行失败: {0}")]
    TaskExecutionFailed(String),
    
    #[error("工作节点未找到: {0}")]
    WorkerNotFound(String),
    
    #[error("任务未找到: {0}")]
    TaskNotFound(String),
    
    #[error("资源不足")]
    ResourceExhausted,
}

// 使用示例
pub async fn distributed_task_scheduling_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = SchedulerConfig {
        max_concurrent_tasks: 100,
        task_timeout: Duration::from_secs(300),
        worker_timeout: Duration::from_secs(60),
        heartbeat_interval: Duration::from_secs(10),
        scheduling_algorithm: SchedulingAlgorithm::RoundRobin,
    };
    
    let scheduler = DistributedTaskScheduler::new(config);
    
    // 注册工作节点
    let worker_def = WorkerDefinition {
        name: "worker-1".to_string(),
        address: "192.168.1.100:8080".to_string(),
        capabilities: WorkerCapabilities {
            cpu_cores: 4.0,
            memory_mb: 8192,
            disk_gb: 100,
            network_bandwidth: 1000,
            supported_commands: vec!["python".to_string(), "node".to_string()],
            max_concurrent_tasks: 10,
        },
    };
    
    let worker_id = scheduler.register_worker(worker_def).await?;
    println!("工作节点注册成功，ID: {}", worker_id);
    
    // 提交任务
    let task_def = TaskDefinition {
        name: "data-processing".to_string(),
        description: "数据处理任务".to_string(),
        command: "python".to_string(),
        args: vec!["process_data.py".to_string()],
        metadata: TaskMetadata {
            timeout: Duration::from_secs(300),
            retry_count: 0,
            max_retries: 3,
            dependencies: Vec::new(),
            resource_requirements: ResourceRequirements {
                cpu_cores: 2.0,
                memory_mb: 2048,
                disk_gb: 10,
                network_bandwidth: 100,
            },
            scheduling_constraints: SchedulingConstraints {
                preferred_workers: Vec::new(),
                excluded_workers: Vec::new(),
                time_window: None,
                affinity_rules: Vec::new(),
            },
        },
        priority: TaskPriority::Normal,
    };
    
    let task_id = scheduler.submit_task(task_def).await?;
    println!("任务提交成功，ID: {}", task_id);
    
    // 等待任务完成
    tokio::time::sleep(Duration::from_secs(5)).await;
    
    // 获取任务状态
    if let Some(status) = scheduler.get_task_status(&task_id).await {
        println!("任务状态: {:?}", status);
    }
    
    // 获取调度器统计
    let stats = scheduler.get_scheduler_stats().await;
    println!("调度器统计: {:?}", stats);
    
    Ok(())
}
```
