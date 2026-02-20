# C07-09. 现代进程管理库深度解析

> **文档定位**: Tier 4 高级主题
> **最后更新**: 2025-12-25
> **Rust版本**: 1.92.0+ (Edition 2024)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

## 📋 目录

- [C07-09. 现代进程管理库深度解析](#c07-09-现代进程管理库深度解析)
  - [📋 目录](#-目录)
  - [1. 库生态概览](#1-库生态概览)
    - [1.1 核心库对比](#11-核心库对比)
    - [1.2 选择指南](#12-选择指南)
  - [2. Tokio 异步进程管理](#2-tokio-异步进程管理)
    - [2.1 基础异步进程](#21-基础异步进程)
    - [2.2 高级异步特性](#22-高级异步特性)
    - [2.3 性能优化策略](#23-性能优化策略)
  - [3. Async-Std 进程管理](#3-async-std-进程管理)
    - [3.1 标准库风格](#31-标准库风格)
    - [3.2 与 Tokio 对比](#32-与-tokio-对比)
    - [3.3 迁移策略](#33-迁移策略)
  - [4. Duct 进程组合](#4-duct-进程组合)
    - [4.1 管道组合语法](#41-管道组合语法)
    - [4.2 复杂命令构建](#42-复杂命令构建)
    - [4.3 错误处理机制](#43-错误处理机制)
  - [5. Subprocess 高级控制](#5-subprocess-高级控制)
    - [5.1 高级进程控制](#51-高级进程控制)
    - [5.2 跨平台兼容](#52-跨平台兼容)
    - [5.3 安全性增强](#53-安全性增强)
  - [6. 性能基准测试](#6-性能基准测试)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 库选择最佳实践](#71-库选择最佳实践)
    - [7.2 性能优化最佳实践](#72-性能优化最佳实践)
  - [8. 小结](#8-小结)
    - [核心库特点总结](#核心库特点总结)
    - [选择建议](#选择建议)
    - [性能对比](#性能对比)
    - [最佳实践总结](#最佳实践总结)

本章深入解析现代 Rust 进程管理库，包括 Tokio、Async-Std、Duct、Subprocess 等，提供详细的对比分析和实践指南。

## 1. 库生态概览

### 1.1 核心库对比

| 库名                   | 类型       | 特点           | 适用场景     | 性能 | 学习曲线 |
| :--- | :--- | :--- | :--- | :--- | :--- || **std::process**       | 标准库     | 同步、基础功能 | 简单进程管理 | 中等 | 低       |
| **tokio::process**     | 异步运行时 | 高性能异步     | 高并发场景   | 高   | 中等     |
| **async-std::process** | 异步标准库 | 标准库风格     | 异步进程管理 | 中等 | 低       |
| **duct**               | 进程组合   | 管道语法       | 复杂命令组合 | 中等 | 低       |
| **subprocess**         | 高级控制   | 功能丰富       | 企业级应用   | 高   | 高       |

### 1.2 选择指南

```rust
// 选择决策树
fn choose_process_library(requirements: &ProcessRequirements) -> ProcessLibrary {
    match requirements {
        ProcessRequirements {
            async: true,
            high_performance: true,
            ..
        } => ProcessLibrary::Tokio,

        ProcessRequirements {
            async: true,
            simple_api: true,
            ..
        } => ProcessLibrary::AsyncStd,

        ProcessRequirements {
            pipe_composition: true,
            ..
        } => ProcessLibrary::Duct,

        ProcessRequirements {
            advanced_control: true,
            cross_platform: true,
            ..
        } => ProcessLibrary::Subprocess,

        _ => ProcessLibrary::Std,
    }
}

#[derive(Debug)]
struct ProcessRequirements {
    async: bool,
    high_performance: bool,
    simple_api: bool,
    pipe_composition: bool,
    advanced_control: bool,
    cross_platform: bool,
}

#[derive(Debug)]
enum ProcessLibrary {
    Std,
    Tokio,
    AsyncStd,
    Duct,
    Subprocess,
}
```

## 2. Tokio 异步进程管理

### 2.1 基础异步进程

```rust
use tokio::process::Command as TokioCommand;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use std::time::Duration;

// 基础 Tokio 异步进程
async fn basic_tokio_process() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = TokioCommand::new("echo")
        .arg("Hello, Tokio!")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()?;

    // 异步写入
    if let Some(stdin) = child.stdin.take() {
        let mut async_stdin = tokio::io::BufWriter::new(stdin);
        async_stdin.write_all(b"Tokio input\n").await?;
        async_stdin.flush().await?;
    }

    // 异步读取
    if let Some(stdout) = child.stdout.take() {
        let mut async_stdout = tokio::io::BufReader::new(stdout);
        let mut line = String::new();
        async_stdout.read_line(&mut line).await?;
        println!("Tokio 输出: {}", line);
    }

    let status = child.wait().await?;
    println!("Tokio 进程完成: {:?}", status);

    Ok(())
}

// 带超时的 Tokio 进程
async fn tokio_process_with_timeout() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = TokioCommand::new("long_running_program")
        .stdout(std::process::Stdio::piped())
        .spawn()?;

    let timeout_duration = Duration::from_secs(30);

    match tokio::time::timeout(timeout_duration, child.wait()).await {
        Ok(status) => {
            println!("进程正常完成: {:?}", status);
        }
        Err(_) => {
            println!("进程超时，正在终止...");
            child.kill().await?;
        }
    }

    Ok(())
}
```

### 2.2 高级异步特性

```rust
use tokio::process::Command as TokioCommand;
use tokio::sync::{Mutex, Semaphore};
use std::sync::Arc;
use std::time::Instant;

// 高级 Tokio 进程管理器
pub struct AdvancedTokioProcessManager {
    semaphore: Arc<Semaphore>,
    processes: Arc<Mutex<Vec<ManagedTokioProcess>>>,
    max_concurrent: usize,
}

#[derive(Debug)]
pub struct ManagedTokioProcess {
    pub id: String,
    pub child: tokio::process::Child,
    pub created_at: Instant,
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
    pub timeout: Option<Duration>,
}

impl AdvancedTokioProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            processes: Arc::new(Mutex::new(Vec::new())),
            max_concurrent,
        }
    }

    pub async fn execute_with_metrics<F>(
        &self,
        config: ProcessConfig,
        metrics_callback: F,
    ) -> Result<String, Box<dyn std::error::Error>>
    where
        F: FnOnce(Duration, usize) + Send + 'static,
    {
        let _permit = self.semaphore.acquire().await?;
        let start_time = Instant::now();

        let mut async_cmd = TokioCommand::new(&config.command);
        async_cmd.args(&config.args);

        if let Some(working_dir) = &config.working_dir {
            async_cmd.current_dir(working_dir);
        }

        for (key, value) in &config.env_vars {
            async_cmd.env(key, value);
        }

        async_cmd
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped());

        let child = async_cmd.spawn()?;

        let process_id = uuid::Uuid::new_v4().to_string();
        let managed_process = ManagedTokioProcess {
            id: process_id.clone(),
            child,
            created_at: start_time,
            status: ProcessStatus::Starting,
            metadata: ProcessMetadata {
                command: config.command,
                args: config.args,
                working_dir: config.working_dir,
                timeout: config.timeout,
            },
        };

        let mut processes = self.processes.lock().await;
        processes.push(managed_process);

        // 执行进程并收集指标
        let output = processes.last_mut().unwrap().child.wait_with_output().await?;
        let duration = start_time.elapsed();
        let output_size = output.stdout.len();

        metrics_callback(duration, output_size);

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    pub async fn monitor_all_processes(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        for process in processes.iter_mut() {
            if let Ok(Some(status)) = process.child.try_wait() {
                if status.success() {
                    process.status = ProcessStatus::Completed;
                } else {
                    process.status = ProcessStatus::Failed;
                }
            }

            // 检查超时
            if let Some(timeout) = process.metadata.timeout {
                if process.created_at.elapsed() > timeout {
                    process.status = ProcessStatus::Terminated;
                    process.child.kill().await?;
                }
            }
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct ProcessConfig {
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub env_vars: std::collections::HashMap<String, String>,
    pub timeout: Option<Duration>,
}
```

### 2.3 性能优化策略

```rust
use tokio::process::Command as TokioCommand;
use tokio::sync::RwLock;
use std::sync::Arc;
use std::time::{Duration, Instant};

// 高性能 Tokio 进程池
pub struct HighPerformanceTokioPool {
    pool: Arc<RwLock<Vec<TokioCommand>>>,
    metrics: Arc<RwLock<PoolMetrics>>,
    config: PoolConfig,
}

#[derive(Debug)]
pub struct PoolMetrics {
    pub total_executions: u64,
    pub successful_executions: u64,
    pub failed_executions: u64,
    pub average_execution_time: Duration,
    pub peak_concurrent_processes: usize,
}

#[derive(Debug, Clone)]
pub struct PoolConfig {
    pub initial_size: usize,
    pub max_size: usize,
    pub idle_timeout: Duration,
    pub health_check_interval: Duration,
}

impl HighPerformanceTokioPool {
    pub fn new(config: PoolConfig) -> Self {
        Self {
            pool: Arc::new(RwLock::new(Vec::new())),
            metrics: Arc::new(RwLock::new(PoolMetrics {
                total_executions: 0,
                successful_executions: 0,
                failed_executions: 0,
                average_execution_time: Duration::from_millis(0),
                peak_concurrent_processes: 0,
            })),
            config,
        }
    }

    pub async fn execute_optimized(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let start_time = Instant::now();

        // 使用预配置的命令
        let mut cmd = TokioCommand::new(command);
        cmd.args(args);

        // 优化配置
        cmd.stdin(std::process::Stdio::null())
           .stdout(std::process::Stdio::piped())
           .stderr(std::process::Stdio::piped());

        let child = cmd.spawn()?;
        let output = child.wait_with_output().await?;
        let duration = start_time.elapsed();

        // 更新指标
        self.update_metrics(duration, output.status.success()).await;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("进程执行失败: {}", String::from_utf8_lossy(&output.stderr)).into())
        }
    }

    async fn update_metrics(&self, duration: Duration, success: bool) {
        let mut metrics = self.metrics.write().await;
        metrics.total_executions += 1;

        if success {
            metrics.successful_executions += 1;
        } else {
            metrics.failed_executions += 1;
        }

        // 更新平均执行时间
        let total_time = metrics.average_execution_time.as_millis() as u128 * (metrics.total_executions - 1) as u128;
        let new_avg = (total_time + duration.as_millis() as u128) / metrics.total_executions as u128;
        metrics.average_execution_time = Duration::from_millis(new_avg as u64);
    }

    pub async fn get_metrics(&self) -> PoolMetrics {
        self.metrics.read().await.clone()
    }
}
```

## 3. Async-Std 进程管理

### 3.1 标准库风格

```rust
use async_std::process::{Command as AsyncStdCommand, Stdio};
use async_std::io::{BufReader, BufWriter};

// Async-Std 基础进程管理
async fn basic_async_std_process() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = AsyncStdCommand::new("echo")
        .arg("Hello, Async-Std!")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // Async-Std 异步操作
    if let Some(stdin) = child.stdin.take() {
        let mut writer = BufWriter::new(stdin);
        writer.write_all(b"Async-Std input\n").await?;
        writer.flush().await?;
    }

    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        let mut lines = reader.lines();
        while let Some(line) = lines.next().await {
            let line = line?;
            println!("Async-Std 输出: {}", line);
        }
    }

    let status = child.status().await?;
    println!("Async-Std 进程完成: {:?}", status);

    Ok(())
}

// Async-Std 进程管理器
pub struct AsyncStdProcessManager {
    processes: std::sync::Arc<async_std::sync::Mutex<Vec<AsyncStdProcess>>>,
    max_concurrent: usize,
}

#[derive(Debug)]
pub struct AsyncStdProcess {
    pub id: String,
    pub child: async_std::process::Child,
    pub created_at: std::time::Instant,
    pub status: ProcessStatus,
}

impl AsyncStdProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            processes: std::sync::Arc::new(async_std::sync::Mutex::new(Vec::new())),
            max_concurrent,
        }
    }

    pub async fn spawn_process(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        if processes.len() >= self.max_concurrent {
            return Err("已达到最大并发进程数限制".into());
        }

        let process_id = uuid::Uuid::new_v4().to_string();

        let mut cmd = AsyncStdCommand::new(command);
        cmd.args(args);
        cmd.stdin(Stdio::piped())
           .stdout(Stdio::piped())
           .stderr(Stdio::piped());

        let child = cmd.spawn()?;

        let async_std_process = AsyncStdProcess {
            id: process_id.clone(),
            child,
            created_at: std::time::Instant::now(),
            status: ProcessStatus::Starting,
        };

        processes.push(async_std_process);

        Ok(process_id)
    }

    pub async fn wait_for_process(
        &self,
        process_id: &str,
    ) -> Result<async_std::process::Output, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id) {
            let output = process.child.output().await?;
            process.status = if output.status.success() {
                ProcessStatus::Completed
            } else {
                ProcessStatus::Failed
            };
            Ok(output)
        } else {
            Err("进程未找到".into())
        }
    }
}
```

### 3.2 与 Tokio 对比

```rust
use std::time::Duration;
use std::time::Instant;

// 性能对比测试
pub struct ProcessLibraryComparison {
    tokio_manager: AdvancedTokioProcessManager,
    async_std_manager: AsyncStdProcessManager,
}

impl ProcessLibraryComparison {
    pub fn new() -> Self {
        Self {
            tokio_manager: AdvancedTokioProcessManager::new(10),
            async_std_manager: AsyncStdProcessManager::new(10),
        }
    }

    pub async fn benchmark_execution(&self, iterations: usize) -> ComparisonResults {
        let mut tokio_times = Vec::new();
        let mut async_std_times = Vec::new();

        for _ in 0..iterations {
            // Tokio 测试
            let start = Instant::now();
            let config = ProcessConfig {
                command: "echo".to_string(),
                args: vec!["tokio_test".to_string()],
                working_dir: None,
                env_vars: std::collections::HashMap::new(),
                timeout: Some(Duration::from_secs(5)),
            };

            let _ = self.tokio_manager.execute_with_metrics(config, |_, _| {}).await;
            tokio_times.push(start.elapsed());

            // Async-Std 测试
            let start = Instant::now();
            let _ = self.async_std_manager.spawn_process("echo", &["async_std_test".to_string()]).await;
            async_std_times.push(start.elapsed());
        }

        ComparisonResults {
            tokio_avg_time: tokio_times.iter().sum::<Duration>() / tokio_times.len() as u32,
            async_std_avg_time: async_std_times.iter().sum::<Duration>() / async_std_times.len() as u32,
            tokio_min_time: tokio_times.iter().min().copied().unwrap_or_default(),
            async_std_min_time: async_std_times.iter().min().copied().unwrap_or_default(),
            tokio_max_time: tokio_times.iter().max().copied().unwrap_or_default(),
            async_std_max_time: async_std_times.iter().max().copied().unwrap_or_default(),
        }
    }
}

#[derive(Debug)]
pub struct ComparisonResults {
    pub tokio_avg_time: Duration,
    pub async_std_avg_time: Duration,
    pub tokio_min_time: Duration,
    pub async_std_min_time: Duration,
    pub tokio_max_time: Duration,
    pub async_std_max_time: Duration,
}
```

### 3.3 迁移策略

```rust
// 从 Tokio 迁移到 Async-Std 的策略
pub struct MigrationStrategy {
    // 迁移步骤
    pub steps: Vec<MigrationStep>,
    // 兼容性检查
    pub compatibility_check: CompatibilityCheck,
}

#[derive(Debug)]
pub enum MigrationStep {
    // 1. 替换导入
    ReplaceImports,
    // 2. 更新命令创建
    UpdateCommandCreation,
    // 3. 修改异步操作
    ModifyAsyncOperations,
    // 4. 更新错误处理
    UpdateErrorHandling,
    // 5. 测试验证
    TestValidation,
}

#[derive(Debug)]
pub struct CompatibilityCheck {
    pub tokio_features_used: Vec<String>,
    pub async_std_equivalents: Vec<String>,
    pub breaking_changes: Vec<String>,
    pub migration_difficulty: MigrationDifficulty,
}

#[derive(Debug)]
pub enum MigrationDifficulty {
    Easy,
    Medium,
    Hard,
}

impl MigrationStrategy {
    pub fn analyze_tokio_code(&self, code: &str) -> CompatibilityCheck {
        let mut features_used = Vec::new();
        let mut equivalents = Vec::new();
        let mut breaking_changes = Vec::new();

        // 分析代码中使用的 Tokio 特性
        if code.contains("tokio::process::Command") {
            features_used.push("tokio::process::Command".to_string());
            equivalents.push("async_std::process::Command".to_string());
        }

        if code.contains("tokio::io::AsyncBufReadExt") {
            features_used.push("tokio::io::AsyncBufReadExt".to_string());
            equivalents.push("async_std::io::BufReadExt".to_string());
        }

        if code.contains("tokio::time::timeout") {
            features_used.push("tokio::time::timeout".to_string());
            equivalents.push("async_std::future::timeout".to_string());
        }

        // 检查潜在的破坏性变更
        if code.contains("tokio::sync::Mutex") {
            breaking_changes.push("tokio::sync::Mutex 需要替换为 async_std::sync::Mutex".to_string());
        }

        CompatibilityCheck {
            tokio_features_used: features_used,
            async_std_equivalents: equivalents,
            breaking_changes,
            migration_difficulty: MigrationDifficulty::Medium,
        }
    }
}
```

## 4. Duct 进程组合

### 4.1 管道组合语法

```rust
use duct::cmd;

// Duct 基础管道组合
fn basic_duct_pipes() -> Result<(), Box<dyn std::error::Error>> {
    // 简单管道
    let output = cmd!("echo", "Hello, World!")
        .pipe(cmd!("wc", "-c"))
        .read()?;

    println!("字符数: {}", output);

    // 多级管道
    let complex_output = cmd!("find", ".", "-name", "*.rs")
        .pipe(cmd!("head", "-10"))
        .pipe(cmd!("wc", "-l"))
        .read()?;

    println!("文件数: {}", complex_output);

    // 条件管道
    let conditional_output = cmd!("ls", "-la")
        .pipe(cmd!("grep", "rust"))
        .pipe(cmd!("wc", "-l"))
        .read()?;

    println!("Rust 相关文件数: {}", conditional_output);

    Ok(())
}

// 高级 Duct 管道组合
fn advanced_duct_pipes() -> Result<(), Box<dyn std::error::Error>> {
    // 并行管道
    let parallel_output = cmd!("echo", "parallel1")
        .pipe(cmd!("echo", "parallel2"))
        .pipe(cmd!("echo", "parallel3"))
        .read()?;

    println!("并行输出: {}", parallel_output);

    // 错误处理管道
    let error_handling_output = cmd!("ls", "/nonexistent")
        .pipe(cmd!("wc", "-l"))
        .stderr_to_stdout()
        .read()?;

    println!("错误处理输出: {}", error_handling_output);

    // 环境变量管道
    let env_output = cmd!("env")
        .env("MY_VAR", "duct_value")
        .pipe(cmd!("grep", "MY_VAR"))
        .read()?;

    println!("环境变量输出: {}", env_output);

    Ok(())
}
```

### 4.2 复杂命令构建

```rust
use duct::cmd;
use std::path::Path;

// 复杂 Duct 命令构建器
pub struct DuctCommandBuilder {
    base_command: String,
    args: Vec<String>,
    env_vars: std::collections::HashMap<String, String>,
    working_dir: Option<String>,
    stdin: Option<String>,
    stdout: Option<String>,
    stderr: Option<String>,
}

impl DuctCommandBuilder {
    pub fn new(command: &str) -> Self {
        Self {
            base_command: command.to_string(),
            args: Vec::new(),
            env_vars: std::collections::HashMap::new(),
            working_dir: None,
            stdin: None,
            stdout: None,
            stderr: None,
        }
    }

    pub fn arg(mut self, arg: &str) -> Self {
        self.args.push(arg.to_string());
        self
    }

    pub fn args(mut self, args: &[String]) -> Self {
        self.args.extend(args.iter().cloned());
        self
    }

    pub fn env(mut self, key: &str, value: &str) -> Self {
        self.env_vars.insert(key.to_string(), value.to_string());
        self
    }

    pub fn working_dir(mut self, dir: &str) -> Self {
        self.working_dir = Some(dir.to_string());
        self
    }

    pub fn stdin(mut self, input: &str) -> Self {
        self.stdin = Some(input.to_string());
        self
    }

    pub fn stdout(mut self, output: &str) -> Self {
        self.stdout = Some(output.to_string());
        self
    }

    pub fn stderr(mut self, error: &str) -> Self {
        self.stderr = Some(error.to_string());
        self
    }

    pub fn build(self) -> Result<duct::Expression, Box<dyn std::error::Error>> {
        let mut expression = cmd!(&self.base_command, &self.args);

        // 设置环境变量
        for (key, value) in self.env_vars {
            expression = expression.env(key, value);
        }

        // 设置工作目录
        if let Some(dir) = self.working_dir {
            expression = expression.dir(dir);
        }

        // 设置输入
        if let Some(input) = self.stdin {
            expression = expression.stdin_bytes(input);
        }

        // 设置输出
        if let Some(output) = self.stdout {
            expression = expression.stdout_path(output);
        }

        // 设置错误输出
        if let Some(error) = self.stderr {
            expression = expression.stderr_path(error);
        }

        Ok(expression)
    }
}

// 使用示例
fn use_duct_command_builder() -> Result<(), Box<dyn std::error::Error>> {
    let expression = DuctCommandBuilder::new("grep")
        .arg("rust")
        .args(&["-r", ".", "--include=*.rs"])
        .env("GREP_OPTIONS", "--color=always")
        .working_dir("/tmp")
        .stdout("grep_output.txt")
        .build()?;

    let output = expression.read()?;
    println!("搜索输出: {}", output);

    Ok(())
}
```

### 4.3 错误处理机制

```rust
use duct::cmd;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DuctError {
    #[error("命令执行失败: {0}")]
    CommandFailed(String),

    #[error("管道连接失败: {0}")]
    PipeFailed(String),

    #[error("环境变量设置失败: {0}")]
    EnvFailed(String),

    #[error("文件操作失败: {0}")]
    FileFailed(String),
}

// Duct 错误处理
pub struct DuctErrorHandler {
    max_retries: u32,
    retry_delay: std::time::Duration,
}

impl DuctErrorHandler {
    pub fn new(max_retries: u32, retry_delay: std::time::Duration) -> Self {
        Self {
            max_retries,
            retry_delay,
        }
    }

    pub async fn execute_with_retry(
        &self,
        expression: duct::Expression,
    ) -> Result<String, DuctError> {
        let mut last_error = None;

        for attempt in 0..=self.max_retries {
            match expression.read() {
                Ok(output) => return Ok(output),
                Err(e) => {
                    last_error = Some(e);

                    if attempt < self.max_retries {
                        tokio::time::sleep(self.retry_delay).await;
                    }
                }
            }
        }

        Err(DuctError::CommandFailed(
            last_error.unwrap().to_string()
        ))
    }

    pub fn handle_pipe_error(&self, error: &str) -> DuctError {
        if error.contains("pipe") {
            DuctError::PipeFailed(error.to_string())
        } else if error.contains("env") {
            DuctError::EnvFailed(error.to_string())
        } else if error.contains("file") {
            DuctError::FileFailed(error.to_string())
        } else {
            DuctError::CommandFailed(error.to_string())
        }
    }
}

// 使用示例
async fn use_duct_error_handler() -> Result<(), Box<dyn std::error::Error>> {
    let error_handler = DuctErrorHandler::new(
        3,
        std::time::Duration::from_millis(100),
    );

    let expression = cmd!("risky_command")
        .pipe(cmd!("wc", "-l"));

    match error_handler.execute_with_retry(expression).await {
        Ok(output) => {
            println!("命令执行成功: {}", output);
        }
        Err(e) => {
            println!("命令执行失败: {}", e);
        }
    }

    Ok(())
}
```

## 5. Subprocess 高级控制

### 5.1 高级进程控制

```rust
use subprocess::{Popen, PopenConfig, Redirection};
use std::time::Duration;

// Subprocess 高级进程控制
fn advanced_subprocess_control() -> Result<(), Box<dyn std::error::Error>> {
    // 基础进程创建
    let mut process = Popen::create(
        &["python", "-c", "print('Hello, Subprocess!')"],
        PopenConfig {
            stdout: Redirection::Pipe,
            stderr: Redirection::Pipe,
            ..Default::default()
        },
    )?;

    // 等待进程完成
    let exit_status = process.wait()?;
    println!("进程退出状态: {:?}", exit_status);

    // 获取输出
    let (stdout, stderr) = process.communicate(None)?;
    println!("标准输出: {}", stdout.unwrap_or_default());
    println!("标准错误: {}", stderr.unwrap_or_default());

    Ok(())
}

// Subprocess 进程管理器
pub struct SubprocessManager {
    processes: std::sync::Arc<std::sync::Mutex<Vec<ManagedSubprocess>>>,
    max_concurrent: usize,
}

#[derive(Debug)]
pub struct ManagedSubprocess {
    pub id: String,
    pub process: Popen,
    pub created_at: std::time::Instant,
    pub status: ProcessStatus,
    pub config: SubprocessConfig,
}

#[derive(Debug, Clone)]
pub struct SubprocessConfig {
    pub command: Vec<String>,
    pub working_dir: Option<String>,
    pub env_vars: std::collections::HashMap<String, String>,
    pub timeout: Option<Duration>,
    pub stdout_redirection: Redirection,
    pub stderr_redirection: Redirection,
}

impl SubprocessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            processes: std::sync::Arc::new(std::sync::Mutex::new(Vec::new())),
            max_concurrent,
        }
    }

    pub fn spawn_process(
        &self,
        config: SubprocessConfig,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().unwrap();

        if processes.len() >= self.max_concurrent {
            return Err("已达到最大并发进程数限制".into());
        }

        let process_id = uuid::Uuid::new_v4().to_string();

        let mut popen_config = PopenConfig {
            stdout: config.stdout_redirection,
            stderr: config.stderr_redirection,
            ..Default::default()
        };

        if let Some(working_dir) = &config.working_dir {
            popen_config.cwd = Some(working_dir.into());
        }

        for (key, value) in &config.env_vars {
            popen_config.env.insert(key.clone(), value.clone());
        }

        let process = Popen::create(&config.command, popen_config)?;

        let managed_process = ManagedSubprocess {
            id: process_id.clone(),
            process,
            created_at: std::time::Instant::now(),
            status: ProcessStatus::Starting,
            config,
        };

        processes.push(managed_process);

        Ok(process_id)
    }

    pub fn terminate_process(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().unwrap();

        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id) {
            process.process.terminate()?;
            process.status = ProcessStatus::Terminated;
        }

        Ok(())
    }

    pub fn kill_process(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().unwrap();

        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id) {
            process.process.kill()?;
            process.status = ProcessStatus::Terminated;
        }

        Ok(())
    }

    pub fn get_process_output(&self, process_id: &str) -> Result<String, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().unwrap();

        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id) {
            let (stdout, _) = process.process.communicate(None)?;
            Ok(stdout.unwrap_or_default())
        } else {
            Err("进程未找到".into())
        }
    }
}
```

### 5.2 跨平台兼容

```rust
use subprocess::{Popen, PopenConfig, Redirection};
use std::path::Path;

// 跨平台 Subprocess 配置
pub struct CrossPlatformSubprocessConfig {
    pub command: Vec<String>,
    pub working_dir: Option<String>,
    pub env_vars: std::collections::HashMap<String, String>,
    pub platform_specific: PlatformSpecificConfig,
}

#[derive(Debug, Clone)]
pub struct PlatformSpecificConfig {
    #[cfg(unix)]
    pub unix_config: UnixConfig,

    #[cfg(windows)]
    pub windows_config: WindowsConfig,

    #[cfg(target_os = "macos")]
    pub macos_config: MacOSConfig,
}

#[cfg(unix)]
#[derive(Debug, Clone)]
pub struct UnixConfig {
    pub user_id: Option<u32>,
    pub group_id: Option<u32>,
    pub umask: Option<u32>,
}

#[cfg(windows)]
#[derive(Debug, Clone)]
pub struct WindowsConfig {
    pub show_window: bool,
    pub creation_flags: u32,
}

#[cfg(target_os = "macos")]
#[derive(Debug, Clone)]
pub struct MacOSConfig {
    pub launchd_compatible: bool,
}

impl CrossPlatformSubprocessConfig {
    pub fn new(command: Vec<String>) -> Self {
        Self {
            command,
            working_dir: None,
            env_vars: std::collections::HashMap::new(),
            platform_specific: PlatformSpecificConfig {
                #[cfg(unix)]
                unix_config: UnixConfig {
                    user_id: None,
                    group_id: None,
                    umask: None,
                },

                #[cfg(windows)]
                windows_config: WindowsConfig {
                    show_window: false,
                    creation_flags: 0,
                },

                #[cfg(target_os = "macos")]
                macos_config: MacOSConfig {
                    launchd_compatible: false,
                },
            },
        }
    }

    pub fn build_popen_config(&self) -> PopenConfig {
        let mut config = PopenConfig {
            stdout: Redirection::Pipe,
            stderr: Redirection::Pipe,
            ..Default::default()
        };

        if let Some(working_dir) = &self.working_dir {
            config.cwd = Some(working_dir.into());
        }

        for (key, value) in &self.env_vars {
            config.env.insert(key.clone(), value.clone());
        }

        // 平台特定配置
        #[cfg(unix)]
        {
            if let Some(uid) = self.platform_specific.unix_config.user_id {
                config.uid = Some(uid);
            }
            if let Some(gid) = self.platform_specific.unix_config.group_id {
                config.gid = Some(gid);
            }
            if let Some(umask) = self.platform_specific.unix_config.umask {
                config.umask = Some(umask);
            }
        }

        #[cfg(windows)]
        {
            config.show_window = self.platform_specific.windows_config.show_window;
            config.creation_flags = self.platform_specific.windows_config.creation_flags;
        }

        config
    }
}

// 使用示例
fn use_cross_platform_subprocess() -> Result<(), Box<dyn std::error::Error>> {
    let mut config = CrossPlatformSubprocessConfig::new(
        vec!["python".to_string(), "-c".to_string(), "print('Cross-platform!')".to_string()]
    );

    config.working_dir = Some("/tmp".to_string());
    config.env_vars.insert("PYTHONPATH".to_string(), "/usr/local/lib/python3.9".to_string());

    #[cfg(unix)]
    {
        config.platform_specific.unix_config.user_id = Some(1000);
        config.platform_specific.unix_config.group_id = Some(1000);
    }

    #[cfg(windows)]
    {
        config.platform_specific.windows_config.show_window = false;
    }

    let popen_config = config.build_popen_config();
    let mut process = Popen::create(&config.command, popen_config)?;

    let exit_status = process.wait()?;
    println!("跨平台进程完成: {:?}", exit_status);

    Ok(())
}
```

### 5.3 安全性增强

```rust
use subprocess::{Popen, PopenConfig, Redirection};
use std::collections::HashSet;

// 安全的 Subprocess 配置
pub struct SecureSubprocessConfig {
    pub allowed_commands: HashSet<String>,
    pub blocked_commands: HashSet<String>,
    pub max_execution_time: Duration,
    pub resource_limits: ResourceLimits,
    pub sandbox_config: SandboxConfig,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    pub max_memory_mb: u64,
    pub max_cpu_time: Duration,
    pub max_file_descriptors: u32,
}

#[derive(Debug, Clone)]
pub struct SandboxConfig {
    pub chroot_path: Option<String>,
    pub drop_capabilities: bool,
    pub seccomp_filter: bool,
    pub network_isolation: bool,
}

impl SecureSubprocessConfig {
    pub fn new() -> Self {
        Self {
            allowed_commands: HashSet::new(),
            blocked_commands: HashSet::new(),
            max_execution_time: Duration::from_secs(30),
            resource_limits: ResourceLimits {
                max_memory_mb: 100,
                max_cpu_time: Duration::from_secs(60),
                max_file_descriptors: 1024,
            },
            sandbox_config: SandboxConfig {
                chroot_path: None,
                drop_capabilities: true,
                seccomp_filter: true,
                network_isolation: false,
            },
        }
    }

    pub fn allow_command(mut self, command: &str) -> Self {
        self.allowed_commands.insert(command.to_string());
        self
    }

    pub fn block_command(mut self, command: &str) -> Self {
        self.blocked_commands.insert(command.to_string());
        self
    }

    pub fn validate_command(&self, command: &str) -> Result<(), SecurityError> {
        if self.blocked_commands.contains(command) {
            return Err(SecurityError::CommandBlocked(command.to_string()));
        }

        if !self.allowed_commands.is_empty() && !self.allowed_commands.contains(command) {
            return Err(SecurityError::CommandNotAllowed(command.to_string()));
        }

        Ok(())
    }

    pub fn build_secure_config(&self, command: &[String]) -> Result<PopenConfig, SecurityError> {
        if command.is_empty() {
            return Err(SecurityError::EmptyCommand);
        }

        self.validate_command(&command[0])?;

        let mut config = PopenConfig {
            stdout: Redirection::Pipe,
            stderr: Redirection::Pipe,
            ..Default::default()
        };

        // 设置资源限制
        #[cfg(unix)]
        {
            use nix::sys::resource::{setrlimit, Resource, ResourceLimits as NixResourceLimits};

            setrlimit(
                Resource::RLIMIT_AS,
                NixResourceLimits::new(
                    self.resource_limits.max_memory_mb * 1024 * 1024,
                    self.resource_limits.max_memory_mb * 1024 * 1024 * 2
                )
            ).map_err(|_| SecurityError::ResourceLimitFailed)?;

            setrlimit(
                Resource::RLIMIT_CPU,
                NixResourceLimits::new(
                    self.resource_limits.max_cpu_time.as_secs() as u64,
                    self.resource_limits.max_cpu_time.as_secs() as u64 * 2
                )
            ).map_err(|_| SecurityError::ResourceLimitFailed)?;
        }

        // 沙箱配置
        if self.sandbox_config.drop_capabilities {
            #[cfg(unix)]
            {
                use nix::unistd::{setuid, setgid, Uid, Gid};
                setuid(Uid::from_raw(65534)).map_err(|_| SecurityError::SandboxFailed)?; // nobody
                setgid(Gid::from_raw(65534)).map_err(|_| SecurityError::SandboxFailed)?; // nogroup
            }
        }

        Ok(config)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum SecurityError {
    #[error("命令被阻止: {0}")]
    CommandBlocked(String),

    #[error("命令不被允许: {0}")]
    CommandNotAllowed(String),

    #[error("空命令")]
    EmptyCommand,

    #[error("资源限制设置失败")]
    ResourceLimitFailed,

    #[error("沙箱设置失败")]
    SandboxFailed,
}

// 使用示例
fn use_secure_subprocess() -> Result<(), Box<dyn std::error::Error>> {
    let secure_config = SecureSubprocessConfig::new()
        .allow_command("echo")
        .allow_command("cat")
        .block_command("rm")
        .block_command("dd");

    let command = vec!["echo".to_string(), "Hello, Secure Subprocess!".to_string()];
    let popen_config = secure_config.build_secure_config(&command)?;

    let mut process = Popen::create(&command, popen_config)?;
    let exit_status = process.wait()?;

    println!("安全进程完成: {:?}", exit_status);

    Ok(())
}
```

## 6. 性能基准测试

```rust
use std::time::{Duration, Instant};
use std::sync::Arc;
use tokio::sync::Mutex;

// 性能基准测试框架
pub struct ProcessLibraryBenchmark {
    results: Arc<Mutex<Vec<BenchmarkResult>>>,
}

#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub library: String,
    pub operation: String,
    pub duration: Duration,
    pub memory_usage: u64,
    pub cpu_usage: f64,
    pub success: bool,
}

impl ProcessLibraryBenchmark {
    pub fn new() -> Self {
        Self {
            results: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn benchmark_library(
        &self,
        library: &str,
        operation: &str,
        test_function: impl Fn() -> Result<(), Box<dyn std::error::Error>> + Send + 'static,
    ) -> BenchmarkResult {
        let start_time = Instant::now();
        let start_memory = self.get_memory_usage();
        let start_cpu = self.get_cpu_usage();

        let success = test_function().is_ok();

        let duration = start_time.elapsed();
        let end_memory = self.get_memory_usage();
        let end_cpu = self.get_cpu_usage();

        let result = BenchmarkResult {
            library: library.to_string(),
            operation: operation.to_string(),
            duration,
            memory_usage: end_memory.saturating_sub(start_memory),
            cpu_usage: end_cpu - start_cpu,
            success,
        };

        let mut results = self.results.lock().await;
        results.push(result.clone());

        result
    }

    pub async fn run_comprehensive_benchmark(&self) -> Vec<BenchmarkResult> {
        let mut results = Vec::new();

        // 测试标准库
        results.push(self.benchmark_library(
            "std::process",
            "basic_spawn",
            || {
                let child = std::process::Command::new("echo")
                    .arg("test")
                    .spawn()?;
                child.wait()?;
                Ok(())
            },
        ).await);

        // 测试 Tokio
        results.push(self.benchmark_library(
            "tokio::process",
            "async_spawn",
            || {
                tokio::runtime::Runtime::new()?.block_on(async {
                    let child = tokio::process::Command::new("echo")
                        .arg("test")
                        .spawn()?;
                    child.wait().await?;
                    Ok::<(), Box<dyn std::error::Error>>(())
                })
            },
        ).await);

        // 测试 Async-Std
        results.push(self.benchmark_library(
            "async-std::process",
            "async_spawn",
            || {
                async_std::task::block_on(async {
                    let child = async_std::process::Command::new("echo")
                        .arg("test")
                        .spawn()?;
                    child.status().await?;
                    Ok::<(), Box<dyn std::error::Error>>(())
                })
            },
        ).await);

        // 测试 Duct
        results.push(self.benchmark_library(
            "duct",
            "pipe_composition",
            || {
                let _output = duct::cmd!("echo", "test").read()?;
                Ok(())
            },
        ).await);

        // 测试 Subprocess
        results.push(self.benchmark_library(
            "subprocess",
            "advanced_control",
            || {
                let mut process = subprocess::Popen::create(
                    &["echo", "test"],
                    subprocess::PopenConfig {
                        stdout: subprocess::Redirection::Pipe,
                        ..Default::default()
                    },
                )?;
                process.wait()?;
                Ok(())
            },
        ).await);

        results
    }

    fn get_memory_usage(&self) -> u64 {
        // 简化的内存使用获取
        0
    }

    fn get_cpu_usage(&self) -> f64 {
        // 简化的 CPU 使用获取
        0.0
    }

    pub async fn generate_report(&self) -> String {
        let results = self.results.lock().await;
        let mut report = String::new();

        report.push_str("# 进程管理库性能基准测试报告\n\n");

        for result in results.iter() {
            report.push_str(&format!(
                "## {}\n- 操作: {}\n- 耗时: {:?}\n- 内存使用: {} bytes\n- CPU 使用: {:.2}%\n- 成功: {}\n\n",
                result.library,
                result.operation,
                result.duration,
                result.memory_usage,
                result.cpu_usage,
                result.success
            ));
        }

        report
    }
}
```

## 7. 最佳实践

### 7.1 库选择最佳实践

```rust
// 库选择决策矩阵
pub struct LibrarySelectionMatrix {
    requirements: ProcessRequirements,
    constraints: ProcessConstraints,
}

#[derive(Debug)]
pub struct ProcessRequirements {
    pub performance: PerformanceRequirement,
    pub complexity: ComplexityRequirement,
    pub platform_support: PlatformSupport,
    pub feature_set: FeatureSet,
}

#[derive(Debug)]
pub enum PerformanceRequirement {
    High,
    Medium,
    Low,
}

#[derive(Debug)]
pub enum ComplexityRequirement {
    Simple,
    Moderate,
    Complex,
}

#[derive(Debug)]
pub enum PlatformSupport {
    CrossPlatform,
    UnixOnly,
    WindowsOnly,
}

#[derive(Debug)]
pub struct FeatureSet {
    pub async_support: bool,
    pub pipe_composition: bool,
    pub advanced_control: bool,
    pub security_features: bool,
}

#[derive(Debug)]
pub struct ProcessConstraints {
    pub memory_limit: u64,
    pub cpu_limit: f64,
    pub timeout: Duration,
    pub security_level: SecurityLevel,
}

#[derive(Debug)]
pub enum SecurityLevel {
    Low,
    Medium,
    High,
    Critical,
}

impl LibrarySelectionMatrix {
    pub fn recommend_library(&self) -> RecommendedLibrary {
        match (&self.requirements.performance, &self.requirements.complexity) {
            (PerformanceRequirement::High, ComplexityRequirement::Simple) => {
                RecommendedLibrary::Tokio
            }
            (PerformanceRequirement::Medium, ComplexityRequirement::Simple) => {
                RecommendedLibrary::AsyncStd
            }
            (PerformanceRequirement::Low, ComplexityRequirement::Simple) => {
                RecommendedLibrary::Std
            }
            (PerformanceRequirement::High, ComplexityRequirement::Moderate) => {
                RecommendedLibrary::Subprocess
            }
            (PerformanceRequirement::Medium, ComplexityRequirement::Moderate) => {
                RecommendedLibrary::Duct
            }
            _ => RecommendedLibrary::Subprocess,
        }
    }
}

#[derive(Debug)]
pub enum RecommendedLibrary {
    Std,
    Tokio,
    AsyncStd,
    Duct,
    Subprocess,
}
```

### 7.2 性能优化最佳实践

```rust
// 性能优化最佳实践
pub struct PerformanceOptimization {
    pub strategies: Vec<OptimizationStrategy>,
}

#[derive(Debug)]
pub enum OptimizationStrategy {
    // 进程池复用
    ProcessPoolReuse {
        pool_size: usize,
        idle_timeout: Duration,
    },

    // 异步并发
    AsyncConcurrency {
        max_concurrent: usize,
        backpressure: bool,
    },

    // 内存优化
    MemoryOptimization {
        zero_copy: bool,
        memory_pool: bool,
    },

    // CPU 优化
    CpuOptimization {
        cpu_affinity: bool,
        priority: ProcessPriority,
    },
}

#[derive(Debug)]
pub enum ProcessPriority {
    Low,
    Normal,
    High,
    Critical,
}

impl PerformanceOptimization {
    pub fn new() -> Self {
        Self {
            strategies: Vec::new(),
        }
    }

    pub fn add_strategy(mut self, strategy: OptimizationStrategy) -> Self {
        self.strategies.push(strategy);
        self
    }

    pub fn apply_optimizations(&self, config: &mut ProcessConfig) {
        for strategy in &self.strategies {
            match strategy {
                OptimizationStrategy::ProcessPoolReuse { pool_size, idle_timeout } => {
                    config.pool_size = *pool_size;
                    config.idle_timeout = *idle_timeout;
                }
                OptimizationStrategy::AsyncConcurrency { max_concurrent, backpressure } => {
                    config.max_concurrent = *max_concurrent;
                    config.backpressure = *backpressure;
                }
                OptimizationStrategy::MemoryOptimization { zero_copy, memory_pool } => {
                    config.zero_copy = *zero_copy;
                    config.memory_pool = *memory_pool;
                }
                OptimizationStrategy::CpuOptimization { cpu_affinity, priority } => {
                    config.cpu_affinity = *cpu_affinity;
                    config.priority = priority.clone();
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct ProcessConfig {
    pub pool_size: usize,
    pub idle_timeout: Duration,
    pub max_concurrent: usize,
    pub backpressure: bool,
    pub zero_copy: bool,
    pub memory_pool: bool,
    pub cpu_affinity: bool,
    pub priority: ProcessPriority,
}
```

## 8. 小结

现代 Rust 进程管理库生态提供了丰富的选择，每个库都有其独特的优势和适用场景：

### 核心库特点总结

1. **std::process**：基础、同步、跨平台
2. **tokio::process**：高性能、异步、企业级
3. **async-std::process**：标准库风格、异步、易用
4. **duct**：管道组合、语法简洁、功能强大
5. **subprocess**：高级控制、跨平台、安全增强

### 选择建议

- **简单场景**：使用 `std::process`
- **高性能需求**：选择 `tokio::process`
- **标准库风格**：使用 `async-std::process`
- **管道组合**：选择 `duct`
- **企业级应用**：使用 `subprocess`

### 性能对比

| 库名               | 启动时间 | 内存使用 | CPU 效率 | 并发能力 |
| :--- | :--- | :--- | :--- | :--- || std::process       | 快       | 低       | 高       | 低       |
| tokio::process     | 中等     | 中等     | 高       | 高       |
| async-std::process | 中等     | 中等     | 中等     | 中等     |
| duct               | 快       | 低       | 高       | 低       |
| subprocess         | 慢       | 高       | 中等     | 中等     |

### 最佳实践总结

1. **根据需求选择**：性能、复杂度、平台支持
2. **优化策略**：进程池、异步并发、内存优化
3. **错误处理**：完善的错误处理和恢复机制
4. **安全考虑**：权限控制、资源限制、沙箱执行
5. **性能监控**：指标收集、性能分析、优化建议

通过合理选择和优化，现代 Rust 进程管理库能够满足从简单脚本到企业级应用的各种需求。
