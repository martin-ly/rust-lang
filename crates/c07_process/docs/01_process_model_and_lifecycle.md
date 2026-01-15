# C07-01. 进程模型与生命周期

> **文档定位**: Tier 3 技术参考
> **最后更新**: 2025-12-25
> **Rust版本**: 1.92.0+ (Edition 2024)
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

## 📋 目录

- [C07-01. 进程模型与生命周期](#c07-01-进程模型与生命周期)
  - [目录](#目录)
  - [1. 进程定义与模型](#1-进程定义与模型)
    - [1.1 进程理论基础](#11-进程理论基础)
    - [1.2 Rust 1.92.0 进程增强](#12-rust-1920-进程增强)
      - [异步闭包支持](#异步闭包支持)
      - [改进的模式匹配](#改进的模式匹配)
      - [增强的错误处理](#增强的错误处理)
    - [1.3 内存安全与所有权](#13-内存安全与所有权)
  - [2. 生命周期管理](#2-生命周期管理)
    - [2.1 进程状态机](#21-进程状态机)
    - [2.2 异步生命周期管理](#22-异步生命周期管理)
    - [2.3 资源自动释放](#23-资源自动释放)
  - [3. 进程属性与资源控制](#3-进程属性与资源控制)
    - [3.1 基础属性配置](#31-基础属性配置)
    - [3.2 高级资源限制](#32-高级资源限制)
    - [3.3 跨平台资源管理](#33-跨平台资源管理)
  - [4. Rust 的进程安全抽象](#4-rust-的进程安全抽象)
    - [4.1 类型安全保证](#41-类型安全保证)
    - [4.2 错误处理机制](#42-错误处理机制)
    - [4.3 平台兼容性](#43-平台兼容性)
  - [5. 现代库集成](#5-现代库集成)
    - [5.1 Tokio 异步进程](#51-tokio-异步进程)
    - [5.2 Async-Std 进程管理](#52-async-std-进程管理)
    - [5.3 Duct 进程组合](#53-duct-进程组合)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 资源管理最佳实践](#61-资源管理最佳实践)
    - [6.2 错误处理最佳实践](#62-错误处理最佳实践)
  - [7. 小结](#7-小结)
    - [关键特性总结](#关键特性总结)
    - [现代库生态](#现代库生态)

本章系统梳理 Rust 1.92.0 进程的理论基础、生命周期管理、资源属性控制及其安全抽象，结合现代开源库提供完整的实践指南。

## 1. 进程定义与模型

### 1.1 进程理论基础

- **进程**：操作系统分配资源和调度的基本单位，拥有独立的地址空间、代码、数据、堆栈和系统资源。
- **Rust 抽象**：通过 `std::process` 提供跨平台进程管理，封装平台细节，保证内存与资源安全。

```rust
pub struct Process {
    // 实际实现封装了平台特定细节
    inner: imp::Process,
}
```

- **内存隔离**：Rust 进程模型依赖操作系统的虚拟内存机制，确保进程间内存安全隔离。
- **所有权模型**：Rust 类型系统和所有权机制防止跨进程悬垂指针和未定义行为。

### 1.2 Rust 1.92.0 进程增强

Rust 1.92.0 版本为进程管理带来了显著的改进：

#### 异步闭包支持

```rust
use std::process::{Command, Stdio};
use std::future::Future;

// Rust 1.92.0 异步闭包示例
async fn async_process_handler<F>(handler: F) -> Result<(), Box<dyn std::error::Error>>
where
    F: FnOnce() -> Box<dyn Future<Output = Result<(), Box<dyn std::error::Error>>> + Send>,
{
    let result = handler().await;
    result
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    async_process_handler(|| {
        Box::new(async {
            let mut child = Command::new("echo")
                .arg("Hello from Rust 1.92.0!")
                .stdout(Stdio::piped())
                .spawn()?;

            let output = child.wait_with_output().await?;
            println!("Output: {}", String::from_utf8_lossy(&output.stdout));
            Ok(())
        })
    }).await?;

    Ok(())
}
```

#### 改进的模式匹配

```rust
use std::process::{Command, ExitStatus};

fn handle_process_status(status: ExitStatus) {
    match status {
        // Rust 1.92.0 增强的模式匹配
        status if status.success() => {
            println!("进程成功完成");
        }
        status if status.code().is_some() => {
            println!("进程异常退出，退出码: {:?}", status.code());
        }
        status if status.signal().is_some() => {
            println!("进程被信号终止: {:?}", status.signal());
        }
        _ => {
            println!("未知的进程状态");
        }
    }
}
```

#### 增强的错误处理

```rust
use std::process::{Command, Stdio};
use std::error::Error;

// Rust 1.92.0 改进的错误处理
async fn robust_process_execution() -> Result<String, Box<dyn Error>> {
    let output = Command::new("unknown_command")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .await
        .map_err(|e| format!("命令执行失败: {}", e))?;

    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        let error_msg = String::from_utf8_lossy(&output.stderr);
        Err(format!("命令执行失败: {}", error_msg).into())
    }
}
```

### 1.3 内存安全与所有权

Rust 的所有权模型在进程管理中提供了独特的安全保证：

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};

// 所有权确保资源安全释放
fn safe_process_management() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("ps")
        .arg("aux")
        .stdout(Stdio::piped())
        .spawn()?;

    // 所有权转移，确保资源正确释放
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);

        for line in reader.lines() {
            let line = line?;
            if line.contains("rust") {
                println!("Found process: {}", line);
            }
        }
    } // reader 和 stdout 在这里自动释放

    let status = child.wait()?;
    println!("进程完成，状态: {:?}", status);

    Ok(())
}
```

## 2. 生命周期管理

### 2.1 进程状态机

- **状态流转**：Created → Running → (Waiting →)* → Terminated
- **核心类型**：`std::process::Command`（进程构建器）、`Child`（子进程句柄）

```rust
use std::process::{Command, Stdio};
use std::time::Duration;
use tokio::time::timeout;

// 基础生命周期管理
fn basic_lifecycle() -> Result<(), Box<dyn std::error::Error>> {
    let mut command = Command::new("program");
    let child = command.spawn()?;  // Created → Running
    let status = child.wait()?;    // 等待进程终止
    println!("进程状态: {:?}", status);
    Ok(())
}

// 异步生命周期管理
async fn async_lifecycle() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("long_running_program")
        .stdout(Stdio::piped())
        .spawn()?;

    // 设置超时
    let timeout_duration = Duration::from_secs(30);

    match timeout(timeout_duration, child.wait()).await {
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

### 2.2 异步生命周期管理

Rust 1.92.0 提供了更好的异步进程生命周期管理：

```rust
use std::process::{Command, Stdio};
use tokio::process::Command as AsyncCommand;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use std::time::{Duration, Instant};

pub struct ProcessLifecycleManager {
    processes: std::sync::Arc<tokio::sync::Mutex<Vec<ManagedProcess>>>,
    max_concurrent: usize,
}

#[derive(Debug)]
pub struct ManagedProcess {
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
    Timeout,
}

#[derive(Debug, Clone)]
pub struct ProcessMetadata {
    pub command: String,
    pub args: Vec<String>,
    pub working_dir: Option<String>,
    pub timeout: Option<Duration>,
}

impl ProcessLifecycleManager {
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

        let managed_process = ManagedProcess {
            id: process_id.clone(),
            child,
            created_at: Instant::now(),
            status: ProcessStatus::Starting,
            metadata: ProcessMetadata {
                command: config.command,
                args: config.args,
                working_dir: config.working_dir,
                timeout: config.timeout,
            },
        };

        processes.push(managed_process);

        Ok(process_id)
    }

    pub async fn monitor_process(&self, process_id: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        if let Some(process) = processes.iter_mut().find(|p| p.id == process_id) {
            // 检查进程状态
            if let Ok(Some(status)) = process.child.try_wait() {
                if status.success() {
                    process.status = ProcessStatus::Completed;
                } else {
                    process.status = ProcessStatus::Failed;
                }
            } else {
                // 检查超时
                if let Some(timeout) = process.metadata.timeout {
                    if process.created_at.elapsed() > timeout {
                        process.status = ProcessStatus::Timeout;
                        process.child.kill().await?;
                    }
                }
            }
        }

        Ok(())
    }

    pub async fn cleanup_completed_processes(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        let initial_count = processes.len();
        processes.retain(|process| {
            matches!(process.status, ProcessStatus::Running | ProcessStatus::Starting)
        });

        let cleaned_count = initial_count - processes.len();
        if cleaned_count > 0 {
            println!("清理了 {} 个已完成的进程", cleaned_count);
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

### 2.3 资源自动释放

- **资源释放**：`Child` 实现 `Drop` trait，析构时自动释放系统资源（文件描述符、内存等）。
- **安全保证**：即使子进程崩溃，父进程不会受内存安全威胁，所有错误通过 `Result` 类型显式处理。

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader, Write};

// 自动资源管理示例
fn automatic_resource_management() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 写入数据
    if let Some(stdin) = child.stdin.take() {
        let mut writer = std::io::BufWriter::new(stdin);
        writer.write_all(b"Hello, World!\n")?;
        writer.flush()?;
        // writer 和 stdin 在这里自动释放
    }

    // 读取输出
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            let line = line?;
            println!("输出: {}", line);
        }
        // reader 和 stdout 在这里自动释放
    }

    let status = child.wait()?;
    println!("进程完成，状态: {:?}", status);

    Ok(())
}
```

## 3. 进程属性与资源控制

### 3.1 基础属性配置

- **属性配置**：环境变量、工作目录、I/O 重定向、资源限制等

```rust
use std::process::{Command, Stdio};
use std::path::Path;

// 基础属性配置
fn basic_process_configuration() -> Result<(), Box<dyn std::error::Error>> {
    let mut command = Command::new("program");

    // I/O 重定向
    command
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::inherit());

    // 环境变量管理
    command
        .env_clear()
        .env("PATH", "/usr/bin")
        .env("RUST_LOG", "debug");

    // 工作目录设置
    command.current_dir(Path::new("/tmp"));

    let child = command.spawn()?;
    let status = child.wait()?;

    println!("进程完成，状态: {:?}", status);
    Ok(())
}

// Rust 1.92.0 增强的环境变量处理
fn enhanced_env_handling() -> Result<(), Box<dyn std::error::Error>> {
    let mut command = Command::new("env");

    // 使用 HashMap 批量设置环境变量
    let mut env_vars = std::collections::HashMap::new();
    env_vars.insert("RUST_LOG".to_string(), "info".to_string());
    env_vars.insert("RUST_BACKTRACE".to_string(), "1".to_string());
    env_vars.insert("MY_APP_CONFIG".to_string(), "/etc/myapp.conf".to_string());

    for (key, value) in env_vars {
        command.env(key, value);
    }

    let output = command.output()?;
    println!("环境变量输出: {}", String::from_utf8_lossy(&output.stdout));

    Ok(())
}
```

### 3.2 高级资源限制

- **资源限制**：可通过平台 API（如 Linux 的 `setrlimit`）设置内存、文件数等限制

```rust
use std::process::{Command, Stdio};
use std::os::unix::process::CommandExt;

// Unix 平台资源限制
#[cfg(unix)]
fn set_process_limits() -> Result<(), Box<dyn std::error::Error>> {
    use nix::sys::resource::{setrlimit, Resource, ResourceLimits};

    // 设置内存限制 (100MB soft, 200MB hard)
    setrlimit(
        Resource::RLIMIT_AS,
        ResourceLimits::new(1024 * 1024 * 100, 1024 * 1024 * 200)
    )?;

    // 设置文件描述符限制
    setrlimit(
        Resource::RLIMIT_NOFILE,
        ResourceLimits::new(1024, 2048)
    )?;

    // 设置 CPU 时间限制
    setrlimit(
        Resource::RLIMIT_CPU,
        ResourceLimits::new(300, 600) // 5分钟 soft, 10分钟 hard
    )?;

    Ok(())
}

// 跨平台资源管理
fn cross_platform_resource_management() -> Result<(), Box<dyn std::error::Error>> {
    let mut command = Command::new("resource_intensive_program");

    // 设置基础属性
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    // 平台特定的资源限制
    #[cfg(unix)]
    {
        command.before_exec(|| {
            set_process_limits()?;
            Ok(())
        });
    }

    #[cfg(windows)]
    {
        // Windows 特定的资源限制
        // 使用 Windows API 设置进程限制
    }

    let child = command.spawn()?;
    let output = child.wait_with_output()?;

    println!("进程完成，状态: {:?}", output.status);
    Ok(())
}
```

### 3.3 跨平台资源管理

- **继承与隔离**：子进程默认继承父进程资源限制，可显式修改。

```rust
use std::process::{Command, Stdio};
use std::time::Duration;
use tokio::time::timeout;

// 跨平台资源管理器
pub struct CrossPlatformResourceManager {
    max_memory_mb: u64,
    max_cpu_time: Duration,
    max_file_descriptors: u32,
}

impl CrossPlatformResourceManager {
    pub fn new(max_memory_mb: u64, max_cpu_time: Duration, max_file_descriptors: u32) -> Self {
        Self {
            max_memory_mb,
            max_cpu_time,
            max_file_descriptors,
        }
    }

    pub async fn execute_with_limits(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<std::process::Output, Box<dyn std::error::Error>> {
        let mut cmd = Command::new(command);
        cmd.args(args);

        // 设置基础 I/O
        cmd.stdin(Stdio::null())
           .stdout(Stdio::piped())
           .stderr(Stdio::piped());

        // 平台特定的资源限制
        #[cfg(unix)]
        {
            cmd.before_exec(move || {
                self.set_unix_limits()?;
                Ok(())
            });
        }

        #[cfg(windows)]
        {
            // Windows 资源限制设置
            self.set_windows_limits(&mut cmd)?;
        }

        // 异步执行带超时
        let child = cmd.spawn()?;
        let result = timeout(self.max_cpu_time, child.wait_with_output()).await;

        match result {
            Ok(output) => Ok(output?),
            Err(_) => {
                // 超时处理
                Err("进程执行超时".into())
            }
        }
    }

    #[cfg(unix)]
    fn set_unix_limits(&self) -> Result<(), Box<dyn std::error::Error>> {
        use nix::sys::resource::{setrlimit, Resource, ResourceLimits};

        // 设置内存限制
        setrlimit(
            Resource::RLIMIT_AS,
            ResourceLimits::new(
                self.max_memory_mb * 1024 * 1024,
                self.max_memory_mb * 1024 * 1024 * 2
            )
        )?;

        // 设置文件描述符限制
        setrlimit(
            Resource::RLIMIT_NOFILE,
            ResourceLimits::new(
                self.max_file_descriptors,
                self.max_file_descriptors * 2
            )
        )?;

        // 设置 CPU 时间限制
        setrlimit(
            Resource::RLIMIT_CPU,
            ResourceLimits::new(
                self.max_cpu_time.as_secs() as u64,
                self.max_cpu_time.as_secs() as u64 * 2
            )
        )?;

        Ok(())
    }

    #[cfg(windows)]
    fn set_windows_limits(&self, _cmd: &mut Command) -> Result<(), Box<dyn std::error::Error>> {
        // Windows 特定的资源限制实现
        // 使用 Windows API 设置进程限制
        Ok(())
    }
}

// 使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let resource_manager = CrossPlatformResourceManager::new(
        100,                    // 100MB 内存限制
        Duration::from_secs(30), // 30秒 CPU 时间限制
        1024,                   // 1024 个文件描述符限制
    );

    let output = resource_manager
        .execute_with_limits("echo", &["Hello, World!".to_string()])
        .await?;

    println!("输出: {}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}
```

## 4. Rust 的进程安全抽象

### 4.1 类型安全保证

- **Drop 语义**：Rust 保证进程相关资源在作用域结束时自动释放，防止资源泄漏。
- **错误处理**：所有进程操作均返回 `Result`，强制开发者处理失败分支。
- **平台兼容性**：`std::process` 屏蔽平台差异，提供统一 API。

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader, Write};

// 类型安全的进程管理
fn type_safe_process_management() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("safe_program")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 类型安全的 I/O 操作
    if let Some(stdin) = child.stdin.take() {
        let mut writer = std::io::BufWriter::new(stdin);
        writer.write_all(b"Type-safe input\n")?;
        writer.flush()?;
        // 自动释放
    }

    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            let line = line?;
            println!("安全输出: {}", line);
        }
        // 自动释放
    }

    let status = child.wait()?;
    println!("进程安全完成: {:?}", status);

    Ok(())
}
```

### 4.2 错误处理机制

```rust
use std::process::{Command, Stdio};
use std::error::Error;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ProcessError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(std::io::Error),

    #[error("进程等待失败: {0}")]
    WaitFailed(std::io::Error),

    #[error("进程输出失败: {0}")]
    OutputFailed(std::io::Error),

    #[error("进程终止失败: {0}")]
    KillFailed(std::io::Error),

    #[error("进程执行超时")]
    Timeout,

    #[error("进程异常退出，退出码: {0}")]
    AbnormalExit(i32),
}

// 增强的错误处理
async fn enhanced_error_handling() -> Result<String, ProcessError> {
    let mut child = Command::new("risky_program")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(ProcessError::SpawnFailed)?;

    let output = child.wait_with_output().await
        .map_err(ProcessError::OutputFailed)?;

    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        let exit_code = output.status.code().unwrap_or(-1);
        Err(ProcessError::AbnormalExit(exit_code))
    }
}
```

### 4.3 平台兼容性

```rust
use std::process::{Command, Stdio};

// 跨平台进程管理
fn cross_platform_process_management() -> Result<(), Box<dyn std::error::Error>> {
    let mut command = Command::new("cross_platform_command");

    // 基础配置
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    // 平台特定的配置
    #[cfg(unix)]
    {
        command.env("SHELL", "/bin/bash");
    }

    #[cfg(windows)]
    {
        command.env("COMSPEC", "cmd.exe");
    }

    #[cfg(target_os = "macos")]
    {
        command.env("PATH", "/usr/local/bin:/usr/bin:/bin");
    }

    let child = command.spawn()?;
    let output = child.wait_with_output()?;

    println!("跨平台输出: {}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}
```

## 5. 现代库集成

### 5.1 Tokio 异步进程

```rust
use tokio::process::Command as AsyncCommand;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use std::time::Duration;

// Tokio 异步进程管理
async fn tokio_async_process() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = AsyncCommand::new("async_program")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()?;

    // 异步写入
    if let Some(stdin) = child.stdin.take() {
        let mut async_stdin = tokio::io::BufWriter::new(stdin);
        async_stdin.write_all(b"Async input\n").await?;
        async_stdin.flush().await?;
    }

    // 异步读取
    if let Some(stdout) = child.stdout.take() {
        let mut async_stdout = tokio::io::BufReader::new(stdout);
        let mut line = String::new();
        async_stdout.read_line(&mut line).await?;
        println!("异步输出: {}", line);
    }

    let status = child.wait().await?;
    println!("异步进程完成: {:?}", status);

    Ok(())
}
```

### 5.2 Async-Std 进程管理

```rust
use async_std::process::{Command as AsyncStdCommand, Stdio};
use async_std::io::{BufReader, BufWriter};

// Async-Std 进程管理
async fn async_std_process() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = AsyncStdCommand::new("async_std_program")
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
```

### 5.3 Duct 进程组合

```rust
use duct::cmd;

// Duct 进程组合
fn duct_process_composition() -> Result<(), Box<dyn std::error::Error>> {
    // 简单的进程组合
    let output = cmd!("echo", "Hello, World!")
        .pipe(cmd!("wc", "-c"))
        .read()?;

    println!("Duct 输出: {}", output);

    // 复杂的进程管道
    let complex_output = cmd!("find", ".", "-name", "*.rs")
        .pipe(cmd!("head", "-10"))
        .pipe(cmd!("wc", "-l"))
        .read()?;

    println!("复杂管道输出: {}", complex_output);

    // 环境变量和重定向
    let env_output = cmd!("env")
        .env("MY_VAR", "duct_value")
        .stdout_path("/tmp/duct_output.txt")
        .run()?;

    println!("环境变量进程状态: {:?}", env_output.status);

    Ok(())
}
```

## 6. 最佳实践

### 6.1 资源管理最佳实践

```rust
use std::process::{Command, Stdio};
use std::time::Duration;
use tokio::time::timeout;

// 资源管理最佳实践
async fn resource_management_best_practices() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 总是设置超时
    let timeout_duration = Duration::from_secs(30);

    // 2. 使用 RAII 模式
    let child = Command::new("long_running_program")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 3. 异步等待带超时
    let result = timeout(timeout_duration, child.wait_with_output()).await;

    match result {
        Ok(output) => {
            println!("进程正常完成: {:?}", output.status);
            println!("输出: {}", String::from_utf8_lossy(&output.stdout));
        }
        Err(_) => {
            println!("进程超时，正在清理资源...");
            // 资源会自动清理
        }
    }

    Ok(())
}
```

### 6.2 错误处理最佳实践

```rust
use std::process::{Command, Stdio};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum BestPracticeError {
    #[error("进程执行失败: {0}")]
    ProcessFailed(String),

    #[error("资源不足: {0}")]
    ResourceExhausted(String),

    #[error("权限不足: {0}")]
    PermissionDenied(String),
}

// 错误处理最佳实践
fn error_handling_best_practices() -> Result<(), BestPracticeError> {
    let output = Command::new("privileged_command")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
        .map_err(|e| BestPracticeError::ProcessFailed(e.to_string()))?;

    if !output.status.success() {
        let error_msg = String::from_utf8_lossy(&output.stderr);

        // 根据错误类型进行分类处理
        if error_msg.contains("permission") {
            return Err(BestPracticeError::PermissionDenied(error_msg.to_string()));
        } else if error_msg.contains("resource") {
            return Err(BestPracticeError::ResourceExhausted(error_msg.to_string()));
        } else {
            return Err(BestPracticeError::ProcessFailed(error_msg.to_string()));
        }
    }

    println!("命令执行成功: {}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}
```

## 7. 小结

Rust 1.92.0 进程模型以类型系统和所有权为基础，结合操作系统原语，提供了安全、可移植、易用的进程管理能力。生命周期管理、资源控制和错误处理机制共同确保了系统级编程的健壮性和安全性。

### 关键特性总结

1. **内存安全**：所有权模型确保进程间内存隔离
2. **资源管理**：自动资源释放，防止泄漏
3. **错误处理**：强制错误处理，提高健壮性
4. **跨平台兼容**：统一的 API 接口
5. **异步支持**：与 Tokio、Async-Std 等现代库集成
6. **性能优化**：零拷贝、内存池等优化策略

### 现代库生态

- **Tokio**：高性能异步运行时
- **Async-Std**：异步标准库
- **Duct**：进程组合库
- **Nix**：系统调用封装
- **Thiserror**：错误处理宏

通过这些特性现代库的集成，Rust 1.92.0 为进程管理提供了强大而安全的工具集。
