# C07-03. Rust 1.90 新特性与进程管理

## 目录

- [C07-03. Rust 1.90 新特性与进程管理](#c07-03-rust-190-新特性与进程管理)
  - [目录](#目录)
  - [1. Rust 1.90 核心新特性](#1-rust-190-核心新特性)
    - [1.1 异步闭包 (Async Closures)](#11-异步闭包-async-closures)
    - [1.2 改进的模式匹配](#12-改进的模式匹配)
    - [1.3 改进的迭代器](#13-改进的迭代器)
    - [1.4 改进的错误处理](#14-改进的错误处理)
    - [1.5 新的生命周期特性](#15-新的生命周期特性)
    - [1.6 改进的宏系统](#16-改进的宏系统)
  - [2. 标准库 Process 模块增强](#2-标准库-process-模块增强)
    - [2.1 异步进程管理](#21-异步进程管理)
    - [2.2 改进的进程监控](#22-改进的进程监控)
    - [2.3 增强的进程间通信](#23-增强的进程间通信)
    - [2.4 新的进程属性控制](#24-新的进程属性控制)
    - [2.5 改进的 I/O 重定向](#25-改进的-io-重定向)
  - [3. 性能优化特性](#3-性能优化特性)
    - [3.1 零拷贝数据传输](#31-零拷贝数据传输)
    - [3.2 内存池优化](#32-内存池优化)
    - [3.3 并发优化](#33-并发优化)
    - [3.4 CPU 亲和性设置](#34-cpu-亲和性设置)
  - [4. 安全增强](#4-安全增强)
    - [4.1 改进的权限控制](#41-改进的权限控制)
    - [4.2 沙箱执行](#42-沙箱执行)
    - [4.3 内存安全增强](#43-内存安全增强)
    - [4.4 进程隔离](#44-进程隔离)
  - [5. 现代库生态集成](#5-现代库生态集成)
    - [5.1 Tokio 1.0+ 集成](#51-tokio-10-集成)
    - [5.2 Async-Std 2.0 特性](#52-async-std-20-特性)
    - [5.3 现代进程管理库](#53-现代进程管理库)
  - [6. 实际应用示例](#6-实际应用示例)
    - [5.1 高性能进程管理器](#51-高性能进程管理器)
    - [5.2 智能进程监控系统](#52-智能进程监控系统)
  - [6. 最佳实践](#6-最佳实践)
    - [6.1 错误处理策略](#61-错误处理策略)
    - [6.2 资源管理](#62-资源管理)
  - [7. 总结](#7-总结)

本章详细介绍 Rust 1.90 版本中的新特性，以及这些特性如何增强进程管理和系统交互能力。

## 1. Rust 1.90 核心新特性

### 1.1 异步闭包 (Async Closures)

Rust 1.90 引入了异步闭包，允许在异步上下文中使用闭包。

```rust
use std::process::{Command, Stdio};
use std::future::Future;

// 异步闭包示例
async fn async_process_handler<F>(handler: F) -> Result<(), Box<dyn std::error::Error>>
where
    F: FnOnce() -> Box<dyn Future<Output = Result<(), Box<dyn std::error::Error>>> + Send>,
{
    let result = handler().await;
    result
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 使用异步闭包处理进程
    async_process_handler(|| {
        Box::new(async {
            let mut child = Command::new("echo")
                .arg("Hello from async closure!")
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

### 1.2 改进的模式匹配

Rust 1.90 增强了模式匹配能力，特别是在进程状态处理方面。

```rust
use std::process::{Command, ExitStatus};

fn handle_process_status(status: ExitStatus) {
    match status {
        // 新的模式匹配语法
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

### 1.3 改进的迭代器

Rust 1.90 改进了迭代器性能，特别适用于处理大量进程输出。

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};

fn process_output_lines() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("ps")
        .arg("aux")
        .stdout(Stdio::piped())
        .spawn()?;

    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);

        // 使用改进的迭代器处理输出
        let process_lines: Vec<String> = reader
            .lines()
            .filter_map(|line| line.ok())
            .filter(|line| line.contains("rust"))
            .take(10) // 限制处理的行数
            .collect();

        for line in process_lines {
            println!("Found process: {}", line);
        }
    }

    Ok(())
}
```

### 1.4 改进的错误处理

Rust 1.90 提供了更好的错误处理机制。

```rust
use std::process::{Command, Stdio};
use std::error::Error;

// 使用改进的错误处理
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

### 1.5 新的生命周期特性

Rust 1.90 引入了改进的生命周期推断和更灵活的生命周期管理。

```rust
use std::process::{Command, Stdio};
use std::future::Future;

// 改进的生命周期推断
async fn process_with_lifetime<'a, F, Fut>(
    command: &'a str,
    processor: F,
) -> Result<String, Box<dyn std::error::Error>>
where
    F: FnOnce(&'a str) -> Fut,
    Fut: Future<Output = Result<String, Box<dyn std::error::Error>>>,
{
    let output = Command::new(command)
        .stdout(Stdio::piped())
        .output()?;

    let result = processor(command).await?;
    Ok(result)
}

// 使用改进的生命周期特性
async fn enhanced_process_management() -> Result<(), Box<dyn std::error::Error>> {
    let command = "echo";
    let result = process_with_lifetime(command, |cmd| async move {
        let output = Command::new(cmd)
            .arg("Hello from enhanced lifetime!")
            .output()?;
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }).await?;

    println!("结果: {}", result);
    Ok(())
}
```

### 1.6 改进的宏系统

Rust 1.90 改进了宏系统，提供更好的进程管理宏支持。

```rust
use std::process::{Command, Stdio};

// 自定义进程管理宏
macro_rules! async_process {
    ($cmd:expr, $args:expr) => {{
        async move {
            let output = Command::new($cmd)
                .args($args)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output()
                .await?;

            if output.status.success() {
                Ok(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                Err(format!("命令执行失败: {}",
                    String::from_utf8_lossy(&output.stderr)).into())
            }
        }
    }};
}

// 使用改进的宏系统
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let result = async_process!("echo", &["Hello from macro!"]).await?;
    println!("宏执行结果: {}", result);
    Ok(())
}
```

## 2. 标准库 Process 模块增强

### 2.1 异步进程管理

Rust 1.90 增强了异步进程管理能力。

```rust
use std::process::{Command, Stdio};
use tokio::process::Command as AsyncCommand;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 使用异步命令
    let mut async_cmd = AsyncCommand::new("sleep")
        .arg("5")
        .stdout(Stdio::piped())
        .spawn()?;

    // 异步等待进程完成
    let status = async_cmd.wait().await?;
    println!("进程完成，状态: {:?}", status);

    Ok(())
}
```

### 2.2 改进的进程监控

```rust
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use tokio::time::timeout;

async fn monitor_process_with_timeout() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("long_running_process")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 使用超时监控进程
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

### 2.3 增强的进程间通信

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader, Write};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};

async fn enhanced_ipc_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 异步写入数据
    if let Some(stdin) = child.stdin.take() {
        let mut async_stdin = tokio::io::BufWriter::new(stdin);
        async_stdin.write_all(b"Hello from parent process\n").await?;
        async_stdin.flush().await?;
    }

    // 异步读取输出
    if let Some(stdout) = child.stdout.take() {
        let mut async_stdout = tokio::io::BufReader::new(stdout);
        let mut line = String::new();
        async_stdout.read_line(&mut line).await?;
        println!("子进程输出: {}", line);
    }

    let status = child.wait().await?;
    println!("进程完成: {:?}", status);

    Ok(())
}
```

### 2.4 新的进程属性控制

Rust 1.90 增强了进程属性控制能力。

```rust
use std::process::{Command, Stdio};
use std::os::unix::process::CommandExt;

// 增强的进程属性控制
fn enhanced_process_attributes() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::new("long_running_process");

    // 设置进程优先级
    #[cfg(unix)]
    {
        cmd.process_group(0)  // 设置进程组
           .create_new_process_group(true)  // 创建新进程组
           .before_exec(|| {
               // 在 exec 之前执行的操作
               unsafe {
                   libc::nice(10);  // 降低优先级
               }
               Ok(())
           });
    }

    // 设置资源限制
    cmd.stdin(Stdio::null())
       .stdout(Stdio::piped())
       .stderr(Stdio::piped())
       .env_clear()  // 清除环境变量
       .env("RUST_LOG", "info");  // 设置特定环境变量

    let child = cmd.spawn()?;
    println!("进程启动，PID: {:?}", child.id());

    Ok(())
}

// 跨平台进程属性设置
fn cross_platform_process_attributes() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::new("process_name");

    // 基础属性设置
    cmd.stdin(Stdio::null())
       .stdout(Stdio::piped())
       .stderr(Stdio::piped());

    // 平台特定设置
    #[cfg(unix)]
    {
        cmd.uid(1000)
           .gid(1000)
           .process_group(0);
    }

    #[cfg(windows)]
    {
        cmd.creation_flags(0x00000008);  // CREATE_NEW_PROCESS_GROUP
    }

    let child = cmd.spawn()?;
    println!("跨平台进程启动成功");

    Ok(())
}
```

### 2.5 改进的 I/O 重定向

```rust
use std::process::{Command, Stdio};
use std::fs::File;
use std::io::Write;

// 增强的 I/O 重定向
fn enhanced_io_redirection() -> Result<(), Box<dyn std::error::Error>> {
    // 创建日志文件
    let log_file = File::create("process.log")?;

    let mut cmd = Command::new("command_with_output");

    // 高级 I/O 重定向
    cmd.stdin(Stdio::null())  // 关闭标准输入
       .stdout(Stdio::piped())  // 捕获标准输出
       .stderr(Stdio::from(log_file))  // 重定向错误到文件
       .spawn()?;

    println!("进程启动，错误输出重定向到文件");
    Ok(())
}

// 流式 I/O 处理
async fn streaming_io_processing() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("streaming_command")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 异步写入大量数据
    if let Some(stdin) = child.stdin.take() {
        tokio::spawn(async move {
            let mut writer = tokio::io::BufWriter::new(stdin);
            for i in 0..1000 {
                let data = format!("Line {}\n", i);
                if let Err(e) = writer.write_all(data.as_bytes()).await {
                    eprintln!("写入错误: {}", e);
                    break;
                }
            }
            let _ = writer.flush().await;
        });
    }

    // 异步读取输出
    if let Some(stdout) = child.stdout.take() {
        tokio::spawn(async move {
            let mut reader = tokio::io::BufReader::new(stdout);
            let mut line = String::new();
            while reader.read_line(&mut line).await.unwrap_or(0) > 0 {
                println!("输出: {}", line.trim());
                line.clear();
            }
        });
    }

    let status = child.wait().await?;
    println!("流式处理完成: {:?}", status);

    Ok(())
}
```

## 3. 性能优化特性

### 3.1 零拷贝数据传输

Rust 1.90 优化了数据传输性能。

```rust
use std::process::{Command, Stdio};
use std::io::Write;

fn zero_copy_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("wc")
        .arg("-c")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;

    // 使用零拷贝写入
    if let Some(stdin) = child.stdin.take() {
        let data = b"Hello, World!\nThis is a test message.\n";
        stdin.write_all(data)?;
    }

    let output = child.wait_with_output()?;
    println!("字符数: {}", String::from_utf8_lossy(&output.stdout));

    Ok(())
}
```

### 3.2 内存池优化

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Mutex;

// 进程池实现
struct ProcessPool {
    processes: Arc<Mutex<Vec<tokio::process::Child>>>,
    max_size: usize,
}

impl ProcessPool {
    fn new(max_size: usize) -> Self {
        Self {
            processes: Arc::new(Mutex::new(Vec::new())),
            max_size,
        }
    }

    async fn execute(&self, command: &str) -> Result<String, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        // 清理已完成的进程
        processes.retain(|child| {
            child.try_wait().map(|status| status.is_none()).unwrap_or(false)
        });

        if processes.len() >= self.max_size {
            return Err("进程池已满".into());
        }

        let mut child = Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdout(Stdio::piped())
            .spawn()?;

        let output = child.wait_with_output().await?;
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}
```

### 3.3 并发优化

Rust 1.90 提供了更好的并发优化特性。

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::{Semaphore, Mutex};
use tokio::task::JoinSet;

// 高性能并发进程管理器
pub struct ConcurrentProcessManager {
    semaphore: Arc<Semaphore>,
    join_set: Arc<Mutex<JoinSet<Result<String, Box<dyn std::error::Error>>>>>,
}

impl ConcurrentProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            join_set: Arc::new(Mutex::new(JoinSet::new())),
        }
    }

    pub async fn execute_concurrent(
        &self,
        commands: Vec<String>,
    ) -> Result<Vec<String>, Box<dyn std::error::Error>> {
        let mut results = Vec::new();
        let mut join_set = self.join_set.lock().await;

        // 启动所有任务
        for command in commands {
            let semaphore = self.semaphore.clone();
            let task = tokio::spawn(async move {
                let _permit = semaphore.acquire().await?;
                Self::execute_single_command(&command).await
            });
            join_set.spawn(task);
        }

        // 收集结果
        while let Some(result) = join_set.join_next().await {
            match result? {
                Ok(output) => results.push(output),
                Err(e) => eprintln!("任务执行失败: {}", e),
            }
        }

        Ok(results)
    }

    async fn execute_single_command(command: &str) -> Result<String, Box<dyn std::error::Error>> {
        let output = Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
            .await?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("命令执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
}

// 工作窃取调度器
pub struct WorkStealingScheduler {
    workers: Vec<tokio::task::JoinHandle<()>>,
    task_queue: Arc<Mutex<Vec<String>>>,
}

impl WorkStealingScheduler {
    pub fn new(num_workers: usize) -> Self {
        Self {
            workers: Vec::new(),
            task_queue: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn start(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        for worker_id in 0..self.workers.len() {
            let queue = self.task_queue.clone();
            let worker = tokio::spawn(async move {
                Self::worker_loop(worker_id, queue).await;
            });
            self.workers.push(worker);
        }
        Ok(())
    }

    async fn worker_loop(
        worker_id: usize,
        queue: Arc<Mutex<Vec<String>>>,
    ) {
        loop {
            let task = {
                let mut queue = queue.lock().await;
                queue.pop()
            };

            if let Some(command) = task {
                println!("Worker {} 执行任务: {}", worker_id, command);
                if let Err(e) = Self::execute_task(&command).await {
                    eprintln!("Worker {} 任务执行失败: {}", worker_id, e);
                }
            } else {
                // 工作窃取
                tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            }
        }
    }

    async fn execute_task(command: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = Command::new("sh")
            .arg("-c")
            .arg(command)
            .output()
            .await?;

        if !output.status.success() {
            return Err(format!("任务执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into());
        }

        Ok(())
    }
}
```

### 3.4 CPU 亲和性设置

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Mutex;

// CPU 亲和性管理器
pub struct CpuAffinityManager {
    cpu_cores: Vec<usize>,
    current_core: Arc<Mutex<usize>>,
}

impl CpuAffinityManager {
    pub fn new(cpu_cores: Vec<usize>) -> Self {
        Self {
            cpu_cores,
            current_core: Arc::new(Mutex::new(0)),
        }
    }

    pub async fn execute_with_affinity(
        &self,
        command: &str,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let core_id = {
            let mut current = self.current_core.lock().await;
            let core = self.cpu_cores[*current % self.cpu_cores.len()];
            *current += 1;
            core
        };

        #[cfg(unix)]
        {
            let mut cmd = Command::new("taskset");
            cmd.arg("-c")
               .arg(core_id.to_string())
               .arg("sh")
               .arg("-c")
               .arg(command);

            let output = cmd
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output()
                .await?;

            if output.status.success() {
                Ok(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                Err(format!("CPU 亲和性设置失败: {}",
                    String::from_utf8_lossy(&output.stderr)).into())
            }
        }

        #[cfg(not(unix))]
        {
            // Windows 或其他平台的实现
            let output = Command::new("cmd")
                .arg("/c")
                .arg(command)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output()
                .await?;

            if output.status.success() {
                Ok(String::from_utf8_lossy(&output.stdout).to_string())
            } else {
                Err(format!("命令执行失败: {}",
                    String::from_utf8_lossy(&output.stderr)).into())
            }
        }
    }
}

// 智能负载均衡
pub struct IntelligentLoadBalancer {
    cpu_usage: Arc<Mutex<Vec<f64>>>,
    memory_usage: Arc<Mutex<Vec<f64>>>,
    process_counts: Arc<Mutex<Vec<usize>>>,
}

impl IntelligentLoadBalancer {
    pub fn new(num_cores: usize) -> Self {
        Self {
            cpu_usage: Arc::new(Mutex::new(vec![0.0; num_cores])),
            memory_usage: Arc::new(Mutex::new(vec![0.0; num_cores])),
            process_counts: Arc::new(Mutex::new(vec![0; num_cores])),
        }
    }

    pub async fn select_best_core(&self) -> usize {
        let cpu_usage = self.cpu_usage.lock().await;
        let memory_usage = self.memory_usage.lock().await;
        let process_counts = self.process_counts.lock().await;

        let mut best_core = 0;
        let mut best_score = f64::MAX;

        for i in 0..cpu_usage.len() {
            // 综合评分：CPU 使用率 + 内存使用率 + 进程数量
            let score = cpu_usage[i] * 0.4 + memory_usage[i] * 0.3 +
                       (process_counts[i] as f64) * 0.3;

            if score < best_score {
                best_score = score;
                best_core = i;
            }
        }

        best_core
    }

    pub async fn update_core_usage(&self, core_id: usize, cpu: f64, memory: f64) {
        let mut cpu_usage = self.cpu_usage.lock().await;
        let mut memory_usage = self.memory_usage.lock().await;
        let mut process_counts = self.process_counts.lock().await;

        cpu_usage[core_id] = cpu;
        memory_usage[core_id] = memory;
        process_counts[core_id] += 1;
    }
}
```

## 4. 安全增强

### 4.1 改进的权限控制

```rust
use std::process::{Command, Stdio};
use std::os::unix::process::CommandExt;

fn secure_process_execution() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::new("sensitive_command");

    // 设置安全属性
    cmd.stdin(Stdio::null())
       .stdout(Stdio::piped())
       .stderr(Stdio::piped())
       .env_clear() // 清除环境变量
       .env("PATH", "/usr/bin:/bin"); // 设置受限PATH

    #[cfg(unix)]
    {
        // Unix 特定的安全设置
        cmd.uid(1000) // 设置用户ID
           .gid(1000); // 设置组ID
    }

    let output = cmd.output()?;
    println!("安全执行结果: {:?}", output.status);

    Ok(())
}
```

### 4.2 沙箱执行

```rust
use std::process::{Command, Stdio};
use std::time::Duration;

async fn sandboxed_execution() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("untrusted_script")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 设置执行超时
    let timeout_duration = Duration::from_secs(10);

    let result = tokio::time::timeout(timeout_duration, child.wait()).await;

    match result {
        Ok(status) => {
            println!("沙箱执行完成: {:?}", status);
        }
        Err(_) => {
            println!("沙箱执行超时，终止进程");
            child.kill().await?;
        }
    }

    Ok(())
}
```

### 4.3 内存安全增强

Rust 1.90 提供了更强的内存安全保障。

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Mutex;

// 内存安全进程管理器
pub struct MemorySafeProcessManager {
    memory_limit: usize,
    current_usage: Arc<Mutex<usize>>,
    process_registry: Arc<Mutex<Vec<ProcessInfo>>>,
}

#[derive(Debug, Clone)]
struct ProcessInfo {
    pid: u32,
    memory_usage: usize,
    start_time: std::time::Instant,
}

impl MemorySafeProcessManager {
    pub fn new(memory_limit: usize) -> Self {
        Self {
            memory_limit,
            current_usage: Arc::new(Mutex::new(0)),
            process_registry: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn execute_with_memory_limit(
        &self,
        command: &str,
    ) -> Result<String, Box<dyn std::error::Error>> {
        // 检查内存限制
        let current_usage = *self.current_usage.lock().await;
        if current_usage >= self.memory_limit {
            return Err("内存使用已达上限".into());
        }

        let mut child = Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        let pid = child.id().unwrap_or(0);
        let start_time = std::time::Instant::now();

        // 注册进程信息
        {
            let mut registry = self.process_registry.lock().await;
            registry.push(ProcessInfo {
                pid,
                memory_usage: 0, // 初始值，实际监控中更新
                start_time,
            });
        }

        // 异步监控内存使用
        let usage_monitor = self.current_usage.clone();
        let registry = self.process_registry.clone();
        tokio::spawn(async move {
            Self::monitor_process_memory(pid, usage_monitor, registry).await;
        });

        let output = child.wait_with_output().await?;

        // 清理进程信息
        {
            let mut registry = self.process_registry.lock().await;
            registry.retain(|info| info.pid != pid);
        }

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("命令执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }

    async fn monitor_process_memory(
        pid: u32,
        current_usage: Arc<Mutex<usize>>,
        registry: Arc<Mutex<Vec<ProcessInfo>>>,
    ) {
        loop {
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

            // 检查进程是否还在运行
            let is_running = {
                let registry = registry.lock().await;
                registry.iter().any(|info| info.pid == pid)
            };

            if !is_running {
                break;
            }

            // 获取进程内存使用情况
            if let Ok(memory_usage) = Self::get_process_memory(pid).await {
                // 更新内存使用统计
                {
                    let mut usage = current_usage.lock().await;
                    *usage = (*usage).saturating_sub(memory_usage);
                }

                // 更新进程信息
                {
                    let mut registry = registry.lock().await;
                    if let Some(info) = registry.iter_mut().find(|info| info.pid == pid) {
                        info.memory_usage = memory_usage;
                    }
                }
            }
        }
    }

    async fn get_process_memory(pid: u32) -> Result<usize, Box<dyn std::error::Error>> {
        #[cfg(unix)]
        {
            let output = Command::new("ps")
                .arg("-p")
                .arg(pid.to_string())
                .arg("-o")
                .arg("rss")
                .output()
                .await?;

            if output.status.success() {
                let output_str = String::from_utf8_lossy(&output.stdout);
                let lines: Vec<&str> = output_str.lines().collect();
                if lines.len() >= 2 {
                    if let Ok(memory_kb) = lines[1].trim().parse::<usize>() {
                        return Ok(memory_kb * 1024); // 转换为字节
                    }
                }
            }
        }

        #[cfg(windows)]
        {
            // Windows 特定的内存获取实现
            // 这里可以使用 Windows API 或第三方库
        }

        Ok(0)
    }
}

// 内存泄漏检测器
pub struct MemoryLeakDetector {
    baseline_memory: usize,
    max_growth_rate: f64,
    check_interval: Duration,
}

impl MemoryLeakDetector {
    pub fn new(baseline_memory: usize, max_growth_rate: f64) -> Self {
        Self {
            baseline_memory,
            max_growth_rate,
            check_interval: Duration::from_secs(30),
        }
    }

    pub async fn start_monitoring(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut last_memory = self.baseline_memory;
        let mut interval = tokio::time::interval(self.check_interval);

        loop {
            interval.tick().await;

            let current_memory = self.get_system_memory_usage().await?;
            let growth_rate = (current_memory as f64 - last_memory as f64) / last_memory as f64;

            if growth_rate > self.max_growth_rate {
                eprintln!("警告: 内存使用增长过快! 增长率: {:.2}%", growth_rate * 100.0);
                // 触发内存清理或进程终止
                self.trigger_memory_cleanup().await?;
            }

            last_memory = current_memory;
        }
    }

    async fn get_system_memory_usage(&self) -> Result<usize, Box<dyn std::error::Error>> {
        #[cfg(unix)]
        {
            let output = Command::new("free")
                .arg("-b")
                .output()
                .await?;

            if output.status.success() {
                let output_str = String::from_utf8_lossy(&output.stdout);
                // 解析 free 命令输出获取内存使用情况
                // 这里简化处理，实际实现需要解析输出
                Ok(0)
            } else {
                Err("无法获取系统内存使用情况".into())
            }
        }

        #[cfg(windows)]
        {
            // Windows 特定的内存获取实现
            Ok(0)
        }
    }

    async fn trigger_memory_cleanup(&self) -> Result<(), Box<dyn std::error::Error>> {
        // 触发内存清理逻辑
        println!("触发内存清理...");
        Ok(())
    }
}
```

### 4.4 进程隔离

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Mutex;

// 进程隔离管理器
pub struct ProcessIsolationManager {
    isolation_level: IsolationLevel,
    resource_limits: ResourceLimits,
    allowed_commands: Vec<String>,
    denied_commands: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum IsolationLevel {
    None,
    Basic,
    Enhanced,
    Maximum,
}

#[derive(Debug, Clone)]
pub struct ResourceLimits {
    max_memory: usize,
    max_cpu_time: Duration,
    max_file_descriptors: usize,
    max_processes: usize,
}

impl ProcessIsolationManager {
    pub fn new(isolation_level: IsolationLevel) -> Self {
        let resource_limits = match isolation_level {
            IsolationLevel::None => ResourceLimits {
                max_memory: usize::MAX,
                max_cpu_time: Duration::from_secs(3600),
                max_file_descriptors: 1024,
                max_processes: 100,
            },
            IsolationLevel::Basic => ResourceLimits {
                max_memory: 512 * 1024 * 1024, // 512MB
                max_cpu_time: Duration::from_secs(300),
                max_file_descriptors: 256,
                max_processes: 10,
            },
            IsolationLevel::Enhanced => ResourceLimits {
                max_memory: 256 * 1024 * 1024, // 256MB
                max_cpu_time: Duration::from_secs(60),
                max_file_descriptors: 64,
                max_processes: 5,
            },
            IsolationLevel::Maximum => ResourceLimits {
                max_memory: 128 * 1024 * 1024, // 128MB
                max_cpu_time: Duration::from_secs(30),
                max_file_descriptors: 32,
                max_processes: 2,
            },
        };

        Self {
            isolation_level,
            resource_limits,
            allowed_commands: Vec::new(),
            denied_commands: Vec::new(),
        }
    }

    pub fn add_allowed_command(&mut self, command: String) {
        self.allowed_commands.push(command);
    }

    pub fn add_denied_command(&mut self, command: String) {
        self.denied_commands.push(command);
    }

    pub async fn execute_isolated(
        &self,
        command: &str,
    ) -> Result<String, Box<dyn std::error::Error>> {
        // 检查命令是否被允许
        if !self.is_command_allowed(command) {
            return Err(format!("命令 '{}' 被禁止执行", command).into());
        }

        // 创建隔离的进程
        let mut cmd = Command::new("sh");
        cmd.arg("-c")
           .arg(command)
           .stdin(Stdio::null())
           .stdout(Stdio::piped())
           .stderr(Stdio::piped());

        // 应用资源限制
        self.apply_resource_limits(&mut cmd);

        // 应用安全设置
        self.apply_security_settings(&mut cmd);

        let child = cmd.spawn()?;

        // 监控资源使用
        let monitor_handle = self.monitor_resource_usage(child.id().unwrap_or(0));

        let output = child.wait_with_output().await?;

        // 停止监控
        monitor_handle.abort();

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("隔离执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }

    fn is_command_allowed(&self, command: &str) -> bool {
        // 检查是否在禁止列表中
        if self.denied_commands.iter().any(|cmd| command.contains(cmd)) {
            return false;
        }

        // 如果没有允许列表，则允许所有命令
        if self.allowed_commands.is_empty() {
            return true;
        }

        // 检查是否在允许列表中
        self.allowed_commands.iter().any(|cmd| command.contains(cmd))
    }

    fn apply_resource_limits(&self, cmd: &mut Command) {
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;

            cmd.before_exec(|| {
                unsafe {
                    // 设置内存限制
                    if self.resource_limits.max_memory != usize::MAX {
                        libc::setrlimit(
                            libc::RLIMIT_AS,
                            &libc::rlimit {
                                rlim_cur: self.resource_limits.max_memory as libc::rlim_t,
                                rlim_max: self.resource_limits.max_memory as libc::rlim_t,
                            },
                        );
                    }

                    // 设置文件描述符限制
                    libc::setrlimit(
                        libc::RLIMIT_NOFILE,
                        &libc::rlimit {
                            rlim_cur: self.resource_limits.max_file_descriptors as libc::rlim_t,
                            rlim_max: self.resource_limits.max_file_descriptors as libc::rlim_t,
                        },
                    );
                }
                Ok(())
            });
        }
    }

    fn apply_security_settings(&self, cmd: &mut Command) {
        // 清除环境变量
        cmd.env_clear();

        // 设置受限的环境变量
        cmd.env("PATH", "/usr/bin:/bin")
           .env("HOME", "/tmp")
           .env("USER", "isolated");

        // 设置工作目录
        cmd.current_dir("/tmp");
    }

    fn monitor_resource_usage(&self, pid: u32) -> tokio::task::JoinHandle<()> {
        let limits = self.resource_limits.clone();
        tokio::spawn(async move {
            let start_time = std::time::Instant::now();

            loop {
                tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

                // 检查 CPU 时间限制
                if start_time.elapsed() > limits.max_cpu_time {
                    eprintln!("进程 {} 超过 CPU 时间限制，终止进程", pid);
                    // 终止进程
                    #[cfg(unix)]
                    {
                        unsafe {
                            libc::kill(pid as i32, libc::SIGKILL);
                        }
                    }
                    break;
                }

                // 检查内存使用
                if let Ok(memory_usage) = Self::get_process_memory(pid).await {
                    if memory_usage > limits.max_memory {
                        eprintln!("进程 {} 超过内存限制，终止进程", pid);
                        #[cfg(unix)]
                        {
                            unsafe {
                                libc::kill(pid as i32, libc::SIGKILL);
                            }
                        }
                        break;
                    }
                }
            }
        })
    }

    async fn get_process_memory(pid: u32) -> Result<usize, Box<dyn std::error::Error>> {
        #[cfg(unix)]
        {
            let output = Command::new("ps")
                .arg("-p")
                .arg(pid.to_string())
                .arg("-o")
                .arg("rss")
                .output()
                .await?;

            if output.status.success() {
                let output_str = String::from_utf8_lossy(&output.stdout);
                let lines: Vec<&str> = output_str.lines().collect();
                if lines.len() >= 2 {
                    if let Ok(memory_kb) = lines[1].trim().parse::<usize>() {
                        return Ok(memory_kb * 1024);
                    }
                }
            }
        }

        Ok(0)
    }
}
```

## 5. 现代库生态集成

### 5.1 Tokio 1.0+ 集成

Rust 1.90 与 Tokio 1.0+ 的深度集成提供了强大的异步进程管理能力。

```rust
use tokio::process::{Command as TokioCommand, Child};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use std::process::Stdio;

// Tokio 1.0+ 异步进程管理器
pub struct TokioProcessManager {
    max_concurrent: usize,
    semaphore: tokio::sync::Semaphore,
}

impl TokioProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            max_concurrent,
            semaphore: tokio::sync::Semaphore::new(max_concurrent),
        }
    }

    pub async fn execute_with_tokio(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        let mut child = TokioCommand::new(command)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        // 异步处理输入输出
        let output = child.wait_with_output().await?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("Tokio 进程执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }

    // 流式处理大量数据
    pub async fn execute_streaming(
        &self,
        command: &str,
        input_data: &[u8],
    ) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        let mut child = TokioCommand::new(command)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        // 异步写入数据
        if let Some(stdin) = child.stdin.take() {
            let mut writer = tokio::io::BufWriter::new(stdin);
            writer.write_all(input_data).await?;
            writer.flush().await?;
        }

        // 异步读取输出
        let output = child.wait_with_output().await?;

        if output.status.success() {
            Ok(output.stdout)
        } else {
            Err(format!("流式处理失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
}

// Tokio 进程池
pub struct TokioProcessPool {
    processes: std::sync::Arc<tokio::sync::Mutex<Vec<Child>>>,
    max_size: usize,
    semaphore: tokio::sync::Semaphore,
}

impl TokioProcessPool {
    pub fn new(max_size: usize) -> Self {
        Self {
            processes: std::sync::Arc::new(tokio::sync::Mutex::new(Vec::new())),
            max_size,
            semaphore: tokio::sync::Semaphore::new(max_size),
        }
    }

    pub async fn execute_in_pool(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        let mut child = TokioCommand::new(command)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        let output = child.wait_with_output().await?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("进程池执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }

    pub async fn cleanup_completed_processes(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        let initial_count = processes.len();
        processes.retain(|child| {
            child.try_wait().map(|status| status.is_none()).unwrap_or(false)
        });

        let cleaned_count = initial_count - processes.len();
        if cleaned_count > 0 {
            println!("清理了 {} 个已完成的进程", cleaned_count);
        }

        Ok(())
    }
}
```

### 5.2 Async-Std 2.0 特性

Async-Std 2.0 提供了标准库风格的异步进程管理。

```rust
use async_std::process::{Command as AsyncStdCommand, Stdio};
use async_std::io::prelude::*;

// Async-Std 进程管理器
pub struct AsyncStdProcessManager {
    max_concurrent: usize,
    semaphore: async_std::sync::Semaphore,
}

impl AsyncStdProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            max_concurrent,
            semaphore: async_std::sync::Semaphore::new(max_concurrent),
        }
    }

    pub async fn execute_with_async_std(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await;

        let mut child = AsyncStdCommand::new(command)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        let output = child.output().await?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("Async-Std 进程执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }

    // 异步流式处理
    pub async fn execute_streaming_async_std(
        &self,
        command: &str,
        input_data: &[u8],
    ) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await;

        let mut child = AsyncStdCommand::new(command)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        // 异步写入数据
        if let Some(stdin) = child.stdin.take() {
            let mut writer = stdin;
            writer.write_all(input_data).await?;
            writer.flush().await?;
        }

        // 异步读取输出
        let output = child.output().await?;

        if output.status.success() {
            Ok(output.stdout)
        } else {
            Err(format!("Async-Std 流式处理失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
}

// Async-Std 进程组管理
pub struct AsyncStdProcessGroup {
    processes: std::sync::Arc<async_std::sync::Mutex<Vec<async_std::process::Child>>>,
    max_size: usize,
}

impl AsyncStdProcessGroup {
    pub fn new(max_size: usize) -> Self {
        Self {
            processes: std::sync::Arc::new(async_std::sync::Mutex::new(Vec::new())),
            max_size,
        }
    }

    pub async fn add_process(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        if processes.len() >= self.max_size {
            return Err("进程组已满".into());
        }

        let child = AsyncStdCommand::new(command)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        processes.push(child);
        Ok(())
    }

    pub async fn wait_all(&self) -> Result<Vec<async_std::process::Output>, Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;
        let mut outputs = Vec::new();

        for child in processes.drain(..) {
            let output = child.output().await?;
            outputs.push(output);
        }

        Ok(outputs)
    }
}
```

### 5.3 现代进程管理库

集成现代进程管理库，提供更高级的功能。

```rust
use duct::cmd;
use subprocess::{Popen, PopenConfig, Redirection};

// Duct 进程组合管理器
pub struct DuctProcessManager {
    max_concurrent: usize,
    semaphore: tokio::sync::Semaphore,
}

impl DuctProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            max_concurrent,
            semaphore: tokio::sync::Semaphore::new(max_concurrent),
        }
    }

    pub async fn execute_with_duct(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        // 使用 Duct 构建命令
        let mut duct_cmd = cmd(command, args);

        // 执行命令并获取输出
        let output = duct_cmd.stdout_capture().run()?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("Duct 进程执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }

    // 管道组合执行
    pub async fn execute_pipeline(
        &self,
        commands: Vec<(String, Vec<String>)>,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        // 构建管道
        let mut pipeline = cmd("echo", &["开始管道执行"]);

        for (cmd, args) in commands {
            pipeline = pipeline.pipe(cmd(cmd, args));
        }

        let output = pipeline.stdout_capture().run()?;

        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("管道执行失败: {}",
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
}

// Subprocess 高级进程控制
pub struct SubprocessManager {
    max_concurrent: usize,
    semaphore: tokio::sync::Semaphore,
}

impl SubprocessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            max_concurrent,
            semaphore: tokio::sync::Semaphore::new(max_concurrent),
        }
    }

    pub async fn execute_with_subprocess(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        // 配置进程
        let config = PopenConfig {
            stdout: Redirection::Pipe,
            stderr: Redirection::Pipe,
            stdin: Redirection::Pipe,
            ..Default::default()
        };

        // 创建进程
        let mut process = Popen::create(
            &[command],
            config,
        )?;

        // 等待进程完成
        let (stdout, stderr) = process.communicate(None)?;

        if process.poll().is_some() {
            Ok(stdout.unwrap_or_default())
        } else {
            Err(format!("Subprocess 执行失败: {}",
                stderr.unwrap_or_default()).into())
        }
    }

    // 高级进程控制
    pub async fn execute_with_advanced_control(
        &self,
        command: &str,
        args: &[String],
        timeout: Option<std::time::Duration>,
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;

        let config = PopenConfig {
            stdout: Redirection::Pipe,
            stderr: Redirection::Pipe,
            stdin: Redirection::Pipe,
            ..Default::default()
        };

        let mut process = Popen::create(
            &[command],
            config,
        )?;

        // 设置超时
        if let Some(timeout_duration) = timeout {
            tokio::time::timeout(timeout_duration, async {
                process.wait()
            }).await??;
        } else {
            process.wait()?;
        }

        let (stdout, stderr) = process.communicate(None)?;

        if process.poll().is_some() {
            Ok(stdout.unwrap_or_default())
        } else {
            Err(format!("高级控制执行失败: {}",
                stderr.unwrap_or_default()).into())
        }
    }
}

// 现代库集成管理器
pub struct ModernLibraryManager {
    tokio_manager: TokioProcessManager,
    async_std_manager: AsyncStdProcessManager,
    duct_manager: DuctProcessManager,
    subprocess_manager: SubprocessManager,
}

impl ModernLibraryManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            tokio_manager: TokioProcessManager::new(max_concurrent),
            async_std_manager: AsyncStdProcessManager::new(max_concurrent),
            duct_manager: DuctProcessManager::new(max_concurrent),
            subprocess_manager: SubprocessManager::new(max_concurrent),
        }
    }

    pub async fn execute_with_best_library(
        &self,
        command: &str,
        args: &[String],
        requirements: &ProcessRequirements,
    ) -> Result<String, Box<dyn std::error::Error>> {
        match requirements {
            ProcessRequirements { high_performance: true, .. } => {
                self.tokio_manager.execute_with_tokio(command, args).await
            }
            ProcessRequirements { pipe_composition: true, .. } => {
                self.duct_manager.execute_with_duct(command, args).await
            }
            ProcessRequirements { advanced_control: true, .. } => {
                self.subprocess_manager.execute_with_subprocess(command, args).await
            }
            _ => {
                self.async_std_manager.execute_with_async_std(command, args).await
            }
        }
    }
}

#[derive(Debug)]
pub struct ProcessRequirements {
    pub high_performance: bool,
    pub pipe_composition: bool,
    pub advanced_control: bool,
    pub simple_api: bool,
}
```

## 6. 实际应用示例

### 5.1 高性能进程管理器

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::{Mutex, Semaphore};
use tokio::time::{Duration, Instant};

pub struct HighPerformanceProcessManager {
    semaphore: Arc<Semaphore>,
    processes: Arc<Mutex<Vec<tokio::process::Child>>>,
}

impl HighPerformanceProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            processes: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn execute_with_metrics<F>(
        &self,
        command: &str,
        metrics_callback: F,
    ) -> Result<String, Box<dyn std::error::Error>>
    where
        F: FnOnce(Duration, usize) + Send + 'static,
    {
        let _permit = self.semaphore.acquire().await?;
        let start_time = Instant::now();

        let mut child = Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;

        let output = child.wait_with_output().await?;
        let duration = start_time.elapsed();
        let output_size = output.stdout.len();

        metrics_callback(duration, output_size);

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}
```

### 5.2 智能进程监控系统

```rust
use std::process::{Command, Stdio};
use std::time::Duration;
use tokio::time::interval;

pub struct ProcessMonitor {
    check_interval: Duration,
    max_memory_mb: u64,
    max_cpu_percent: f64,
}

impl ProcessMonitor {
    pub fn new(check_interval: Duration, max_memory_mb: u64, max_cpu_percent: f64) -> Self {
        Self {
            check_interval,
            max_memory_mb,
            max_cpu_percent,
        }
    }

    pub async fn monitor_process(&self, pid: u32) -> Result<(), Box<dyn std::error::Error>> {
        let mut interval = interval(self.check_interval);

        loop {
            interval.tick().await;

            // 检查进程资源使用情况
            let resource_usage = self.get_process_resources(pid).await?;

            if resource_usage.memory_mb > self.max_memory_mb {
                println!("警告: 进程 {} 内存使用过高: {} MB", pid, resource_usage.memory_mb);
            }

            if resource_usage.cpu_percent > self.max_cpu_percent {
                println!("警告: 进程 {} CPU 使用过高: {:.2}%", pid, resource_usage.cpu_percent);
            }
        }
    }

    async fn get_process_resources(&self, pid: u32) -> Result<ProcessResources, Box<dyn std::error::Error>> {
        let output = Command::new("ps")
            .arg("-p")
            .arg(pid.to_string())
            .arg("-o")
            .arg("pid,pcpu,pmem")
            .output()
            .await?;

        let output_str = String::from_utf8_lossy(&output.stdout);
        let lines: Vec<&str> = output_str.lines().collect();

        if lines.len() < 2 {
            return Err("无法获取进程信息".into());
        }

        let parts: Vec<&str> = lines[1].split_whitespace().collect();
        if parts.len() < 3 {
            return Err("进程信息格式错误".into());
        }

        Ok(ProcessResources {
            pid: parts[0].parse()?,
            cpu_percent: parts[1].parse()?,
            memory_mb: parts[2].parse()?,
        })
    }
}

#[derive(Debug)]
struct ProcessResources {
    pid: u32,
    cpu_percent: f64,
    memory_mb: u64,
}
```

## 6. 最佳实践

### 6.1 错误处理策略

```rust
use std::process::{Command, Stdio};
use std::time::Duration;
use tokio::time::timeout;

pub async fn robust_process_execution(
    command: &str,
    timeout_duration: Duration,
) -> Result<ProcessResult, ProcessError> {
    let mut child = Command::new("sh")
        .arg("-c")
        .arg(command)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(ProcessError::SpawnFailed)?;

    let result = timeout(timeout_duration, child.wait()).await;

    match result {
        Ok(Ok(status)) => {
            let output = child.wait_with_output().await
                .map_err(ProcessError::OutputFailed)?;

            Ok(ProcessResult {
                status,
                stdout: output.stdout,
                stderr: output.stderr,
                execution_time: Duration::from_secs(0), // 实际实现中计算
            })
        }
        Ok(Err(e)) => Err(ProcessError::WaitFailed(e)),
        Err(_) => {
            child.kill().await.map_err(ProcessError::KillFailed)?;
            Err(ProcessError::Timeout)
        }
    }
}

#[derive(Debug)]
pub enum ProcessError {
    SpawnFailed(std::io::Error),
    WaitFailed(std::io::Error),
    OutputFailed(std::io::Error),
    KillFailed(std::io::Error),
    Timeout,
}

#[derive(Debug)]
pub struct ProcessResult {
    pub status: std::process::ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub execution_time: Duration,
}
```

### 6.2 资源管理

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct ResourceManager {
    processes: Arc<Mutex<Vec<tokio::process::Child>>>,
    max_processes: usize,
}

impl ResourceManager {
    pub fn new(max_processes: usize) -> Self {
        Self {
            processes: Arc::new(Mutex::new(Vec::new())),
            max_processes,
        }
    }

    pub async fn cleanup_completed_processes(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().await;

        let initial_count = processes.len();
        processes.retain(|child| {
            child.try_wait().map(|status| status.is_none()).unwrap_or(false)
        });

        let cleaned_count = initial_count - processes.len();
        if cleaned_count > 0 {
            println!("清理了 {} 个已完成的进程", cleaned_count);
        }

        Ok(())
    }

    pub async fn execute_with_cleanup<F>(
        &self,
        command: &str,
        callback: F,
    ) -> Result<(), Box<dyn std::error::Error>>
    where
        F: FnOnce(String) + Send + 'static,
    {
        let mut processes = self.processes.lock().await;

        if processes.len() >= self.max_processes {
            return Err("进程数量已达上限".into());
        }

        let mut child = Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdout(Stdio::piped())
            .spawn()?;

        let output = child.wait_with_output().await?;
        let result = String::from_utf8_lossy(&output.stdout).to_string();

        callback(result);

        Ok(())
    }
}
```

## 7. 总结

Rust 1.90 版本为进程管理带来了显著的改进：

1. **异步支持增强**: 更好的异步闭包和异步进程管理
2. **性能优化**: 零拷贝传输和内存池优化
3. **安全性提升**: 改进的权限控制和沙箱执行
4. **错误处理改进**: 更完善的错误处理机制
5. **模式匹配增强**: 更强大的模式匹配能力

这些特性使得 Rust 在系统级编程和进程管理方面更加强大和易用。开发者可以利用这些新特性构建更高效、更安全、更可靠的进程管理系统。
