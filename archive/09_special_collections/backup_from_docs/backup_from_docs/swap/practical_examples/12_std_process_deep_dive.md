# C07-12. 标准库 Process 模块深度解析

## 目录

- [C07-12. 标准库 Process 模块深度解析](#c07-12-标准库-process-模块深度解析)
  - [目录](#目录)
  - [1. 模块概览](#1-模块概览)
    - [1.1 核心结构体](#11-核心结构体)
    - [1.2 主要功能](#12-主要功能)
    - [1.3 Rust 1.90 增强](#13-rust-190-增强)
  - [2. Command 结构体详解](#2-command-结构体详解)
    - [2.1 基础用法](#21-基础用法)
    - [2.2 高级配置](#22-高级配置)
    - [2.3 跨平台兼容性](#23-跨平台兼容性)
    - [2.4 性能优化](#24-性能优化)
  - [3. Child 进程句柄管理](#3-child-进程句柄管理)
    - [3.1 生命周期管理](#31-生命周期管理)
    - [3.2 进程监控](#32-进程监控)
    - [3.3 资源清理](#33-资源清理)
  - [4. Output 输出处理](#4-output-输出处理)
    - [4.1 标准输出处理](#41-标准输出处理)
    - [4.2 错误输出处理](#42-错误输出处理)
    - [4.3 流式处理](#43-流式处理)
  - [5. ExitStatus 状态分析](#5-exitstatus-状态分析)
    - [5.1 状态码解析](#51-状态码解析)
    - [5.2 信号处理](#52-信号处理)
    - [5.3 错误诊断](#53-错误诊断)
  - [6. 高级特性](#6-高级特性)
    - [6.1 进程组管理](#61-进程组管理)
    - [6.2 资源限制](#62-资源限制)
    - [6.3 安全执行](#63-安全执行)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 错误处理](#71-错误处理)
    - [7.2 性能优化](#72-性能优化)
    - [7.3 安全实践](#73-安全实践)
  - [8. 实战案例](#8-实战案例)
    - [8.1 命令行工具开发](#81-命令行工具开发)
    - [8.2 系统管理工具](#82-系统管理工具)
    - [8.3 批处理系统](#83-批处理系统)
  - [9. 总结](#9-总结)
    - [核心特性](#核心特性)
    - [高级功能](#高级功能)
    - [最佳实践](#最佳实践)
    - [实战应用](#实战应用)

本章深入解析 Rust 标准库 `std::process` 模块的所有功能，包括核心结构体、高级特性、最佳实践和实战案例。

## 1. 模块概览

### 1.1 核心结构体

`std::process` 模块提供了以下核心结构体：

```rust
use std::process::{Command, Child, Output, ExitStatus, Stdio};

// 核心结构体
pub struct Command { /* ... */ }           // 进程构建器
pub struct Child { /* ... */ }             // 子进程句柄
pub struct Output { /* ... */ }            // 进程输出
pub struct ExitStatus { /* ... */ }        // 退出状态
pub struct Stdio { /* ... */ }             // 标准 I/O 重定向
```

### 1.2 主要功能

- **进程创建与管理**：创建、启动、监控子进程
- **I/O 重定向**：控制标准输入、输出、错误流
- **进程间通信**：通过管道进行数据交换
- **资源管理**：自动清理进程资源
- **跨平台支持**：统一的跨平台 API

### 1.3 Rust 1.90 增强

Rust 1.90 版本为 `std::process` 模块带来了以下增强：

```rust
use std::process::{Command, Stdio};
use std::time::Duration;

// Rust 1.90 新特性示例
async fn rust_190_enhancements() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 改进的错误处理
    let output = Command::new("echo")
        .arg("Hello Rust 1.90!")
        .output()
        .await  // 新增异步支持
        .map_err(|e| format!("命令执行失败: {}", e))?;
    
    // 2. 增强的模式匹配
    match output.status {
        status if status.success() => {
            println!("命令执行成功");
        }
        status if status.code().is_some() => {
            println!("命令异常退出: {:?}", status.code());
        }
        _ => {
            println!("未知状态");
        }
    }
    
    Ok(())
}
```

## 2. Command 结构体详解

### 2.1 基础用法

`Command` 是进程管理的核心，提供了丰富的配置选项。

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};

// 基础命令执行
pub fn basic_command_execution() -> Result<String, Box<dyn std::error::Error>> {
    let output = Command::new("echo")
        .arg("Hello, World!")
        .output()?;
    
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        Err(format!("命令执行失败: {}", 
            String::from_utf8_lossy(&output.stderr)).into())
    }
}

// 带参数的命令执行
pub fn command_with_args() -> Result<String, Box<dyn std::error::Error>> {
    let output = Command::new("ls")
        .arg("-la")
        .arg("/tmp")
        .output()?;
    
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        Err(format!("ls 命令执行失败: {}", 
            String::from_utf8_lossy(&output.stderr)).into())
    }
}

// 环境变量设置
pub fn command_with_env() -> Result<String, Box<dyn std::error::Error>> {
    let output = Command::new("env")
        .env("RUST_LOG", "debug")
        .env("MY_VAR", "test_value")
        .output()?;
    
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        Err(format!("env 命令执行失败: {}", 
            String::from_utf8_lossy(&output.stderr)).into())
    }
}
```

### 2.2 高级配置

```rust
use std::process::{Command, Stdio};
use std::fs::File;
use std::io::Write;

// 高级 I/O 重定向
pub fn advanced_io_redirection() -> Result<(), Box<dyn std::error::Error>> {
    // 创建日志文件
    let mut log_file = File::create("command.log")?;
    
    let mut child = Command::new("long_running_command")
        .stdin(Stdio::null())           // 关闭标准输入
        .stdout(Stdio::piped())         // 捕获标准输出
        .stderr(Stdio::from(log_file))  // 重定向错误到文件
        .spawn()?;
    
    // 处理标准输出
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            let line = line?;
            println!("输出: {}", line);
        }
    }
    
    // 等待进程完成
    let status = child.wait()?;
    println!("进程完成，状态: {:?}", status);
    
    Ok(())
}

// 工作目录设置
pub fn command_with_working_dir() -> Result<String, Box<dyn std::error::Error>> {
    let output = Command::new("pwd")
        .current_dir("/tmp")
        .output()?;
    
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        Err(format!("pwd 命令执行失败: {}", 
            String::from_utf8_lossy(&output.stderr)).into())
    }
}

// 用户权限设置
pub fn command_with_user_permissions() -> Result<String, Box<dyn std::error::Error>> {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        
        let output = Command::new("whoami")
            .uid(1000)  // 设置用户 ID
            .gid(1000)  // 设置组 ID
            .output()?;
        
        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("whoami 命令执行失败: {}", 
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
    
    #[cfg(not(unix))]
    {
        Err("用户权限设置仅在 Unix 系统上支持".into())
    }
}
```

### 2.3 跨平台兼容性

```rust
use std::process::{Command, Stdio};

// 跨平台命令执行
pub fn cross_platform_command() -> Result<String, Box<dyn std::error::Error>> {
    let (command, args) = if cfg!(windows) {
        ("cmd", vec!["/C".to_string(), "echo Hello Windows".to_string()])
    } else {
        ("echo", vec!["Hello Unix".to_string()])
    };
    
    let output = Command::new(command)
        .args(args)
        .output()?;
    
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        Err(format!("跨平台命令执行失败: {}", 
            String::from_utf8_lossy(&output.stderr)).into())
    }
}

// 平台特定功能
pub fn platform_specific_features() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::new("platform_command");
    
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        
        cmd.process_group(0)
           .create_new_process_group(true)
           .before_exec(|| {
               // Unix 特定的预处理
               unsafe {
                   libc::nice(10);  // 降低优先级
               }
               Ok(())
           });
    }
    
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        
        cmd.creation_flags(0x00000008);  // CREATE_NEW_PROCESS_GROUP
    }
    
    let child = cmd.spawn()?;
    println!("平台特定进程启动成功");
    
    Ok(())
}
```

### 2.4 性能优化

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Semaphore;

// 高性能命令执行
pub struct HighPerformanceCommandExecutor {
    semaphore: Arc<Semaphore>,
    max_concurrent: usize,
}

impl HighPerformanceCommandExecutor {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent,
        }
    }
    
    pub async fn execute_with_limit(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;
        
        let output = Command::new(command)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()?;
        
        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("高性能执行失败: {}", 
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
}

// 零拷贝数据传输
pub fn zero_copy_execution() -> Result<(), Box<dyn std::error::Error>> {
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

## 3. Child 进程句柄管理

### 3.1 生命周期管理

```rust
use std::process::{Command, Stdio};
use std::time::Duration;

// 进程生命周期管理
pub struct ProcessLifecycleManager {
    processes: std::collections::HashMap<u32, std::process::Child>,
}

impl ProcessLifecycleManager {
    pub fn new() -> Self {
        Self {
            processes: std::collections::HashMap::new(),
        }
    }
    
    pub fn spawn_process(
        &mut self,
        command: &str,
        args: &[String],
    ) -> Result<u32, Box<dyn std::error::Error>> {
        let mut child = Command::new(command)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        
        let pid = child.id().unwrap_or(0);
        self.processes.insert(pid, child);
        
        Ok(pid)
    }
    
    pub fn wait_for_process(
        &mut self,
        pid: u32,
    ) -> Result<std::process::ExitStatus, Box<dyn std::error::Error>> {
        if let Some(mut child) = self.processes.remove(&pid) {
            Ok(child.wait()?)
        } else {
            Err(format!("进程 {} 不存在", pid).into())
        }
    }
    
    pub fn kill_process(
        &mut self,
        pid: u32,
    ) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(mut child) = self.processes.remove(&pid) {
            child.kill()?;
            Ok(())
        } else {
            Err(format!("进程 {} 不存在", pid).into())
        }
    }
    
    pub fn cleanup_completed_processes(&mut self) -> usize {
        let mut completed_pids = Vec::new();
        
        for (pid, child) in &mut self.processes {
            if child.try_wait().map(|status| status.is_some()).unwrap_or(false) {
                completed_pids.push(*pid);
            }
        }
        
        for pid in completed_pids {
            self.processes.remove(&pid);
        }
        
        completed_pids.len()
    }
}
```

### 3.2 进程监控

```rust
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
use tokio::time::interval;

// 进程监控器
pub struct ProcessMonitor {
    check_interval: Duration,
    max_execution_time: Duration,
    max_memory_mb: u64,
}

impl ProcessMonitor {
    pub fn new(check_interval: Duration, max_execution_time: Duration, max_memory_mb: u64) -> Self {
        Self {
            check_interval,
            max_execution_time,
            max_memory_mb,
        }
    }
    
    pub async fn monitor_process(
        &self,
        mut child: std::process::Child,
    ) -> Result<std::process::ExitStatus, Box<dyn std::error::Error>> {
        let start_time = Instant::now();
        let pid = child.id().unwrap_or(0);
        let mut interval = interval(self.check_interval);
        
        loop {
            interval.tick().await;
            
            // 检查执行时间
            if start_time.elapsed() > self.max_execution_time {
                eprintln!("进程 {} 执行超时，终止进程", pid);
                child.kill()?;
                break;
            }
            
            // 检查进程状态
            if let Some(status) = child.try_wait()? {
                println!("进程 {} 正常完成", pid);
                return Ok(status);
            }
            
            // 检查内存使用
            if let Ok(memory_usage) = self.get_process_memory(pid).await {
                if memory_usage > self.max_memory_mb {
                    eprintln!("进程 {} 内存使用过高: {} MB", pid, memory_usage);
                    child.kill()?;
                    break;
                }
            }
        }
        
        child.wait()
    }
    
    async fn get_process_memory(&self, pid: u32) -> Result<u64, Box<dyn std::error::Error>> {
        #[cfg(unix)]
        {
            let output = Command::new("ps")
                .arg("-p")
                .arg(pid.to_string())
                .arg("-o")
                .arg("rss")
                .output()?;
            
            if output.status.success() {
                let output_str = String::from_utf8_lossy(&output.stdout);
                let lines: Vec<&str> = output_str.lines().collect();
                if lines.len() >= 2 {
                    if let Ok(memory_kb) = lines[1].trim().parse::<u64>() {
                        return Ok(memory_kb / 1024); // 转换为 MB
                    }
                }
            }
        }
        
        Ok(0)
    }
}
```

### 3.3 资源清理

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Mutex;

// 自动资源清理
pub struct AutoResourceCleanup {
    processes: Arc<Mutex<Vec<std::process::Child>>>,
    cleanup_interval: Duration,
}

impl AutoResourceCleanup {
    pub fn new(cleanup_interval: Duration) -> Self {
        Self {
            processes: Arc::new(Mutex::new(Vec::new())),
            cleanup_interval,
        }
    }
    
    pub async fn spawn_with_cleanup(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<u32, Box<dyn std::error::Error>> {
        let child = Command::new(command)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        
        let pid = child.id().unwrap_or(0);
        
        {
            let mut processes = self.processes.lock().await;
            processes.push(child);
        }
        
        // 启动清理任务
        self.start_cleanup_task().await;
        
        Ok(pid)
    }
    
    async fn start_cleanup_task(&self) {
        let processes = self.processes.clone();
        let interval = self.cleanup_interval;
        
        tokio::spawn(async move {
            let mut cleanup_interval = tokio::time::interval(interval);
            
            loop {
                cleanup_interval.tick().await;
                
                let mut processes = processes.lock().await;
                let initial_count = processes.len();
                
                processes.retain(|child| {
                    child.try_wait().map(|status| status.is_none()).unwrap_or(false)
                });
                
                let cleaned_count = initial_count - processes.len();
                if cleaned_count > 0 {
                    println!("自动清理了 {} 个已完成的进程", cleaned_count);
                }
            }
        });
    }
}
```

## 4. Output 输出处理

### 4.1 标准输出处理

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};

// 标准输出处理
pub fn process_stdout() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("ls")
        .arg("-la")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            let line = line?;
            println!("文件: {}", line);
        }
    }
    
    let status = child.wait()?;
    println!("ls 命令完成，状态: {:?}", status);
    
    Ok(())
}

// 流式输出处理
pub fn stream_output_processing() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("tail")
        .arg("-f")
        .arg("/var/log/syslog")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            let line = line?;
            println!("日志: {}", line);
            
            // 处理特定日志
            if line.contains("ERROR") {
                eprintln!("发现错误日志: {}", line);
            }
        }
    }
    
    Ok(())
}
```

### 4.2 错误输出处理

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};

// 错误输出处理
pub fn process_stderr() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("invalid_command")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    let output = child.wait_with_output()?;
    
    if !output.status.success() {
        if let Some(stderr) = child.stderr.take() {
            let reader = BufReader::new(stderr);
            for line in reader.lines() {
                let line = line?;
                eprintln!("错误: {}", line);
            }
        }
    }
    
    Ok(())
}

// 错误分类处理
pub fn categorize_errors() -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new("some_command")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()?;
    
    if !output.status.success() {
        let error_output = String::from_utf8_lossy(&output.stderr);
        
        if error_output.contains("permission denied") {
            eprintln!("权限错误: {}", error_output);
        } else if error_output.contains("not found") {
            eprintln!("文件未找到: {}", error_output);
        } else if error_output.contains("timeout") {
            eprintln!("超时错误: {}", error_output);
        } else {
            eprintln!("未知错误: {}", error_output);
        }
    }
    
    Ok(())
}
```

### 4.3 流式处理

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader, Write};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};

// 异步流式处理
pub async fn async_stream_processing() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    // 异步写入数据
    if let Some(stdin) = child.stdin.take() {
        tokio::spawn(async move {
            let mut writer = tokio::io::BufWriter::new(stdin);
            for i in 0..100 {
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

// 双向流式处理
pub async fn bidirectional_stream_processing() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("interactive_command")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    // 创建双向通道
    let (tx, mut rx) = tokio::sync::mpsc::channel(100);
    
    // 输入处理任务
    if let Some(stdin) = child.stdin.take() {
        let tx_clone = tx.clone();
        tokio::spawn(async move {
            let mut writer = tokio::io::BufWriter::new(stdin);
            while let Some(data) = rx.recv().await {
                if let Err(e) = writer.write_all(data.as_bytes()).await {
                    eprintln!("写入错误: {}", e);
                    break;
                }
                if let Err(e) = writer.flush().await {
                    eprintln!("刷新错误: {}", e);
                    break;
                }
            }
        });
    }
    
    // 输出处理任务
    if let Some(stdout) = child.stdout.take() {
        tokio::spawn(async move {
            let mut reader = tokio::io::BufReader::new(stdout);
            let mut line = String::new();
            while reader.read_line(&mut line).await.unwrap_or(0) > 0 {
                println!("收到: {}", line.trim());
                
                // 根据输出发送响应
                if line.contains("请输入") {
                    let _ = tx.send("响应数据\n".to_string()).await;
                }
                
                line.clear();
            }
        });
    }
    
    let status = child.wait().await?;
    println!("双向流式处理完成: {:?}", status);
    
    Ok(())
}
```

## 5. ExitStatus 状态分析

### 5.1 状态码解析

```rust
use std::process::{Command, ExitStatus};

// 状态码解析
pub fn analyze_exit_status(status: ExitStatus) {
    if status.success() {
        println!("进程成功完成");
    } else {
        match status.code() {
            Some(code) => {
                match code {
                    0 => println!("进程正常退出"),
                    1 => println!("一般错误"),
                    2 => println!("误用 shell 命令"),
                    126 => println!("命令不可执行"),
                    127 => println!("命令未找到"),
                    128 => println!("无效的退出参数"),
                    _ => println!("未知退出码: {}", code),
                }
            }
            None => {
                println!("进程被信号终止");
                if let Some(signal) = status.signal() {
                    match signal {
                        1 => println!("SIGHUP - 挂起信号"),
                        2 => println!("SIGINT - 中断信号"),
                        9 => println!("SIGKILL - 强制终止"),
                        15 => println!("SIGTERM - 终止信号"),
                        _ => println!("信号 {} 终止了进程", signal),
                    }
                }
            }
        }
    }
}

// 详细状态分析
pub fn detailed_status_analysis(status: ExitStatus) -> ProcessStatus {
    if status.success() {
        ProcessStatus::Success
    } else if let Some(code) = status.code() {
        match code {
            0 => ProcessStatus::Success,
            1..=125 => ProcessStatus::Error(code),
            126 => ProcessStatus::NotExecutable,
            127 => ProcessStatus::NotFound,
            128..=255 => ProcessStatus::FatalError(code),
            _ => ProcessStatus::UnknownError(code),
        }
    } else if let Some(signal) = status.signal() {
        ProcessStatus::KilledBySignal(signal)
    } else {
        ProcessStatus::Unknown
    }
}

#[derive(Debug)]
pub enum ProcessStatus {
    Success,
    Error(i32),
    NotExecutable,
    NotFound,
    FatalError(i32),
    UnknownError(i32),
    KilledBySignal(i32),
    Unknown,
}
```

### 5.2 信号处理

```rust
use std::process::{Command, ExitStatus};
use std::os::unix::process::CommandExt;

// 信号处理
pub fn signal_handling_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("long_running_process")
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()?;
    
    let pid = child.id().unwrap_or(0);
    
    // 设置信号处理器
    #[cfg(unix)]
    {
        use signal_hook::flag;
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;
        
        let term_now = Arc::new(AtomicBool::new(false));
        flag::register(signal_hook::consts::SIGTERM, Arc::clone(&term_now))?;
        flag::register(signal_hook::consts::SIGINT, Arc::clone(&term_now))?;
        
        // 监控信号
        while !term_now.load(Ordering::Relaxed) {
            if let Some(status) = child.try_wait()? {
                println!("进程完成: {:?}", status);
                break;
            }
            
            std::thread::sleep(std::time::Duration::from_millis(100));
        }
        
        if term_now.load(Ordering::Relaxed) {
            println!("收到终止信号，正在终止进程 {}", pid);
            child.kill()?;
        }
    }
    
    Ok(())
}
```

### 5.3 错误诊断

```rust
use std::process::{Command, ExitStatus};
use std::collections::HashMap;

// 错误诊断系统
pub struct ErrorDiagnostic {
    error_patterns: HashMap<String, String>,
}

impl ErrorDiagnostic {
    pub fn new() -> Self {
        let mut patterns = HashMap::new();
        patterns.insert("permission denied".to_string(), "权限不足，请检查文件权限".to_string());
        patterns.insert("not found".to_string(), "文件或命令未找到，请检查路径".to_string());
        patterns.insert("timeout".to_string(), "操作超时，请检查网络连接".to_string());
        patterns.insert("out of memory".to_string(), "内存不足，请释放内存".to_string());
        patterns.insert("disk full".to_string(), "磁盘空间不足，请清理磁盘".to_string());
        
        Self {
            error_patterns: patterns,
        }
    }
    
    pub fn diagnose_error(&self, status: ExitStatus, stderr: &str) -> DiagnosticResult {
        if status.success() {
            return DiagnosticResult::Success;
        }
        
        let error_text = stderr.to_lowercase();
        
        for (pattern, suggestion) in &self.error_patterns {
            if error_text.contains(pattern) {
                return DiagnosticResult::Error {
                    code: status.code().unwrap_or(-1),
                    message: stderr.to_string(),
                    suggestion: suggestion.clone(),
                };
            }
        }
        
        DiagnosticResult::UnknownError {
            code: status.code().unwrap_or(-1),
            message: stderr.to_string(),
        }
    }
}

#[derive(Debug)]
pub enum DiagnosticResult {
    Success,
    Error {
        code: i32,
        message: String,
        suggestion: String,
    },
    UnknownError {
        code: i32,
        message: String,
    },
}
```

## 6. 高级特性

### 6.1 进程组管理

```rust
use std::process::{Command, Stdio};
use std::os::unix::process::CommandExt;

// 进程组管理器
pub struct ProcessGroupManager {
    processes: std::collections::HashMap<u32, std::process::Child>,
    process_groups: std::collections::HashMap<u32, Vec<u32>>,
}

impl ProcessGroupManager {
    pub fn new() -> Self {
        Self {
            processes: std::collections::HashMap::new(),
            process_groups: std::collections::HashMap::new(),
        }
    }
    
    pub fn create_process_group(
        &mut self,
        group_id: u32,
        commands: Vec<(String, Vec<String>)>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut pids = Vec::new();
        
        for (command, args) in commands {
            let mut cmd = Command::new(command);
            cmd.args(args)
               .stdout(Stdio::piped())
               .stderr(Stdio::piped());
            
            #[cfg(unix)]
            {
                cmd.process_group(group_id as i32)
                   .create_new_process_group(group_id == 0);
            }
            
            let child = cmd.spawn()?;
            let pid = child.id().unwrap_or(0);
            
            self.processes.insert(pid, child);
            pids.push(pid);
        }
        
        self.process_groups.insert(group_id, pids);
        Ok(())
    }
    
    pub fn kill_process_group(&mut self, group_id: u32) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(pids) = self.process_groups.remove(&group_id) {
            for pid in pids {
                if let Some(mut child) = self.processes.remove(&pid) {
                    child.kill()?;
                }
            }
        }
        Ok(())
    }
    
    pub fn wait_for_process_group(&mut self, group_id: u32) -> Result<Vec<std::process::ExitStatus>, Box<dyn std::error::Error>> {
        let mut statuses = Vec::new();
        
        if let Some(pids) = self.process_groups.remove(&group_id) {
            for pid in pids {
                if let Some(mut child) = self.processes.remove(&pid) {
                    statuses.push(child.wait()?);
                }
            }
        }
        
        Ok(statuses)
    }
}
```

### 6.2 资源限制

```rust
use std::process::{Command, Stdio};
use std::os::unix::process::CommandExt;

// 资源限制管理器
pub struct ResourceLimitManager {
    max_memory: usize,
    max_cpu_time: std::time::Duration,
    max_file_descriptors: usize,
}

impl ResourceLimitManager {
    pub fn new(max_memory: usize, max_cpu_time: std::time::Duration, max_file_descriptors: usize) -> Self {
        Self {
            max_memory,
            max_cpu_time,
            max_file_descriptors,
        }
    }
    
    pub fn apply_limits(&self, cmd: &mut Command) -> Result<(), Box<dyn std::error::Error>> {
        #[cfg(unix)]
        {
            cmd.before_exec(|| {
                unsafe {
                    // 设置内存限制
                    libc::setrlimit(
                        libc::RLIMIT_AS,
                        &libc::rlimit {
                            rlim_cur: self.max_memory as libc::rlim_t,
                            rlim_max: self.max_memory as libc::rlim_t,
                        },
                    );
                    
                    // 设置文件描述符限制
                    libc::setrlimit(
                        libc::RLIMIT_NOFILE,
                        &libc::rlimit {
                            rlim_cur: self.max_file_descriptors as libc::rlim_t,
                            rlim_max: self.max_file_descriptors as libc::rlim_t,
                        },
                    );
                    
                    // 设置 CPU 时间限制
                    libc::setrlimit(
                        libc::RLIMIT_CPU,
                        &libc::rlimit {
                            rlim_cur: self.max_cpu_time.as_secs() as libc::rlim_t,
                            rlim_max: self.max_cpu_time.as_secs() as libc::rlim_t,
                        },
                    );
                }
                Ok(())
            });
        }
        
        Ok(())
    }
}
```

### 6.3 安全执行

```rust
use std::process::{Command, Stdio};

// 安全执行管理器
pub struct SecureExecutionManager {
    allowed_commands: std::collections::HashSet<String>,
    denied_commands: std::collections::HashSet<String>,
    sandbox_mode: bool,
}

impl SecureExecutionManager {
    pub fn new() -> Self {
        Self {
            allowed_commands: std::collections::HashSet::new(),
            denied_commands: std::collections::HashSet::new(),
            sandbox_mode: false,
        }
    }
    
    pub fn enable_sandbox_mode(&mut self) {
        self.sandbox_mode = true;
    }
    
    pub fn add_allowed_command(&mut self, command: String) {
        self.allowed_commands.insert(command);
    }
    
    pub fn add_denied_command(&mut self, command: String) {
        self.denied_commands.insert(command);
    }
    
    pub fn execute_securely(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<std::process::Output, Box<dyn std::error::Error>> {
        // 检查命令是否被允许
        if !self.is_command_allowed(command) {
            return Err(format!("命令 '{}' 被禁止执行", command).into());
        }
        
        let mut cmd = Command::new(command);
        cmd.args(args)
           .stdout(Stdio::piped())
           .stderr(Stdio::piped());
        
        // 应用安全设置
        if self.sandbox_mode {
            self.apply_sandbox_settings(&mut cmd);
        }
        
        Ok(cmd.output()?)
    }
    
    fn is_command_allowed(&self, command: &str) -> bool {
        // 检查是否在禁止列表中
        if self.denied_commands.contains(command) {
            return false;
        }
        
        // 如果没有允许列表，则允许所有命令
        if self.allowed_commands.is_empty() {
            return true;
        }
        
        // 检查是否在允许列表中
        self.allowed_commands.contains(command)
    }
    
    fn apply_sandbox_settings(&self, cmd: &mut Command) {
        // 清除环境变量
        cmd.env_clear();
        
        // 设置受限的环境变量
        cmd.env("PATH", "/usr/bin:/bin")
           .env("HOME", "/tmp")
           .env("USER", "sandbox");
        
        // 设置工作目录
        cmd.current_dir("/tmp");
        
        // 设置资源限制
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            
            cmd.before_exec(|| {
                unsafe {
                    // 设置内存限制
                    libc::setrlimit(
                        libc::RLIMIT_AS,
                        &libc::rlimit {
                            rlim_cur: 128 * 1024 * 1024, // 128MB
                            rlim_max: 128 * 1024 * 1024,
                        },
                    );
                    
                    // 设置文件描述符限制
                    libc::setrlimit(
                        libc::RLIMIT_NOFILE,
                        &libc::rlimit {
                            rlim_cur: 32,
                            rlim_max: 32,
                        },
                    );
                }
                Ok(())
            });
        }
    }
}
```

## 7. 最佳实践

### 7.1 错误处理

```rust
use std::process::{Command, ExitStatus};
use thiserror::Error;

// 自定义错误类型
#[derive(Error, Debug)]
pub enum ProcessError {
    #[error("进程启动失败: {0}")]
    SpawnFailed(std::io::Error),
    
    #[error("进程执行失败: {0}")]
    ExecutionFailed(String),
    
    #[error("进程超时")]
    Timeout,
    
    #[error("权限不足")]
    PermissionDenied,
    
    #[error("资源不足: {0}")]
    ResourceExhausted(String),
}

// 健壮的错误处理
pub fn robust_process_execution(
    command: &str,
    args: &[String],
) -> Result<String, ProcessError> {
    let output = Command::new(command)
        .args(args)
        .output()
        .map_err(ProcessError::SpawnFailed)?;
    
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        let error_msg = String::from_utf8_lossy(&output.stderr);
        
        // 根据错误类型进行分类
        if error_msg.contains("permission denied") {
            Err(ProcessError::PermissionDenied)
        } else if error_msg.contains("out of memory") {
            Err(ProcessError::ResourceExhausted("内存不足".to_string()))
        } else {
            Err(ProcessError::ExecutionFailed(error_msg.to_string()))
        }
    }
}
```

### 7.2 性能优化

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::Semaphore;

// 高性能进程执行器
pub struct HighPerformanceExecutor {
    semaphore: Arc<Semaphore>,
    process_pool: Arc<tokio::sync::Mutex<Vec<std::process::Child>>>,
}

impl HighPerformanceExecutor {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            process_pool: Arc::new(tokio::sync::Mutex::new(Vec::new())),
        }
    }
    
    pub async fn execute_optimized(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        let _permit = self.semaphore.acquire().await?;
        
        // 清理已完成的进程
        self.cleanup_completed_processes().await?;
        
        let output = Command::new(command)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()?;
        
        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("执行失败: {}", 
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
    
    async fn cleanup_completed_processes(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.process_pool.lock().await;
        processes.retain(|child| {
            child.try_wait().map(|status| status.is_none()).unwrap_or(false)
        });
        Ok(())
    }
}
```

### 7.3 安全实践

```rust
use std::process::{Command, Stdio};
use std::collections::HashSet;

// 安全进程执行器
pub struct SecureProcessExecutor {
    whitelist: HashSet<String>,
    blacklist: HashSet<String>,
    max_execution_time: std::time::Duration,
}

impl SecureProcessExecutor {
    pub fn new() -> Self {
        let mut blacklist = HashSet::new();
        blacklist.insert("rm".to_string());
        blacklist.insert("format".to_string());
        blacklist.insert("del".to_string());
        
        Self {
            whitelist: HashSet::new(),
            blacklist,
            max_execution_time: std::time::Duration::from_secs(30),
        }
    }
    
    pub fn add_to_whitelist(&mut self, command: String) {
        self.whitelist.insert(command);
    }
    
    pub fn execute_securely(
        &self,
        command: &str,
        args: &[String],
    ) -> Result<String, Box<dyn std::error::Error>> {
        // 安全检查
        if !self.is_command_safe(command) {
            return Err(format!("命令 '{}' 被安全策略禁止", command).into());
        }
        
        // 参数安全检查
        if !self.are_args_safe(args) {
            return Err("参数包含不安全内容".into());
        }
        
        let output = Command::new(command)
            .args(args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()?;
        
        if output.status.success() {
            Ok(String::from_utf8_lossy(&output.stdout).to_string())
        } else {
            Err(format!("安全执行失败: {}", 
                String::from_utf8_lossy(&output.stderr)).into())
        }
    }
    
    fn is_command_safe(&self, command: &str) -> bool {
        // 检查黑名单
        if self.blacklist.contains(command) {
            return false;
        }
        
        // 如果有白名单，检查白名单
        if !self.whitelist.is_empty() {
            return self.whitelist.contains(command);
        }
        
        true
    }
    
    fn are_args_safe(&self, args: &[String]) -> bool {
        for arg in args {
            // 检查危险参数
            if arg.contains("..") || arg.contains("~") || arg.starts_with("/") {
                return false;
            }
        }
        true
    }
}
```

## 8. 实战案例

### 8.1 命令行工具开发

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};
use clap::{App, Arg};

// 系统信息收集工具
pub struct SystemInfoCollector {
    commands: Vec<(String, Vec<String>)>,
}

impl SystemInfoCollector {
    pub fn new() -> Self {
        Self {
            commands: vec![
                ("uname".to_string(), vec!["-a".to_string()]),
                ("uptime".to_string(), vec![]),
                ("free".to_string(), vec!["-h".to_string()]),
                ("df".to_string(), vec!["-h".to_string()]),
                ("ps".to_string(), vec!["aux".to_string()]),
            ],
        }
    }
    
    pub fn collect_system_info(&self) -> Result<SystemInfo, Box<dyn std::error::Error>> {
        let mut info = SystemInfo::new();
        
        for (command, args) in &self.commands {
            let output = Command::new(command)
                .args(args)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .output()?;
            
            if output.status.success() {
                let result = String::from_utf8_lossy(&output.stdout).to_string();
                info.add_command_result(command, result);
            } else {
                eprintln!("命令 {} 执行失败", command);
            }
        }
        
        Ok(info)
    }
}

#[derive(Debug)]
pub struct SystemInfo {
    pub uname: Option<String>,
    pub uptime: Option<String>,
    pub memory: Option<String>,
    pub disk: Option<String>,
    pub processes: Option<String>,
}

impl SystemInfo {
    pub fn new() -> Self {
        Self {
            uname: None,
            uptime: None,
            memory: None,
            disk: None,
            processes: None,
        }
    }
    
    pub fn add_command_result(&mut self, command: &str, result: String) {
        match command {
            "uname" => self.uname = Some(result),
            "uptime" => self.uptime = Some(result),
            "free" => self.memory = Some(result),
            "df" => self.disk = Some(result),
            "ps" => self.processes = Some(result),
            _ => {}
        }
    }
}
```

### 8.2 系统管理工具

```rust
use std::process::{Command, Stdio};
use std::collections::HashMap;

// 系统服务管理器
pub struct ServiceManager {
    services: HashMap<String, ServiceInfo>,
}

#[derive(Debug, Clone)]
pub struct ServiceInfo {
    pub name: String,
    pub status: ServiceStatus,
    pub pid: Option<u32>,
    pub memory_usage: Option<u64>,
    pub cpu_usage: Option<f64>,
}

#[derive(Debug, Clone)]
pub enum ServiceStatus {
    Running,
    Stopped,
    Failed,
    Unknown,
}

impl ServiceManager {
    pub fn new() -> Self {
        Self {
            services: HashMap::new(),
        }
    }
    
    pub fn discover_services(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        // 使用 systemctl 发现服务
        let output = Command::new("systemctl")
            .args(&["list-units", "--type=service", "--no-pager"])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()?;
        
        if output.status.success() {
            let output_str = String::from_utf8_lossy(&output.stdout);
            self.parse_systemctl_output(&output_str);
        }
        
        Ok(())
    }
    
    fn parse_systemctl_output(&mut self, output: &str) {
        for line in output.lines() {
            if line.contains(".service") {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 4 {
                    let name = parts[0].to_string();
                    let status = match parts[2] {
                        "active" => ServiceStatus::Running,
                        "inactive" => ServiceStatus::Stopped,
                        "failed" => ServiceStatus::Failed,
                        _ => ServiceStatus::Unknown,
                    };
                    
                    self.services.insert(name.clone(), ServiceInfo {
                        name,
                        status,
                        pid: None,
                        memory_usage: None,
                        cpu_usage: None,
                    });
                }
            }
        }
    }
    
    pub fn get_service_status(&self, service_name: &str) -> Option<&ServiceInfo> {
        self.services.get(service_name)
    }
    
    pub fn start_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = Command::new("systemctl")
            .args(&["start", service_name])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()?;
        
        if output.status.success() {
            println!("服务 {} 启动成功", service_name);
        } else {
            let error = String::from_utf8_lossy(&output.stderr);
            return Err(format!("启动服务失败: {}", error).into());
        }
        
        Ok(())
    }
    
    pub fn stop_service(&self, service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = Command::new("systemctl")
            .args(&["stop", service_name])
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()?;
        
        if output.status.success() {
            println!("服务 {} 停止成功", service_name);
        } else {
            let error = String::from_utf8_lossy(&output.stderr);
            return Err(format!("停止服务失败: {}", error).into());
        }
        
        Ok(())
    }
}
```

### 8.3 批处理系统

```rust
use std::process::{Command, Stdio};
use std::sync::Arc;
use tokio::sync::{Semaphore, Mutex};
use std::collections::VecDeque;

// 批处理任务管理器
pub struct BatchTaskManager {
    task_queue: Arc<Mutex<VecDeque<BatchTask>>>,
    semaphore: Arc<Semaphore>,
    max_concurrent: usize,
    completed_tasks: Arc<Mutex<Vec<BatchTaskResult>>>,
}

#[derive(Debug, Clone)]
pub struct BatchTask {
    pub id: String,
    pub command: String,
    pub args: Vec<String>,
    pub timeout: Option<std::time::Duration>,
    pub retry_count: u32,
    pub priority: u32,
}

#[derive(Debug)]
pub struct BatchTaskResult {
    pub task_id: String,
    pub status: TaskStatus,
    pub output: Option<String>,
    pub error: Option<String>,
    pub execution_time: std::time::Duration,
}

#[derive(Debug)]
pub enum TaskStatus {
    Success,
    Failed,
    Timeout,
    RetryExhausted,
}

impl BatchTaskManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            task_queue: Arc::new(Mutex::new(VecDeque::new())),
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent,
            completed_tasks: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    pub async fn add_task(&self, task: BatchTask) {
        let mut queue = self.task_queue.lock().await;
        queue.push_back(task);
    }
    
    pub async fn start_processing(&self) -> Result<(), Box<dyn std::error::Error>> {
        let mut handles = Vec::new();
        
        for _ in 0..self.max_concurrent {
            let queue = self.task_queue.clone();
            let semaphore = self.semaphore.clone();
            let completed = self.completed_tasks.clone();
            
            let handle = tokio::spawn(async move {
                Self::worker_loop(queue, semaphore, completed).await;
            });
            
            handles.push(handle);
        }
        
        // 等待所有工作线程完成
        for handle in handles {
            handle.await?;
        }
        
        Ok(())
    }
    
    async fn worker_loop(
        queue: Arc<Mutex<VecDeque<BatchTask>>>,
        semaphore: Arc<Semaphore>,
        completed: Arc<Mutex<Vec<BatchTaskResult>>>,
    ) {
        loop {
            let task = {
                let mut queue = queue.lock().await;
                queue.pop_front()
            };
            
            if let Some(task) = task {
                let _permit = semaphore.acquire().await.unwrap();
                let result = Self::execute_task(&task).await;
                
                let mut completed_tasks = completed.lock().await;
                completed_tasks.push(result);
            } else {
                // 没有任务，等待一段时间
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        }
    }
    
    async fn execute_task(task: &BatchTask) -> BatchTaskResult {
        let start_time = std::time::Instant::now();
        
        let output = Command::new(&task.command)
            .args(&task.args)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output();
        
        let execution_time = start_time.elapsed();
        
        match output {
            Ok(output) => {
                if output.status.success() {
                    BatchTaskResult {
                        task_id: task.id.clone(),
                        status: TaskStatus::Success,
                        output: Some(String::from_utf8_lossy(&output.stdout).to_string()),
                        error: None,
                        execution_time,
                    }
                } else {
                    BatchTaskResult {
                        task_id: task.id.clone(),
                        status: TaskStatus::Failed,
                        output: None,
                        error: Some(String::from_utf8_lossy(&output.stderr).to_string()),
                        execution_time,
                    }
                }
            }
            Err(e) => {
                BatchTaskResult {
                    task_id: task.id.clone(),
                    status: TaskStatus::Failed,
                    output: None,
                    error: Some(e.to_string()),
                    execution_time,
                }
            }
        }
    }
    
    pub async fn get_completed_tasks(&self) -> Vec<BatchTaskResult> {
        let completed = self.completed_tasks.lock().await;
        completed.clone()
    }
}
```

## 9. 总结

本章深入解析了 Rust 标准库 `std::process` 模块的所有功能：

### 核心特性

1. **Command 结构体**：强大的进程构建器，支持丰富的配置选项
2. **Child 进程句柄**：完整的进程生命周期管理
3. **Output 输出处理**：灵活的标准输出和错误输出处理
4. **ExitStatus 状态分析**：详细的状态码和信号处理

### 高级功能

1. **进程组管理**：支持进程组的创建、控制和清理
2. **资源限制**：内存、CPU 时间、文件描述符等资源限制
3. **安全执行**：沙箱模式、命令白名单/黑名单等安全特性

### 最佳实践

1. **错误处理**：使用自定义错误类型，提供详细的错误信息
2. **性能优化**：进程池、并发控制、资源清理等优化策略
3. **安全实践**：命令验证、参数检查、资源限制等安全措施

### 实战应用

1. **命令行工具开发**：系统信息收集、服务管理等工具
2. **系统管理工具**：服务管理、进程监控等系统工具
3. **批处理系统**：任务队列、并发执行、结果收集等批处理功能

通过本章的学习，读者可以全面掌握 Rust 标准库进程管理的所有功能，并能够开发出高效、安全、可靠的进程管理应用。
