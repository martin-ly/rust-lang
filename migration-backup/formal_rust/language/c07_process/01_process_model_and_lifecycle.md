# 进程模型与生命周期

## 概述

Rust 的进程模型建立在操作系统原生进程抽象之上，通过类型安全的 API 提供了内存安全和并发安全的进程管理能力。本章深入探讨 Rust 进程模型的设计哲学、生命周期管理机制以及资源控制策略。

## 进程模型基础

### 设计哲学

Rust 的进程模型遵循以下核心原则：

1. **内存安全** - 通过所有权系统确保进程间资源的安全传递
2. **类型安全** - 利用类型系统防止进程间通信的类型错误
3. **零成本抽象** - 在保证安全性的同时最小化运行时开销
4. **跨平台兼容** - 提供统一的 API 适配不同操作系统

### 进程抽象

```rust
use std::process::{Command, Child, ExitStatus};
use std::io::{self, Write};

// 进程创建的基本模式
fn create_process() -> io::Result<Child> {
    Command::new("ls")
        .arg("-la")
        .spawn()
}

// 进程生命周期管理
fn manage_process_lifecycle() -> io::Result<ExitStatus> {
    let mut child = Command::new("sleep")
        .arg("10")
        .spawn()?;
    
    // 等待进程完成
    child.wait()
}
```

## 进程创建与终止

### 进程创建模式

Rust 提供了多种进程创建模式：

#### 1. 基本进程创建

```rust
use std::process::Command;

// 同步执行
fn execute_sync() -> io::Result<()> {
    let output = Command::new("echo")
        .arg("Hello, World!")
        .output()?;
    
    println!("Output: {}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}

// 异步执行
fn execute_async() -> io::Result<Child> {
    Command::new("long_running_process")
        .spawn()
}
```

#### 2. 环境配置

```rust
use std::env;
use std::collections::HashMap;

fn create_with_environment() -> io::Result<Child> {
    let mut env_vars = HashMap::new();
    env_vars.insert("RUST_LOG".to_string(), "debug".to_string());
    env_vars.insert("DATABASE_URL".to_string(), "postgres://localhost/db".to_string());
    
    Command::new("my_app")
        .envs(env_vars.iter())
        .spawn()
}
```

#### 3. 工作目录设置

```rust
fn create_with_working_dir() -> io::Result<Child> {
    Command::new("git")
        .arg("status")
        .current_dir("/path/to/repo")
        .spawn()
}
```

### 进程终止策略

#### 1. 优雅终止

```rust
use std::process::Stdio;

fn graceful_shutdown(mut child: Child) -> io::Result<ExitStatus> {
    // 发送 SIGTERM (Unix) 或 CTRL+C (Windows)
    child.kill()?;
    
    // 等待进程响应终止信号
    child.wait()
}
```

#### 2. 强制终止

```rust
fn force_kill(mut child: Child) -> io::Result<()> {
    // 强制终止进程
    child.kill()?;
    
    // 清理资源
    drop(child);
    Ok(())
}
```

## 资源管理与安全抽象

### 文件描述符管理

```rust
use std::fs::File;
use std::os::unix::io::{AsRawFd, FromRawFd};

fn manage_file_descriptors() -> io::Result<Child> {
    let file = File::open("input.txt")?;
    let fd = file.as_raw_fd();
    
    Command::new("process")
        .stdin(unsafe { Stdio::from_raw_fd(fd) })
        .spawn()
}
```

### 内存映射

```rust
use memmap2::MmapMut;

fn shared_memory_process() -> io::Result<()> {
    // 创建共享内存区域
    let mut mmap = MmapMut::map_anon(1024)?;
    
    // 在共享内存中写入数据
    mmap[0..4].copy_from_slice(b"data");
    
    // 将共享内存传递给子进程
    let child = Command::new("child_process")
        .env("SHARED_MEMORY_SIZE", "1024")
        .spawn()?;
    
    Ok(())
}
```

### 信号处理

```rust
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn signal_handling() -> io::Result<()> {
    let running = Arc::new(AtomicBool::new(true));
    let running_clone = running.clone();
    
    ctrlc::set_handler(move || {
        running_clone.store(false, Ordering::SeqCst);
    })?;
    
    while running.load(Ordering::SeqCst) {
        // 主进程逻辑
        std::thread::sleep(std::time::Duration::from_millis(100));
    }
    
    Ok(())
}
```

## 进程间关系

### 父子进程

```rust
fn parent_child_relationship() -> io::Result<()> {
    let child = Command::new("child_process")
        .spawn()?;
    
    let pid = child.id();
    println!("Child process PID: {}", pid);
    
    // 等待子进程完成
    let status = child.wait()?;
    println!("Child exited with: {}", status);
    
    Ok(())
}
```

### 进程组

```rust
use std::os::unix::process::CommandExt;

fn process_group_management() -> io::Result<()> {
    // 创建新的进程组
    let child = Command::new("daemon_process")
        .process_group(0) // 创建新的进程组
        .spawn()?;
    
    Ok(())
}
```

## 安全抽象与错误处理

### 类型安全的进程句柄

```rust
use std::process::{Child, ChildStdin, ChildStdout, ChildStderr};

struct ProcessHandle {
    child: Child,
    stdin: Option<ChildStdin>,
    stdout: Option<ChildStdout>,
    stderr: Option<ChildStderr>,
}

impl ProcessHandle {
    fn new(mut child: Child) -> io::Result<Self> {
        let stdin = child.stdin.take();
        let stdout = child.stdout.take();
        let stderr = child.stderr.take();
        
        Ok(ProcessHandle {
            child,
            stdin,
            stdout,
            stderr,
        })
    }
    
    fn write_stdin(&mut self, data: &[u8]) -> io::Result<()> {
        if let Some(ref mut stdin) = self.stdin {
            stdin.write_all(data)?;
        }
        Ok(())
    }
    
    fn read_stdout(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        if let Some(ref mut stdout) = self.stdout {
            stdout.read(buffer)
        } else {
            Ok(0)
        }
    }
}
```

### 错误处理策略

```rust
use std::error::Error;

#[derive(Debug)]
enum ProcessError {
    SpawnFailed(io::Error),
    ExecutionFailed(ExitStatus),
    CommunicationFailed(io::Error),
}

impl std::fmt::Display for ProcessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProcessError::SpawnFailed(e) => write!(f, "Failed to spawn process: {}", e),
            ProcessError::ExecutionFailed(status) => write!(f, "Process execution failed: {}", status),
            ProcessError::CommunicationFailed(e) => write!(f, "Process communication failed: {}", e),
        }
    }
}

impl Error for ProcessError {}

fn robust_process_execution() -> Result<(), ProcessError> {
    let child = Command::new("critical_process")
        .spawn()
        .map_err(ProcessError::SpawnFailed)?;
    
    let status = child.wait()
        .map_err(|e| ProcessError::CommunicationFailed(e))?;
    
    if !status.success() {
        return Err(ProcessError::ExecutionFailed(status));
    }
    
    Ok(())
}
```

## 性能优化

### 进程池模式

```rust
use std::sync::mpsc;
use std::thread;

struct ProcessPool {
    workers: Vec<thread::JoinHandle<()>>,
    sender: mpsc::Sender<ProcessTask>,
}

struct ProcessTask {
    command: String,
    args: Vec<String>,
    callback: Box<dyn FnOnce(io::Result<ExitStatus>) + Send>,
}

impl ProcessPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = std::sync::Arc::new(std::sync::Mutex::new(receiver));
        
        let mut workers = Vec::new();
        for _ in 0..size {
            let receiver = receiver.clone();
            workers.push(thread::spawn(move || {
                while let Ok(task) = receiver.lock().unwrap().recv() {
                    let result = Command::new(&task.command)
                        .args(&task.args)
                        .status();
                    (task.callback)(result);
                }
            }));
        }
        
        ProcessPool { workers, sender }
    }
    
    fn execute<F>(&self, command: String, args: Vec<String>, callback: F)
    where
        F: FnOnce(io::Result<ExitStatus>) + Send + 'static,
    {
        let task = ProcessTask {
            command,
            args,
            callback: Box::new(callback),
        };
        self.sender.send(task).unwrap();
    }
}
```

## 总结

Rust 的进程模型通过类型安全的抽象提供了强大的进程管理能力。通过所有权系统、错误处理机制和零成本抽象，Rust 确保了进程间通信的安全性和效率。本章介绍的基础概念为后续章节的进程间通信和同步机制奠定了重要基础。

### 关键要点

1. **类型安全** - Rust 的类型系统确保进程间通信的安全性
2. **资源管理** - 通过所有权系统自动管理进程资源
3. **错误处理** - 全面的错误处理机制确保系统稳定性
4. **性能优化** - 零成本抽象和进程池模式提升性能

### 下一步

在下一章中，我们将深入探讨进程间通信的各种机制，包括管道、共享内存、消息队列和套接字通信。
