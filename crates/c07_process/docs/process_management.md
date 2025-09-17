# 进程管理详解

本文档详细介绍 Rust 中的进程管理，包括进程创建、子进程管理、进程间通信等核心概念。

## 目录

- [进程基础](#进程基础)
- [进程创建与执行](#进程创建与执行)
- [子进程管理](#子进程管理)
- [进程间通信](#进程间通信)
- [环境变量管理](#环境变量管理)
- [信号处理](#信号处理)
- [进程监控](#进程监控)
- [最佳实践](#最佳实践)

## 进程基础

### 进程概念

进程是操作系统进行资源分配和调度的基本单位。在 Rust 中，我们可以通过 `std::process` 模块来管理进程。

```rust
use std::process;

fn main() {
    println!("Current process ID: {}", process::id());
    
    // 获取当前进程的命令行参数
    let args: Vec<String> = std::env::args().collect();
    println!("Arguments: {:?}", args);
    
    // 获取环境变量
    for (key, value) in std::env::vars() {
        println!("{}: {}", key, value);
    }
}
```

### 进程状态

```rust
use std::process::{Command, ExitStatus};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new("echo")
        .arg("Hello, World!")
        .output()?;
    
    println!("Status: {:?}", output.status);
    println!("Stdout: {}", String::from_utf8_lossy(&output.stdout));
    println!("Stderr: {}", String::from_utf8_lossy(&output.stderr));
    
    Ok(())
}
```

## 进程创建与执行

### 基本命令执行

```rust
use std::process::Command;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 执行简单命令
    let output = Command::new("ls")
        .arg("-la")
        .output()?;
    
    if output.status.success() {
        println!("Output: {}", String::from_utf8_lossy(&output.stdout));
    } else {
        println!("Error: {}", String::from_utf8_lossy(&output.stderr));
    }
    
    Ok(())
}
```

### 异步命令执行

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("ping")
        .arg("google.com")
        .arg("-c")
        .arg("4")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    // 读取输出
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            println!("{}", line?);
        }
    }
    
    // 等待进程完成
    let status = child.wait()?;
    println!("Process exited with status: {:?}", status);
    
    Ok(())
}
```

### 命令链式调用

```rust
use std::process::{Command, Stdio};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 使用管道连接命令
    let output = Command::new("sh")
        .arg("-c")
        .arg("echo 'Hello World' | wc -w")
        .output()?;
    
    println!("Word count: {}", String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}
```

## 子进程管理

### 子进程生命周期

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("sleep")
        .arg("10")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    println!("Child process started with PID: {}", child.id());
    
    // 在另一个线程中等待
    let child_id = child.id();
    thread::spawn(move || {
        thread::sleep(Duration::from_secs(2));
        println!("Checking if process {} is still running...", child_id);
    });
    
    // 等待子进程完成
    let status = child.wait()?;
    println!("Child process exited with status: {:?}", status);
    
    Ok(())
}
```

### 进程终止

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("sleep")
        .arg("30")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    println!("Child process started with PID: {}", child.id());
    
    // 等待一段时间后终止子进程
    thread::sleep(Duration::from_secs(2));
    
    // 尝试优雅终止
    if let Err(e) = child.kill() {
        println!("Failed to kill child process: {}", e);
    } else {
        println!("Child process terminated");
    }
    
    // 等待进程实际退出
    let status = child.wait()?;
    println!("Final status: {:?}", status);
    
    Ok(())
}
```

### 进程组管理

```rust
use std::process::{Command, Stdio};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建新的进程组
    let mut child = Command::new("sh")
        .arg("-c")
        .arg("sleep 10 & sleep 10 & wait")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    println!("Process group started with PID: {}", child.id());
    
    // 等待进程组完成
    let status = child.wait()?;
    println!("Process group exited with status: {:?}", status);
    
    Ok(())
}
```

## 进程间通信

### 管道通信

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader, Write};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建管道
    let mut child = Command::new("grep")
        .arg("hello")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    // 向子进程写入数据
    if let Some(stdin) = child.stdin.as_mut() {
        stdin.write_all(b"hello world\nhi there\nhello rust\n")?;
    }
    
    // 读取子进程输出
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            println!("Filtered: {}", line?);
        }
    }
    
    let status = child.wait()?;
    println!("Grep process exited with status: {:?}", status);
    
    Ok(())
}
```

### 命名管道

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader, Write};
use std::fs::File;
use std::os::unix::net::UnixStream;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建命名管道
    let pipe_path = "/tmp/rust_pipe";
    
    // 创建写入端
    let mut writer = Command::new("sh")
        .arg("-c")
        .arg(&format!("mkfifo {} && echo 'Hello from pipe' > {}", pipe_path, pipe_path))
        .spawn()?;
    
    writer.wait()?;
    
    // 创建读取端
    let mut reader = Command::new("cat")
        .arg(pipe_path)
        .stdout(Stdio::piped())
        .spawn()?;
    
    // 读取数据
    if let Some(stdout) = reader.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            println!("Received: {}", line?);
        }
    }
    
    reader.wait()?;
    
    // 清理
    std::fs::remove_file(pipe_path)?;
    
    Ok(())
}
```

### 共享内存

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建共享内存段
    let shm_name = "/rust_shm";
    
    // 写入进程
    let mut writer = Command::new("sh")
        .arg("-c")
        .arg(&format!("echo 'Shared data' > {}", shm_name))
        .spawn()?;
    
    writer.wait()?;
    
    // 读取进程
    let mut reader = Command::new("cat")
        .arg(shm_name)
        .stdout(Stdio::piped())
        .spawn()?;
    
    if let Some(stdout) = reader.stdout.take() {
        let reader = std::io::BufReader::new(stdout);
        for line in reader.lines() {
            println!("Shared data: {}", line?);
        }
    }
    
    reader.wait()?;
    
    // 清理
    std::fs::remove_file(shm_name)?;
    
    Ok(())
}
```

## 环境变量管理

### 环境变量操作

```rust
use std::process::Command;
use std::env;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 获取环境变量
    let path = env::var("PATH")?;
    println!("PATH: {}", path);
    
    // 设置环境变量
    env::set_var("RUST_LOG", "debug");
    
    // 在子进程中设置环境变量
    let output = Command::new("env")
        .env("CUSTOM_VAR", "custom_value")
        .output()?;
    
    let env_output = String::from_utf8_lossy(&output.stdout);
    if env_output.contains("CUSTOM_VAR=custom_value") {
        println!("Environment variable set successfully");
    }
    
    Ok(())
}
```

### 环境变量继承

```rust
use std::process::Command;
use std::env;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 设置环境变量
    env::set_var("PARENT_VAR", "parent_value");
    
    // 子进程继承环境变量
    let output = Command::new("env")
        .output()?;
    
    let env_output = String::from_utf8_lossy(&output.stdout);
    if env_output.contains("PARENT_VAR=parent_value") {
        println!("Environment variable inherited successfully");
    }
    
    // 清除环境变量
    env::remove_var("PARENT_VAR");
    
    Ok(())
}
```

## 信号处理

### 基本信号处理

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("sleep")
        .arg("30")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    println!("Child process started with PID: {}", child.id());
    
    // 等待一段时间
    thread::sleep(Duration::from_secs(2));
    
    // 发送 SIGTERM 信号
    if let Err(e) = child.kill() {
        println!("Failed to send signal: {}", e);
    } else {
        println!("Signal sent successfully");
    }
    
    // 等待进程退出
    let status = child.wait()?;
    println!("Process exited with status: {:?}", status);
    
    Ok(())
}
```

### 信号处理程序

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建长时间运行的进程
    let mut child = Command::new("sh")
        .arg("-c")
        .arg("trap 'echo Signal received; exit 0' SIGTERM; while true; do sleep 1; done")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    println!("Child process started with PID: {}", child.id());
    
    // 等待一段时间
    thread::sleep(Duration::from_secs(2));
    
    // 发送信号
    if let Err(e) = child.kill() {
        println!("Failed to send signal: {}", e);
    }
    
    // 读取输出
    if let Some(stdout) = child.stdout.take() {
        let reader = std::io::BufReader::new(stdout);
        for line in reader.lines() {
            println!("Child output: {}", line?);
        }
    }
    
    let status = child.wait()?;
    println!("Process exited with status: {:?}", status);
    
    Ok(())
}
```

## 进程监控

### 进程状态监控

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("sleep")
        .arg("10")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    let child_id = child.id();
    println!("Monitoring process {}", child_id);
    
    // 监控进程状态
    let monitor_thread = thread::spawn(move || {
        for i in 1..=5 {
            thread::sleep(Duration::from_secs(1));
            println!("Process {} still running... ({}s)", child_id, i);
        }
    });
    
    // 等待进程完成
    let status = child.wait()?;
    monitor_thread.join().unwrap();
    
    println!("Process {} exited with status: {:?}", child_id, status);
    
    Ok(())
}
```

### 资源使用监控

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("sh")
        .arg("-c")
        .arg("while true; do echo 'Working...'; sleep 1; done")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    let child_id = child.id();
    println!("Monitoring resource usage for process {}", child_id);
    
    // 监控资源使用
    let monitor_thread = thread::spawn(move || {
        for i in 1..=3 {
            thread::sleep(Duration::from_secs(2));
            
            // 使用 ps 命令监控资源使用
            let output = Command::new("ps")
                .arg("-p")
                .arg(&child_id.to_string())
                .arg("-o")
                .arg("pid,ppid,pcpu,pmem,comm")
                .output();
            
            if let Ok(output) = output {
                let ps_output = String::from_utf8_lossy(&output.stdout);
                println!("Resource usage ({}s):\n{}", i * 2, ps_output);
            }
        }
    });
    
    // 等待一段时间后终止进程
    thread::sleep(Duration::from_secs(6));
    child.kill()?;
    
    monitor_thread.join().unwrap();
    child.wait()?;
    
    println!("Monitoring completed");
    
    Ok(())
}
```

## 最佳实践

### 1. 错误处理

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader};

fn run_command_safely() -> Result<String, Box<dyn std::error::Error>> {
    let output = Command::new("ls")
        .arg("-la")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()?;
    
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    } else {
        Err(format!("Command failed: {}", String::from_utf8_lossy(&output.stderr)).into())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    match run_command_safely() {
        Ok(output) => println!("Command output:\n{}", output),
        Err(e) => println!("Error: {}", e),
    }
    
    Ok(())
}
```

### 2. 超时处理

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::time::Duration;

fn run_with_timeout(timeout: Duration) -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("sleep")
        .arg("30")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    
    let child_id = child.id();
    
    // 超时处理
    let timeout_thread = thread::spawn(move || {
        thread::sleep(timeout);
        println!("Timeout reached, terminating process {}", child_id);
    });
    
    // 等待进程完成或超时
    let status = child.wait()?;
    timeout_thread.join().unwrap();
    
    println!("Process exited with status: {:?}", status);
    
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    run_with_timeout(Duration::from_secs(5))?;
    Ok(())
}
```

### 3. 进程池管理

```rust
use std::process::{Command, Stdio};
use std::thread;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

struct ProcessPool {
    processes: Arc<Mutex<VecDeque<std::process::Child>>>,
    max_processes: usize,
}

impl ProcessPool {
    fn new(max_processes: usize) -> Self {
        Self {
            processes: Arc::new(Mutex::new(VecDeque::new())),
            max_processes,
        }
    }
    
    fn execute(&self, command: &str) -> Result<(), Box<dyn std::error::Error>> {
        let mut processes = self.processes.lock().unwrap();
        
        // 清理已完成的进程
        processes.retain(|child| {
            match child.try_wait() {
                Ok(Some(_)) => false, // 进程已完成
                Ok(None) => true,     // 进程仍在运行
                Err(_) => false,      // 错误，移除进程
            }
        });
        
        // 检查进程数量限制
        if processes.len() >= self.max_processes {
            return Err("Process pool is full".into());
        }
        
        // 启动新进程
        let child = Command::new("sh")
            .arg("-c")
            .arg(command)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?;
        
        processes.push_back(child);
        
        Ok(())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let pool = ProcessPool::new(3);
    
    // 执行多个任务
    for i in 1..=5 {
        match pool.execute(&format!("echo 'Task {}' && sleep 2", i)) {
            Ok(_) => println!("Task {} started", i),
            Err(e) => println!("Failed to start task {}: {}", i, e),
        }
        
        thread::sleep(Duration::from_millis(500));
    }
    
    // 等待所有任务完成
    thread::sleep(Duration::from_secs(10));
    
    Ok(())
}
```

### 4. 安全考虑

```rust
use std::process::{Command, Stdio};

fn secure_command_execution() -> Result<(), Box<dyn std::error::Error>> {
    // 验证输入
    let user_input = "ls -la";
    let allowed_commands = ["ls", "pwd", "whoami"];
    
    let parts: Vec<&str> = user_input.split_whitespace().collect();
    if parts.is_empty() || !allowed_commands.contains(&parts[0]) {
        return Err("Command not allowed".into());
    }
    
    // 安全执行命令
    let output = Command::new(parts[0])
        .args(&parts[1..])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()?;
    
    if output.status.success() {
        println!("Output: {}", String::from_utf8_lossy(&output.stdout));
    } else {
        println!("Error: {}", String::from_utf8_lossy(&output.stderr));
    }
    
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    secure_command_execution()?;
    Ok(())
}
```

## 相关主题

- [系统调用与底层接口](./system_calls.md)
- [进程间通信进阶](./advanced_ipc.md)
- [进程监控与调试](./process_monitoring.md)
- [跨平台进程管理](./cross_platform.md)
