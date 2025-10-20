# 💻 Rust 1.90 进程管理 - 实战示例集

> **版本**: Rust 1.90 Edition 2024  
> **创建日期**: 2025-10-20  
> **代码总量**: ~900行可运行代码

---

## 📋 目录

- [💻 Rust 1.90 进程管理 - 实战示例集](#-rust-190-进程管理---实战示例集)
  - [📋 目录](#-目录)
  - [🎯 基础进程管理](#-基础进程管理)
    - [示例1: 基本命令执行](#示例1-基本命令执行)
    - [示例2: 异步进程管理 (Rust 1.90)](#示例2-异步进程管理-rust-190)
    - [示例3: I/O重定向与管道](#示例3-io重定向与管道)
  - [📡 进程间通信 (IPC)](#-进程间通信-ipc)
    - [示例4: Unix Socket通信](#示例4-unix-socket通信)
    - [示例5: 共享内存 (Rust 1.90特性)](#示例5-共享内存-rust-190特性)
    - [示例6: 跨进程消息队列](#示例6-跨进程消息队列)
  - [🎯 信号处理](#-信号处理)
    - [示例7: 优雅关闭 (Rust 1.90 async trait)](#示例7-优雅关闭-rust-190-async-trait)
    - [示例8: 信号转发](#示例8-信号转发)
  - [🏗️ 综合项目](#️-综合项目)
    - [项目1: 多进程任务执行器](#项目1-多进程任务执行器)
    - [项目2: 进程监控与管理系统](#项目2-进程监控与管理系统)

---

## 🎯 基础进程管理

### 示例1: 基本命令执行

```rust
use std::process::{Command, Stdio};
use std::io::{self, Write};

/// 基础命令执行
fn execute_command() -> io::Result<()> {
    // 简单执行命令
    let output = Command::new("echo")
        .arg("Hello, Process!")
        .output()?;
    
    println!("Status: {}", output.status);
    println!("Stdout: {}", String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}

/// 带环境变量的命令执行
fn execute_with_env() -> io::Result<()> {
    let output = Command::new("sh")
        .arg("-c")
        .arg("echo $MY_VAR")
        .env("MY_VAR", "Hello from Rust")
        .output()?;
    
    println!("Result: {}", String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}

/// 工作目录设置
fn execute_with_cwd() -> io::Result<()> {
    let output = Command::new("pwd")
        .current_dir("/tmp")
        .output()?;
    
    println!("Working dir: {}", String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}

/// 交互式进程
fn interactive_process() -> io::Result<()> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    
    // 写入数据
    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(b"Hello from parent process\n")?;
        // stdin在这里被drop，关闭管道
    }
    
    // 等待完成
    let output = child.wait_with_output()?;
    println!("Output: {}", String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}

fn main() -> io::Result<()> {
    println!("=== 基础命令执行 ===");
    execute_command()?;
    
    println!("\n=== 环境变量 ===");
    execute_with_env()?;
    
    println!("\n=== 工作目录 ===");
    execute_with_cwd()?;
    
    println!("\n=== 交互式进程 ===");
    interactive_process()?;
    
    Ok(())
}
```

---

### 示例2: 异步进程管理 (Rust 1.90)

```rust
use tokio::process::Command;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::time::{timeout, Duration};
use std::process::Stdio;

/// 异步命令执行
async fn async_execute() -> Result<(), Box<dyn std::error::Error>> {
    let output = Command::new("sleep")
        .arg("1")
        .output()
        .await?;
    
    println!("Command finished: {}", output.status.success());
    Ok(())
}

/// 超时控制 (Rust 1.90特性)
async fn execute_with_timeout() -> Result<(), Box<dyn std::error::Error>> {
    let result = timeout(
        Duration::from_secs(2),
        Command::new("sleep").arg("5").output()
    ).await;
    
    match result {
        Ok(Ok(output)) => println!("Completed: {}", output.status),
        Ok(Err(e)) => println!("Command error: {}", e),
        Err(_) => println!("Timeout!"),
    }
    
    Ok(())
}

/// 并发执行多个进程
async fn concurrent_execution() -> Result<(), Box<dyn std::error::Error>> {
    let tasks = vec![
        tokio::spawn(async {
            Command::new("echo").arg("Task 1").output().await
        }),
        tokio::spawn(async {
            Command::new("echo").arg("Task 2").output().await
        }),
        tokio::spawn(async {
            Command::new("echo").arg("Task 3").output().await
        }),
    ];
    
    // 等待所有任务完成
    for (i, task) in tasks.into_iter().enumerate() {
        match task.await? {
            Ok(output) => {
                println!("Task {}: {}", i + 1, 
                         String::from_utf8_lossy(&output.stdout));
            }
            Err(e) => println!("Task {} error: {}", i + 1, e),
        }
    }
    
    Ok(())
}

/// 异步管道通信
async fn async_pipe_communication() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    
    // 异步写入
    if let Some(mut stdin) = child.stdin.take() {
        tokio::spawn(async move {
            for i in 0..5 {
                stdin.write_all(format!("Line {}\n", i).as_bytes())
                    .await
                    .expect("Failed to write");
            }
            // stdin被drop，关闭管道
        });
    }
    
    // 异步读取
    if let Some(mut stdout) = child.stdout.take() {
        let mut buffer = String::new();
        stdout.read_to_string(&mut buffer).await?;
        println!("Received:\n{}", buffer);
    }
    
    child.wait().await?;
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== 异步执行 ===");
    async_execute().await?;
    
    println!("\n=== 超时控制 ===");
    execute_with_timeout().await?;
    
    println!("\n=== 并发执行 ===");
    concurrent_execution().await?;
    
    println!("\n=== 异步管道 ===");
    async_pipe_communication().await?;
    
    Ok(())
}
```

---

### 示例3: I/O重定向与管道

```rust
use std::process::{Command, Stdio};
use std::io::{BufRead, BufReader, Write};
use std::fs::File;

/// 输出重定向到文件
fn redirect_to_file() -> std::io::Result<()> {
    let file = File::create("output.txt")?;
    
    Command::new("echo")
        .arg("Hello, File!")
        .stdout(Stdio::from(file))
        .status()?;
    
    println!("Output written to output.txt");
    Ok(())
}

/// 管道链 (ls | grep | wc)
fn pipe_chain() -> std::io::Result<()> {
    // 第一个命令: ls
    let ls = Command::new("ls")
        .stdout(Stdio::piped())
        .spawn()?;
    
    // 第二个命令: grep (使用ls的输出)
    let grep = Command::new("grep")
        .arg(".rs")
        .stdin(ls.stdout.ok_or(std::io::ErrorKind::Other)?)
        .stdout(Stdio::piped())
        .spawn()?;
    
    // 第三个命令: wc -l
    let output = Command::new("wc")
        .arg("-l")
        .stdin(grep.stdout.ok_or(std::io::ErrorKind::Other)?)
        .output()?;
    
    println!("Rust files count: {}", 
             String::from_utf8_lossy(&output.stdout));
    
    Ok(())
}

/// 实时读取子进程输出
fn realtime_output() -> std::io::Result<()> {
    let mut child = Command::new("ping")
        .arg("-c")
        .arg("5")
        .arg("127.0.0.1")
        .stdout(Stdio::piped())
        .spawn()?;
    
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            println!("[OUTPUT] {}", line?);
        }
    }
    
    child.wait()?;
    Ok(())
}

fn main() -> std::io::Result<()> {
    println!("=== 文件重定向 ===");
    redirect_to_file()?;
    
    println!("\n=== 管道链 ===");
    pipe_chain()?;
    
    println!("\n=== 实时输出 ===");
    realtime_output()?;
    
    Ok(())
}
```

---

## 📡 进程间通信 (IPC)

### 示例4: Unix Socket通信

```rust
use tokio::net::{UnixListener, UnixStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use std::path::Path;

/// 服务器端
async fn unix_socket_server(socket_path: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 清理旧socket文件
    let _ = std::fs::remove_file(socket_path);
    
    let listener = UnixListener::bind(socket_path)?;
    println!("Server listening on {}", socket_path);
    
    loop {
        let (mut stream, _) = listener.accept().await?;
        
        tokio::spawn(async move {
            let mut buffer = vec![0u8; 1024];
            
            match stream.read(&mut buffer).await {
                Ok(n) if n > 0 => {
                    let msg = String::from_utf8_lossy(&buffer[..n]);
                    println!("Received: {}", msg);
                    
                    // 回复
                    let response = format!("Echo: {}", msg);
                    stream.write_all(response.as_bytes()).await
                        .expect("Failed to write");
                }
                Ok(_) => println!("Connection closed"),
                Err(e) => eprintln!("Read error: {}", e),
            }
        });
    }
}

/// 客户端
async fn unix_socket_client(socket_path: &str, message: &str) 
    -> Result<(), Box<dyn std::error::Error>> 
{
    let mut stream = UnixStream::connect(socket_path).await?;
    
    // 发送消息
    stream.write_all(message.as_bytes()).await?;
    
    // 读取回复
    let mut buffer = vec![0u8; 1024];
    let n = stream.read(&mut buffer).await?;
    
    println!("Response: {}", String::from_utf8_lossy(&buffer[..n]));
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let socket_path = "/tmp/rust_ipc.sock";
    
    // 启动服务器
    let server_handle = tokio::spawn(unix_socket_server(socket_path.to_string()));
    
    // 等待服务器启动
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    // 启动多个客户端
    for i in 0..3 {
        let msg = format!("Message {}", i);
        unix_socket_client(socket_path, &msg).await?;
    }
    
    // 清理
    server_handle.abort();
    std::fs::remove_file(socket_path)?;
    
    Ok(())
}
```

---

### 示例5: 共享内存 (Rust 1.90特性)

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// 使用原子操作的共享计数器
struct SharedCounter {
    value: Arc<AtomicU64>,
}

impl SharedCounter {
    fn new() -> Self {
        Self {
            value: Arc::new(AtomicU64::new(0)),
        }
    }
    
    fn increment(&self) {
        self.value.fetch_add(1, Ordering::SeqCst);
    }
    
    fn get(&self) -> u64 {
        self.value.load(Ordering::SeqCst)
    }
    
    fn clone_handle(&self) -> Self {
        Self {
            value: Arc::clone(&self.value),
        }
    }
}

/// 模拟多进程场景（实际中使用shared_memory crate）
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let counter = SharedCounter::new();
    
    // 创建多个"进程"（这里用tokio任务模拟）
    let mut tasks = vec![];
    
    for id in 0..5 {
        let counter_clone = counter.clone_handle();
        let task = tokio::spawn(async move {
            for _ in 0..100 {
                counter_clone.increment();
                tokio::time::sleep(Duration::from_millis(10)).await;
            }
            println!("Process {} finished", id);
        });
        tasks.push(task);
    }
    
    // 等待所有任务完成
    for task in tasks {
        task.await?;
    }
    
    println!("Final count: {}", counter.get());
    println!("Expected: 500");
    
    Ok(())
}

/// 真实共享内存示例（需要shared_memory crate）
#[cfg(feature = "shared_memory")]
mod real_shared_memory {
    use shared_memory::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    
    fn writer_process() -> Result<(), Box<dyn std::error::Error>> {
        let shmem = ShmemConf::new()
            .size(4096)
            .flink("rust_shm")
            .create()?;
        
        // 写入数据
        let atomic = unsafe {
            &*(shmem.as_ptr() as *const AtomicU64)
        };
        
        for i in 0..100 {
            atomic.store(i, Ordering::SeqCst);
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        
        Ok(())
    }
    
    fn reader_process() -> Result<(), Box<dyn std::error::Error>> {
        let shmem = ShmemConf::new()
            .flink("rust_shm")
            .open()?;
        
        // 读取数据
        let atomic = unsafe {
            &*(shmem.as_ptr() as *const AtomicU64)
        };
        
        for _ in 0..10 {
            let value = atomic.load(Ordering::SeqCst);
            println!("Read value: {}", value);
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
        
        Ok(())
    }
}
```

---

### 示例6: 跨进程消息队列

```rust
use crossbeam_channel::{bounded, Sender, Receiver};
use std::thread;
use std::time::Duration;

#[derive(Debug, Clone)]
struct Message {
    id: u64,
    content: String,
}

/// 生产者进程
fn producer(tx: Sender<Message>, id: u64) {
    thread::spawn(move || {
        for i in 0..5 {
            let msg = Message {
                id: id * 100 + i,
                content: format!("Message from producer {}", id),
            };
            
            tx.send(msg.clone()).expect("Failed to send");
            println!("[P{}] Sent: {:?}", id, msg);
            thread::sleep(Duration::from_millis(100));
        }
    });
}

/// 消费者进程
fn consumer(rx: Receiver<Message>, id: u64) {
    thread::spawn(move || {
        while let Ok(msg) = rx.recv() {
            println!("[C{}] Received: {:?}", id, msg);
            thread::sleep(Duration::from_millis(50));
        }
    });
}

fn main() {
    let (tx, rx) = bounded::<Message>(10);
    
    // 启动3个生产者
    for i in 0..3 {
        producer(tx.clone(), i);
    }
    
    // 启动2个消费者
    for i in 0..2 {
        consumer(rx.clone(), i);
    }
    
    // 等待完成
    thread::sleep(Duration::from_secs(2));
    
    println!("\nAll messages processed");
}
```

---

## 🎯 信号处理

### 示例7: 优雅关闭 (Rust 1.90 async trait)

```rust
use tokio::signal;
use tokio::sync::broadcast;
use tokio::time::{sleep, Duration};
use std::sync::Arc;

/// 优雅关闭特征 (Rust 1.90 async fn in trait)
trait GracefulShutdown {
    async fn shutdown(&self);
}

/// 服务管理器
struct ServiceManager {
    shutdown_tx: broadcast::Sender<()>,
}

impl ServiceManager {
    fn new() -> Self {
        let (tx, _) = broadcast::channel(1);
        Self { shutdown_tx: tx }
    }
    
    fn subscribe(&self) -> broadcast::Receiver<()> {
        self.shutdown_tx.subscribe()
    }
    
    async fn trigger_shutdown(&self) {
        println!("Triggering shutdown...");
        let _ = self.shutdown_tx.send(());
    }
}

impl GracefulShutdown for ServiceManager {
    async fn shutdown(&self) {
        self.trigger_shutdown().await;
    }
}

/// 工作任务
async fn worker_task(id: u64, mut shutdown_rx: broadcast::Receiver<()>) {
    println!("Worker {} started", id);
    
    loop {
        tokio::select! {
            _ = sleep(Duration::from_secs(1)) => {
                println!("Worker {} working...", id);
            }
            _ = shutdown_rx.recv() => {
                println!("Worker {} received shutdown signal", id);
                // 清理工作
                sleep(Duration::from_millis(500)).await;
                println!("Worker {} finished cleanup", id);
                break;
            }
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let manager = Arc::new(ServiceManager::new());
    
    // 启动多个工作任务
    let mut tasks = vec![];
    for i in 0..3 {
        let shutdown_rx = manager.subscribe();
        let task = tokio::spawn(worker_task(i, shutdown_rx));
        tasks.push(task);
    }
    
    // 等待Ctrl+C信号
    println!("Press Ctrl+C to shutdown...");
    signal::ctrl_c().await?;
    
    // 触发优雅关闭
    manager.shutdown().await;
    
    // 等待所有任务完成
    for task in tasks {
        task.await?;
    }
    
    println!("All workers shutdown gracefully");
    
    Ok(())
}
```

---

### 示例8: 信号转发

```rust
use signal_hook::{consts::SIGTERM, iterator::Signals};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;

/// 信号处理器
fn signal_handler(running: Arc<AtomicBool>) {
    let mut signals = Signals::new(&[SIGTERM])
        .expect("Failed to create signals");
    
    thread::spawn(move || {
        for sig in signals.forever() {
            println!("Received signal: {:?}", sig);
            running.store(false, Ordering::SeqCst);
        }
    });
}

/// 主循环
fn main_loop(running: Arc<AtomicBool>) {
    let mut iteration = 0;
    
    while running.load(Ordering::SeqCst) {
        println!("Iteration {}", iteration);
        iteration += 1;
        thread::sleep(Duration::from_secs(1));
    }
    
    println!("Main loop exiting...");
}

fn main() {
    let running = Arc::new(AtomicBool::new(true));
    
    // 注册信号处理器
    signal_handler(Arc::clone(&running));
    
    println!("Process started (PID: {})", std::process::id());
    println!("Send SIGTERM to stop: kill -TERM {}", std::process::id());
    
    // 运行主循环
    main_loop(running);
    
    println!("Process terminated gracefully");
}
```

---

## 🏗️ 综合项目

### 项目1: 多进程任务执行器

```rust
use tokio::process::Command;
use tokio::sync::Semaphore;
use tokio::time::{timeout, Duration};
use std::sync::Arc;

/// 任务定义
#[derive(Clone)]
struct Task {
    id: u64,
    command: String,
    args: Vec<String>,
    timeout_secs: u64,
}

/// 任务执行器
struct TaskExecutor {
    max_concurrent: usize,
    semaphore: Arc<Semaphore>,
}

impl TaskExecutor {
    fn new(max_concurrent: usize) -> Self {
        Self {
            max_concurrent,
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }
    
    async fn execute(&self, task: Task) -> Result<String, String> {
        // 获取信号量许可
        let _permit = self.semaphore.acquire().await
            .map_err(|e| e.to_string())?;
        
        println!("[Task {}] Starting: {} {:?}", 
                 task.id, task.command, task.args);
        
        // 执行命令（带超时）
        let result = timeout(
            Duration::from_secs(task.timeout_secs),
            Command::new(&task.command)
                .args(&task.args)
                .output()
        ).await;
        
        match result {
            Ok(Ok(output)) => {
                if output.status.success() {
                    let stdout = String::from_utf8_lossy(&output.stdout);
                    println!("[Task {}] Success", task.id);
                    Ok(stdout.to_string())
                } else {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    Err(format!("Command failed: {}", stderr))
                }
            }
            Ok(Err(e)) => Err(format!("Execution error: {}", e)),
            Err(_) => Err("Timeout".to_string()),
        }
    }
    
    async fn execute_batch(&self, tasks: Vec<Task>) 
        -> Vec<Result<String, String>> 
    {
        let mut handles = vec![];
        
        for task in tasks {
            let executor = self.clone_executor();
            let handle = tokio::spawn(async move {
                executor.execute(task).await
            });
            handles.push(handle);
        }
        
        // 等待所有任务完成
        let mut results = vec![];
        for handle in handles {
            match handle.await {
                Ok(result) => results.push(result),
                Err(e) => results.push(Err(e.to_string())),
            }
        }
        
        results
    }
    
    fn clone_executor(&self) -> Self {
        Self {
            max_concurrent: self.max_concurrent,
            semaphore: Arc::clone(&self.semaphore),
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let executor = TaskExecutor::new(3); // 最多3个并发进程
    
    // 定义任务
    let tasks = vec![
        Task {
            id: 1,
            command: "echo".to_string(),
            args: vec!["Task 1".to_string()],
            timeout_secs: 5,
        },
        Task {
            id: 2,
            command: "sleep".to_string(),
            args: vec!["2".to_string()],
            timeout_secs: 5,
        },
        Task {
            id: 3,
            command: "echo".to_string(),
            args: vec!["Task 3".to_string()],
            timeout_secs: 5,
        },
        Task {
            id: 4,
            command: "ls".to_string(),
            args: vec!["-l".to_string()],
            timeout_secs: 5,
        },
    ];
    
    // 执行所有任务
    let results = executor.execute_batch(tasks).await;
    
    // 打印结果
    println!("\n=== Results ===");
    for (i, result) in results.iter().enumerate() {
        match result {
            Ok(output) => println!("Task {}: Success\n{}", i + 1, output),
            Err(e) => println!("Task {}: Error - {}", i + 1, e),
        }
    }
    
    Ok(())
}
```

---

### 项目2: 进程监控与管理系统

```rust
use tokio::process::Command;
use tokio::time::{interval, Duration};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 进程信息
#[derive(Clone, Debug)]
struct ProcessInfo {
    pid: u32,
    command: String,
    status: ProcessStatus,
    restart_count: u32,
}

#[derive(Clone, Debug, PartialEq)]
enum ProcessStatus {
    Running,
    Stopped,
    Failed,
}

/// 进程监控器
struct ProcessMonitor {
    processes: Arc<RwLock<HashMap<String, ProcessInfo>>>,
    max_restarts: u32,
}

impl ProcessMonitor {
    fn new(max_restarts: u32) -> Self {
        Self {
            processes: Arc::new(RwLock::new(HashMap::new())),
            max_restarts,
        }
    }
    
    async fn start_process(&self, name: String, command: String) 
        -> Result<(), String> 
    {
        let mut child = Command::new(&command)
            .spawn()
            .map_err(|e| e.to_string())?;
        
        let pid = child.id().ok_or("Failed to get PID")?;
        
        let info = ProcessInfo {
            pid,
            command: command.clone(),
            status: ProcessStatus::Running,
            restart_count: 0,
        };
        
        self.processes.write().await.insert(name.clone(), info);
        
        // 监控进程退出
        let processes = Arc::clone(&self.processes);
        let max_restarts = self.max_restarts;
        
        tokio::spawn(async move {
            let status = child.wait().await;
            
            let mut procs = processes.write().await;
            if let Some(info) = procs.get_mut(&name) {
                match status {
                    Ok(s) if s.success() => {
                        info.status = ProcessStatus::Stopped;
                        println!("[{}] Exited normally", name);
                    }
                    _ => {
                        info.status = ProcessStatus::Failed;
                        info.restart_count += 1;
                        println!("[{}] Failed (restarts: {})", 
                                 name, info.restart_count);
                    }
                }
            }
        });
        
        Ok(())
    }
    
    async fn get_status(&self, name: &str) -> Option<ProcessInfo> {
        self.processes.read().await.get(name).cloned()
    }
    
    async fn list_processes(&self) -> Vec<(String, ProcessInfo)> {
        self.processes.read().await
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }
    
    async fn health_check(&self) {
        let mut ticker = interval(Duration::from_secs(5));
        
        loop {
            ticker.tick().await;
            
            println!("\n=== Health Check ===");
            let processes = self.list_processes().await;
            
            for (name, info) in processes {
                println!("{}: {:?} (PID: {}, Restarts: {})",
                         name, info.status, info.pid, info.restart_count);
            }
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let monitor = Arc::new(ProcessMonitor::new(3));
    
    // 启动进程
    monitor.start_process("worker1".to_string(), "sleep".to_string()).await?;
    monitor.start_process("worker2".to_string(), "sleep".to_string()).await?;
    
    // 启动健康检查
    let monitor_clone = Arc::clone(&monitor);
    tokio::spawn(async move {
        monitor_clone.health_check().await;
    });
    
    // 运行一段时间
    tokio::time::sleep(Duration::from_secs(15)).await;
    
    println!("\n=== Final Status ===");
    for (name, info) in monitor.list_processes().await {
        println!("{}: {:?}", name, info);
    }
    
    Ok(())
}
```

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**代码总量**: ~900行  
**维护者**: Rust Learning Community

---

💻 **掌握进程管理，构建可靠的多进程系统！** 🚀✨
