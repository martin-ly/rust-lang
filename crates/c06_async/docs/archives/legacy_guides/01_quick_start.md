# 快速开始指南

## 📊 目录

- [快速开始指南](#快速开始指南)
  - [📊 目录](#-目录)
  - [安装和设置](#安装和设置)
    - [1. 创建新项目](#1-创建新项目)
    - [2. 添加依赖](#2-添加依赖)
    - [3. 基本异步函数](#3-基本异步函数)
  - [核心概念](#核心概念)
    - [Future Trait](#future-trait)
    - [async/await 语法](#asyncawait-语法)
  - [运行时选择](#运行时选择)
    - [Tokio（推荐用于生产环境）](#tokio推荐用于生产环境)
    - [async-std（推荐用于学习）](#async-std推荐用于学习)
    - [smol（推荐用于轻量级应用）](#smol推荐用于轻量级应用)
  - [并发编程](#并发编程)
    - [并行执行任务](#并行执行任务)
    - [任务选择](#任务选择)
  - [错误处理](#错误处理)
    - [基本错误处理](#基本错误处理)
    - [错误传播](#错误传播)
  - [同步原语](#同步原语)
    - [Mutex](#mutex)
    - [信号量](#信号量)
  - [下一步](#下一步)

## 安装和设置

### 1. 创建新项目

```bash
cargo new my-async-project
cd my-async-project
```

### 2. 添加依赖

在 `Cargo.toml` 中添加必要的依赖：

```toml
[dependencies]
tokio = { version = "1.40", features = ["full"] }
futures = "0.3"
anyhow = "1.0"
serde = { version = "1.0", features = ["derive"] }
async-trait = "0.1"
```

### 3. 基本异步函数

```rust
use tokio::time::sleep;
use std::time::Duration;

async fn hello_async() {
    println!("开始异步操作");
    sleep(Duration::from_secs(1)).await;
    println!("异步操作完成");
}

#[tokio::main]
async fn main() {
    hello_async().await;
}
```

## 核心概念

### Future Trait

```rust
use std::future::Future;

async fn my_async_function() -> String {
    "Hello, Future!".to_string()
}

// 等价于
fn my_async_function() -> impl Future<Output = String> {
    async {
        "Hello, Future!".to_string()
    }
}
```

### async/await 语法

```rust
async fn fetch_data() -> Result<String, Box<dyn std::error::Error>> {
    // 模拟网络请求
    tokio::time::sleep(Duration::from_millis(100)).await;
    Ok("数据获取成功".to_string())
}

async fn process_data() -> Result<(), Box<dyn std::error::Error>> {
    let data = fetch_data().await?;
    println!("处理数据: {}", data);
    Ok(())
}
```

## 运行时选择

### Tokio（推荐用于生产环境）

```rust
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    
    loop {
        let (mut socket, _) = listener.accept().await?;
        
        tokio::spawn(async move {
            let mut buf = [0; 1024];
            match socket.read(&mut buf).await {
                Ok(0) => return,
                Ok(n) => {
                    if socket.write_all(&buf[..n]).await.is_err() {
                        return;
                    }
                }
                Err(_) => return,
            }
        });
    }
}
```

### async-std（推荐用于学习）

```rust
use async_std::task;
use async_std::fs;

async fn read_file() -> Result<String, std::io::Error> {
    let contents = fs::read_to_string("file.txt").await?;
    Ok(contents)
}

fn main() {
    task::block_on(async {
        match read_file().await {
            Ok(contents) => println!("文件内容: {}", contents),
            Err(e) => println!("读取文件失败: {}", e),
        }
    });
}
```

### smol（推荐用于轻量级应用）

```rust
use smol::Async;
use std::net::TcpStream;

fn main() -> std::io::Result<()> {
    smol::block_on(async {
        let stream = Async::<TcpStream>::connect("127.0.0.1:8080").await?;
        // 处理连接
        Ok(())
    })
}
```

## 并发编程

### 并行执行任务

```rust
use futures::future::join_all;

async fn parallel_tasks() {
    let tasks = vec![
        async { "任务1".to_string() },
        async { "任务2".to_string() },
        async { "任务3".to_string() },
    ];
    
    let results = join_all(tasks).await;
    println!("并行任务结果: {:?}", results);
}
```

### 任务选择

```rust
use futures::future::select;

async fn select_tasks() {
    let task1 = async {
        tokio::time::sleep(Duration::from_secs(1)).await;
        "任务1完成"
    };
    
    let task2 = async {
        tokio::time::sleep(Duration::from_millis(500)).await;
        "任务2完成"
    };
    
    match select(Box::pin(task1), Box::pin(task2)).await {
        futures::future::Either::Left((result, _)) => println!("任务1先完成: {}", result),
        futures::future::Either::Right((result, _)) => println!("任务2先完成: {}", result),
    }
}
```

## 错误处理

### 基本错误处理

```rust
use anyhow::Result;

async fn risky_operation() -> Result<String> {
    // 可能失败的操作
    if rand::random::<bool>() {
        Ok("操作成功".to_string())
    } else {
        Err(anyhow::anyhow!("操作失败"))
    }
}

async fn handle_errors() -> Result<()> {
    match risky_operation().await {
        Ok(result) => println!("成功: {}", result),
        Err(e) => println!("失败: {}", e),
    }
    Ok(())
}
```

### 错误传播

```rust
async fn error_propagation() -> Result<String> {
    let result = risky_operation().await?; // 使用 ? 操作符传播错误
    Ok(format!("处理结果: {}", result))
}
```

## 同步原语

### Mutex

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

async fn shared_state_example() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = Vec::new();
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut count = counter.lock().await;
            *count += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    println!("最终计数: {}", *counter.lock().await);
}
```

### 信号量

```rust
use tokio::sync::Semaphore;

async fn semaphore_example() {
    let semaphore = Arc::new(Semaphore::new(3)); // 最多3个并发任务
    
    let mut handles = Vec::new();
    
    for i in 0..10 {
        let semaphore = Arc::clone(&semaphore);
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            println!("任务 {} 开始执行", i);
            tokio::time::sleep(Duration::from_secs(1)).await;
            println!("任务 {} 执行完成", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
}
```

## 下一步

- 查看 [核心概念](core_concepts.md) 了解更深入的理论
- 阅读 [运行时对比](runtime_comparison.md) 选择合适的运行时
- 探索 [集成框架](integration_framework.md) 构建复杂应用
- 参考 [最佳实践](best_practices.md) 优化性能
