# 🔗 跨模块集成示例指南

> **文档类型**: 实践指南
> **最后更新**: 2026-01-26
> **适用版本**: Rust 1.93.0+

---

## 📋 目录

- [🔗 跨模块集成示例指南](#-跨模块集成示例指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [示例1: 所有权与类型系统集成](#示例1-所有权与类型系统集成)
    - [场景：类型安全的资源管理](#场景类型安全的资源管理)
  - [示例2: 异步与网络编程集成](#示例2-异步与网络编程集成)
    - [场景：异步HTTP服务器](#场景异步http服务器)
  - [示例3: 线程与进程管理集成](#示例3-线程与进程管理集成)
    - [场景：多线程进程池](#场景多线程进程池)
  - [示例4: 宏系统与设计模式集成](#示例4-宏系统与设计模式集成)
    - [场景：使用宏实现设计模式](#场景使用宏实现设计模式)
  - [示例5: 算法与性能优化集成](#示例5-算法与性能优化集成)
    - [场景：高性能数据处理管道](#场景高性能数据处理管道)
  - [示例6: WASM与跨平台集成](#示例6-wasm与跨平台集成)
    - [场景：WASM模块与Rust后端集成](#场景wasm模块与rust后端集成)
  - [最佳实践](#最佳实践)
    - [1. 模块边界清晰](#1-模块边界清晰)
    - [2. 错误处理统一](#2-错误处理统一)
    - [3. 性能考虑](#3-性能考虑)
    - [4. 测试策略](#4-测试策略)

---

## 概述

本文档提供跨模块集成的实际示例，展示如何将不同的Rust模块组合使用，构建完整的应用程序。

---

## 示例1: 所有权与类型系统集成

### 场景：类型安全的资源管理

```rust
use c01_ownership_borrow_scope::*;
use c02_type_system::*;

/// 类型安全的资源管理器
struct ResourceManager<T> {
    resources: Vec<T>,
}

impl<T> ResourceManager<T> {
    /// 创建新的资源管理器
    fn new() -> Self {
        ResourceManager {
            resources: Vec::new(),
        }
    }

    /// 添加资源（转移所有权）
    fn add_resource(&mut self, resource: T) {
        self.resources.push(resource);
    }

    /// 获取资源（借用）
    fn get_resource(&self, index: usize) -> Option<&T> {
        self.resources.get(index)
    }

    /// 获取可变资源（可变借用）
    fn get_resource_mut(&mut self, index: usize) -> Option<&mut T> {
        self.resources.get_mut(index)
    }
}

#[test]
fn test_resource_manager() {
    let mut manager = ResourceManager::new();
    manager.add_resource(42);

    assert_eq!(manager.get_resource(0), Some(&42));
}
```

---

## 示例2: 异步与网络编程集成

### 场景：异步HTTP服务器

```rust
use c06_async::*;
use c10_networks::*;
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

/// 异步HTTP服务器
async fn async_http_server() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;

    loop {
        let (mut socket, _) = listener.accept().await?;

        tokio::spawn(async move {
            let mut buffer = [0; 1024];
            socket.read(&mut buffer).await?;

            let response = b"HTTP/1.1 200 OK\r\n\r\nHello, World!";
            socket.write_all(response).await?;

            Ok::<(), Box<dyn std::error::Error>>(())
        });
    }
}
```

---

## 示例3: 线程与进程管理集成

### 场景：多线程进程池

```rust
use c05_threads::*;
use c07_process::*;
use std::sync::{Arc, Mutex};
use std::thread;

/// 线程池管理器
struct ThreadPool {
    workers: Vec<thread::JoinHandle<()>>,
    sender: Option<std::sync::mpsc::Sender<Job>>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    /// 创建新的线程池
    fn new(size: usize) -> Self {
        let (sender, receiver) = std::sync::mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for _ in 0..size {
            let receiver = Arc::clone(&receiver);
            let worker = thread::spawn(move || loop {
                let job = receiver.lock().unwrap().recv();
                match job {
                    Ok(job) => job(),
                    Err(_) => break,
                }
            });
            workers.push(worker);
        }

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    /// 执行任务
    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        drop(self.sender.take());

        for worker in &mut self.workers {
            worker.join().unwrap();
        }
    }
}
```

---

## 示例4: 宏系统与设计模式集成

### 场景：使用宏实现设计模式

```rust
use c11_macro_system::*;
use c09_design_pattern::*;

/// 使用宏实现单例模式
macro_rules! singleton {
    ($name:ident, $type:ty) => {
        struct $name {
            value: std::sync::Mutex<Option<$type>>,
        }

        impl $name {
            fn get_instance() -> &'static $name {
                static INSTANCE: std::sync::OnceLock<$name> = std::sync::OnceLock::new();
                INSTANCE.get_or_init(|| $name {
                    value: std::sync::Mutex::new(None),
                })
            }

            fn set_value(&self, value: $type) {
                *self.value.lock().unwrap() = Some(value);
            }

            fn get_value(&self) -> Option<$type> {
                self.value.lock().unwrap().take()
            }
        }
    };
}

singleton!(Config, String);

#[test]
fn test_singleton() {
    let config = Config::get_instance();
    config.set_value("test".to_string());
    assert_eq!(config.get_value(), Some("test".to_string()));
}
```

---

## 示例5: 算法与性能优化集成

### 场景：高性能数据处理管道

```rust
use c08_algorithms::*;
use std::time::Instant;

/// 高性能数据处理管道
fn process_data_pipeline(data: &mut Vec<i32>) {
    let start = Instant::now();

    // 排序
    data.sort();

    // 去重
    data.dedup();

    // 过滤
    data.retain(|&x| x > 0);

    let duration = start.elapsed();
    println!("处理耗时: {:?}", duration);
}

#[test]
fn test_data_pipeline() {
    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
    process_data_pipeline(&mut data);
    assert_eq!(data, vec![1, 2, 3, 4, 5, 6, 9]);
}
```

---

## 示例6: WASM与跨平台集成

### 场景：WASM模块与Rust后端集成

```rust
use c12_wasm::*;

/// WASM函数导出
#[cfg(target_arch = "wasm32")]
#[no_mangle]
pub extern "C" fn wasm_add(a: i32, b: i32) -> i32 {
    a + b
}

/// Rust后端实现
#[cfg(not(target_arch = "wasm32"))]
pub fn wasm_add(a: i32, b: i32) -> i32 {
    a + b
}

#[test]
fn test_wasm_integration() {
    assert_eq!(wasm_add(3, 4), 7);
}
```

---

## 最佳实践

### 1. 模块边界清晰

- 每个模块应该有明确的职责
- 使用trait定义模块接口
- 避免循环依赖

### 2. 错误处理统一

- 使用统一的错误类型
- 实现From trait进行错误转换
- 提供详细的错误上下文

### 3. 性能考虑

- 使用零成本抽象
- 避免不必要的克隆
- 利用编译期优化

### 4. 测试策略

- 为每个模块编写单元测试
- 编写集成测试验证模块协作
- 使用基准测试验证性能

---

**报告日期**: 2026-01-26
**维护者**: Rust 项目推进团队
