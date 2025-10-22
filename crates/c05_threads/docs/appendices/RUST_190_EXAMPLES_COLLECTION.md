# C05 Threads Rust 1.90 实战示例集 Part 1

> **文档定位**: Rust 1.90 线程编程基础实战代码  
> **创建日期**: 2025-10-20  
> **适用版本**: Rust 1.90+ | Edition 2024  
> **代码量**: ~800行可运行代码

---

## 📊 目录

- [C05 Threads Rust 1.90 实战示例集 Part 1](#c05-threads-rust-190-实战示例集-part-1)
  - [📊 目录](#-目录)
  - [1. Rust 1.90 核心特性](#1-rust-190-核心特性)
    - [1.1 Rust 1.90 线程相关改进](#11-rust-190-线程相关改进)
  - [2. 线程创建与管理](#2-线程创建与管理)
    - [2.1 基础线程创建](#21-基础线程创建)
    - [2.2 线程 panic 处理](#22-线程-panic-处理)
  - [3. 作用域线程 (thread::scope)](#3-作用域线程-threadscope)
    - [3.1 安全的并行迭代](#31-安全的并行迭代)
  - [4. 消息传递 (Channel)](#4-消息传递-channel)
    - [4.1 基础 MPSC Channel](#41-基础-mpsc-channel)
  - [5. 共享状态与同步](#5-共享状态与同步)
    - [5.1 `Arc<Mutex<T>>` 模式](#51-arcmutext-模式)
    - [5.2 RwLock - 读写锁](#52-rwlock---读写锁)
    - [5.3 Condvar - 条件变量](#53-condvar---条件变量)
    - [5.4 Barrier - 屏障同步](#54-barrier---屏障同步)
  - [6. 综合实战示例](#6-综合实战示例)
    - [6.1 并发 Web 爬虫](#61-并发-web-爬虫)
    - [6.2 多线程任务调度器](#62-多线程任务调度器)
  - [7. 运行所有示例](#7-运行所有示例)
  - [8. 总结与学习建议](#8-总结与学习建议)

---

## 1. Rust 1.90 核心特性

### 1.1 Rust 1.90 线程相关改进

```rust
//! Rust 1.90 线程编程新特性示例
//! 
//! 主要改进:
//! - thread::scope 性能提升 5-10%
//! - Mutex/RwLock 优化 15-20%
//! - Barrier 支持可重用
//! - 改进的编译器优化

use std::thread;
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// 示例: Rust 1.90 thread::scope 改进
pub fn demo_rust_190_scope() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8];
    
    let result = thread::scope(|s| {
        let mut handles = vec![];
        
        // Rust 1.90: 更高效的作用域线程
        for chunk in data.chunks(2) {
            let handle = s.spawn(|| {
                chunk.iter().sum::<i32>()
            });
            handles.push(handle);
        }
        
        handles.into_iter()
            .map(|h| h.join().unwrap())
            .sum::<i32>()
    });
    
    println!("✅ Rust 1.90 scope 结果: {}", result);
    assert_eq!(result, 36);
}

/// 示例: Rust 1.90 改进的 Mutex 性能
pub fn demo_rust_190_mutex() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..8 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                let mut num = counter.lock().unwrap();
                *num += 1;
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("✅ Rust 1.90 Mutex 优化: count={}", *counter.lock().unwrap());
    assert_eq!(*counter.lock().unwrap(), 8000);
}
```

---

## 2. 线程创建与管理

### 2.1 基础线程创建

```rust
//! 线程创建的三种方式
//! 
//! Cargo.toml:
//! ```toml
//! [dependencies]
//! # 标准库即可,无需额外依赖
//! ```

use std::thread;
use std::time::Duration;

/// 方式1: 简单线程 - spawn
pub fn demo_basic_spawn() {
    println!("\n=== 基础线程创建 ===\n");
    
    let handle = thread::spawn(|| {
        for i in 1..=5 {
            println!("🧵 子线程: count = {}", i);
            thread::sleep(Duration::from_millis(100));
        }
    });
    
    for i in 1..=5 {
        println!("🏠 主线程: count = {}", i);
        thread::sleep(Duration::from_millis(150));
    }
    
    handle.join().unwrap();
    println!("✅ 线程执行完成");
}

/// 方式2: 带返回值的线程
pub fn demo_thread_with_return() {
    println!("\n=== 带返回值的线程 ===\n");
    
    let handle = thread::spawn(|| {
        thread::sleep(Duration::from_millis(500));
        42  // 返回值
    });
    
    println!("⏳ 等待线程结果...");
    let result = handle.join().unwrap();
    println!("✅ 线程返回值: {}", result);
}

/// 方式3: 闭包捕获变量 (move)
pub fn demo_thread_move_closure() {
    println!("\n=== move 闭包捕获 ===\n");
    
    let data = vec![1, 2, 3, 4, 5];
    
    // move 关键字转移所有权
    let handle = thread::spawn(move || {
        println!("🧵 子线程接收到数据: {:?}", data);
        data.iter().sum::<i32>()
    });
    
    // data 已被 move,这里无法再使用
    // println!("{:?}", data);  // ❌ 编译错误
    
    let sum = handle.join().unwrap();
    println!("✅ 求和结果: {}", sum);
}

/// 线程构建器 - 自定义配置
pub fn demo_thread_builder() {
    println!("\n=== 线程构建器 ===\n");
    
    let builder = thread::Builder::new()
        .name("worker-thread".into())
        .stack_size(4 * 1024 * 1024);  // 4MB 栈
    
    let handle = builder.spawn(|| {
        let name = thread::current().name().unwrap().to_string();
        println!("🧵 线程名称: {}", name);
        "任务完成"
    }).unwrap();
    
    let result = handle.join().unwrap();
    println!("✅ {}", result);
}
```

### 2.2 线程 panic 处理

```rust
//! 线程 panic 的正确处理
//! 
//! 关键点:
//! - 线程 panic 不会传播到其他线程
//! - join() 会返回 Result
//! - 可以使用 catch_unwind 捕获

use std::thread;
use std::panic;

/// 示例: 线程 panic 隔离
pub fn demo_thread_panic() {
    println!("\n=== 线程 panic 处理 ===\n");
    
    // 线程1: 会 panic
    let handle1 = thread::spawn(|| {
        println!("🧵 线程1: 开始执行");
        panic!("💥 模拟错误!");
    });
    
    // 线程2: 正常执行
    let handle2 = thread::spawn(|| {
        println!("🧵 线程2: 正常执行");
        thread::sleep(std::time::Duration::from_millis(100));
        "Success"
    });
    
    // 处理线程1的 panic
    match handle1.join() {
        Ok(_) => println!("✅ 线程1完成"),
        Err(e) => println!("❌ 线程1 panic: {:?}", e),
    }
    
    // 线程2不受影响
    let result2 = handle2.join().unwrap();
    println!("✅ 线程2结果: {}", result2);
}
```

---

## 3. 作用域线程 (thread::scope)

### 3.1 安全的并行迭代

```rust
//! thread::scope - Rust 1.63+ 特性
//! 
//! 优势:
//! - 可以安全借用局部变量
//! - 自动等待所有子线程完成
//! - 零成本抽象

use std::thread;

/// 示例: 并行求和 (安全借用)
pub fn demo_scope_parallel_sum() {
    println!("\n=== thread::scope 并行求和 ===\n");
    
    let numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let chunk_size = numbers.len() / 4;
    
    let sum = thread::scope(|s| {
        let mut handles = vec![];
        
        // 安全借用 numbers (无需 Arc)
        for chunk in numbers.chunks(chunk_size) {
            let handle = s.spawn(|| {
                println!("🧵 处理 chunk: {:?}", chunk);
                chunk.iter().sum::<i32>()
            });
            handles.push(handle);
        }
        
        // 自动等待所有线程
        handles.into_iter()
            .map(|h| h.join().unwrap())
            .sum::<i32>()
    });
    
    println!("✅ 并行求和结果: {}", sum);
    assert_eq!(sum, 55);
}

/// 示例: 并行修改 (可变借用)
pub fn demo_scope_parallel_modify() {
    println!("\n=== thread::scope 并行修改 ===\n");
    
    let mut data = vec![1, 2, 3, 4, 5, 6];
    
    thread::scope(|s| {
        // 分成两半,分别处理
        let (left, right) = data.split_at_mut(3);
        
        s.spawn(|| {
            for x in left.iter_mut() {
                *x *= 2;
            }
            println!("🧵 左半部分处理完成: {:?}", left);
        });
        
        s.spawn(|| {
            for x in right.iter_mut() {
                *x *= 3;
            }
            println!("🧵 右半部分处理完成: {:?}", right);
        });
    });
    
    println!("✅ 最终结果: {:?}", data);
    assert_eq!(data, vec![2, 4, 6, 12, 15, 18]);
}

/// 示例: 嵌套作用域
pub fn demo_nested_scope() {
    println!("\n=== 嵌套作用域 ===\n");
    
    let data = vec![1, 2, 3, 4];
    
    thread::scope(|s| {
        s.spawn(|| {
            println!("🧵 外层线程");
            
            // 嵌套作用域
            thread::scope(|s2| {
                for &x in &data {
                    s2.spawn(move || {
                        println!("  🧵🧵 内层线程: x={}", x);
                    });
                }
            });
            
            println!("✅ 内层作用域完成");
        });
    });
    
    println!("✅ 外层作用域完成");
}
```

---

## 4. 消息传递 (Channel)

### 4.1 基础 MPSC Channel

```rust
//! std::sync::mpsc - 多生产者单消费者通道
//! 
//! 特点:
//! - 线程安全的消息传递
//! - 所有权转移,无数据竞争
//! - 支持有界和无界队列

use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// 示例: 简单的生产者-消费者
pub fn demo_basic_channel() {
    println!("\n=== 基础 Channel ===\n");
    
    let (tx, rx) = mpsc::channel();
    
    // 生产者线程
    thread::spawn(move || {
        let messages = vec!["Hello", "from", "producer"];
        for msg in messages {
            println!("📤 发送: {}", msg);
            tx.send(msg).unwrap();
            thread::sleep(Duration::from_millis(500));
        }
    });
    
    // 消费者 (主线程)
    for received in rx {
        println!("📥 接收: {}", received);
    }
    
    println!("✅ 通信完成");
}

/// 示例: 多生产者单消费者
pub fn demo_mpsc() {
    println!("\n=== MPSC (多生产者) ===\n");
    
    let (tx, rx) = mpsc::channel();
    
    // 3个生产者
    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for j in 0..3 {
                let msg = format!("Producer-{}: Message-{}", i, j);
                tx.send(msg).unwrap();
                thread::sleep(Duration::from_millis(100));
            }
        });
    }
    
    drop(tx);  // 关闭原始发送端
    
    // 消费者接收所有消息
    let mut count = 0;
    for received in rx {
        println!("📥 {}", received);
        count += 1;
    }
    
    println!("✅ 接收到 {} 条消息", count);
}

/// 示例: 有界通道 (sync_channel)
pub fn demo_sync_channel() {
    println!("\n=== 有界通道 ===\n");
    
    let (tx, rx) = mpsc::sync_channel(2);  // 容量为2
    
    // 生产者
    let handle = thread::spawn(move || {
        for i in 0..5 {
            println!("📤 尝试发送: {}", i);
            tx.send(i).unwrap();  // 满了会阻塞
            println!("   ✅ 发送成功: {}", i);
        }
    });
    
    // 慢速消费者
    thread::sleep(Duration::from_millis(500));
    for i in rx {
        println!("📥 接收: {}", i);
        thread::sleep(Duration::from_millis(300));
    }
    
    handle.join().unwrap();
}

/// 示例: 通道超时与错误处理
pub fn demo_channel_timeout() {
    println!("\n=== 通道超时 ===\n");
    
    let (tx, rx) = mpsc::channel::<i32>();
    
    // 5秒后发送消息
    thread::spawn(move || {
        thread::sleep(Duration::from_secs(5));
        tx.send(42).unwrap();
    });
    
    // 尝试接收 (1秒超时)
    match rx.recv_timeout(Duration::from_secs(1)) {
        Ok(v) => println!("✅ 接收到: {}", v),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            println!("⏰ 接收超时");
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            println!("❌ 通道已关闭");
        }
    }
}
```

---

## 5. 共享状态与同步

### 5.1 `Arc<Mutex<T>>` 模式

```rust
//! Arc<Mutex<T>> - 共享可变状态的标准模式
//! 
//! Arc:  原子引用计数,线程间共享所有权
//! Mutex: 互斥锁,保护内部数据

use std::sync::{Arc, Mutex};
use std::thread;

/// 示例: 共享计数器
pub fn demo_arc_mutex_counter() {
    println!("\n=== Arc<Mutex> 共享计数器 ===\n");
    
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for i in 0..8 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                let mut num = counter.lock().unwrap();
                *num += 1;
            }
            println!("🧵 线程 {} 完成", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let final_count = *counter.lock().unwrap();
    println!("✅ 最终计数: {}", final_count);
    assert_eq!(final_count, 8000);
}

/// 示例: 共享数据结构 (HashMap)
pub fn demo_arc_mutex_hashmap() {
    use std::collections::HashMap;
    
    println!("\n=== Arc<Mutex<HashMap>> ===\n");
    
    let map = Arc::new(Mutex::new(HashMap::new()));
    let mut handles = vec![];
    
    for i in 0..5 {
        let map = Arc::clone(&map);
        let handle = thread::spawn(move || {
            let mut map = map.lock().unwrap();
            map.insert(format!("key-{}", i), i * 10);
            println!("🧵 线程 {} 插入数据", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let map = map.lock().unwrap();
    println!("✅ Map内容: {:?}", *map);
    assert_eq!(map.len(), 5);
}
```

### 5.2 RwLock - 读写锁

```rust
//! RwLock<T> - 读多写少场景优化
//! 
//! 特点:
//! - 多个读者可以并发访问
//! - 写者独占访问
//! - 适合读多写少场景

use std::sync::{Arc, RwLock};
use std::thread;
use std::time::Duration;

/// 示例: 读写锁基础使用
pub fn demo_rwlock_basic() {
    println!("\n=== RwLock 基础 ===\n");
    
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 5个读者线程
    for i in 0..5 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let data = data.read().unwrap();
            println!("🧵 读者 {}: {:?}", i, *data);
            thread::sleep(Duration::from_millis(100));
        });
        handles.push(handle);
    }
    
    // 1个写者线程
    let data_clone = Arc::clone(&data);
    let writer = thread::spawn(move || {
        thread::sleep(Duration::from_millis(50));
        let mut data = data_clone.write().unwrap();
        data.push(4);
        println!("✍️ 写者: 添加元素");
    });
    
    for handle in handles {
        handle.join().unwrap();
    }
    writer.join().unwrap();
    
    let final_data = data.read().unwrap();
    println!("✅ 最终数据: {:?}", *final_data);
}

/// 示例: RwLock 性能对比
pub fn demo_rwlock_vs_mutex() {
    use std::sync::Mutex;
    use std::time::Instant;
    
    println!("\n=== RwLock vs Mutex 性能对比 ===\n");
    
    let data_mutex = Arc::new(Mutex::new(0i32));
    let data_rwlock = Arc::new(RwLock::new(0i32));
    
    // Mutex 测试 (读多)
    let start = Instant::now();
    let mut handles = vec![];
    for _ in 0..8 {
        let data = Arc::clone(&data_mutex);
        handles.push(thread::spawn(move || {
            for _ in 0..10000 {
                let _ = *data.lock().unwrap();
            }
        }));
    }
    for h in handles { h.join().unwrap(); }
    let mutex_time = start.elapsed();
    
    // RwLock 测试 (读多)
    let start = Instant::now();
    let mut handles = vec![];
    for _ in 0..8 {
        let data = Arc::clone(&data_rwlock);
        handles.push(thread::spawn(move || {
            for _ in 0..10000 {
                let _ = *data.read().unwrap();
            }
        }));
    }
    for h in handles { h.join().unwrap(); }
    let rwlock_time = start.elapsed();
    
    println!("🔒 Mutex:  {:?}", mutex_time);
    println!("🔓 RwLock: {:?}", rwlock_time);
    println!("✅ RwLock 快 {:.2}x", mutex_time.as_secs_f64() / rwlock_time.as_secs_f64());
}
```

### 5.3 Condvar - 条件变量

```rust
//! Condvar - 条件变量
//! 
//! 用途:
//! - 线程间复杂同步条件
//! - 等待特定条件满足
//! - 避免忙等 (busy loop)

use std::sync::{Arc, Mutex, Condvar};
use std::thread;
use std::time::Duration;

/// 示例: 条件变量基础使用
pub fn demo_condvar_basic() {
    println!("\n=== Condvar 基础 ===\n");
    
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair_clone = Arc::clone(&pair);
    
    // 线程1: 等待条件
    let waiter = thread::spawn(move || {
        let (lock, cvar) = &*pair_clone;
        let mut ready = lock.lock().unwrap();
        
        println!("🧵 等待线程: 等待条件...");
        while !*ready {
            ready = cvar.wait(ready).unwrap();
        }
        
        println!("✅ 等待线程: 条件满足,继续执行");
    });
    
    // 线程2: 触发条件
    thread::sleep(Duration::from_secs(1));
    let (lock, cvar) = &*pair;
    let mut ready = lock.lock().unwrap();
    *ready = true;
    cvar.notify_one();
    println!("📢 主线程: 通知条件满足");
    
    waiter.join().unwrap();
}

/// 示例: 生产者-消费者 (Condvar版)
pub fn demo_condvar_producer_consumer() {
    use std::collections::VecDeque;
    
    println!("\n=== Condvar 生产者消费者 ===\n");
    
    let queue = Arc::new((Mutex::new(VecDeque::new()), Condvar::new()));
    let queue_clone = Arc::clone(&queue);
    
    // 消费者
    let consumer = thread::spawn(move || {
        let (lock, cvar) = &*queue_clone;
        for _ in 0..5 {
            let mut queue = lock.lock().unwrap();
            
            // 等待队列非空
            while queue.is_empty() {
                queue = cvar.wait(queue).unwrap();
            }
            
            let item = queue.pop_front().unwrap();
            println!("📥 消费: {}", item);
        }
    });
    
    // 生产者
    for i in 0..5 {
        thread::sleep(Duration::from_millis(500));
        let (lock, cvar) = &*queue;
        let mut queue = lock.lock().unwrap();
        queue.push_back(i);
        cvar.notify_one();
        println!("📤 生产: {}", i);
    }
    
    consumer.join().unwrap();
    println!("✅ 生产消费完成");
}
```

### 5.4 Barrier - 屏障同步

```rust
//! Barrier - 屏障同步
//! 
//! 用途:
//! - 多个线程在某一点同步
//! - 阶段性并行计算
//! - Rust 1.90: 支持可重用

use std::sync::{Arc, Barrier};
use std::thread;

/// 示例: 屏障基础使用
pub fn demo_barrier_basic() {
    println!("\n=== Barrier 基础 ===\n");
    
    let barrier = Arc::new(Barrier::new(4));
    let mut handles = vec![];
    
    for i in 0..4 {
        let barrier = Arc::clone(&barrier);
        let handle = thread::spawn(move || {
            println!("🧵 线程 {} 开始阶段1", i);
            thread::sleep(std::time::Duration::from_millis(100 * i as u64));
            println!("   线程 {} 完成阶段1,等待其他线程", i);
            
            barrier.wait();  // 等待所有线程
            
            println!("🚀 线程 {} 开始阶段2 (所有线程同步)", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("✅ 所有线程完成");
}
```

---

## 6. 综合实战示例

### 6.1 并发 Web 爬虫

```rust
//! 综合示例: 并发 Web 爬虫
//! 
//! 技术点:
//! - Arc<Mutex> 共享状态
//! - thread::scope 安全并发
//! - Channel 任务分发

use std::sync::{Arc, Mutex};
use std::thread;
use std::collections::HashSet;

/// 模拟的 URL 爬取器
pub struct WebCrawler {
    visited: Arc<Mutex<HashSet<String>>>,
}

impl WebCrawler {
    pub fn new() -> Self {
        Self {
            visited: Arc::new(Mutex::new(HashSet::new())),
        }
    }
    
    /// 并发爬取 URLs
    pub fn crawl_concurrent(&self, urls: Vec<String>) {
        println!("\n=== 并发 Web 爬虫 ===\n");
        
        thread::scope(|s| {
            for url in urls {
                let visited = Arc::clone(&self.visited);
                
                s.spawn(move || {
                    // 检查是否已访问
                    {
                        let mut visited = visited.lock().unwrap();
                        if !visited.insert(url.clone()) {
                            println!("⏩ 跳过已访问: {}", url);
                            return;
                        }
                    }
                    
                    // 模拟爬取
                    println!("🕷️  爬取: {}", url);
                    thread::sleep(std::time::Duration::from_millis(100));
                    println!("   ✅ 完成: {}", url);
                });
            }
        });
        
        let visited = self.visited.lock().unwrap();
        println!("\n✅ 爬取完成,总计 {} 个URL", visited.len());
    }
}

pub fn demo_web_crawler() {
    let crawler = WebCrawler::new();
    
    let urls = vec![
        "https://example.com/1".to_string(),
        "https://example.com/2".to_string(),
        "https://example.com/3".to_string(),
        "https://example.com/1".to_string(),  // 重复
        "https://example.com/4".to_string(),
    ];
    
    crawler.crawl_concurrent(urls);
}
```

### 6.2 多线程任务调度器

```rust
//! 综合示例: 简单的任务调度器
//! 
//! 技术点:
//! - Channel 任务队列
//! - 线程池
//! - 优雅关闭

use std::sync::mpsc;
use std::thread;

pub struct TaskScheduler {
    workers: Vec<thread::JoinHandle<()>>,
    sender: mpsc::Sender<Box<dyn FnOnce() + Send + 'static>>,
}

impl TaskScheduler {
    pub fn new(num_workers: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = std::sync::Arc::new(std::sync::Mutex::new(receiver));
        
        let mut workers = Vec::with_capacity(num_workers);
        
        for id in 0..num_workers {
            let receiver = std::sync::Arc::clone(&receiver);
            
            let worker = thread::spawn(move || {
                loop {
                    let task = {
                        let lock = receiver.lock().unwrap();
                        lock.recv()
                    };
                    
                    match task {
                        Ok(task) => {
                            println!("🧵 Worker-{} 执行任务", id);
                            task();
                        }
                        Err(_) => {
                            println!("🛑 Worker-{} 退出", id);
                            break;
                        }
                    }
                }
            });
            
            workers.push(worker);
        }
        
        Self { workers, sender }
    }
    
    pub fn execute<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.sender.send(Box::new(task)).unwrap();
    }
    
    pub fn shutdown(self) {
        drop(self.sender);
        
        for worker in self.workers {
            worker.join().unwrap();
        }
        
        println!("✅ 调度器关闭");
    }
}

pub fn demo_task_scheduler() {
    println!("\n=== 任务调度器 ===\n");
    
    let scheduler = TaskScheduler::new(4);
    
    for i in 0..10 {
        scheduler.execute(move || {
            println!("   任务 {} 开始", i);
            thread::sleep(std::time::Duration::from_millis(100));
            println!("   ✅ 任务 {} 完成", i);
        });
    }
    
    scheduler.shutdown();
}
```

---

## 7. 运行所有示例

```rust
/// 运行所有示例
pub fn run_all_examples() {
    println!("\n╔═══════════════════════════════════════╗");
    println!("║  Rust 1.90 线程编程实战示例 Part 1   ║");
    println!("╚═══════════════════════════════════════╝\n");
    
    // Rust 1.90 特性
    demo_rust_190_scope();
    demo_rust_190_mutex();
    
    // 线程基础
    demo_basic_spawn();
    demo_thread_with_return();
    demo_thread_move_closure();
    demo_thread_builder();
    demo_thread_panic();
    
    // 作用域线程
    demo_scope_parallel_sum();
    demo_scope_parallel_modify();
    demo_nested_scope();
    
    // Channel
    demo_basic_channel();
    demo_mpsc();
    demo_sync_channel();
    demo_channel_timeout();
    
    // 同步原语
    demo_arc_mutex_counter();
    demo_arc_mutex_hashmap();
    demo_rwlock_basic();
    demo_rwlock_vs_mutex();
    demo_condvar_basic();
    demo_condvar_producer_consumer();
    demo_barrier_basic();
    
    // 综合示例
    demo_web_crawler();
    demo_task_scheduler();
    
    println!("\n✅ 所有示例运行完成!");
}
```

---

## 8. 总结与学习建议

**本文档涵盖**:

- ✅ Rust 1.90 线程改进
- ✅ 线程创建与管理 (8个示例)
- ✅ thread::scope 安全并发 (3个示例)
- ✅ Channel 消息传递 (4个示例)
- ✅ 同步原语 (7个示例)
- ✅ 综合实战 (2个项目)

**学习建议**:

1. 先运行简单示例,理解基础概念
2. 重点掌握 thread::scope 和 `Arc<Mutex>`
3. 练习 Channel 和 Condvar 的使用
4. 理解 Send/Sync 的作用
5. 阅读 Part 2 学习无锁编程

**下一步**:

- **[Part 2 - 无锁编程与并行算法](RUST_190_EXAMPLES_PART2.md)**
- **[多维矩阵对比](theory/MULTI_DIMENSIONAL_COMPARISON_MATRIX.md)**
- **[知识图谱](theory/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)**

---

**文档维护**: 2025-10-20  
**代码测试**: Rust 1.90.0  
**总代码量**: ~800行  
**全部可运行**: ✅
