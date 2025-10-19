# 模式与实践 (Patterns)

本目录包含Rust异步编程的设计模式、反模式和实战技巧。

## 📚 文档列表

### [01_patterns_comparison.md](./01_patterns_comparison.md) - 模式对比 ⭐⭐⭐⭐
**核心参考**

异步设计模式全面对比：
- Actor模式
- Pipeline模式
- Fan-out/Fan-in
- Stream处理模式
- 并发控制模式
- 模式适用场景对比

**适合**: 架构设计和模式选择

---

### [02_patterns_and_pitfalls.md](./02_patterns_and_pitfalls.md) - 模式与陷阱 ⭐⭐⭐⭐⭐
**必读文档**

常见模式和陷阱：
- ✅ 推荐的设计模式
- ❌ 常见错误和陷阱
- 🔧 问题诊断和修复
- 💡 最佳实践建议

**适合**: 所有异步开发者

---

### [03_advanced_patterns.md](./03_advanced_patterns.md) - 高级模式 ⭐⭐⭐⭐
**进阶内容**

高级设计模式：
- 自定义Future实现
- 零拷贝模式
- 背压处理
- 优雅关闭
- 错误恢复策略

**适合**: 有经验的开发者

---

## 🎯 核心模式速览

### 1. Actor模式
**场景**: 状态管理和消息传递

```rust
use tokio::sync::mpsc;

struct Actor {
    receiver: mpsc::Receiver<Message>,
}

impl Actor {
    async fn run(&mut self) {
        while let Some(msg) = self.receiver.recv().await {
            self.handle_message(msg).await;
        }
    }
}
```

**优势**:
- 隔离状态
- 简化并发
- 易于测试

---

### 2. Pipeline模式
**场景**: 数据处理流水线

```rust
use tokio_stream::StreamExt;

async fn pipeline(input: impl Stream<Item = Data>) {
    input
        .filter(|x| x.is_valid())
        .map(|x| transform(x))
        .for_each(|x| process(x))
        .await;
}
```

**优势**:
- 清晰的数据流
- 易于组合
- 支持背压

---

### 3. Fan-out/Fan-in
**场景**: 并发处理后聚合

```rust
use futures::future::join_all;

async fn fan_out_in(items: Vec<Item>) -> Vec<Result> {
    let tasks: Vec<_> = items
        .into_iter()
        .map(|item| tokio::spawn(async move {
            process_item(item).await
        }))
        .collect();
    
    join_all(tasks).await
}
```

**优势**:
- 最大化并发
- 简单聚合
- 适合独立任务

---

### 4. Stream处理
**场景**: 异步迭代和转换

```rust
use tokio_stream::wrappers::ReceiverStream;

async fn stream_processing(rx: mpsc::Receiver<Item>) {
    let mut stream = ReceiverStream::new(rx);
    
    while let Some(item) = stream.next().await {
        // 处理每个item
    }
}
```

**优势**:
- 惰性求值
- 内存效率
- 组合能力强

---

## ⚠️ 常见陷阱

### 1. 未处理的spawn
```rust
// ❌ 错误：忽略spawn的结果
tokio::spawn(async {
    dangerous_operation().await; // 错误被忽略！
});

// ✅ 正确：正确处理结果
let handle = tokio::spawn(async {
    dangerous_operation().await
});
match handle.await {
    Ok(result) => // 处理成功,
    Err(e) => // 处理panic,
}
```

---

### 2. 死锁
```rust
// ❌ 错误：可能死锁
let lock = mutex.lock().await;
other_async_fn().await; // 如果这里也需要锁？
drop(lock);

// ✅ 正确：及时释放锁
{
    let data = mutex.lock().await;
    // 处理data
} // 锁自动释放
other_async_fn().await;
```

---

### 3. 过度await
```rust
// ❌ 低效：串行执行
let a = fetch_a().await;
let b = fetch_b().await;
let c = fetch_c().await;

// ✅ 高效：并发执行
let (a, b, c) = tokio::join!(
    fetch_a(),
    fetch_b(),
    fetch_c()
);
```

---

### 4. 忘记.await
```rust
// ❌ 错误：Future不会执行
let future = do_something(); // 只是创建Future，不执行！

// ✅ 正确：需要.await才执行
let result = do_something().await;
```

---

### 5. 阻塞操作
```rust
// ❌ 错误：阻塞整个线程
async fn bad() {
    std::thread::sleep(Duration::from_secs(1));
    let data = std::fs::read("file.txt").unwrap();
}

// ✅ 正确：使用异步API或spawn_blocking
async fn good() {
    tokio::time::sleep(Duration::from_secs(1)).await;
    let data = tokio::fs::read("file.txt").await.unwrap();
}

async fn good_blocking() {
    tokio::task::spawn_blocking(|| {
        std::fs::read("file.txt").unwrap()
    }).await.unwrap();
}
```

---

## 💡 最佳实践

### 1. 结构化并发
```rust
use tokio::select;

async fn structured_concurrency() {
    let mut task1 = tokio::spawn(work1());
    let mut task2 = tokio::spawn(work2());
    
    select! {
        _ = &mut task1 => {
            // task1完成，取消task2
            task2.abort();
        }
        _ = &mut task2 => {
            // task2完成，取消task1
            task1.abort();
        }
    }
}
```

---

### 2. 优雅关闭
```rust
use tokio::signal;

async fn graceful_shutdown(server: Server) {
    signal::ctrl_c().await.unwrap();
    println!("收到关闭信号，开始优雅关闭...");
    
    server.shutdown().await;
    println!("服务器已关闭");
}
```

---

### 3. 超时控制
```rust
use tokio::time::{timeout, Duration};

async fn with_timeout() {
    match timeout(Duration::from_secs(5), long_operation()).await {
        Ok(result) => println!("完成: {:?}", result),
        Err(_) => println!("超时！"),
    }
}
```

---

### 4. 错误处理
```rust
use anyhow::Result;

async fn proper_error_handling() -> Result<()> {
    let data = fetch_data().await
        .context("获取数据失败")?;
    
    process_data(data).await
        .context("处理数据失败")?;
    
    Ok(())
}
```

---

### 5. 资源管理
```rust
use tokio::sync::Semaphore;
use std::sync::Arc;

async fn resource_management() {
    let semaphore = Arc::new(Semaphore::new(10)); // 最多10个并发
    
    let permit = semaphore.acquire().await.unwrap();
    // 执行需要限制的操作
    drop(permit); // 释放许可
}
```

---

## 📊 模式选择指南

| 场景 | 推荐模式 | 替代方案 |
|------|---------|---------|
| **状态管理** | Actor | 共享状态+锁 |
| **数据处理** | Pipeline/Stream | 手动循环 |
| **并发请求** | Fan-out/Fan-in | join_all |
| **事件驱动** | Observer | 回调函数 |
| **流量控制** | 背压+Semaphore | 缓冲队列 |
| **错误恢复** | Retry + Circuit Breaker | 简单重试 |

---

## 🎓 学习路径

### 初学者
1. 先掌握基础（[../guides/](../guides/)）
2. 阅读 [02_patterns_and_pitfalls.md](./02_patterns_and_pitfalls.md)
3. 避免常见陷阱
4. 运行示例代码

### 有经验者
1. 研读 [01_patterns_comparison.md](./01_patterns_comparison.md)
2. 学习 [03_advanced_patterns.md](./03_advanced_patterns.md)
3. 应用到实际项目
4. 总结自己的模式

---

## 📖 相关资源

### 本模块资源
- [../guides/04_best_practices.md](../guides/04_best_practices.md) - 最佳实践
- [../core/](../core/) - 理论基础
- [../comprehensive/](../comprehensive/) - 综合指南

### 示例代码
```bash
cd ../../examples/patterns/
cargo run --example actor_pattern
cargo run --example pipeline_pattern
cargo run --example fan_out_in
```

### 外部资源
- [Tokio Patterns](https://tokio.rs/tokio/topics)
- [Async Rust Book - Patterns](https://rust-lang.github.io/async-book/)

---

## 🔍 快速查找

**问题导向**:
- "怎么管理状态？" → Actor模式
- "怎么并发处理？" → Fan-out/Fan-in
- "怎么处理数据流？" → Pipeline/Stream
- "怎么限制并发？" → Semaphore模式
- "怎么优雅关闭？" → Shutdown模式

**错误导向**:
- "死锁了" → [02_patterns_and_pitfalls.md](./02_patterns_and_pitfalls.md) 死锁章节
- "任务panic了" → 错误处理模式
- "性能很差" → 查看 [../performance/](../performance/)

---

**目录状态**: ✅ 完整  
**实用性**: ⭐⭐⭐⭐⭐  
**最后更新**: 2025-10-19

