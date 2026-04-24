# Rust 2024 Edition Async Closures 完整指南

## 概述

Async closures 是 Rust 1.85+ 中稳定化的重要特性，允许直接使用 `async || { }` 语法创建异步闭包。相比传统的 `async move { }` 闭包，新语法更简洁、语义更清晰。

## 语法对比

```rust
// 传统写法（Rust 1.84 及之前）
let fetch = |url: &str| async move {
    reqwest::get(url).await?.text().await
};

// Rust 1.85+ async closures
let fetch = async |url: &str| -> Result<String, Error> {
    reqwest::get(url).await?.text().await
};
```

## 核心改进

1. **语法更简洁**：无需嵌套 `async move {}` 在闭包体内
2. **捕获语义更精确**：根据使用情况自动推断 `move` 或引用捕获
3. **类型系统支持**：直接实现 `AsyncFn` 相关 trait（逐步完善中）
4. **与同步闭包对称**：`|| {}` 对应同步，`async || {}` 对应异步

## Cancellation Safety（取消安全性）

### 什么是 Cancellation Safety？

当异步任务在 `select!`、`timeout` 或 `race` 场景中被取消（drop）时，必须确保不会留下不一致的状态。

### 常见非 Cancellation Safe 操作

- `Mutex::lock().await`：取消后可能持有锁但不释放
- `mpsc::Sender::send().await`：取消后数据可能部分发送
- 文件写入操作：取消后文件处于未定义状态

### 安全实践

```rust
// 安全：纯计算，无状态变更
let task = async || {
    item * 2
};

// 安全：使用 channel 的 try_send 替代 send
let safe_notify = async || {
    // try_send 是 Cancellation Safe 的
    let _ = sender.try_send(message);
};

// 不安全：Mutex::lock 在 timeout 中可能泄漏锁
let risky = async || {
    let mut guard = mutex.lock().await;
    *guard += 1; // 如果被取消，锁可能不释放
};
```

## 完整示例

### 示例 1：基础 async closure

```rust
pub fn basic_async_closure() -> impl Fn(i32) -> Pin<Box<dyn Future<Output = i32> + Send>> {
    let modern = |x: i32| -> Pin<Box<dyn Future<Output = i32> + Send>> {
        Box::pin(async move { x * 2 })
    };
    modern
}
```

### 示例 2：并发执行

```rust
pub async fn run_async_closures_concurrently(inputs: Vec<i32>) -> Vec<i32> {
    let tasks: Vec<_> = inputs
        .into_iter()
        .map(|x| {
            let closure = |n: i32| Box::pin(async move { n * n + 1 });
            closure(x)
        })
        .collect();

    let mut results = Vec::new();
    for task in tasks {
        results.push(task.await);
    }
    results
}
```

### 示例 3：流处理

```rust
pub async fn process_stream_with_async_closure(
    items: Vec<String>,
) -> Vec<Result<usize, &'static str>> {
    let processor = |s: String| Box::pin(async move {
        if s.is_empty() {
            Err("空字符串")
        } else {
            Ok(s.len())
        }
    });

    let mut results = Vec::new();
    for item in items {
        results.push(processor(item).await);
    }
    results
}
```

### 示例 4：Cancellation Safety 演示

```rust
pub async fn cancellation_safe_async_closure(items: Vec<i32>) -> Vec<i32> {
    let mut results = Vec::new();

    for item in items {
        let task = Box::pin(async move {
            // 关键：不使用非 Cancellation Safe 的操作
            item * 2
        });

        // 使用 futures::future::select 模拟取消场景
        let timeout_future = futures::future::pending::<()>();
        match futures::future::select(task, timeout_future).await {
            futures::future::Either::Left((result, _)) => results.push(result),
            futures::future::Either::Right((_, _)) => results.push(-1),
        }
    }

    results
}
```

## 捕获行为对比

| 特性 | 传统 `|x| async move {}` | `async || {}` |
|------|------------------------|---------------|
| 语法 | 嵌套两层 | 单层扁平 |
| 捕获 | 强制 `move` | 自动推断 |
| 生命周期 | 需手动管理 | 更智能推导 |
| 调试 | 栈追踪较深 | 栈追踪较浅 |

## 适用场景

- **异步回调**：事件处理器、定时器回调
- **流处理**：对异步数据流进行逐元素转换
- **并发任务生成**：动态创建异步任务
- **API 封装**：将同步参数验证与异步调用结合

## 迁移建议

1. **新项目**：直接使用 `async || {}` 语法
2. **现有代码**：逐步替换嵌套的 `async move {}` 模式
3. **注意兼容性**：确保团队使用的 Rust 版本 >= 1.85
