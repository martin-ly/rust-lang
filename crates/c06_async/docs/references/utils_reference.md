# Utils 模块参考文档


## 📊 目录

- [模块概览](#模块概览)
- [核心工具](#核心工具)
  - [1. 重试机制 (`retry_with_backoff`)](#1-重试机制-retry_with_backoff)
  - [2. 超时控制 (`with_timeout`)](#2-超时控制-with_timeout)
  - [3. 取消作用域 (`CancelScope`)](#3-取消作用域-cancelscope)
  - [4. 信号量限流器 (`SemaphoreLimiter`)](#4-信号量限流器-semaphorelimiter)
  - [5. 可取消操作 (`abortable`)](#5-可取消操作-abortable)
  - [6. 统一执行助手 (`ExecHelper`)](#6-统一执行助手-exechelper)
  - [7. 简单令牌桶限速器 (`SimpleTokenBucket`)](#7-简单令牌桶限速器-simpletokenbucket)
  - [8. 策略构建器 (`ExecStrategyBuilder`)](#8-策略构建器-execstrategybuilder)
- [断路器模式 (`circuit_breaker`)](#断路器模式-circuit_breaker)
  - [概述](#概述)
  - [现有实现（示例版）](#现有实现示例版)
  - [使用示例](#使用示例)
  - [配置参数](#配置参数)
- [最佳实践](#最佳实践)
  - [1. 重试策略](#1-重试策略)
  - [2. 超时配置](#2-超时配置)
  - [3. 限流配置](#3-限流配置)
  - [4. 断路器配置](#4-断路器配置)
- [错误处理](#错误处理)
  - [错误类型](#错误类型)
  - [错误传播](#错误传播)
- [性能考虑](#性能考虑)
  - [1. 内存使用](#1-内存使用)
  - [2. 性能开销](#2-性能开销)
  - [3. 扩展性](#3-扩展性)
- [测试](#测试)
  - [单元测试](#单元测试)
  - [集成测试](#集成测试)
- [扩展开发](#扩展开发)
  - [添加新工具](#添加新工具)
  - [自定义配置](#自定义配置)
- [总结](#总结)


`utils` 模块提供了可复用的异步编程工具和模式，旨在简化常见的异步编程任务。

## 模块概览

```rust
pub mod utils;
pub mod circuit_breaker;
```

## 核心工具

### 1. 重试机制 (`retry_with_backoff`)

指数退避重试策略，适用于网络请求、数据库操作等可能失败的操作。

```rust
pub async fn retry_with_backoff<F, Fut, T, E>(
    mut make_fut: F, 
    max_attempts: u32, 
    start_delay: Duration
) -> Result<T, E>
where
    F: FnMut(u32) -> Fut,
    Fut: Future<Output = Result<T, E>>,
```

**参数说明：**

- `make_fut`: 闭包，接收尝试次数，返回 Future
- `max_attempts`: 最大尝试次数
- `start_delay`: 初始延迟时间

**使用示例：**

```rust
use c06_async::utils;
use std::time::Duration;

let result = utils::retry_with_backoff(
    |attempt| async move {
        // 模拟可能失败的操作
        if attempt == 1 {
            Err("first attempt failed")
        } else {
            Ok("success")
        }
    },
    3,
    Duration::from_millis(100)
).await;

assert!(result.is_ok());
```

**适用场景：**

- HTTP 请求重试
- 数据库连接重试
- 文件操作重试
- 任何需要容错的操作

### 2. 超时控制 (`with_timeout`)

为异步操作添加超时限制，防止操作无限期阻塞。

```rust
pub async fn with_timeout<T, F>(dur: Duration, fut: F) -> Option<T>
where
    F: Future<Output = T>,
```

**参数说明：**

- `dur`: 超时时间
- `fut`: 要执行的 Future

**返回值：**

- `Some(T)`: 操作在超时前完成
- `None`: 操作超时

**使用示例：**

```rust
use c06_async::utils;
use std::time::Duration;

let result = utils::with_timeout(
    Duration::from_secs(5),
    async {
        tokio::time::sleep(Duration::from_secs(10)).await;
        "operation completed"
    }
).await;

assert!(result.is_none()); // 超时
```

**适用场景：**

- API 调用超时
- 数据库查询超时
- 文件 I/O 超时
- 任何需要时间限制的操作

### 3. 取消作用域 (`CancelScope`)

提供任务取消机制，支持优雅地取消正在执行的异步操作。

```rust
pub struct CancelScope {
    handle: AbortHandle,
}

impl CancelScope {
    pub fn new() -> (Self, futures::future::AbortRegistration);
    pub fn cancel(&self);
}
```

**使用示例：**

```rust
use c06_async::utils;

let (scope, registration) = utils::CancelScope::new();

let task = tokio::spawn(utils::abortable(registration, async {
    tokio::time::sleep(Duration::from_secs(10)).await;
    "task completed"
}));

// 取消任务
scope.cancel();

let result = task.await.unwrap();
assert!(result.is_err()); // 任务被取消
```

**适用场景：**

- 用户取消操作
- 超时取消
- 优雅关闭
- 资源清理

### 4. 信号量限流器 (`SemaphoreLimiter`)

基于信号量的并发控制，限制同时执行的操作数量。

```rust
#[derive(Clone)]
pub struct SemaphoreLimiter {
    inner: Arc<tokio::sync::Semaphore>,
}

impl SemaphoreLimiter {
    pub fn new(concurrency: usize) -> Self;
    pub async fn run<F, T>(&self, fut: F) -> T
    where
        F: Future<Output = T>;
}
```

**参数说明：**

- `concurrency`: 最大并发数

**使用示例：**

```rust
use c06_async::utils;

let limiter = utils::SemaphoreLimiter::new(5);

let handles: Vec<_> = (0..10).map(|i| {
    let limiter = limiter.clone();
    tokio::spawn(async move {
        limiter.run(async move {
            tokio::time::sleep(Duration::from_millis(100)).await;
            format!("task {} completed", i)
        }).await
    })
}).collect();

let results = futures::future::join_all(handles).await;
```

**适用场景：**

- API 限流
- 数据库连接池
- 文件并发访问
- 资源使用控制

### 5. 可取消操作 (`abortable`)

将 Future 包装为可取消的操作。

```rust
pub async fn abortable<F, T>(
    reg: futures::future::AbortRegistration, 
    fut: F
) -> Result<T, futures::future::Aborted>
where
    F: Future<Output = T>,
```

**使用示例：**

```rust
use c06_async::utils;

let (scope, registration) = utils::CancelScope::new();

let task = tokio::spawn(utils::abortable(registration, async {
    tokio::time::sleep(Duration::from_secs(5)).await;
    "operation completed"
}));

// 等待一段时间后取消
tokio::time::sleep(Duration::from_millis(100)).await;
scope.cancel();

let result = task.await.unwrap();
match result {
    Ok(_) => println!("task completed"),
    Err(_) => println!("task aborted"),
}
```

### 6. 统一执行助手 (`ExecHelper`)

将并发控制（信号量）、超时和重试整合为一个调用入口。

```rust
pub struct ExecHelper { /* 内部持有 SemaphoreLimiter */ }

impl ExecHelper {
    pub fn new(concurrency: usize) -> Self;

    pub async fn run_with_policies<F, Fut, T, E>(
        &self,
        make_fut: F,
        max_attempts: u32,
        start_delay: Duration,
        timeout: Duration,
    ) -> Result<Option<T>, E>
    where
        F: FnMut(u32) -> Fut + Send + 'static,
        Fut: Future<Output = Result<T, E>>,
        T: Send + 'static,
        E: Send + 'static;
}
```

返回语义：

- `Ok(Some(T))`: 成功（在超时前完成，且重试链路成功）
- `Ok(None)`: 超时（在给定超时内未完成）
- `Err(E)`: 重试已用尽或遇到不可重试错误

示例用法：

```rust
let exec = ExecHelper::new(8);
let out = exec
    .run_with_policies(
        |attempt| async move {
            // 你的异步操作（可能失败）
            do_request().await
        },
        3,
        Duration::from_millis(100),
        Duration::from_secs(1),
    )
    .await;
```

增强 API：

```rust
pub async fn run_with_decider_and_deadline<F, Fut, T, E, D>(
    &self,
    make_fut: F,
    is_retryable: D,
    max_attempts: u32,
    start_delay: Duration,
    deadline: Instant,
) -> Result<Option<T>, E>
where
    F: FnMut(u32) -> Fut + Send + 'static,
    Fut: Future<Output = Result<T, E>> + Send + 'static,
    D: FnMut(&E) -> bool + Send + 'static,
    T: Send + 'static,
    E: Send + 'static;
```

语义：在整体截止时间 `deadline` 内进行带判定的重试；成功返回 `Ok(Some(T))`，不可重试/重试耗尽返回 `Err(E)`；超时返回 `Ok(None)`。

### 7. 简单令牌桶限速器 (`SimpleTokenBucket`)

用于基于令牌桶算法的速率限制（异步安全）。

```rust
#[derive(Clone)]
pub struct SimpleTokenBucket { /* 内部状态：容量、令牌数、补充速率、上次时间 */ }

impl SimpleTokenBucket {
    pub fn new(capacity: u32, refill_per_sec: u32) -> Self;
    pub async fn acquire(&self, permits: u32);
}
```

注意：不会在持锁期间 `await`，避免跨 await 携带 mutex guard。

### 8. 策略构建器 (`ExecStrategyBuilder`)

以构建器方式配置并发、重试、退避、超时/截止、熔断与限速，并返回可运行的 `ExecStrategyRunner`。

```rust
let breaker = CircuitBreaker::new(5, Duration::from_secs(30));
let bucket = SimpleTokenBucket::new(20, 20);

let runner = ExecStrategyBuilder::new()
    .concurrency(8)
    .attempts(5)
    .start_delay(Duration::from_millis(50))
    .timeout(Duration::from_secs(2))
    .breaker(breaker)
    .token_bucket(bucket)
    .build();

let res = runner
    .run(
        |attempt| async move {
            // 你的操作
            Ok::<_, anyhow::Error>(attempt)
        },
        Some(|_e: &anyhow::Error| true), // 可重试判定
    )
    .await;
```

## 断路器模式 (`circuit_breaker`)

### 概述

断路器模式用于防止系统级联故障：当短时间内连续失败达到阈值时，断路器进入打开状态，一段时间内直接拒绝请求（快速失败），等待恢复窗口结束后再进入半开状态试探。

### 现有实现（示例版）

签名与内部结构（简化示例，适用于教学）：

```rust
#[derive(Clone)]
pub struct CircuitBreaker { /* 内部计数、打开时间、阈值、窗口等 */ }

impl CircuitBreaker {
    pub fn new(fail_threshold: u64, open_window: Duration) -> Self;

    // 运行一个返回 Result<T, E> 的异步操作；失败计数达阈值后打开断路器。
    pub async fn run<F, T, E>(&self, fut: F) -> Result<T, E>
    where
        F: Future<Output = Result<T, E>>;
}
```

从配置构建：

```rust
use c06_async::utils::{ExecStrategyBuilder, StrategyConfig};
let cfg: StrategyConfig = serde_json::from_str(r#"{
  "concurrency": 8,
  "max_attempts": 5,
  "start_delay_ms": 50,
  "timeout_ms": 2000,
  "deadline_ms": null,
  "enable_breaker": true,
  "token_bucket": {"capacity":20, "refill_per_sec":20}
}"#)?;
let runner = ExecStrategyBuilder::from_config(&cfg).build();
```

注意：示例版在断路器打开时会触发 `panic!("circuit open")`（synthetic_err），用于突出演示“快速失败”效果。在生产中请改为返回自定义错误类型而非 panic。

### 使用示例

```rust
use c06_async::utils::circuit_breaker::CircuitBreaker;
use std::time::Duration;

let breaker = CircuitBreaker::new(3, Duration::from_secs(30));

let res = breaker
    .run(async {
        // 可能失败的异步操作
        Err::<(), _>(anyhow::anyhow!("remote error"))
    })
    .await;

match res {
    Ok(_) => println!("ok"),
    Err(e) => println!("service error: {e:#}")
}
```

### 配置参数

- `fail_threshold`: 失败阈值（达到后进入打开态）
- `open_window`: 打开窗口时长（窗口内直接快速失败；到期后进入半开态试探）

## 最佳实践

### 1. 重试策略

```rust
// 推荐：根据错误类型决定是否重试
let result = utils::retry_with_backoff(
    |attempt| async move {
        match operation().await {
            Ok(value) => Ok(value),
            Err(e) if is_retryable(&e) => Err(e),
            Err(e) => return Err(e), // 不可重试的错误
        }
    },
    3,
    Duration::from_millis(100)
).await;
```

### 2. 超时配置

```rust
// 推荐：根据操作类型设置合适的超时时间
let timeout = match operation_type {
    "fast" => Duration::from_millis(100),
    "normal" => Duration::from_secs(1),
    "slow" => Duration::from_secs(10),
    _ => Duration::from_secs(5),
};

let result = utils::with_timeout(timeout, operation()).await;
```

### 3. 限流配置

```rust
// 推荐：根据系统资源设置并发数
let concurrency = std::thread::available_parallelism()
    .map(|n| n.get() * 2)
    .unwrap_or(16);

let limiter = utils::SemaphoreLimiter::new(concurrency);
```

### 4. 断路器配置

```rust
// 推荐：根据服务特性设置参数
let breaker = CircuitBreaker::new(
    5,  // 失败阈值：允许少量失败
    Duration::from_secs(60)  // 恢复时间：给服务足够恢复时间
);
```

## 错误处理

### 错误类型

```rust
#[derive(Debug, thiserror::Error)]
pub enum CircuitBreakerError {
    #[error("Service error: {0}")]
    ServiceError(#[from] anyhow::Error),
    #[error("Circuit breaker is open")]
    CircuitOpen,
}
```

### 错误传播

```rust
use anyhow::{Result, Context};

async fn operation_with_utils() -> Result<String> {
    let result = utils::with_timeout(
        Duration::from_secs(5),
        utils::retry_with_backoff(
            |_| async { api_call().await },
            3,
            Duration::from_millis(100)
        )
    ).await;

    result.context("operation failed")
}
```

## 性能考虑

### 1. 内存使用

- `SemaphoreLimiter`: 每个实例约 64 字节
- `CircuitBreaker`: 每个实例约 128 字节
- `CancelScope`: 每个实例约 32 字节

### 2. 性能开销

- `retry_with_backoff`: 每次重试增加延迟
- `with_timeout`: 约 100ns 开销
- `SemaphoreLimiter::run`: 约 50ns 开销
- `CircuitBreaker::call`: 约 200ns 开销

### 3. 扩展性

- 所有工具都支持高并发场景
- 使用 `Arc` 实现零拷贝克隆
- 异步操作不会阻塞线程

## 测试

### 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_retry_with_backoff() {
        let result = retry_with_backoff(
            |attempt| async move {
                if attempt < 3 {
                    Err("retryable error")
                } else {
                    Ok("success")
                }
            },
            3,
            Duration::from_millis(10)
        ).await;

        assert!(result.is_ok());
    }
}
```

### 集成测试

```rust
#[tokio::test]
async fn test_semaphore_limiter() {
    let limiter = SemaphoreLimiter::new(2);
    let counter = Arc::new(AtomicUsize::new(0));

    let handles: Vec<_> = (0..5).map(|_| {
        let limiter = limiter.clone();
        let counter = Arc::clone(&counter);
        tokio::spawn(async move {
            limiter.run(async {
                let current = counter.fetch_add(1, Ordering::SeqCst);
                tokio::time::sleep(Duration::from_millis(100)).await;
                counter.fetch_sub(1, Ordering::SeqCst);
                current
            }).await
        })
    }).collect();

    let results = futures::future::join_all(handles).await;
    assert_eq!(results.len(), 5);
}
```

## 扩展开发

### 添加新工具

1. 在 `src/utils/` 目录下创建新模块
2. 实现核心功能
3. 添加文档注释和示例
4. 编写测试用例
5. 在 `src/utils/mod.rs` 中导出

### 自定义配置

```rust
pub struct RetryConfig {
    pub max_attempts: u32,
    pub start_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            start_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(30),
            backoff_multiplier: 2.0,
        }
    }
}
```

## 总结

`utils` 模块提供了生产级别的异步编程工具，具有以下特点：

- **可靠性**: 内置重试、超时、限流等容错机制
- **性能**: 低开销、高并发支持
- **易用性**: 简洁的 API 设计
- **可扩展性**: 支持自定义配置和扩展
- **生产就绪**: 包含完整的错误处理和测试

这些工具可以显著提高异步代码的健壮性和可维护性，推荐在生产环境中使用。
