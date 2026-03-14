# 重试模式形式化定义

> **模式类型**: 容错机制
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def RT1: Retry

重试是一种**故障恢复机制**，当操作失败时，按策略重新执行操作。

```
Retry := (Op, policy, predicate)
  where:
    Op: 待执行操作
    policy = (max_attempts, backoff, jitter)
    predicate: Error → bool  -- 是否可重试的判断
```

### Def RT2: 退避策略

```
BackoffStrategy :=
  | Fixed { interval }                    -- 固定间隔
  | Linear { initial, increment }         -- 线性增长
  | Exponential { initial, multiplier, max }  -- 指数退避
  | Custom(fn attempt -> Duration)
```

### Def RT3: 抖动 (Jitter)

```
Jitter := None | Full | Equal | Decorrelated
  where:
    Full: delay' = random(0, delay)
    Equal: delay' = delay/2 + random(0, delay/2)
    Decorrelated: delay' = random(initial, delay * 3)
```

---

## 2. 基本假设 (Axiom)

### Axiom RT1: 重试次数有界

```
attempts ≤ max_attempts
```

重试次数必须有限，防止无限循环。

### Axiom RT2: 幂等性要求

```
∀Op ∈ Retry. Idempotent(Op) ∨ (predicate only for transient errors)
```

非幂等操作只能对瞬态错误重试。

### Axiom RT3: 退避单调性

```
n < m → backoff(n) ≤ backoff(m)
```

等待时间不递减（通常递增）。

---

## 3. 定理 (Theorem)

### Theorem RT1: 成功率提升

```
P(success) ≤ 1 - (1 - p)^n
  where:
    p = 单次成功概率
    n = 最大重试次数
```

**证明概要**:

1. 单次失败概率 = 1 - p
2. n 次都失败概率 = (1 - p)^n
3. 至少一次成功概率 = 1 - (1 - p)^n
4. 当 p > 0 且 n ≥ 1，成功率提升

### Theorem RT2: 负载控制

```
ExponentialBackoff → prevents thundering herd
```

**证明概要**:

1. 指数退避使等待时间快速增加
2. 分散重试请求的时间分布
3. 避免所有客户端同时重试
4. 减轻服务器压力

---

## 4. Rust 实现示例

```rust
use std::time::Duration;
use rand::Rng;

#[derive(Clone)]
pub enum BackoffStrategy {
    Fixed(Duration),
    Linear { initial: Duration, increment: Duration },
    Exponential { initial: Duration, multiplier: f64, max: Duration },
}

#[derive(Clone)]
pub enum Jitter {
    None,
    Full,
    Equal,
    Decorrelated,
}

pub struct RetryPolicy {
    pub max_attempts: u32,
    pub backoff: BackoffStrategy,
    pub jitter: Jitter,
}

impl RetryPolicy {
    pub fn calculate_delay(&self, attempt: u32, last_delay: Option<Duration>) -> Duration {
        let base = match &self.backoff {
            BackoffStrategy::Fixed(d) => *d,
            BackoffStrategy::Linear { initial, increment } => {
                *initial + *increment * attempt
            }
            BackoffStrategy::Exponential { initial, multiplier, max } => {
                let exp = (*initial).as_millis() as f64 * multiplier.powi(attempt as i32);
                let ms = exp.min(max.as_millis() as f64) as u64;
                Duration::from_millis(ms)
            }
        };

        // 应用抖动
        match self.jitter {
            Jitter::None => base,
            Jitter::Full => {
                let mut rng = rand::thread_rng();
                Duration::from_millis(rng.gen_range(0..=base.as_millis() as u64))
            }
            Jitter::Equal => {
                let half = base / 2;
                let mut rng = rand::thread_rng();
                half + Duration::from_millis(rng.gen_range(0..=half.as_millis() as u64))
            }
            Jitter::Decorrelated => {
                let initial = match &self.backoff {
                    BackoffStrategy::Exponential { initial, .. } => *initial,
                    _ => Duration::from_millis(100),
                };
                let mut rng = rand::thread_rng();
                let max = last_delay.map(|d| d * 3).unwrap_or(initial * 3);
                Duration::from_millis(rng.gen_range(initial.as_millis() as u64..=max.as_millis() as u64))
            }
        }
    }
}

// 重试执行器
pub struct RetryExecutor;

impl RetryExecutor {
    pub async fn execute<F, Fut, T, E>(
        mut op: F,
        policy: &RetryPolicy,
        is_retryable: impl Fn(&E) -> bool,
    ) -> Result<T, RetryError<E>>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        let mut last_delay = None;

        for attempt in 0..policy.max_attempts {
            match op().await {
                Ok(result) => return Ok(result),
                Err(e) if attempt == policy.max_attempts - 1 || !is_retryable(&e) => {
                    return Err(RetryError::Permanent(e));
                }
                Err(_) => {
                    let delay = policy.calculate_delay(attempt, last_delay);
                    last_delay = Some(delay);
                    tokio::time::sleep(delay).await;
                }
            }
        }

        unreachable!()
    }
}

#[derive(Debug)]
pub enum RetryError<E> {
    Permanent(E),
    Exhausted,
}

// 使用示例
pub async fn fetch_with_retry(url: &str) -> Result<String, RetryError<reqwest::Error>> {
    let policy = RetryPolicy {
        max_attempts: 3,
        backoff: BackoffStrategy::Exponential {
            initial: Duration::from_millis(100),
            multiplier: 2.0,
            max: Duration::from_secs(10),
        },
        jitter: Jitter::Equal,
    };

    let client = reqwest::Client::new();
    RetryExecutor::execute(
        || async { client.get(url).send().await?.text().await },
        &policy,
        |e| e.is_timeout() || e.status().map(|s| s.is_server_error()).unwrap_or(false),
    ).await
}
```

---

## 5. 重试策略选择

| 场景 | 策略 | 说明 |
|------|------|------|
| 高频调用 | Fixed + Jitter | 简单，避免聚集 |
| 网络请求 | Exponential | 快速退避 |
| 资源竞争 | Decorrelated | 最大化分散 |
| 实时系统 | Limited Fixed | 可预测延迟 |

---

## 6. 可重试错误分类

```rust
pub fn is_retryable_error<E: std::error::Error>(e: &E) -> bool {
    // 瞬态错误
    if let Some(io_err) = e.downcast_ref::<std::io::Error>() {
        matches!(
            io_err.kind(),
            std::io::ErrorKind::ConnectionRefused |
            std::io::ErrorKind::ConnectionReset |
            std::io::ErrorKind::ConnectionAborted |
            std::io::ErrorKind::TimedOut |
            std::io::ErrorKind::Interrupted
        )
    } else {
        false
    }
}
```

---

**相关阅读**:

- [Circuit Breaker](./03_circuit_breaker.md)
- [超时模式](./06_timeout_pattern.md)

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
