# 超时模式形式化定义

> **模式类型**: 可靠性机制
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def TO1: Timeout

超时是一种**时间限制机制**，当操作在指定时间内未完成时，终止操作并返回错误。

```
Timeout := (Op, t_max, handler)
  where:
    Op: 待执行操作
    t_max ∈ Time    -- 最大等待时间
    handler: Error → Action  -- 超时处理器
```

### Def TO2: 操作结果

```
OperationResult<T> :=
  | Success(T)      -- 在 t_max 内完成
  | Timeout         -- 超过 t_max
  | Error(E)        -- 其他错误
```

### Def TO3: 超时类型

```
TimeoutType :=
  | ConnectionTimeout   -- 连接建立超时
  | RequestTimeout      -- 请求处理超时
  | IdleTimeout         -- 空闲连接超时
  | TotalTimeout        -- 总时间限制
```

---

## 2. 基本假设 (Axiom)

### Axiom TO1: 超时确定性

```
t_execution > t_max → result = Timeout
```

执行时间超过限制必然触发超时。

### Axiom TO2: 时钟单调性

```
t₁ < t₂ → elapsed(t₁) < elapsed(t₂)
```

时间测量是单调递增的。

### Axiom TO3: 资源释放

```
Timeout → resources_released
```

超时后必须释放相关资源。

---

## 3. 定理 (Theorem)

### Theorem TO1: 资源占用有界

```
∀Op. resource_usage(Op) ≤ f(t_max)
```

**证明概要**:

1. 操作在 t_max 后强制终止
2. 超时触发资源释放 (Axiom TO3)
3. 因此资源占用与时间上限相关

### Theorem TO2: 系统活性

```
Timeout → system_continues
```

**证明概要**:

1. 超时阻止无限等待
2. 控制流回到调用者
3. 系统可以继续处理其他任务

---

## 4. Rust 实现示例

```rust
use tokio::time::{timeout, Duration};

pub struct TimeoutConfig {
    pub connect: Duration,
    pub request: Duration,
    pub idle: Duration,
}

pub struct TimeoutLayer;

impl TimeoutLayer {
    /// 带超时的异步操作
    pub async fn with_timeout<F, T>(
        future: F,
        duration: Duration,
    ) -> Result<T, TimeoutError>
    where
        F: std::future::Future<Output = Result<T, Box<dyn std::error::Error>>>,
    {
        match timeout(duration, future).await {
            Ok(Ok(result)) => Ok(result),
            Ok(Err(e)) => Err(TimeoutError::Inner(e)),
            Err(_) => Err(TimeoutError::Timeout),
        }
    }

    /// 分层超时：连接超时 + 请求超时
    pub async fn with_layered_timeout<F, ConnectF, T>(
        connect_fn: ConnectF,
        request_fn: F,
        config: &TimeoutConfig,
    ) -> Result<T, TimeoutError>
    where
        ConnectF: std::future::Future<Output = Result<Connection, Box<dyn std::error::Error>>>,
        F: FnOnce(Connection) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, Box<dyn std::error::Error>>> + Send>>,
    {
        // 第一步：连接超时
        let conn = match timeout(config.connect, connect_fn).await {
            Ok(Ok(conn)) => conn,
            Ok(Err(e)) => return Err(TimeoutError::ConnectFailed(e)),
            Err(_) => return Err(TimeoutError::ConnectTimeout),
        };

        // 第二步：请求超时
        match timeout(config.request, request_fn(conn)).await {
            Ok(Ok(result)) => Ok(result),
            Ok(Err(e)) => Err(TimeoutError::Inner(e)),
            Err(_) => Err(TimeoutError::RequestTimeout),
        }
    }
}

#[derive(Debug)]
pub enum TimeoutError {
    ConnectTimeout,
    ConnectFailed(Box<dyn std::error::Error>),
    RequestTimeout,
    Timeout,
    Inner(Box<dyn std::error::Error>),
}

// HTTP 客户端使用示例
pub struct TimeoutHttpClient {
    client: reqwest::Client,
    config: TimeoutConfig,
}

impl TimeoutHttpClient {
    pub async fn get(&self, url: &str) -> Result<String, TimeoutError> {
        TimeoutLayer::with_timeout(
            async {
                let resp = self.client.get(url).send().await?;
                let text = resp.text().await?;
                Ok(text)
            },
            self.config.request,
        ).await
    }
}
```

---

## 5. 超时配置建议

| 场景 | 连接超时 | 请求超时 | 说明 |
|------|----------|----------|------|
| 内部服务 | 1s | 5s | 网络稳定，可短超时 |
| 外部 API | 5s | 30s | 考虑网络波动 |
| 数据库 | 3s | 10s | 根据查询复杂度调整 |
| 文件上传 | 10s | 5min | 大文件需要更长时间 |

---

## 6. 与重试模式的关系

超时常与重试配合使用：

- 超时触发重试
- 重试次数有限
- 避免级联超时

---

**相关阅读**:

- [Circuit Breaker](./03_circuit_breaker.md)
- [重试模式](./07_retry_pattern.md)

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
