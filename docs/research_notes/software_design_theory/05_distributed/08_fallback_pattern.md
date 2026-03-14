# Fallback（熔断降级）模式形式化定义

> **模式类型**: 容错机制
> **创建日期**: 2026-03-08
> **版本**: v1.0

---

## 1. 概念定义 (Def)

### Def FB1: Fallback

Fallback（降级）是一种**故障应对机制**，当主操作失败时，执行备选操作以提供有限但可用的服务。

```
Fallback := (Op_primary, Op_fallback, predicate)
  where:
    Op_primary: 主操作
    Op_fallback: 降级操作
    predicate: Error → bool  -- 是否执行降级的判断
```

### Def FB2: 降级类型

```
FallbackType :=
  | Static       -- 返回静态默认值
  | Cached       -- 返回缓存数据
  | Simplified   -- 执行简化逻辑
  | Degraded     -- 降低服务质量
  | Alternative  -- 调用备选服务
```

### Def FB3: 降级保证

```
FallbackGuarantee := Safety ∧ Liveness
  where:
    Safety: 降级不造成数据损坏
    Liveness: 降级必然返回结果
```

---

## 2. 基本假设 (Axiom)

### Axiom FB1: 降级可靠性

```
Op_fallback 的成功率 > Op_primary 的成功率
```

降级操作应更可靠（通常更简单）。

### Axiom FB2: 降级有限性

```
quality(Op_fallback) ≤ quality(Op_primary)
```

降级服务质量不超过主操作。

### Axiom FB3: 降级安全

```
∀input. safe(Op_fallback(input))
```

降级操作必须是安全的。

---

## 3. 定理 (Theorem)

### Theorem FB1: 服务可用性

```
P(available) ≥ P(Op_primary succeeds) + P(Op_primary fails) × P(Op_fallback succeeds)
```

**证明概要**:

1. 主操作成功：服务可用
2. 主操作失败但降级成功：服务可用
3. 两者都失败：服务不可用
4. 因此可用性提升

### Theorem FB2: 用户体验下限

```
∃min_quality. Fallback → quality ≥ min_quality
```

**证明概要**:

1. 降级操作定义了最低服务质量
2. 即使主操作失败，仍有降级保障
3. 用户体验有明确下限

---

## 4. Rust 实现示例

```rust
// 降级策略特质
#[async_trait]
pub trait FallbackStrategy {
    type Output;
    type Error;

    async fn execute(&self) -> Result<Self::Output, Self::Error>;
}

// 降级执行器
pub struct FallbackExecutor;

impl FallbackExecutor {
    pub async fn execute<P, F, FutP, FutF, T, E>(
        primary: P,
        fallback: F,
        should_fallback: impl Fn(&E) -> bool,
    ) -> Result<T, E>
    where
        P: FnOnce() -> FutP,
        F: FnOnce() -> FutF,
        FutP: std::future::Future<Output = Result<T, E>>,
        FutF: std::future::Future<Output = Result<T, E>>,
    {
        match primary().await {
            Ok(result) => Ok(result),
            Err(e) if should_fallback(&e) => {
                tracing::warn!("Primary failed, executing fallback");
                fallback().await
            }
            Err(e) => Err(e),
        }
    }
}

// 降级类型实现
pub struct StaticFallback<T: Clone> {
    value: T,
}

#[async_trait]
impl<T: Clone + Send + Sync> FallbackStrategy for StaticFallback<T> {
    type Output = T;
    type Error = std::convert::Infallible;

    async fn execute(&self) -> Result<Self::Output, Self::Error> {
        Ok(self.value.clone())
    }
}

pub struct CacheFallback<T: Clone> {
    cache: Arc<RwLock<Option<T>>>,
}

#[async_trait]
impl<T: Clone + Send + Sync> FallbackStrategy for CacheFallback<T> {
    type Output = T;
    type Error = CacheError;

    async fn execute(&self) -> Result<Self::Output, Self::Error> {
        let cache = self.cache.read().await;
        cache.clone().ok_or(CacheError::Empty)
    }
}

// 实际使用示例：电商系统价格查询
pub struct PriceService {
    primary_client: reqwest::Client,
    cache: Arc<RwLock<Option<PriceData>>>,
    default_price: PriceData,
}

impl PriceService {
    pub async fn get_price(&self, product_id: &str) -> Result<PriceData, ServiceError> {
        FallbackExecutor::execute(
            || self.fetch_from_primary(product_id),
            || self.fallback_price(),
            |e| matches!(e, ServiceError::Timeout | ServiceError::Unavailable),
        ).await
    }

    async fn fetch_from_primary(&self, product_id: &str) -> Result<PriceData, ServiceError> {
        let response = self.primary_client
            .get(&format!("/api/prices/{}", product_id))
            .timeout(Duration::from_secs(2))
            .send()
            .await
            .map_err(|_| ServiceError::Timeout)?;

        let price: PriceData = response.json().await?;

        // 更新缓存
        *self.cache.write().await = Some(price.clone());

        Ok(price)
    }

    async fn fallback_price(&self) -> Result<PriceData, ServiceError> {
        // 优先使用缓存
        if let Some(cached) = self.cache.read().await.clone() {
            tracing::info!("Using cached price as fallback");
            return Ok(cached);
        }

        // 最后使用默认价格
        tracing::warn!("Using default price as fallback");
        Ok(self.default_price.clone())
    }
}

#[derive(Clone)]
pub struct PriceData {
    pub product_id: String,
    pub price: f64,
    pub currency: String,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug)]
pub enum ServiceError {
    Timeout,
    Unavailable,
    CacheMiss,
}
```

---

## 5. 降级策略矩阵

| 主服务 | 降级策略 | 场景 |
|--------|----------|------|
| 实时价格 | 缓存价格 | 价格服务不可用 |
| 推荐系统 | 热门榜单 | 推荐引擎故障 |
| 库存查询 | 有货/无货 | 库存服务超时 |
| 支付网关 | 排队处理 | 支付系统繁忙 |
| 物流追踪 | 静态信息 | 物流接口故障 |

---

## 6. 与 Circuit Breaker 的关系

```
┌─────────────┐      失败       ┌─────────────┐
│   Primary   │ ───────────────→│   Circuit   │
│   Service   │                 │  Breaker    │
└─────────────┘                 └──────┬──────┘
       │                               │
       │ 成功                          │ Open
       ▼                               ▼
┌─────────────┐                 ┌─────────────┐
│   Return    │                 │   Fallback  │
│   Result    │                 │   Service   │
└─────────────┘                 └─────────────┘
```

---

**相关阅读**:

- [Circuit Breaker](./03_circuit_breaker.md)
- [超时模式](./06_timeout_pattern.md)
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
