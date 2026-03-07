# 降级模式语义 (Degradation Pattern Semantics)

## 目录

- [降级模式语义 (Degradation Pattern Semantics)](#降级模式语义-degradation-pattern-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 降级策略分类](#2-降级策略分类)
    - [2.1 降级类型谱系](#21-降级类型谱系)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 数学模型](#3-数学模型)
    - [3.1 负载计算模型](#31-负载计算模型)
    - [3.2 功能权重模型](#32-功能权重模型)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 核心降级框架](#41-核心降级框架)
    - [4.2 回退机制实现](#42-回退机制实现)
    - [4.3 特性开关集成](#43-特性开关集成)
    - [4.4 负载削减实现](#44-负载削减实现)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 降级安全性](#51-降级安全性)
    - [5.2 回退正确性](#52-回退正确性)
  - [6. 总结](#6-总结)

## 1. 引言

优雅降级是分布式系统在高负载或部分故障时保持核心功能可用的关键策略。
本文档深入分析降级模式的语义基础、实现机制及其在 Rust 中的应用。

---

## 2. 降级策略分类

### 2.1 降级类型谱系

```
降级策略层次:

┌──────────────────────────────────────────────────────────────────┐
│                     优雅降级策略                                  │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │                     功能降级 (Feature Degradation)         │  │
│  │                                                            │  │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │  │
│  │  │ 核心功能     │  │ 可选功能     │  │ 实验功能     │     │  │
│  │  │ Critical     │  │ Optional     │  │ Experimental │     │  │
│  │  │              │  │              │  │              │     │  │
│  │  │ 永不下线     │  │ 优先降级     │  │ 首先关闭     │     │  │
│  │  └──────────────┘  └──────────────┘  └──────────────┘     │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │                     数据降级 (Data Degradation)            │  │
│  │                                                            │  │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │  │
│  │  │ 完整数据     │  │ 摘要数据     │  │ 缓存数据     │     │  │
│  │  │ Full         │  │ Summary      │  │ Cached       │     │  │
│  │  │              │  │              │  │              │     │  │
│  │  │ 实时一致     │  │ 聚合视图     │  │ 可能陈旧     │     │  │
│  │  └──────────────┘  └──────────────┘  └──────────────┘     │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │                     质量降级 (Quality Degradation)         │  │
│  │                                                            │  │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐     │  │
│  │  │ 高分辨率     │  │ 标准质量     │  │ 低保真       │     │  │
│  │  │ HD           │  │ SD           │  │ Thumbnail    │     │  │
│  │  │              │  │              │  │              │     │  │
│  │  │ 资源密集     │  │ 平衡模式     │  │ 快速响应     │     │  │
│  │  └──────────────┘  └──────────────┘  └──────────────┘     │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
降级形式化语义:

服务状态空间:
  S = {Normal, Degraded₁, Degraded₂, ..., Emergency}

降级函数:
  Degrade: S × Load × Health → S

  Degrade(Normal, load, health) =
    Normal      if load < threshold₁ ∧ health = OK
    Degraded₁   if threshold₁ ≤ load < threshold₂ ∨ health = Warning
    Degraded₂   if threshold₂ ≤ load < threshold₃ ∨ health = Critical
    Emergency   if load ≥ threshold₃ ∨ health = Failed

功能可用性:
  Availability: Feature × S → {Full, Partial, None}

降级矩阵:
  ┌─────────────┬─────────┬───────────┬───────────┬───────────┐
  │ Feature     │ Normal  │ Degraded₁ │ Degraded₂ │ Emergency │
  ├─────────────┼─────────┼───────────┼───────────┼───────────┤
  │ Core        │ Full    │ Full      │ Full      │ Partial   │
  │ Important   │ Full    │ Full      │ Partial   │ None      │
  │ Optional    │ Full    │ Partial   │ None      │ None      │
  │ Experimental│ Partial │ None      │ None      │ None      │
  └─────────────┴─────────┴───────────┴───────────┴───────────┘

降级不变式:
  □ (Degraded(s) → Availability(Core, s) ≥ Partial)
  □ (Emergency → Availability(CriticalFeatures) > None)
```

---

## 3. 数学模型

### 3.1 负载计算模型

```
综合负载指数:

Load = w₁ × CPU% + w₂ × Memory% + w₃ × RequestRate/RPS_capacity
     + w₄ × Latency/p99_threshold + w₅ × ErrorRate

其中 w₁ + w₂ + w₃ + w₄ + w₅ = 1

归一化到 [0, 1] 区间:
Load_norm = tanh(Load × scale_factor)

健康分数:
HealthScore = 1 - Load_norm
```

### 3.2 功能权重模型

```
功能重要性评分:

Importance(feature) = w₁ × UserImpact + w₂ × BusinessValue
                    + w₃ × Dependencies + w₄ × ResourceCost

降级优先级:
Priority(feature) = Importance(feature)⁻¹

资源分配（降级时）:
Resource(feature) = Resource_total × Importance(feature) / Σ Importance(fᵢ)
```

---

## 4. Rust 实现

### 4.1 核心降级框架

```rust
use std::collections::HashMap;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Arc;
use tokio::sync::{RwLock, broadcast};
use async_trait::async_trait;

/// 系统健康级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum HealthLevel {
    /// 完全健康
    Healthy = 0,
    /// 轻微降级
    MildDegraded = 1,
    /// 中度降级
    ModerateDegraded = 2,
    /// 严重降级
    SevereDegraded = 3,
    /// 紧急模式（仅核心功能）
    Emergency = 4,
}

/// 功能类别
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FeatureClass {
    /// 核心功能（永不降级）
    Critical,
    /// 重要功能
    Essential,
    /// 标准功能
    Standard,
    /// 可选功能
    Optional,
    /// 实验性功能（首先降级）
    Experimental,
}

/// 功能状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FeatureState {
    /// 完全可用
    Full,
    /// 部分可用（限速/限流）
    Partial { capacity_percent: u8 },
    /// 只读模式
    ReadOnly,
    /// 不可用
    Disabled,
}

/// 功能定义
#[derive(Debug, Clone)]
pub struct Feature {
    pub id: String,
    pub class: FeatureClass,
    pub name: String,
    pub current_state: FeatureState,
    pub default_state: FeatureState,
}

/// 降级策略配置
#[derive(Debug, Clone)]
pub struct DegradationPolicy {
    /// 触发降级的健康阈值
    pub health_thresholds: HashMap<HealthLevel, f64>,
    /// 各健康级别下的功能状态映射
    pub feature_policies: HashMap<FeatureClass, HashMap<HealthLevel, FeatureState>>,
    /// 恢复延迟（防止抖动）
    pub recovery_delay: std::time::Duration,
    /// 降级延迟
    pub degradation_delay: std::time::Duration,
}

impl Default for DegradationPolicy {
    fn default() -> Self {
        let mut health_thresholds = HashMap::new();
        health_thresholds.insert(HealthLevel::Healthy, 0.9);
        health_thresholds.insert(HealthLevel::MildDegraded, 0.7);
        health_thresholds.insert(HealthLevel::ModerateDegraded, 0.5);
        health_thresholds.insert(HealthLevel::SevereDegraded, 0.3);
        health_thresholds.insert(HealthLevel::Emergency, 0.0);

        let mut feature_policies = HashMap::new();

        // Critical 功能永不降级
        let mut critical_map = HashMap::new();
        critical_map.insert(HealthLevel::Healthy, FeatureState::Full);
        critical_map.insert(HealthLevel::MildDegraded, FeatureState::Full);
        critical_map.insert(HealthLevel::ModerateDegraded, FeatureState::Full);
        critical_map.insert(HealthLevel::SevereDegraded, FeatureState::Partial { capacity_percent: 80 });
        critical_map.insert(HealthLevel::Emergency, FeatureState::Partial { capacity_percent: 50 });
        feature_policies.insert(FeatureClass::Critical, critical_map);

        // Essential 功能
        let mut essential_map = HashMap::new();
        essential_map.insert(HealthLevel::Healthy, FeatureState::Full);
        essential_map.insert(HealthLevel::MildDegraded, FeatureState::Full);
        essential_map.insert(HealthLevel::ModerateDegraded, FeatureState::Partial { capacity_percent: 70 });
        essential_map.insert(HealthLevel::SevereDegraded, FeatureState::Partial { capacity_percent: 50 });
        essential_map.insert(HealthLevel::Emergency, FeatureState::Disabled);
        feature_policies.insert(FeatureClass::Essential, essential_map);

        // Optional 功能
        let mut optional_map = HashMap::new();
        optional_map.insert(HealthLevel::Healthy, FeatureState::Full);
        optional_map.insert(HealthLevel::MildDegraded, FeatureState::Partial { capacity_percent: 50 });
        optional_map.insert(HealthLevel::ModerateDegraded, FeatureState::Disabled);
        optional_map.insert(HealthLevel::SevereDegraded, FeatureState::Disabled);
        optional_map.insert(HealthLevel::Emergency, FeatureState::Disabled);
        feature_policies.insert(FeatureClass::Optional, optional_map);

        Self {
            health_thresholds,
            feature_policies,
            recovery_delay: std::time::Duration::from_secs(60),
            degradation_delay: std::time::Duration::from_secs(10),
        }
    }
}

/// 降级管理器
pub struct DegradationManager {
    /// 当前健康级别
    current_health: AtomicU8,
    /// 功能注册表
    features: RwLock<HashMap<String, Feature>>,
    /// 降级策略
    policy: DegradationPolicy,
    /// 健康指标
    metrics: Arc<dyn HealthMetrics>,
    /// 状态变更通知
    state_changes: broadcast::Sender<(String, FeatureState)>,
    /// 上次状态变更时间
    last_change: RwLock<std::time::Instant>,
}

impl DegradationManager {
    pub fn new(policy: DegradationPolicy, metrics: Arc<dyn HealthMetrics>) -> Self {
        let (tx, _) = broadcast::channel(100);

        Self {
            current_health: AtomicU8::new(HealthLevel::Healthy as u8),
            features: RwLock::new(HashMap::new()),
            policy,
            metrics,
            state_changes: tx,
            last_change: RwLock::new(std::time::Instant::now()),
        }
    }

    /// 注册功能
    pub async fn register_feature(&self, feature: Feature) {
        let mut features = self.features.write().await;
        features.insert(feature.id.clone(), feature);
    }

    /// 检查功能是否可用
    pub async fn check_feature(&self, feature_id: &str) -> Option<FeatureState> {
        let features = self.features.read().await;
        features.get(feature_id).map(|f| f.current_state)
    }

    /// 执行功能（自动处理降级）
    pub async fn execute<F, Fut, T>(
        &self,
        feature_id: &str,
        operation: F,
    ) -> Result<T, DegradationError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        match self.check_feature(feature_id).await {
            Some(FeatureState::Full) => Ok(operation().await),
            Some(FeatureState::Partial { capacity_percent }) => {
                // 应用容量限制
                if self.should_throttle(capacity_percent) {
                    Err(DegradationError::Throttled)
                } else {
                    Ok(operation().await)
                }
            }
            Some(FeatureState::ReadOnly) => {
                Err(DegradationError::ReadOnly)
            }
            Some(FeatureState::Disabled) => {
                Err(DegradationError::FeatureDisabled)
            }
            None => Err(DegradationError::FeatureNotFound),
        }
    }

    /// 简单令牌桶限速
    fn should_throttle(&self, capacity_percent: u8) -> bool {
        use rand::Rng;
        let threshold = (capacity_percent as f64 / 100.0 * u8::MAX as f64) as u8;
        rand::thread_rng().gen::<u8>() > threshold
    }

    /// 更新健康状态
    pub async fn update_health(&self) -> HealthLevel {
        let health_score = self.metrics.calculate_health_score().await;

        // 确定新的健康级别
        let new_health = self.determine_health_level(health_score);
        let current = self.get_current_health();

        if new_health != current {
            let last_change = *self.last_change.read().await;
            let elapsed = std::time::Instant::now().duration_since(last_change);

            // 检查防抖延迟
            let required_delay = if new_health > current {
                // 降级需要更短的延迟
                self.policy.degradation_delay
            } else {
                // 恢复需要更长的延迟
                self.policy.recovery_delay
            };

            if elapsed >= required_delay {
                tracing::info!(
                    "Health level changing from {:?} to {:?} (score: {})",
                    current, new_health, health_score
                );

                self.apply_degradation(new_health).await;
                self.current_health.store(new_health as u8, Ordering::Relaxed);
                *self.last_change.write().await = std::time::Instant::now();
            }
        }

        new_health
    }

    fn determine_health_level(&self, score: f64) -> HealthLevel {
        if score >= self.policy.health_thresholds[&HealthLevel::Healthy] {
            HealthLevel::Healthy
        } else if score >= self.policy.health_thresholds[&HealthLevel::MildDegraded] {
            HealthLevel::MildDegraded
        } else if score >= self.policy.health_thresholds[&HealthLevel::ModerateDegraded] {
            HealthLevel::ModerateDegraded
        } else if score >= self.policy.health_thresholds[&HealthLevel::SevereDegraded] {
            HealthLevel::SevereDegraded
        } else {
            HealthLevel::Emergency
        }
    }

    fn get_current_health(&self) -> HealthLevel {
        match self.current_health.load(Ordering::Relaxed) {
            0 => HealthLevel::Healthy,
            1 => HealthLevel::MildDegraded,
            2 => HealthLevel::ModerateDegraded,
            3 => HealthLevel::SevereDegraded,
            _ => HealthLevel::Emergency,
        }
    }

    /// 应用降级策略
    async fn apply_degradation(&self, health: HealthLevel) {
        let mut features = self.features.write().await;

        for (id, feature) in features.iter_mut() {
            if let Some(class_policy) = self.policy.feature_policies.get(&feature.class) {
                if let Some(new_state) = class_policy.get(&health) {
                    if feature.current_state != *new_state {
                        tracing::info!(
                            "Feature {} state changing from {:?} to {:?}",
                            id, feature.current_state, new_state
                        );

                        feature.current_state = *new_state;
                        let _ = self.state_changes.send((id.clone(), *new_state));
                    }
                }
            }
        }
    }

    /// 订阅状态变更
    pub fn subscribe(&self) -> broadcast::Receiver<(String, FeatureState)> {
        self.state_changes.subscribe()
    }
}

/// 健康指标 trait
#[async_trait]
pub trait HealthMetrics: Send + Sync {
    async fn calculate_health_score(&self) -> f64;
}

/// 降级错误类型
#[derive(Debug, thiserror::Error)]
pub enum DegradationError {
    #[error("Feature is disabled")]
    FeatureDisabled,
    #[error("Feature is in read-only mode")]
    ReadOnly,
    #[error("Request throttled due to degradation")]
    Throttled,
    #[error("Feature not found")]
    FeatureNotFound,
}
```

### 4.2 回退机制实现

```rust
/// 回退策略 trait
#[async_trait]
pub trait FallbackStrategy<T, E>: Send + Sync {
    async fn fallback(&self, original_error: &E) -> Result<T, E>;
}

/// 缓存回退
pub struct CacheFallback<T: Clone + Send + Sync> {
    cache: Arc<dyn Cache<T>>,
    max_staleness: std::time::Duration,
}

#[async_trait]
impl<T: Clone + Send + Sync + 'static, E: Send + Sync> FallbackStrategy<T, E> for CacheFallback<T> {
    async fn fallback(&self, _original_error: &E) -> Result<T, E> {
        self.cache.get_stale(self.max_staleness).await
            .ok_or_else(|| unreachable!()) // 转换错误类型需要额外处理
    }
}

/// 默认值回退
pub struct DefaultFallback<T: Clone + Send + Sync> {
    default_value: T,
}

#[async_trait]
impl<T: Clone + Send + Sync + 'static, E: Send + Sync> FallbackStrategy<T, E> for DefaultFallback<T> {
    async fn fallback(&self, _original_error: &E) -> Result<T, E> {
        Ok(self.default_value.clone())
    }
}

/// 简化的服务回退
pub struct SimplifiedServiceFallback<T> {
    simplified_endpoint: String,
    client: reqwest::Client,
    _phantom: std::marker::PhantomData<T>,
}

/// 链式回退
pub struct ChainedFallback<T, E> {
    strategies: Vec<Box<dyn FallbackStrategy<T, E>>>,
}

impl<T, E> ChainedFallback<T, E> {
    pub fn new(strategies: Vec<Box<dyn FallbackStrategy<T, E>>>) -> Self {
        Self { strategies }
    }

    pub async fn execute(&self, error: &E) -> Result<T, E> {
        for strategy in &self.strategies {
            match strategy.fallback(error).await {
                Ok(value) => return Ok(value),
                Err(_) => continue,
            }
        }
        Err(error.clone()) // 所有回退都失败
    }
}

/// 带降级和回退的执行器
pub struct ResilientExecutor<T, E> {
    degradation_manager: Arc<DegradationManager>,
    fallback: Option<Box<dyn FallbackStrategy<T, E>>>,
}

impl<T, E> ResilientExecutor<T, E> {
    pub async fn execute<F, Fut>(
        &self,
        feature_id: &str,
        operation: F,
    ) -> Result<T, DegradationError>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
    {
        // 首先检查降级状态
        match self.degradation_manager.check_feature(feature_id).await {
            Some(FeatureState::Disabled) => {
                // 尝试回退
                if let Some(fallback) = &self.fallback {
                    // 构造一个虚拟错误进行回退
                    return fallback.fallback(&unimplemented!())
                        .map_err(|_| DegradationError::FeatureDisabled);
                }
                return Err(DegradationError::FeatureDisabled);
            }
            Some(FeatureState::Partial { capacity_percent }) => {
                // 应用部分容量限制
                if self.should_use_fallback(capacity_percent) {
                    if let Some(fallback) = &self.fallback {
                        return fallback.fallback(&unimplemented!())
                            .map_err(|_| DegradationError::Throttled);
                    }
                }
            }
            _ => {}
        }

        // 执行主操作
        match operation().await {
            Ok(result) => Ok(result),
            Err(error) => {
                // 主操作失败，尝试回退
                if let Some(fallback) = &self.fallback {
                    fallback.fallback(&error)
                        .map_err(|_| DegradationError::FeatureDisabled)
                } else {
                    Err(DegradationError::FeatureDisabled)
                }
            }
        }
    }

    fn should_use_fallback(&self, capacity_percent: u8) -> bool {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        rng.gen::<f64>() > (capacity_percent as f64 / 100.0)
    }
}
```

### 4.3 特性开关集成

```rust
use std::collections::HashSet;

/// 特性开关管理器
pub struct FeatureFlagManager {
    /// 启用的特性集合
    enabled_features: RwLock<HashSet<String>>
}

impl FeatureFlagManager {
    pub async fn is_enabled(&self, feature: &str) -> bool {
        self.enabled_features.read().await.contains(feature)
    }

    pub async fn enable(&self, feature: &str) {
        self.enabled_features.write().await.insert(feature.to_string());
    }

    pub async fn disable(&self, feature: &str) {
        self.enabled_features.write().await.remove(feature);
    }
}

/// 集成降级和特性开关
pub struct FeatureController {
    degradation: Arc<DegradationManager>,
    flags: Arc<FeatureFlagManager>,
}

impl FeatureController {
    /// 综合检查特性是否可用
    pub async fn is_available(&self, feature_id: &str) -> bool {
        // 特性开关检查
        if !self.flags.is_enabled(feature_id).await {
            return false;
        }

        // 降级状态检查
        match self.degradation.check_feature(feature_id).await {
            Some(FeatureState::Full) | Some(FeatureState::Partial { .. }) => true,
            _ => false,
        }
    }
}
```

### 4.4 负载削减实现

```rust
use tokio::sync::Semaphore;

/// 负载削减器
pub struct LoadShedder {
    /// 当前负载指标
    current_load: AtomicU8,
    /// 负载阈值
    threshold: f64,
    /// 拒绝概率
    reject_probability: AtomicU8, // 0-100
    /// 信号量限制并发
    concurrency_limit: Arc<Semaphore>,
}

impl LoadShedder {
    pub fn new(threshold: f64, max_concurrent: usize) -> Self {
        Self {
            current_load: AtomicU8::new(0),
            threshold,
            reject_probability: AtomicU8::new(0),
            concurrency_limit: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    /// 尝试获取执行许可
    pub async fn try_acquire(&self) -> Result<tokio::sync::SemaphorePermit, LoadShedError> {
        // 概率拒绝
        let reject_prob = self.reject_probability.load(Ordering::Relaxed);
        if reject_prob > 0 {
            use rand::Rng;
            if rand::thread_rng().gen::<u8>() < reject_prob {
                return Err(LoadShedError::ProbabilisticRejection);
            }
        }

        // 并发限制
        match self.concurrency_limit.try_acquire() {
            Ok(permit) => Ok(permit),
            Err(_) => Err(LoadShedError::ConcurrencyLimit),
        }
    }

    /// 更新负载状态
    pub fn update_load(&self, load: f64) {
        self.current_load.store((load * 100.0) as u8, Ordering::Relaxed);

        // 计算拒绝概率
        let reject_prob = if load > self.threshold {
            let excess = load - self.threshold;
            let range = 1.0 - self.threshold;
            ((excess / range) * 100.0).min(100.0) as u8
        } else {
            0
        };

        self.reject_probability.store(reject_prob, Ordering::Relaxed);
    }
}

#[derive(Debug)]
pub enum LoadShedError {
    ProbabilisticRejection,
    ConcurrencyLimit,
}
```

---

## 5. 形式化验证

### 5.1 降级安全性

```
降级安全性保证:

1. 核心功能可用性:
   □ (HealthLevel = s → Availability(Critical, s) ≥ Partial)

2. 单调降级:
   □ (s₁ < s₂ → Availability(f, s₁) ≥ Availability(f, s₂))

3. 无振荡:
   □ (Change(s₁→s₂) → ◇□ s = s₂ until HealthScore stable)

4. 资源守恒:
   Σ Resource(fᵢ) ≤ Resource_total
```

### 5.2 回退正确性

```
回退性质:

1. 完备性:
   □ (PrimaryFails ∧ FallbackAvailable → ◇ Success)

2. 一致性:
   □ (FallbackUsed → Result ≈ PrimaryResult)

3. 有界延迟:
   □ (FallbackTime ≤ PrimaryTime + Δ)
```

---

## 6. 总结

| 降级级别 | 触发条件 | 功能影响 |
|----------|----------|----------|
| Healthy | 负载 < 10% | 全部功能 |
| Mild | 负载 10-30% | 可选功能限速 50% |
| Moderate | 负载 30-50% | 可选功能关闭，重要功能限速 |
| Severe | 负载 50-70% | 仅核心功能，限速运行 |
| Emergency | 负载 > 70% | 最简核心功能 |

核心公式:

$$
\text{HealthScore} = w_1 \cdot \text{CPU} + w_2 \cdot \text{Memory} + w_3 \cdot \frac{\text{Rate}}{\text{Capacity}} + w_4 \cdot \frac{\text{Latency}}{\text{Threshold}}
$$

$$
\text{Availability}(f, s) = \text{Policy}(\text{Class}(f), s)
$$

$$
\text{RejectProb} = \max(0, \frac{L - L_{threshold}}{1 - L_{threshold}} \times 100\%)
$$
