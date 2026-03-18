# 限流语义 (Rate Limiting Semantics)

## 目录

- [限流语义 (Rate Limiting Semantics)](#限流语义-rate-limiting-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 限流算法分类](#2-限流算法分类)
    - [2.1 算法类型谱系](#21-算法类型谱系)
    - [2.2 形式化定义](#22-形式化定义)
  - [3. 算法数学模型](#3-算法数学模型)
    - [3.1 令牌桶算法](#31-令牌桶算法)
    - [3.2 漏桶算法](#32-漏桶算法)
    - [3.3 滑动窗口计数器](#33-滑动窗口计数器)
    - [3.4 分布式限流](#34-分布式限流)
  - [4. Rust 实现](#4-rust-实现)
    - [4.1 核心限流框架](#41-核心限流框架)
    - [4.2 分布式限流实现](#42-分布式限流实现)
    - [4.3 自适应限流](#43-自适应限流)
    - [4.4 多级限流](#44-多级限流)
  - [5. 形式化验证](#5-形式化验证)
    - [5.1 限流正确性](#51-限流正确性)
    - [5.2 令牌桶分析](#52-令牌桶分析)
  - [6. 性能分析](#6-性能分析)
  - [7. 总结](#7-总结)

## 1. 引言

限流是保护系统免受过载、确保公平资源分配的关键机制。
本文档深入分析各种限流算法的数学模型、语义保证及其在 Rust 中的实现。

---

## 2. 限流算法分类

### 2.1 算法类型谱系

```
限流算法分类:

┌──────────────────────────────────────────────────────────────────┐
│                      限流算法                                     │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌───────────────────┐  ┌───────────────────┐                   │
│  │   计数器算法      │  │   桶算法          │                   │
│  ├───────────────────┤  ├───────────────────┤                   │
│  │ • 固定窗口        │  │ • 令牌桶          │                   │
│  │ • 滑动窗口        │  │ • 漏桶            │                   │
│  │ • 滑动日志        │  │ • 弹性令牌桶      │                   │
│  └───────────────────┘  └───────────────────┘                   │
│                                                                  │
│  ┌───────────────────┐  ┌───────────────────┐                   │
│  │   分布式限流      │  │   自适应限流      │                   │
│  ├───────────────────┤  ├───────────────────┤                   │
│  │ • 集中式存储      │  │ • 基于延迟反馈    │                   │
│  │ • Gossip 协议     │  │ • 基于错误率      │                   │
│  │ • 分区协调        │  │ • 基于负载        │                   │
│  └───────────────────┘  └───────────────────┘                   │
│                                                                  │
└──────────────────────────────────────────────────────────────────┘
```

### 2.2 形式化定义

```
限流形式化语义:

限流器状态:
  Limiter = (capacity, current, last_update, rate)

准入决策:
  Admit: Limiter × Request × Time → {Allow, Deny} × Limiter'

限流目标:
  □ (Requests(t, t+Δt) ≤ rate × Δt + burst)

  在任意时间窗口内，请求数不超过允许的最大值

公平性:
  ∀clientᵢ, clientⱼ.
    |allowed(clientᵢ) - allowed(clientⱼ)| ≤ ε

性能目标:
  Minimize: FalsePositive + FalseNegative
  Subject to: Latency(decision) < threshold
```

---

## 3. 算法数学模型

### 3.1 令牌桶算法

```
令牌桶模型:

状态变量:
  tokens: 当前令牌数量
  capacity: 桶容量（最大突发量）
  rate: 令牌生成速率（令牌/秒）
  last_update: 上次更新时间

令牌补充:
  tokens' = min(capacity, tokens + rate × Δt)

请求准入:
  Admit(request, cost) =
    if tokens ≥ cost then
      tokens ← tokens - cost
      Allow
    else
      Deny

关键性质:
  1. 平均速率 ≤ rate
  2. 突发量 ≤ capacity
  3. 长期吞吐量 = min(arrival_rate, rate)

延迟计算:
  WaitTime(cost) = max(0, (cost - tokens) / rate)
```

### 3.2 漏桶算法

```
漏桶模型:

状态变量:
  water: 当前水量
  capacity: 桶容量
  leak_rate: 漏水速率

漏水过程:
  water' = max(0, water - leak_rate × Δt)

请求准入:
  Admit(request, cost) =
    if water + cost ≤ capacity then
      water ← water + cost
      Allow
    else
      Deny

与令牌桶的区别:
  令牌桶: 允许突发，然后限流
  漏桶: 平滑输出，强制限流
```

### 3.3 滑动窗口计数器

```
滑动窗口:

固定窗口问题:
  窗口边界处的突发: 2 × rate 在边界附近

滑动窗口公式:
  current_window = floor(now / window_size)
  previous_count = count[current_window - 1]
  current_count = count[current_window]

  插值:
  elapsed = now % window_size
  weight = elapsed / window_size

  estimated_count = previous_count × (1 - weight) + current_count

  Admit if estimated_count < limit

精确滑动窗口:
  存储每个请求的时间戳
  清理过期时间戳 (> window_size)
  count = |timestamps|

  Admit if count < limit
```

### 3.4 分布式限流

```
分布式限流模型:

集中式:
  每个请求 → 中心存储（Redis/Memcached）
  原子操作: INCR + EXPIRE

  延迟: 2 × RTT (round-trip time)

  一致性: 强一致性

令牌桶分片:
  每个节点持有本地令牌桶
  定期与中心同步或 gossip

  误差边界:
    |actual_rate - target_rate| ≤ n × rate_sync_interval

模糊计数器:
  使用概率数据结构（如 Redis HyperLogLog）
  牺牲精度换取性能

  误差: ± 0.81% / √m  (m 为内存槽位数)
```

---

## 4. Rust 实现

### 4.1 核心限流框架

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;
use async_trait::async_trait;

/// 限流决策
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RateLimitDecision {
    Allow { remaining: u64, reset_after: Duration },
    Deny { retry_after: Duration },
}

/// 限流器 trait
#[async_trait]
pub trait RateLimiter: Send + Sync {
    /// 检查是否允许请求
    async fn check(&self, key: &str, cost: u64) -> RateLimitDecision;

    /// 获取当前状态
    async fn status(&self, key: &str) -> (u64, u64, Duration);
}

/// 令牌桶限流器
pub struct TokenBucket {
    capacity: u64,
    rate: f64, // tokens per second
    buckets: Arc<dashmap::DashMap<String, TokenBucketState>>,
}

#[derive(Debug, Clone)]
struct TokenBucketState {
    tokens: f64,
    last_update: Instant,
}

impl TokenBucket {
    pub fn new(capacity: u64, rate: f64) -> Self {
        Self {
            capacity,
            rate,
            buckets: Arc::new(dashmap::DashMap::new()),
        }
    }

    /// 补充令牌
    fn replenish(&self, state: &mut TokenBucketState) {
        let now = Instant::now();
        let elapsed = now.duration_since(state.last_update).as_secs_f64();
        let tokens_to_add = elapsed * self.rate;

        state.tokens = (state.tokens + tokens_to_add).min(self.capacity as f64);
        state.last_update = now;
    }
}

#[async_trait]
impl RateLimiter for TokenBucket {
    async fn check(&self, key: &str, cost: u64) -> RateLimitDecision {
        let mut entry = self.buckets.entry(key.to_string()).or_insert(TokenBucketState {
            tokens: self.capacity as f64,
            last_update: Instant::now(),
        });

        let state = entry.value_mut();
        self.replenish(state);

        if state.tokens >= cost as f64 {
            state.tokens -= cost as f64;
            let remaining = state.tokens as u64;
            let reset_after = if self.rate > 0.0 {
                Duration::from_secs_f64((self.capacity as f64 - state.tokens) / self.rate)
            } else {
                Duration::MAX
            };

            RateLimitDecision::Allow { remaining, reset_after }
        } else {
            let deficit = cost as f64 - state.tokens;
            let retry_after = Duration::from_secs_f64(deficit / self.rate);

            RateLimitDecision::Deny { retry_after }
        }
    }

    async fn status(&self, key: &str) -> (u64, u64, Duration) {
        if let mut entry = self.buckets.get_mut(key) {
            let state = entry.value_mut();
            self.replenish(state);

            let remaining = state.tokens as u64;
            let reset_after = Duration::from_secs_f64(
                (self.capacity as f64 - state.tokens) / self.rate
            );

            (remaining, self.capacity, reset_after)
        } else {
            (self.capacity, self.capacity, Duration::ZERO)
        }
    }
}

/// 漏桶限流器
pub struct LeakyBucket {
    capacity: u64,
    leak_rate: f64, // units per second
    buckets: Arc<dashmap::DashMap<String, LeakyBucketState>>,
}

#[derive(Debug, Clone)]
struct LeakyBucketState {
    water: f64,
    last_update: Instant,
}

impl LeakyBucket {
    pub fn new(capacity: u64, leak_rate: f64) -> Self {
        Self {
            capacity,
            leak_rate,
            buckets: Arc::new(dashmap::DashMap::new()),
        }
    }

    fn leak(&self, state: &mut LeakyBucketState) {
        let now = Instant::now();
        let elapsed = now.duration_since(state.last_update).as_secs_f64();
        let leaked = elapsed * self.leak_rate;

        state.water = (state.water - leaked).max(0.0);
        state.last_update = now;
    }
}

#[async_trait]
impl RateLimiter for LeakyBucket {
    async fn check(&self, key: &str, cost: u64) -> RateLimitDecision {
        let mut entry = self.buckets.entry(key.to_string()).or_insert(LeakyBucketState {
            water: 0.0,
            last_update: Instant::now(),
        });

        let state = entry.value_mut();
        self.leak(state);

        if state.water + cost as f64 <= self.capacity as f64 {
            state.water += cost as f64;
            let remaining = (self.capacity as f64 - state.water) as u64;
            let reset_after = Duration::from_secs_f64(state.water / self.leak_rate);

            RateLimitDecision::Allow { remaining, reset_after }
        } else {
            let wait_time = (state.water + cost as f64 - self.capacity as f64) / self.leak_rate;
            RateLimitDecision::Deny {
                retry_after: Duration::from_secs_f64(wait_time)
            }
        }
    }

    async fn status(&self, key: &str) -> (u64, u64, Duration) {
        if let mut entry = self.buckets.get_mut(key) {
            let state = entry.value_mut();
            self.leak(state);

            let remaining = (self.capacity as f64 - state.water) as u64;
            let reset_after = Duration::from_secs_f64(state.water / self.leak_rate);

            (remaining, self.capacity, reset_after)
        } else {
            (self.capacity, self.capacity, Duration::ZERO)
        }
    }
}

/// 滑动窗口限流器
pub struct SlidingWindow {
    window_size: Duration,
    limit: u64,
    /// 存储 (时间戳, 计数) 对
    windows: Arc<Mutex<HashMap<String, VecDeque<(Instant, u64)>>>>,
}

impl SlidingWindow {
    pub fn new(window_size: Duration, limit: u64) -> Self {
        Self {
            window_size,
            limit,
            windows: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn cleanup_expired(&self, timestamps: &mut VecDeque<(Instant, u64)>) -> u64 {
        let cutoff = Instant::now() - self.window_size;
        let mut total = 0u64;

        // 移除过期条目并计算总数
        timestamps.retain(|(ts, count)| {
            if *ts > cutoff {
                total += count;
                true
            } else {
                false
            }
        });

        total
    }
}

#[async_trait]
impl RateLimiter for SlidingWindow {
    async fn check(&self, key: &str, cost: u64) -> RateLimitDecision {
        let mut windows = self.windows.lock().await;
        let timestamps = windows.entry(key.to_string()).or_default();

        let current_count = self.cleanup_expired(timestamps).await;

        if current_count + cost <= self.limit {
            timestamps.push_back((Instant::now(), cost));
            let remaining = self.limit - current_count - cost;
            RateLimitDecision::Allow {
                remaining,
                reset_after: self.window_size
            }
        } else {
            // 计算最早可重试时间
            let retry_after = if let Some((earliest, _)) = timestamps.front() {
                self.window_size.saturating_sub(Instant::now().duration_since(*earliest))
            } else {
                self.window_size
            };

            RateLimitDecision::Deny { retry_after }
        }
    }

    async fn status(&self, key: &str) -> (u64, u64, Duration) {
        let mut windows = self.windows.lock().await;
        if let Some(timestamps) = windows.get_mut(key) {
            let count = self.cleanup_expired(timestamps).await;
            let remaining = self.limit.saturating_sub(count);
            (remaining, self.limit, self.window_size)
        } else {
            (self.limit, self.limit, self.window_size)
        }
    }
}

/// 固定窗口限流器（更高效的近似实现）
pub struct FixedWindow {
    window_size: Duration,
    limit: u64,
    counters: Arc<dashmap::DashMap<String, FixedWindowState>>,
}

#[derive(Debug, Clone, Copy)]
struct FixedWindowState {
    count: AtomicU64,
    window_start: Instant,
}

impl FixedWindow {
    pub fn new(window_size: Duration, limit: u64) -> Self {
        Self {
            window_size,
            limit,
            counters: Arc::new(dashmap::DashMap::new()),
        }
    }

    fn current_window_start(&self) -> Instant {
        let now = Instant::now();
        let elapsed = now.elapsed();
        let window_ms = self.window_size.as_millis() as u64;
        let window_idx = elapsed.as_millis() as u64 / window_ms;
        Instant::now() - Duration::from_millis(elapsed.as_millis() as u64 % window_ms)
    }
}

#[async_trait]
impl RateLimiter for FixedWindow {
    async fn check(&self, key: &str, cost: u64) -> RateLimitDecision {
        let current_window = self.current_window_start();

        let mut entry = self.counters.entry(key.to_string()).or_insert(FixedWindowState {
            count: AtomicU64::new(0),
            window_start: current_window,
        });

        let state = entry.value_mut();

        // 检查是否需要重置窗口
        if current_window > state.window_start {
            state.count.store(0, Ordering::Relaxed);
            state.window_start = current_window;
        }

        let current = state.count.load(Ordering::Relaxed);

        if current + cost <= self.limit {
            let new_count = state.count.fetch_add(cost, Ordering::Relaxed) + cost;
            let remaining = self.limit - new_count;
            let reset_after = self.window_size - Instant::now().duration_since(current_window);

            RateLimitDecision::Allow { remaining, reset_after }
        } else {
            let reset_after = self.window_size - Instant::now().duration_since(current_window);
            RateLimitDecision::Deny { retry_after: reset_after }
        }
    }

    async fn status(&self, key: &str) -> (u64, u64, Duration) {
        if let Some(entry) = self.counters.get(key) {
            let state = entry.value();
            let current = state.count.load(Ordering::Relaxed);
            let remaining = self.limit - current;
            let reset_after = self.window_size - Instant::now().duration_since(state.window_start);
            (remaining, self.limit, reset_after)
        } else {
            (self.limit, self.limit, self.window_size)
        }
    }
}
```

### 4.2 分布式限流实现

```rust
use redis::AsyncCommands;

/// Redis 分布式限流器
pub struct RedisRateLimiter {
    client: redis::aio::MultiplexedConnection,
    script: redis::Script,
    window_size: Duration,
    limit: u64,
}

impl RedisRateLimiter {
    pub async fn new(redis_url: &str, window_size: Duration, limit: u64) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        let conn = client.get_multiplexed_async_connection().await?;

        // Lua 脚本实现原子化的滑动窗口限流
        let script = redis::Script::new(r#"
            local key = KEYS[1]
            local window = tonumber(ARGV[1])
            local limit = tonumber(ARGV[2])
            local cost = tonumber(ARGV[3])
            local now = tonumber(ARGV[4])

            -- 清理过期条目
            redis.call('ZREMRANGEBYSCORE', key, 0, now - window)

            -- 获取当前计数
            local current = redis.call('ZCARD', key)

            if current + cost <= limit then
                -- 添加新条目
                for i = 1, cost do
                    redis.call('ZADD', key, now + i/1000, now + i)
                end
                -- 设置过期时间
                redis.call('EXPIRE', key, window / 1000 + 1)

                return {1, limit - current - cost}
            else
                -- 获取最早过期时间
                local oldest = redis.call('ZRANGE', key, 0, 0, 'WITHSCORES')
                local retry_after = 0
                if #oldest > 0 then
                    retry_after = oldest[2] - (now - window)
                end
                return {0, retry_after}
            end
        "#);

        Ok(Self {
            client: conn,
            script,
            window_size,
            limit,
        })
    }

    pub async fn check(&mut self, key: &str, cost: u64) -> RateLimitDecision {
        let now = chrono::Utc::now().timestamp_millis() as u64;
        let window_ms = self.window_size.as_millis() as u64;

        let result: (i64, i64) = self.script
            .key(key)
            .arg(window_ms)
            .arg(self.limit)
            .arg(cost)
            .arg(now)
            .invoke_async(&mut self.client)
            .await
            .unwrap_or((0, 0));

        if result.0 == 1 {
            RateLimitDecision::Allow {
                remaining: result.1 as u64,
                reset_after: self.window_size,
            }
        } else {
            RateLimitDecision::Deny {
                retry_after: Duration::from_millis(result.1.max(0) as u64),
            }
        }
    }
}

/// 令牌桶分布式限流
pub struct DistributedTokenBucket {
    redis: redis::aio::MultiplexedConnection,
    capacity: u64,
    rate: f64,
}

impl DistributedTokenBucket {
    pub async fn new(redis_url: &str, capacity: u64, rate: f64) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        let conn = client.get_multiplexed_async_connection().await?;

        Ok(Self {
            redis: conn,
            capacity,
            rate,
        })
    }

    pub async fn check(&mut self, key: &str, cost: u64) -> RateLimitDecision {
        // 使用 Redis Cell 模块或自定义 Lua 脚本
        let lua_script = r#"
            local key = KEYS[1]
            local capacity = tonumber(ARGV[1])
            local rate = tonumber(ARGV[2])
            local cost = tonumber(ARGV[3])
            local now = redis.call('TIME')
            local now_ms = now[1] * 1000 + now[2] / 1000

            local state = redis.call('HMGET', key, 'tokens', 'last_update')
            local tokens = tonumber(state[1]) or capacity
            local last_update = tonumber(state[2]) or now_ms

            -- 补充令牌
            local elapsed = (now_ms - last_update) / 1000
            tokens = math.min(capacity, tokens + rate * elapsed)

            if tokens >= cost then
                tokens = tokens - cost
                redis.call('HMSET', key, 'tokens', tokens, 'last_update', now_ms)
                redis.call('PEXPIRE', key, 60000)
                return {1, math.floor(tokens)}
            else
                local deficit = cost - tokens
                local retry_after = deficit / rate
                redis.call('HMSET', key, 'tokens', tokens, 'last_update', now_ms)
                redis.call('PEXPIRE', key, 60000)
                return {0, math.ceil(retry_after)}
            end
        "#;

        let result: (i64, i64) = redis::Script::new(lua_script)
            .key(key)
            .arg(self.capacity)
            .arg(self.rate)
            .arg(cost)
            .invoke_async(&mut self.redis)
            .await
            .unwrap_or((0, 0));

        if result.0 == 1 {
            RateLimitDecision::Allow {
                remaining: result.1 as u64,
                reset_after: Duration::from_secs_f64(
                    (self.capacity as f64 - result.1 as f64) / self.rate
                ),
            }
        } else {
            RateLimitDecision::Deny {
                retry_after: Duration::from_secs(result.1.max(0) as u64),
            }
        }
    }
}
```

### 4.3 自适应限流

```rust
/// 自适应限流器（基于延迟反馈）
pub struct AdaptiveRateLimiter {
    /// 基础限流器
    inner: Arc<dyn RateLimiter>,
    /// 延迟阈值
    latency_threshold: Duration,
    /// 错误率阈值
    error_threshold: f64,
    /// 当前限制
    current_limit: AtomicU64,
    /// 最小/最大限制
    min_limit: u64,
    max_limit: u64,
    /// 延迟历史
    latency_history: Arc<RwLock<VecDeque<Duration>>>,
}

impl AdaptiveRateLimiter {
    pub fn new(
        inner: Arc<dyn RateLimiter>,
        latency_threshold: Duration,
        error_threshold: f64,
        min_limit: u64,
        max_limit: u64,
    ) -> Self {
        Self {
            inner,
            latency_threshold,
            error_threshold,
            current_limit: AtomicU64::new(max_limit),
            min_limit,
            max_limit,
            latency_history: Arc::new(RwLock::new(VecDeque::with_capacity(100))),
        }
    }

    /// 记录请求结果
    pub async fn record_result(&self, latency: Duration, success: bool) {
        // 记录延迟
        {
            let mut history = self.latency_history.write().await;
            history.push_back(latency);
            if history.len() > 100 {
                history.pop_front();
            }
        }

        // 计算平均延迟
        let avg_latency = self.average_latency().await;
        let current = self.current_limit.load(Ordering::Relaxed);

        // 自适应调整
        let new_limit = if !success {
            // 错误增加，降低限制
            (current as f64 * 0.9) as u64
        } else if avg_latency > self.latency_threshold {
            // 延迟过高，降低限制
            (current as f64 * 0.95) as u64
        } else if avg_latency < self.latency_threshold / 2 {
            // 延迟较低，可以增加限制
            (current as f64 * 1.05) as u64
        } else {
            current
        };

        let clamped = new_limit.clamp(self.min_limit, self.max_limit);
        self.current_limit.store(clamped, Ordering::Relaxed);

        tracing::debug!(
            "Adaptive rate limit adjusted: {} -> {}, avg_latency: {:?}",
            current, clamped, avg_latency
        );
    }

    async fn average_latency(&self) -> Duration {
        let history = self.latency_history.read().await;
        if history.is_empty() {
            return Duration::ZERO;
        }

        let sum: Duration = history.iter().sum();
        sum / history.len() as u32
    }

    pub fn current_limit(&self) -> u64 {
        self.current_limit.load(Ordering::Relaxed)
    }
}
```

### 4.4 多级限流

```rust
/// 多级限流器
pub struct TieredRateLimiter {
    /// 全局限流器（所有请求）
    global: Arc<dyn RateLimiter>,
    /// 每用户限流器
    per_user: Arc<dyn RateLimiter>,
    /// 每 IP 限流器
    per_ip: Arc<dyn RateLimiter>,
    /// 每 API 限流器
    per_api: Arc<dyn RateLimiter>,
}

impl TieredRateLimiter {
    pub async fn check_all(
        &self,
        user_id: &str,
        ip: &str,
        api: &str,
        cost: u64,
    ) -> TieredRateLimitResult {
        let global_result = self.global.check("global", cost).await;
        let user_result = self.per_user.check(user_id, cost).await;
        let ip_result = self.per_ip.check(ip, cost).await;
        let api_result = self.per_api.check(api, cost).await;

        let all_allowed = matches!(global_result, RateLimitDecision::Allow { .. })
            && matches!(user_result, RateLimitDecision::Allow { .. })
            && matches!(ip_result, RateLimitDecision::Allow { .. })
            && matches!(api_result, RateLimitDecision::Allow { .. });

        TieredRateLimitResult {
            allowed: all_allowed,
            global: global_result,
            user: user_result,
            ip: ip_result,
            api: api_result,
        }
    }
}

#[derive(Debug)]
pub struct TieredRateLimitResult {
    pub allowed: bool,
    pub global: RateLimitDecision,
    pub user: RateLimitDecision,
    pub ip: RateLimitDecision,
    pub api: RateLimitDecision,
}
```

---

## 5. 形式化验证

### 5.1 限流正确性

```
限流性质:

1. 速率保证:
   □ (Requests(t, t+window) ≤ limit + burst)

2. 公平性:
   ∀k₁, k₂. |Allow(key₁) - Allow(key₂)| ≤ ε

3. 无饥饿:
   ◇ (Allow(key) = true) 对于所有遵守速率限制的 key

4. 单调性:
   limit₁ < limit₂ → AllowedSet(limit₁) ⊆ AllowedSet(limit₂)
```

### 5.2 令牌桶分析

```
令牌桶定理:

平均速率:
  lim_{T→∞} AllowedRequests(T) / T = min(arrival_rate, rate)

突发容量:
  max_burst = capacity

瞬时速率:
  在任意时间点，瞬时通过速率 ≤ capacity / Δt_min

时间复杂度:
  更新: O(1)
  查询: O(1)
  空间: O(keys)
```

---

## 6. 性能分析

```
限流算法性能:

| 算法           | 更新复杂度 | 空间复杂度 | 精度   | 分布式支持 |
|----------------|------------|------------|--------|------------|
| 固定窗口       | O(1)       | O(keys)    | 低     | 容易       |
| 滑动窗口(近似) | O(1)       | O(keys)    | 中     | 容易       |
| 滑动窗口(精确) | O(log n)   | O(keys×n)  | 高     | 困难       |
| 令牌桶         | O(1)       | O(keys)    | 高     | 中等       |
| 漏桶           | O(1)       | O(keys)    | 高     | 中等       |
| 分布式(Redis)  | O(1) RTT   | O(keys)    | 高     | 原生       |

分布式限流优化:

1. 本地缓存:
   - 批量预取令牌
   - 减少 Redis 调用次数

2. 一致性哈希分区:
   - 不同 key 路由到不同 Redis 节点
   - 水平扩展

3. 最终一致性:
   - 允许短暂的超限
   - 换取更高性能
```

---

## 7. 总结

| 算法 | 突发处理 | 平滑性 | 实现复杂度 | 推荐场景 |
|------|----------|--------|------------|----------|
| 固定窗口 | 边界突发 | 差 | 低 | 简单场景 |
| 滑动窗口 | 精确控制 | 好 | 中 | 高精度要求 |
| 令牌桶 | 允许突发 | 好 | 低 | 通用场景 |
| 漏桶 | 强制平滑 | 最好 | 低 | 严格限流 |

核心公式:

$$
\text{TokenReplenish}(t) = \min(C, \text{tokens} + r \times \Delta t)
$$

$$
\text{Admit}_{TB} = \begin{cases}
\text{Allow} & \text{if tokens} \geq \text{cost} \\
\text{Deny} & \text{otherwise}
\end{cases}
$$

$$
\text{SlidingWindow} = \sum_{t \in [now-window, now]} \text{count}(t)
$$

$$
\text{AdaptiveLimit}_{t+1} = \begin{cases}
\text{limit}_t \times 0.9 & \text{if error} \\
\text{limit}_t \times 1.05 & \text{if latency} < \theta \\
\text{limit}_t & \text{otherwise}
\end{cases}
$$
