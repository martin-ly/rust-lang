# 限流与幂等模式形式化定义 {#限流与幂等模式形式化定义}

> **概念族**: 软件设计 / 分布式模式 / 限流与幂等
>
> **内容分级**: [归档级]
>
> **分级**: [B]
>
> **Bloom 层级**: L4-L6 (分析/评价/创造)
>
> **模式类型**: 稳定性机制 / 一致性机制
>
> **创建日期**: 2026-06-29
>
> **版本**: v1.0
>
> **最后更新**: 2026-06-29
>
> **Rust 版本**: 1.96.0+ (Edition 2024)
>
> **状态**: ✅ 已完成
>
> **对齐说明**: 本文档按 [Tower 限流中间件](https://docs.rs/tower/latest/tower/limit/rate/struct.RateLimit.html)、[Tokio 时间原语](https://docs.rs/tokio/latest/tokio/time/index.html)、[Rust 标准库](https://doc.rust-lang.org/std/) 与分布式系统经典文献进行权威来源对齐。
>
> **权威来源**: [Tower Docs](https://docs.rs/tower/latest/tower/limit/rate/struct.RateLimit.html) | [Tokio Time](https://docs.rs/tokio/latest/tokio/time/index.html) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Standard Library](https://doc.rust-lang.org/std/)

---

## 📑 目录 {#目录}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [限流与幂等模式形式化定义 {#限流与幂等模式形式化定义}](#限流与幂等模式形式化定义-限流与幂等模式形式化定义)
  - [📑 目录 {#目录}](#-目录-目录)
  - [1. 概念定义 (Def) {#1-概念定义-def}](#1-概念定义-def-1-概念定义-def)
    - [Def RL1: Rate Limiting（限流） {#def-rl1-rate-limiting限流}](#def-rl1-rate-limiting限流-def-rl1-rate-limiting限流)
    - [Def RL2: Token Bucket（令牌桶） {#def-rl2-token-bucket令牌桶}](#def-rl2-token-bucket令牌桶-def-rl2-token-bucket令牌桶)
    - [Def RL3: Leaky Bucket（漏桶） {#def-rl3-leaky-bucket漏桶}](#def-rl3-leaky-bucket漏桶-def-rl3-leaky-bucket漏桶)
    - [Def RL4: Fixed Window（固定窗口） {#def-rl4-fixed-window固定窗口}](#def-rl4-fixed-window固定窗口-def-rl4-fixed-window固定窗口)
    - [Def RL5: Sliding Window（滑动窗口） {#def-rl5-sliding-window滑动窗口}](#def-rl5-sliding-window滑动窗口-def-rl5-sliding-window滑动窗口)
    - [Def ID1: Idempotency（幂等性） {#def-id1-idempotency幂等性}](#def-id1-idempotency幂等性-def-id1-idempotency幂等性)
    - [Def ID2: Idempotency Key（幂等键） {#def-id2-idempotency-key幂等键}](#def-id2-idempotency-key幂等键-def-id2-idempotency-key幂等键)
  - [2. 基本假设 (Axiom) {#2-基本假设-axiom}](#2-基本假设-axiom-2-基本假设-axiom)
    - [Axiom RL1: 容量非负 {#axiom-rl1-容量非负}](#axiom-rl1-容量非负-axiom-rl1-容量非负)
    - [Axiom RL2: 请求计数单调 {#axiom-rl2-请求计数单调}](#axiom-rl2-请求计数单调-axiom-rl2-请求计数单调)
    - [Axiom ID1: 幂等键唯一性 {#axiom-id1-幂等键唯一性}](#axiom-id1-幂等键唯一性-axiom-id1-幂等键唯一性)
    - [Axiom ID2: 幂等结果不变性 {#axiom-id2-幂等结果不变性}](#axiom-id2-幂等结果不变性-axiom-id2-幂等结果不变性)
  - [3. 定理 (Theorem) {#3-定理-theorem}](#3-定理-theorem-3-定理-theorem)
    - [Theorem RL1: 令牌桶速率上界 {#theorem-rl1-令牌桶速率上界}](#theorem-rl1-令牌桶速率上界-theorem-rl1-令牌桶速率上界)
    - [Theorem RL2: 滑动窗口无边界突发 {#theorem-rl2-滑动窗口无边界突发}](#theorem-rl2-滑动窗口无边界突发-theorem-rl2-滑动窗口无边界突发)
    - [Theorem ID1: 幂等执行一致性 {#theorem-id1-幂等执行一致性}](#theorem-id1-幂等执行一致性-theorem-id1-幂等执行一致性)
  - [4. Rust 实现示例 {#4-rust-实现示例}](#4-rust-实现示例-4-rust-实现示例)
  - [5. 反例边界 {#5-反例边界}](#5-反例边界-5-反例边界)
    - [5.1 限流误杀 {#51-限流误杀}](#51-限流误杀-51-限流误杀)
    - [5.2 幂等键冲突 {#52-幂等键冲突}](#52-幂等键冲突-52-幂等键冲突)
    - [5.3 分布式锁与幂等 {#53-分布式锁与幂等}](#53-分布式锁与幂等-53-分布式锁与幂等)
  - [6. 算法选择建议 {#6-算法选择建议}](#6-算法选择建议-6-算法选择建议)
  - [🆕 Rust 1.96 深度整合更新 {#rust-196-深度整合更新}](#-rust-196-深度整合更新-rust-196-深度整合更新)
    - [本文档的 Rust 1.96 更新要点 {#本文档的-rust-196-更新要点}](#本文档的-rust-196-更新要点-本文档的-rust-196-更新要点)
      - [核心特性应用 {#核心特性应用}](#核心特性应用-核心特性应用)
      - [代码示例更新 {#代码示例更新}](#代码示例更新-代码示例更新)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)
    - [P0（核心官方 / 生产级文档） {#p0核心官方-生产级文档}](#p0核心官方--生产级文档-p0核心官方-生产级文档)
    - [P1（行业最佳实践 / 权威工程指南） {#p1行业最佳实践-权威工程指南}](#p1行业最佳实践--权威工程指南-p1行业最佳实践-权威工程指南)
    - [P2（学术 / 社区参考） {#p2学术-社区参考}](#p2学术--社区参考-p2学术-社区参考)

---

## 1. 概念定义 (Def) {#1-概念定义-def}

> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Def RL1: Rate Limiting（限流） {#def-rl1-rate-limiting限流}

> **来源: [Tower Docs – RateLimit](https://docs.rs/tower/latest/tower/limit/rate/struct.RateLimit.html)**
>
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

限流是一种**流量塑形机制**，用于控制单位时间内进入系统或下游服务的请求数量，防止过载、级联故障与资源耗尽。

```text
RateLimiter := (S, policy, classifier)

  where:
    S: 状态（计数器 / 令牌 / 队列）
    policy = (limit, window)
    classifier: Request → key  -- 按客户端、IP、接口等维度分组
```
### Def RL2: Token Bucket（令牌桶） {#def-rl2-token-bucket令牌桶}

> **来源: [Wikipedia - Token Bucket](https://en.wikipedia.org/wiki/Token_bucket)**

```text
TokenBucket := (capacity, refill_rate, tokens)

  where:
    capacity ∈ ℕ              -- 桶容量（最大突发量）
    refill_rate ∈ ℝ⁺          -- 每秒回填令牌数（长期平均速率）
    tokens ∈ [0, capacity]    -- 当前可用令牌数
```
允许一定突发，但长期速率受 `refill_rate` 约束。

### Def RL3: Leaky Bucket（漏桶） {#def-rl3-leaky-bucket漏桶}

> **来源: [Wikipedia - Leaky Bucket](https://en.wikipedia.org/wiki/Leaky_bucket)**

```text
LeakyBucket := (capacity, leak_rate, queue)

  where:
    capacity ∈ ℕ        -- 排队容量
    leak_rate ∈ ℝ⁺      -- 恒定流出速率
    queue: FIFO         -- 待处理请求队列
```
输出速率平滑，但可能引入排队延迟；超出容量则直接拒绝。

### Def RL4: Fixed Window（固定窗口） {#def-rl4-fixed-window固定窗口}

> **来源: [Wikipedia - Rate Limiting](https://en.wikipedia.org/wiki/Rate_limiting)**

```text
FixedWindow := (window, limit, counter)

  where:
    window ∈ Time
    limit ∈ ℕ
    counter 在每个窗口开始时重置
```
实现简单，但在窗口边界处可能出现 **2×limit** 的突发流量。

### Def RL5: Sliding Window（滑动窗口） {#def-rl5-sliding-window滑动窗口}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```text
SlidingWindow := (window, limit, timestamps)

  where:
    timestamps = { t₁, t₂, ..., tₙ | tᵢ ∈ [now - window, now] }
    |timestamps| ≤ limit
```
通过维护最近一段时间内的请求时间戳，消除固定窗口的边界突发问题。

### Def ID1: Idempotency（幂等性） {#def-id1-idempotency幂等性}

> **来源: [IETF HTTP Semantics RFC 9110](https://www.rfc-editor.org/rfc/rfc9110.html)**
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

幂等性是指**同一操作执行一次与执行多次产生的效果相同**，且不会导致副作用重复累积。

```text
Idempotent(Op) := ∀n ≥ 1. Opⁿ ≡ Op¹
```
在分布式系统中，幂等性是重试、超时恢复、消息队列至少一次投递的前提。

### Def ID2: Idempotency Key（幂等键） {#def-id2-idempotency-key幂等键}

> **来源: [Stripe Idempotency](https://stripe.com/docs/api/idempotent_requests)**

```text
IdempotencyKey := (client_id, scope, nonce, ttl)

  where:
    client_id: 调用方标识
    scope: 业务作用域（如 order、payment）
    nonce: 客户端生成的唯一值
    ttl: 键的有效期
```
幂等键通常由客户端生成，服务端在 TTL 内保存 `<key, result>` 映射以实现去重。

---

## 2. 基本假设 (Axiom) {#2-基本假设-axiom}

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Axiom RL1: 容量非负 {#axiom-rl1-容量非负}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```text
capacity ≥ 0 ∧ limit ≥ 0
```
限流器的容量与阈值必须为非负数。

### Axiom RL2: 请求计数单调 {#axiom-rl2-请求计数单调}

> **来源: [Tokio Time](https://docs.rs/tokio/latest/tokio/time/index.html)**

```text
t₁ < t₂ → count(t₁) ≤ count(t₂)
```
在不重置窗口的前提下，累计请求数不会减少。

### Axiom ID1: 幂等键唯一性 {#axiom-id1-幂等键唯一性}

> **来源: [Stripe Idempotency](https://stripe.com/docs/api/idempotent_requests)**

```text
(k₁ ≠ k₂) → Op(k₁) 与 Op(k₂) 相互独立
```
不同幂等键应对应不同的业务语义；键冲突将导致错误去重。

### Axiom ID2: 幂等结果不变性 {#axiom-id2-幂等结果不变性}

> **来源: [IEEE - Resilient Software Architecture](https://standards.ieee.org/)**

```text
key = k ∧ ttl_not_expired(k) → result(k) 保持不变
```
在有效期内，同一幂等键返回的结果必须一致。

---

## 3. 定理 (Theorem) {#3-定理-theorem}

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### Theorem RL1: 令牌桶速率上界 {#theorem-rl1-令牌桶速率上界}

> **来源: [Wikipedia - Token Bucket](https://en.wikipedia.org/wiki/Token_bucket)**

```text
lim_{T→∞} allowed(T) / T ≤ refill_rate
```
**证明概要**:

1. 桶内令牌数上限为 `capacity`。
2. 任意长时间段内，新增令牌总数 ≤ `refill_rate × T + capacity`。
3. 因此单位时间通过的请求长期平均值不超过 `refill_rate`。

### Theorem RL2: 滑动窗口无边界突发 {#theorem-rl2-滑动窗口无边界突发}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```text
∀t. |{ r | time(r) ∈ [t - window, t] }| ≤ limit
```
**证明概要**:

1. 每次请求前先清理过期时间戳。
2. 仅当当前窗口内时间戳数量小于 `limit` 时才允许通过。
3. 由于窗口是连续滑动的，不存在固定窗口的边界重置。

### Theorem ID1: 幂等执行一致性 {#theorem-id1-幂等执行一致性}

> **来源: [ACM - Fault-Tolerant Design Patterns](https://dl.acm.org/)**

```text
∀k. (first_success(k) → result) ∧ (retry(k) within ttl) → result' = result
```
**证明概要**:

1. 首次成功执行后，服务端保存 `<k, result>`。
2. 后续携带相同 `k` 的请求在 TTL 内命中缓存。
3. 缓存结果直接返回，业务逻辑不再执行。

---

## 4. Rust 实现示例 {#4-rust-实现示例}

> **来源: [Tower Docs – RateLimit](https://docs.rs/tower/latest/tower/limit/rate/struct.RateLimit.html)**
>
> **代码锚点**: [crates/c06_async/examples/rate_limiting_idempotency_pattern.rs](../../../../crates/c06_async/examples/rate_limiting_idempotency_pattern.rs)

```rust,ignore
// 节选：Token Bucket + Sliding Window + Idempotency Store
use std::future::Future;
use std::sync::Arc;
use std::time::{Duration, Instant};
use dashmap::DashMap;
use parking_lot::Mutex;
use tokio::time::sleep;

#[derive(Clone)]
pub struct TokenBucket {
    capacity: u64,
    refill_rate_per_sec: u64,
    state: Arc<Mutex<BucketState>>,
}

struct BucketState { tokens: u64, last_refill: Instant }

impl TokenBucket {
    pub fn new(capacity: u64, refill_rate_per_sec: u64) -> Self {
        Self { capacity, refill_rate_per_sec,
               state: Arc::new(Mutex::new(BucketState { tokens: capacity, last_refill: Instant::now() })) }
    }

    pub async fn acquire(&self, n: u64) -> bool {
        loop {
            let wait = {
                let mut s = self.state.lock();
                let now = Instant::now();
                let elapsed = now.duration_since(s.last_refill).as_secs();
                s.tokens = (s.tokens + elapsed * self.refill_rate_per_sec).min(self.capacity);
                s.last_refill = now;
                if s.tokens >= n { s.tokens -= n; return true; }
                let missing = n - s.tokens;
                Duration::from_secs_f64(missing as f64 / self.refill_rate_per_sec as f64)
            };
            sleep(wait).await;
        }
    }
}

#[derive(Clone)]
pub struct SlidingWindow {
    window: Duration, max: usize,
    requests: Arc<Mutex<Vec<Instant>>>,
}

impl SlidingWindow {
    pub fn new(window: Duration, max: usize) -> Self {
        Self { window, max, requests: Arc::new(Mutex::new(Vec::new())) }
    }
    pub fn try_request(&self) -> bool {
        let mut reqs = self.requests.lock();
        let cutoff = Instant::now() - self.window;
        reqs.retain(|t| *t >= cutoff);
        if reqs.len() < self.max { reqs.push(Instant::now()); true } else { false }
    }
}

pub struct IdempotencyStore {
    cells: DashMap<String, Arc<tokio::sync::Mutex<Option<(Instant, String)>>>>,
    ttl: Duration,
}

impl IdempotencyStore {
    pub fn new(ttl: Duration) -> Self { Self { cells: DashMap::new(), ttl } }

    pub async fn execute<F, Fut>(&self, key: &str, op: F) -> anyhow::Result<String>
    where F: FnOnce() -> Fut, Fut: Future<Output = anyhow::Result<String>>
    {
        let cell = self.cells
            .entry(key.to_string())
            .or_insert_with(|| Arc::new(tokio::sync::Mutex::new(None)))
            .clone();
        let mut guard = cell.lock().await;
        if let Some((ts, cached)) = guard.as_ref() {
            if ts.elapsed() < self.ttl { return Ok(cached.clone()); }
        }
        let result = op().await?;
        *guard = Some((Instant::now(), result.clone()));
        Ok(result)
    }
}
```
---

## 5. 反例边界 {#5-反例边界}

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

### 5.1 限流误杀 {#51-限流误杀}

> **来源: [AWS Architecture Blog - Rate Limiting](https://docs.aws.amazon.com/)**

**反例**: 对所有用户共享同一个计数器。

- 某恶意用户刷接口，迅速耗尽全局配额。
- 正常用户请求被误杀，可用性受损。

**边界条件**:

- 限流维度应细化到 `user_id` / `api_key` / `IP`。
- 应区分“硬限制”与“软限制”，为关键用户预留额度。

### 5.2 幂等键冲突 {#52-幂等键冲突}

> **来源: [Stripe Idempotency](https://stripe.com/docs/api/idempotent_requests)**

**反例**: 客户端使用 `UUIDv4` 但不同业务场景复用同一个 key。

```text
支付请求 A: key = "abc"
支付请求 B: key = "abc"  -- 不同金额、不同收款方
```
- 服务端误以为 B 是 A 的重试，返回错误结果。

**边界条件**:

- 幂等键必须包含业务作用域，如 `"payment:{user_id}:{nonce}"`。
- 客户端在收到响应前不得复用同一 key。

### 5.3 分布式锁与幂等 {#53-分布式锁与幂等}

> **来源: [Redis Distributed Locks](https://redis.io/docs/manual/patterns/distributed-locks/)**

**反例**: 仅依赖内存级幂等键，未在跨实例场景加锁。

```text
Instance 1: 检查 key 不存在 → 开始执行业务
Instance 2: 同时检查 key 不存在 → 也开始执行业务
Instance 1: 执行完成，写入 key
Instance 2: 执行完成，覆盖 key
```
- 两个实例都执行了实际写操作，幂等性被破坏。

**边界条件**:

- 在分布式环境中，先获取分布式锁（如 Redis `SET NX EX`），再检查幂等键。
- 锁的 TTL 必须大于业务执行最大耗时；完成后主动释放锁。
- 幂等键 TTL 应大于锁 TTL，防止成功后 key 被提前清理。

---

## 6. 算法选择建议 {#6-算法选择建议}

> **来源: [Tokio Tutorial](https://tokio.rs/tokio/tutorial)**

| 场景 | 推荐算法 | 说明 |
|------|----------|------|
| API 网关限流 | Token Bucket | 允许合理突发，长期速率可控 |
| 消息队列消费 | Leaky Bucket | 平滑消费速率，保护下游 |
| 简单计数限流 | Fixed Window | 实现最简单，但需接受边界突发 |
| 精确限流 | Sliding Window | 无边界突发，内存开销稍高 |
| 分布式全局限流 | Token Bucket + Redis | 使用 Redis 原子计数回填令牌 |
| 支付/订单接口 | Idempotency Key | 配合数据库唯一索引或分布式锁 |

---

## 🆕 Rust 1.96 深度整合更新 {#rust-196-深度整合更新}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本文档的 Rust 1.96 更新要点 {#本文档的-rust-196-更新要点}

#### 核心特性应用 {#核心特性应用}

| 特性 | 应用场景 | 文档章节 |
|------|----------|----------|
| `std::sync::LazyLock` | 全局限流器 / 幂等配置懒加载 | 状态管理、配置 |
| `tokio::time` | 异步令牌回填、TTL 管理 | §4 实现示例 |
| `DashMap` | 高并发幂等键存储 | §4 实现示例 |
| `parking_lot::Mutex` | 低延迟限流状态同步 | §4 实现示例 |

#### 代码示例更新 {#代码示例更新}

- ✅ 使用 Rust 1.96 语法验证
- ✅ 兼容 Edition 2024
- ✅ 通过 `cargo check -p c06_async --examples`

---

**维护者**: Rust 学习项目团队

**最后更新**: 2026-06-29

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-06-29 新增限流与幂等模式文档及对应代码示例

**文档版本**: 1.0

**对应 Rust 版本**: 1.96.0+ (Edition 2024)

**状态**: ✅ 已完成

---

## 相关概念 {#相关概念}

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [Circuit Breaker](03_circuit_breaker.md)
- [重试模式](07_retry_pattern.md)
- [超时模式](06_timeout_pattern.md)
- [05_distributed 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

### P0（核心官方 / 生产级文档） {#p0核心官方-生产级文档}

> **来源: [Tower Docs - RateLimit](https://docs.rs/tower/latest/tower/limit/rate/struct.RateLimit.html)**
> **来源: [Tokio Time](https://docs.rs/tokio/latest/tokio/time/index.html)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

### P1（行业最佳实践 / 权威工程指南） {#p1行业最佳实践-权威工程指南}

> **来源: [Stripe Idempotency](https://stripe.com/docs/api/idempotent_requests)**
> **来源: [AWS Architecture Center](https://docs.aws.amazon.com/)**
> **来源: [Martin Fowler - Idempotent Receiver](https://martinfowler.com/)**

### P2（学术 / 社区参考） {#p2学术-社区参考}

> **来源: [Wikipedia - Token Bucket](https://en.wikipedia.org/wiki/Token_bucket)**
> **来源: [Wikipedia - Leaky Bucket](https://en.wikipedia.org/wiki/Leaky_bucket)**
> **来源: [Wikipedia - Rate Limiting](https://en.wikipedia.org/wiki/Rate_limiting)**
> **来源: [IETF RFC 9110 - HTTP Semantics](https://www.rfc-editor.org/rfc/rfc9110.html)**
> **来源: [Redis Distributed Locks](https://redis.io/docs/manual/patterns/distributed-locks/)**
> **来源: [ACM - Fault-Tolerant Design Patterns](https://dl.acm.org/)**
> **来源: [IEEE - Resilient Software Architecture](https://standards.ieee.org/)**

---
