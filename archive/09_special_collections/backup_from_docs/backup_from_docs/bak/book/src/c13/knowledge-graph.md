# 知识图谱

本页展示可靠性工程的概念关系。

---

## 📊 核心概念关系图

```text
                   [可靠性工程]
                         |
         +---------------+---------------+
         |               |               |
     [容错机制]      [分布式特性]   [可观测性]
         |               |               |
    +----+----+     +----+----+     +----+----+
    |    |    |     |    |    |     |    |    |
  熔断  限流  重试   共识  事务  指标  日志  追踪
  器    器          一致性 一致性            链路
```

---

## 🎯 概念层次

### 1. 容错机制 (Fault Tolerance)

**熔断器** (Circuit Breaker):

- **状态**: Closed, Open, Half-Open
- **阈值**: 失败率、错误数量、响应时间
- **恢复**: 渐进式恢复、健康检查

**限流器** (Rate Limiter):

- **令牌桶** (Token Bucket): 平滑限流
- **漏桶** (Leaky Bucket): 流量整形
- **固定窗口** (Fixed Window): 简单计数
- **滑动窗口** (Sliding Window): 精确控制
- **滑动日志** (Sliding Log): 精确但昂贵

**重试机制** (Retry):

- **固定延迟**: 简单重试
- **指数退避** (Exponential Backoff): 智能重试
- **抖动** (Jitter): 避免雪崩
- **超时控制**: 快速失败

**降级策略** (Degradation):

- **功能降级**: 关闭非核心功能
- **读写分离**: 保护写入
- **缓存降级**: 返回缓存数据

---

### 2. 分布式特性 (Distributed Features)

**共识算法**:

- **Raft**: Leader-based共识
- **Paxos**: 经典共识算法
- **Gossip**: 最终一致性协议

**事务一致性**:

- **2PC**: 两阶段提交
- **3PC**: 三阶段提交
- **Saga**: 长事务模式
- **TCC**: Try-Confirm-Cancel

**一致性哈希**:

- **虚拟节点**: 负载均衡
- **数据分片**: 横向扩展
- **故障转移**: 高可用性

**服务发现**:

- **客户端发现**: 直接连接
- **服务端发现**: 负载均衡
- **健康检查**: 自动剔除

---

### 3. 可观测性 (Observability)

**指标** (Metrics):

- **Counter**: 累计计数
- **Gauge**: 瞬时值
- **Histogram**: 分布统计
- **Summary**: 摘要统计

**日志** (Logging):

- **结构化日志**: 易于查询
- **日志级别**: 分级管理
- **日志聚合**: 集中存储
- **关联ID**: 追踪请求

**追踪** (Tracing):

- **Span**: 操作片段
- **Trace**: 完整链路
- **采样**: 性能优化
- **上下文传播**: 跨服务追踪

**告警** (Alerting):

- **阈值告警**: 超限通知
- **异常检测**: 智能告警
- **告警聚合**: 减少噪音
- **告警路由**: 定向通知

---

## 🔗 概念关联

### 熔断器 ←→ 系统保护

```rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

// 熔断器状态
#[derive(Clone, Copy, PartialEq)]
enum CircuitState {
    Closed,       // 正常状态
    Open,         // 熔断状态
    HalfOpen,     // 半开状态
}

// 熔断器
struct CircuitBreaker {
    state: Arc<Mutex<CircuitState>>,
    failure_count: Arc<Mutex<usize>>,
    threshold: usize,
    timeout: Duration,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
}

impl CircuitBreaker {
    fn new(threshold: usize, timeout: Duration) -> Self {
        CircuitBreaker {
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            failure_count: Arc::new(Mutex::new(0)),
            threshold,
            timeout,
            last_failure_time: Arc::new(Mutex::new(None)),
        }
    }
    
    async fn call<F, T, E>(&self, f: F) -> Result<T, E>
    where
        F: std::future::Future<Output = Result<T, E>>,
    {
        let state = *self.state.lock().unwrap();
        
        match state {
            CircuitState::Open => {
                // 检查是否应该进入半开状态
                let last_failure = *self.last_failure_time.lock().unwrap();
                if let Some(time) = last_failure {
                    if time.elapsed() > self.timeout {
                        *self.state.lock().unwrap() = CircuitState::HalfOpen;
                    } else {
                        return Err(/* CircuitOpenError */);
                    }
                }
            }
            _ => {}
        }
        
        // 执行调用
        match f.await {
            Ok(result) => {
                self.on_success();
                Ok(result)
            }
            Err(e) => {
                self.on_failure();
                Err(e)
            }
        }
    }
    
    fn on_success(&self) {
        *self.failure_count.lock().unwrap() = 0;
        *self.state.lock().unwrap() = CircuitState::Closed;
    }
    
    fn on_failure(&self) {
        let mut count = self.failure_count.lock().unwrap();
        *count += 1;
        
        if *count >= self.threshold {
            *self.state.lock().unwrap() = CircuitState::Open;
            *self.last_failure_time.lock().unwrap() = Some(Instant::now());
        }
    }
}
```

### 限流器 ←→ 流量控制

```rust
use std::sync::Mutex;
use std::time::{Duration, Instant};

// 令牌桶限流器
struct TokenBucket {
    capacity: usize,          // 桶容量
    tokens: Mutex<f64>,       // 当前令牌数
    rate: f64,                // 令牌生成速率
    last_refill: Mutex<Instant>,
}

impl TokenBucket {
    fn new(capacity: usize, rate: f64) -> Self {
        TokenBucket {
            capacity,
            tokens: Mutex::new(capacity as f64),
            rate,
            last_refill: Mutex::new(Instant::now()),
        }
    }
    
    fn try_acquire(&self, count: usize) -> bool {
        let mut tokens = self.tokens.lock().unwrap();
        let mut last_refill = self.last_refill.lock().unwrap();
        
        // 补充令牌
        let now = Instant::now();
        let elapsed = now.duration_since(*last_refill).as_secs_f64();
        let new_tokens = elapsed * self.rate;
        *tokens = (*tokens + new_tokens).min(self.capacity as f64);
        *last_refill = now;
        
        // 尝试获取令牌
        if *tokens >= count as f64 {
            *tokens -= count as f64;
            true
        } else {
            false
        }
    }
}
```

### 分布式追踪 ←→ 链路监控

```rust
use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

// Span表示一个操作
#[derive(Debug, Clone)]
struct Span {
    trace_id: String,         // 追踪ID
    span_id: String,          // 当前Span ID
    parent_span_id: Option<String>,  // 父Span ID
    name: String,             // 操作名称
    start_time: u64,          // 开始时间(微秒)
    duration: Option<u64>,    // 持续时间(微秒)
    tags: HashMap<String, String>,  // 标签
}

impl Span {
    fn new(trace_id: String, name: String) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_micros() as u64;
        
        Span {
            trace_id,
            span_id: uuid::Uuid::new_v4().to_string(),
            parent_span_id: None,
            name,
            start_time: now,
            duration: None,
            tags: HashMap::new(),
        }
    }
    
    fn with_parent(trace_id: String, parent_id: String, name: String) -> Self {
        let mut span = Self::new(trace_id, name);
        span.parent_span_id = Some(parent_id);
        span
    }
    
    fn finish(&mut self) {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_micros() as u64;
        
        self.duration = Some(now - self.start_time);
    }
    
    fn add_tag(&mut self, key: String, value: String) {
        self.tags.insert(key, value);
    }
}

// 使用示例
async fn process_request() {
    let trace_id = uuid::Uuid::new_v4().to_string();
    
    // 创建根Span
    let mut root_span = Span::new(trace_id.clone(), "process_request".to_string());
    
    // 创建子Span
    let mut db_span = Span::with_parent(
        trace_id.clone(),
        root_span.span_id.clone(),
        "database_query".to_string()
    );
    
    // 执行数据库查询
    // ...
    
    db_span.finish();
    root_span.finish();
    
    // 上报到追踪系统
}
```

---

## 📚 学习路径图

```text
第一步: 理解容错基础（熔断、限流）
    ↓
第二步: 掌握分布式一致性
    ↓
第三步: 实现可观测性（指标、日志、追踪）
    ↓
第四步: 构建高可用系统
    ↓
第五步: 性能优化与调优
```

---

## 🎓 可靠性模式对比

### 容错机制

| 模式 | 目的 | 适用场景 |
|------|------|---------|
| **熔断器** | 防止级联失败 | 服务调用 |
| **限流器** | 保护系统资源 | API网关 |
| **重试** | 处理临时故障 | 网络请求 |
| **降级** | 保护核心功能 | 过载情况 |

### 一致性模型

| 模型 | 一致性 | 可用性 | 性能 |
|------|--------|--------|------|
| **强一致** | 高 | 低 | 低 |
| **最终一致** | 低 | 高 | 高 |
| **因果一致** | 中 | 中 | 中 |

---

## 💡 核心原则

### 1. 故障即常态

```text
故障预期 → 容错设计 → 快速恢复
```

### 2. 可观测性优先

```text
指标+日志+追踪 → 全面监控 → 快速定位
```

### 3. 渐进式降级

```text
优雅降级 → 保护核心 → 用户体验
```

---

## 🔍 Rust 1.90 特性应用

### 1. 类型安全的容错

```rust
// 使用类型系统表达容错策略
trait FallibleService {
    type Output;
    type Error;
    
    async fn call(&self) -> Result<Self::Output, Self::Error>;
}

// 容错装饰器
struct ResilientService<S> {
    inner: S,
    circuit_breaker: CircuitBreaker,
    rate_limiter: TokenBucket,
}

impl<S> ResilientService<S>
where
    S: FallibleService,
{
    async fn call_with_protection(&self) -> Result<S::Output, S::Error> {
        // 限流检查
        if !self.rate_limiter.try_acquire(1) {
            return Err(/* RateLimitError */);
        }
        
        // 熔断器保护
        self.circuit_breaker.call(self.inner.call()).await
    }
}
```

### 2. 异步可观测性

```rust
use tracing::{instrument, info, error};

// 自动追踪
#[instrument(skip(db))]
async fn create_user(db: &Database, name: String) -> Result<User, Error> {
    info!("Creating user: {}", name);
    
    let user = db.insert_user(name).await
        .map_err(|e| {
            error!("Failed to create user: {}", e);
            e
        })?;
    
    info!(user_id = %user.id, "User created successfully");
    Ok(user)
}
```

### 3. 高性能指标收集

```rust
use prometheus::{Counter, Histogram, Registry};
use std::time::Instant;

// 指标定义
struct Metrics {
    request_count: Counter,
    request_duration: Histogram,
}

impl Metrics {
    fn new(registry: &Registry) -> Result<Self, Box<dyn std::error::Error>> {
        let request_count = Counter::new("requests_total", "Total requests")?;
        let request_duration = Histogram::new("request_duration_seconds", "Request duration")?;
        
        registry.register(Box::new(request_count.clone()))?;
        registry.register(Box::new(request_duration.clone()))?;
        
        Ok(Metrics {
            request_count,
            request_duration,
        })
    }
    
    async fn track<F, T>(&self, f: F) -> T
    where
        F: std::future::Future<Output = T>,
    {
        let start = Instant::now();
        self.request_count.inc();
        
        let result = f.await;
        
        let duration = start.elapsed().as_secs_f64();
        self.request_duration.observe(duration);
        
        result
    }
}
```

---

## 📖 相关章节

- **[基础概念](./foundations.md)** - 可靠性理论
- **[实践指南](./guides.md)** - 实战技巧
- **[代码示例](./examples.md)** - 完整实现 ⭐
- **[返回模块首页](./README.md)**

---

## 🔗 扩展学习

### 深入阅读

- [可靠性工程完整指南](../../crates/c13_reliability/README.md)
- [Google SRE Book](https://sre.google/books/)
- [Release It!](https://pragprog.com/titles/mnee2/)

### 相关模块

- **[C10: 网络编程](../c10/README.md)** - 网络容错
- **[C12: 领域建模](../c12/README.md)** - 分布式模型
- **[C06: 异步编程](../c06/README.md)** - 异步基础

---

## 🎯 实践项目建议

### 入门级

- 熔断器实现
- 令牌桶限流
- 简单重试机制

### 进阶级

- 分布式追踪系统
- 服务网格
- 指标监控平台

### 高级

- 混沌工程平台
- 自动降级系统
- 分布式事务框架

---

## 📊 可靠性指标

### SLA目标

```text
可用性 = (总时间 - 故障时间) / 总时间

99%    → 3.65天/年停机
99.9%  → 8.76小时/年停机
99.99% → 52.56分钟/年停机
99.999% → 5.26分钟/年停机
```

### 监控指标

- **延迟**: P50, P95, P99
- **吞吐量**: QPS, TPS
- **错误率**: 4xx, 5xx
- **饱和度**: CPU, 内存, 磁盘

---

**可靠性工程是构建生产级系统的必备技能！** 🚀
