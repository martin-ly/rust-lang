# 最佳实践指南

本文档提供使用 c13_reliability 框架的最佳实践建议。

## 📋 目录

- [最佳实践指南](#最佳实践指南)
  - [📋 目录](#-目录)
  - [通用原则](#通用原则)
    - [1. 始终使用 Result 类型](#1-始终使用-result-类型)
    - [2. 使用 Arc 共享状态](#2-使用-arc-共享状态)
    - [3. 合理使用 tracing](#3-合理使用-tracing)
  - [容错机制](#容错机制)
    - [熔断器最佳实践](#熔断器最佳实践)
      - [1. 选择合适的阈值](#1-选择合适的阈值)
      - [2. 组合使用重试和熔断器](#2-组合使用重试和熔断器)
    - [限流器最佳实践](#限流器最佳实践)
      - [1. 选择合适的限流算法](#1-选择合适的限流算法)
      - [2. 分层限流](#2-分层限流)
  - [分布式系统](#分布式系统)
    - [共识算法最佳实践](#共识算法最佳实践)
      - [1. Raft 节点配置](#1-raft-节点配置)
    - [分布式事务最佳实践](#分布式事务最佳实践)
      - [1. 选择合适的事务模式](#1-选择合适的事务模式)
    - [一致性哈希最佳实践](#一致性哈希最佳实践)
      - [1. 选择合适的虚拟节点数](#1-选择合适的虚拟节点数)
  - [并发编程](#并发编程)
    - [Actor 模型最佳实践](#actor-模型最佳实践)
      - [1. 保持 Actor 轻量](#1-保持-actor-轻量)
      - [2. 使用监督树](#2-使用监督树)
    - [STM 最佳实践](#stm-最佳实践)
      - [1. 保持事务短小](#1-保持事务短小)
  - [微服务架构](#微服务架构)
    - [服务发现最佳实践](#服务发现最佳实践)
      - [1. 设置健康检查](#1-设置健康检查)
      - [2. 客户端负载均衡](#2-客户端负载均衡)
  - [可观测性](#可观测性)
    - [指标收集最佳实践](#指标收集最佳实践)
      - [1. 记录关键指标](#1-记录关键指标)
      - [2. 定期清理过期数据](#2-定期清理过期数据)
    - [日志关联最佳实践](#日志关联最佳实践)
      - [1. 使用追踪ID](#1-使用追踪id)
      - [2. 在微服务间传播追踪信息](#2-在微服务间传播追踪信息)
  - [性能优化](#性能优化)
    - [1. 使用连接池](#1-使用连接池)
    - [2. 批量处理](#2-批量处理)
    - [3. 使用 tokio::spawn 并行处理](#3-使用-tokiospawn-并行处理)
    - [4. 避免在锁内进行异步操作](#4-避免在锁内进行异步操作)
  - [错误处理](#错误处理)
    - [1. 提供上下文信息](#1-提供上下文信息)
    - [2. 使用自定义错误类型](#2-使用自定义错误类型)
    - [3. 区分可恢复和不可恢复错误](#3-区分可恢复和不可恢复错误)
  - [测试最佳实践](#测试最佳实践)
    - [1. 编写集成测试](#1-编写集成测试)
    - [2. 使用 mock 进行隔离测试](#2-使用-mock-进行隔离测试)
  - [总结](#总结)
    - [核心原则](#核心原则)
    - [避免的常见错误](#避免的常见错误)
    - [推荐的开发流程](#推荐的开发流程)

---

## 通用原则

### 1. 始终使用 Result 类型

✅ **推荐**:

```rust
async fn fetch_user(id: u64) -> anyhow::Result<User> {
    // 实现
}
```

❌ **不推荐**:

```rust
async fn fetch_user(id: u64) -> Option<User> {
    // 丢失了错误信息
}
```

### 2. 使用 Arc 共享状态

✅ **推荐**:

```rust
let circuit_breaker = Arc::new(CircuitBreaker::new(config));
let cb_clone = Arc::clone(&circuit_breaker);
```

❌ **不推荐**:

```rust
// 不要在异步代码中使用 Rc
let circuit_breaker = Rc::new(CircuitBreaker::new(config));
```

### 3. 合理使用 tracing

✅ **推荐**:

```rust
use tracing::{info, warn, error, debug};

#[tracing::instrument]
async fn process_request(id: u64) -> anyhow::Result<()> {
    debug!("开始处理请求");
    // 处理逻辑
    info!("请求处理完成");
    Ok(())
}
```

---

## 容错机制

### 熔断器最佳实践

#### 1. 选择合适的阈值

✅ **推荐配置**:

```rust
let config = CircuitBreakerConfig {
    failure_threshold: 5,           // 5次失败触发熔断
    success_threshold: 2,           // 2次成功关闭熔断
    recovery_timeout: Duration::from_secs(30),  // 30秒恢复窗口
    half_open_max_requests: 3,      // 半开状态最多3个请求
    sliding_window_size: Duration::from_secs(60),
    minimum_requests: 10,           // 最少10个请求才计算失败率
};
```

**配置建议**:

- `failure_threshold`: 通常设置为 3-10，取决于服务的容错能力
- `recovery_timeout`: 根据下游服务的恢复时间设置，通常 10-60 秒
- `minimum_requests`: 避免因为样本太少而误判

#### 2. 组合使用重试和熔断器

✅ **推荐**:

```rust
let retry_policy = RetryPolicy::exponential_backoff(3, Duration::from_millis(100));

let result = circuit_breaker
    .call(|| async {
        // 先重试，如果多次重试都失败，熔断器才会打开
        retry_with_policy(&retry_policy, || async {
            call_external_service().await
        }).await
    })
    .await?;
```

### 限流器最佳实践

#### 1. 选择合适的限流算法

**场景选择指南**:

| 算法 | 适用场景 | 优点 | 缺点 |
|------|---------|------|------|
| Token Bucket | API 限流 | 允许突发流量 | 配置复杂 |
| Leaky Bucket | 平滑流量 | 流量均匀 | 不允许突发 |
| Fixed Window | 简单计数 | 实现简单 | 边界问题 |
| Sliding Window | 精确限流 | 准确 | 内存占用大 |
| Sliding Window Log | 最精确 | 最准确 | 开销最大 |

✅ **推荐**:

```rust
// API 限流使用 Token Bucket
let api_limiter = TokenBucket::new(1000, Duration::from_secs(1));

// 后台任务使用 Leaky Bucket
let bg_limiter = LeakyBucket::new(10, Duration::from_secs(1));
```

#### 2. 分层限流

✅ **推荐**:

```rust
// 全局限流
let global_limiter = TokenBucket::new(10000, Duration::from_secs(1));

// 用户级限流
let user_limiter = TokenBucket::new(100, Duration::from_secs(1));

// 先检查全局，再检查用户级
if !global_limiter.try_acquire().await {
    return Err(anyhow::anyhow!("系统繁忙"));
}

if !user_limiter.try_acquire().await {
    return Err(anyhow::anyhow!("请求过于频繁"));
}
```

---

## 分布式系统

### 共识算法最佳实践

#### 1. Raft 节点配置

✅ **推荐**:

```rust
// 使用奇数个节点（3、5、7）
let peers = vec![
    "node2".to_string(),
    "node3".to_string(),
];

let raft = RaftNode::new("node1".to_string(), peers);

// 设置合理的超时
// election_timeout: 150-300ms
// heartbeat_interval: 50ms
```

**配置建议**:

- **3节点**: 适合小型集群，容忍1个节点故障
- **5节点**: 适合中型集群，容忍2个节点故障
- **7节点**: 适合大型集群，但性能会下降

### 分布式事务最佳实践

#### 1. 选择合适的事务模式

**选择指南**:

| 模式 | 一致性 | 性能 | 复杂度 | 适用场景 |
|------|--------|------|--------|---------|
| Saga | 最终一致 | 高 | 中 | 长事务、微服务 |
| 2PC | 强一致 | 低 | 低 | 小规模事务 |
| 3PC | 强一致 | 低 | 中 | 需要避免阻塞 |
| TCC | 强一致 | 中 | 高 | 金融交易 |

✅ **推荐 - Saga 用于微服务**:

```rust
let saga = SagaOrchestrator::new();

saga.add_step(
    || async { create_order().await },
    || async { cancel_order().await },
).await?;

saga.add_step(
    || async { deduct_inventory().await },
    || async { restore_inventory().await },
).await?;

saga.execute().await?;
```

### 一致性哈希最佳实践

#### 1. 选择合适的虚拟节点数

✅ **推荐**:

```rust
// 虚拟节点数建议：150-300
let mut ch = ConsistentHash::new(150);

for i in 1..=10 {
    ch.add_node(&format!("server{}", i));
}
```

**配置建议**:

- 物理节点 < 10: 虚拟节点 150-200
- 物理节点 10-50: 虚拟节点 100-150
- 物理节点 > 50: 虚拟节点 50-100

---

## 并发编程

### Actor 模型最佳实践

#### 1. 保持 Actor 轻量

✅ **推荐**:

```rust
struct UserActor {
    user_id: u64,
    session: Arc<Session>,
    // 最小化状态
}

#[async_trait::async_trait]
impl Actor for UserActor {
    type Message = UserMessage;
    
    async fn handle(&mut self, msg: Self::Message, ctx: &ActorContext<Self>) -> anyhow::Result<()> {
        // 快速处理消息
        match msg {
            UserMessage::Login => self.handle_login().await?,
            UserMessage::Logout => self.handle_logout().await?,
        }
        Ok(())
    }
}
```

❌ **不推荐**:

```rust
struct HeavyActor {
    // 不要在 Actor 中保存大量数据
    large_cache: HashMap<String, Vec<u8>>,
    // 不要保存阻塞资源
    blocking_file: std::fs::File,
}
```

#### 2. 使用监督树

✅ **推荐**:

```rust
let supervisor = SupervisorActor::new(RestartStrategy::OneForOne);

// 创建子 Actor
let child1 = supervisor.spawn_child(WorkerActor::new()).await?;
let child2 = supervisor.spawn_child(WorkerActor::new()).await?;

// 如果子 Actor 崩溃，监督者会自动重启
```

### STM 最佳实践

#### 1. 保持事务短小

✅ **推荐**:

```rust
// 短事务
stm_transaction(|| {
    let balance = account.read()?;
    if balance >= amount {
        account.write(balance - amount)?;
        Ok(())
    } else {
        Err(anyhow::anyhow!("余额不足"))
    }
}).await?;
```

❌ **不推荐**:

```rust
// 长事务，容易冲突
stm_transaction(|| {
    // 不要在事务中进行 I/O
    let data = read_from_database().await?;  // ❌
    // 不要在事务中进行复杂计算
    let result = expensive_computation(data)?;  // ❌
    tvar.write(result)?;
    Ok(())
}).await?;
```

---

## 微服务架构

### 服务发现最佳实践

#### 1. 设置健康检查

✅ **推荐**:

```rust
let registry = ServiceRegistry::new();

let mut metadata = HashMap::new();
metadata.insert("version".to_string(), "1.0.0".to_string());
metadata.insert("health_check".to_string(), "/health".to_string());

registry.register(
    "user-service",
    "http://localhost:8080",
    metadata
).await?;

// 定期更新心跳
tokio::spawn(async move {
    loop {
        registry.heartbeat("user-service").await;
        tokio::time::sleep(Duration::from_secs(10)).await;
    }
});
```

#### 2. 客户端负载均衡

✅ **推荐**:

```rust
let services = registry.discover("user-service").await?;

// 使用轮询策略
let service = services[request_count % services.len()];

// 或使用随机策略
let service = services[rand::random::<usize>() % services.len()];
```

---

## 可观测性

### 指标收集最佳实践

#### 1. 记录关键指标

✅ **推荐**:

```rust
let aggregator = MetricsAggregator::new();

// 业务指标
aggregator.record_counter("orders.created", 1.0).await;
aggregator.record_histogram("order.amount", amount).await;

// 性能指标
aggregator.record_histogram("api.latency_ms", latency.as_millis() as f64).await;
aggregator.record_gauge("active_connections", conn_count as f64).await;

// 错误指标
aggregator.record_counter("errors.validation", 1.0).await;
```

**指标命名规范**:

- 使用 `.` 分隔层级：`service.method.metric`
- 使用小写字母和下划线
- 保持简洁但有意义

#### 2. 定期清理过期数据

✅ **推荐**:

```rust
// 使用时间窗口查询
let stats = aggregator
    .get_histogram_stats("api.latency_ms", Duration::from_secs(300))
    .await?;

// 定期清理
tokio::spawn(async move {
    loop {
        aggregator.cleanup_old_data().await;
        tokio::time::sleep(Duration::from_secs(3600)).await;
    }
});
```

### 日志关联最佳实践

#### 1. 使用追踪ID

✅ **推荐**:

```rust
let trace_id = uuid::Uuid::new_v4().to_string();
let request_id = uuid::Uuid::new_v4().to_string();

correlator.log(
    LogLevel::Info,
    "处理用户请求",
    Some(&trace_id),
    Some(&request_id),
    vec![
        ("user_id".to_string(), user_id.to_string()),
        ("action".to_string(), "create_order".to_string()),
    ]
).await?;
```

#### 2. 在微服务间传播追踪信息

✅ **推荐**:

```rust
// 服务 A
let trace_id = extract_trace_id_from_request(&request);
let response = client
    .post("/api/endpoint")
    .header("X-Trace-Id", &trace_id)
    .header("X-Request-Id", &request_id)
    .send()
    .await?;

// 服务 B
let trace_id = request.headers().get("X-Trace-Id");
let request_id = request.headers().get("X-Request-Id");
```

---

## 性能优化

### 1. 使用连接池

✅ **推荐**:

```rust
// 数据库连接池
let pool = DatabasePool::new(pool_size: 20);

// HTTP 客户端连接池
let client = reqwest::Client::builder()
    .pool_max_idle_per_host(10)
    .build()?;
```

### 2. 批量处理

✅ **推荐**:

```rust
// 批量记录指标
let batch = vec![
    ("metric1", 1.0),
    ("metric2", 2.0),
    ("metric3", 3.0),
];

for (name, value) in batch {
    aggregator.record_counter(name, value).await;
}
```

### 3. 使用 tokio::spawn 并行处理

✅ **推荐**:

```rust
let tasks: Vec<_> = users.iter().map(|user| {
    let user = user.clone();
    tokio::spawn(async move {
        process_user(user).await
    })
}).collect();

let results = futures::future::join_all(tasks).await;
```

### 4. 避免在锁内进行异步操作

❌ **不推荐**:

```rust
let mut data = mutex.lock().await;
let result = call_external_service().await;  // ❌ 持有锁时进行异步调用
data.insert(result);
```

✅ **推荐**:

```rust
let result = call_external_service().await;
let mut data = mutex.lock().await;
data.insert(result);  // ✅ 先完成异步操作，再获取锁
```

---

## 错误处理

### 1. 提供上下文信息

✅ **推荐**:

```rust
use anyhow::Context;

async fn fetch_user(id: u64) -> anyhow::Result<User> {
    let user = database
        .query("SELECT * FROM users WHERE id = ?", &[&id])
        .await
        .context(format!("获取用户失败, user_id: {}", id))?;
    
    Ok(user)
}
```

### 2. 使用自定义错误类型

✅ **推荐**:

```rust
#[derive(Debug, thiserror::Error)]
pub enum UserError {
    #[error("用户不存在: {0}")]
    NotFound(u64),
    
    #[error("用户已被禁用: {0}")]
    Disabled(u64),
    
    #[error("权限不足")]
    PermissionDenied,
}
```

### 3. 区分可恢复和不可恢复错误

✅ **推荐**:

```rust
match result {
    Ok(value) => Ok(value),
    Err(e) if e.is_recoverable() => {
        // 重试或降级
        fallback_operation().await
    }
    Err(e) => {
        // 不可恢复，直接返回
        return Err(e);
    }
}
```

---

## 测试最佳实践

### 1. 编写集成测试

✅ **推荐**:

```rust
#[tokio::test]
async fn test_circuit_breaker_opens_on_failures() {
    let cb = CircuitBreaker::new(config);
    
    // 模拟失败
    for _ in 0..5 {
        let _ = cb.call(|| async {
            Err::<(), _>(anyhow::anyhow!("失败"))
        }).await;
    }
    
    // 验证熔断器打开
    assert!(cb.is_open());
}
```

### 2. 使用 mock 进行隔离测试

✅ **推荐**:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use mockall::mock;
    
    mock! {
        ExternalService {}
        
        #[async_trait::async_trait]
        impl ExternalServiceTrait for ExternalService {
            async fn call(&self) -> anyhow::Result<String>;
        }
    }
    
    #[tokio::test]
    async fn test_with_mock() {
        let mut mock = MockExternalService::new();
        mock.expect_call()
            .returning(|| Ok("mock response".to_string()));
        
        let result = process_with_service(&mock).await;
        assert!(result.is_ok());
    }
}
```

---

## 总结

### 核心原则

1. **类型安全优先** - 充分利用 Rust 的类型系统
2. **错误处理完整** - 总是处理所有可能的错误情况
3. **性能与可维护性平衡** - 不过度优化
4. **文档完整** - 为公共 API 提供文档
5. **测试覆盖** - 关键路径必须有测试

### 避免的常见错误

❌ **不要**:

1. 在异步代码中使用 `std::sync::Mutex`
2. 在锁内进行长时间操作
3. 忽略错误（使用 `unwrap()` 或 `expect()`）
4. 在生产代码中使用 `println!`（使用 `tracing`）
5. 过度使用 `clone()`

### 推荐的开发流程

1. 设计 API（类型签名）
2. 编写测试用例
3. 实现功能
4. 添加错误处理
5. 编写文档
6. 性能优化（如果需要）

---

**版本**: 1.0  
**最后更新**: 2025-10-03  
**维护者**: c13_reliability 团队

有问题或建议？欢迎提交 Issue 或 PR！
