# API 文档 (API Documentation)

> **目录定位**: C13 可靠性框架 API 参考文档  
> **适用人群**: 所有开发者  
> **相关文档**: [主索引](../00_MASTER_INDEX.md) | [使用指南](../guides/)

**最后更新**: 2025-10-19  
**文档类型**: 🔌 API参考

---

## 📚 API 文档

### 完整 API 参考

- **[API 参考手册](reference.md)** - 完整的 API 文档
  - 所有公共接口
  - 函数签名
  - 参数说明
  - 返回值
  - 使用示例

---

## 🎯 按模块浏览 API

### 容错机制 (Fault Tolerance)

```rust
use c13_reliability::fault_tolerance::{
    CircuitBreaker,      // 熔断器
    RetryPolicy,         // 重试策略
    Timeout,             // 超时控制
    Bulkhead,           // 舱壁隔离
    RateLimiter,        // 限流器
};
```

**主要接口**:
- `CircuitBreaker::new()` - 创建熔断器
- `CircuitBreaker::call()` - 使用熔断器保护调用
- `RetryPolicy::exponential_backoff()` - 指数退避重试
- `RateLimiter::try_acquire()` - 尝试获取令牌

### 分布式系统 (Distributed Systems)

```rust
use c13_reliability::distributed_systems::{
    RaftNode,              // Raft共识算法
    DistributedLock,       // 分布式锁
    ConsistentHash,        // 一致性哈希
    DistributedTransaction,// 分布式事务
};
```

### 并发模型 (Concurrency Models)

```rust
use c13_reliability::concurrency_models::{
    ActorSystem,           // Actor模型
    Channel,               // CSP模型
    STM,                   // 软件事务内存
    ForkJoinPool,          // Fork-Join框架
};
```

### 微服务架构 (Microservices)

```rust
use c13_reliability::microservices::{
    ServiceRegistry,       // 服务注册与发现
    ApiGateway,           // API网关
    LoadBalancer,         // 负载均衡器
    ConfigCenter,         // 配置中心
};
```

### 可观测性 (Observability)

```rust
use c13_reliability::observability::{
    MetricsAggregator,    // 指标聚合
    LogCorrelator,        // 日志关联
    Tracer,               // 分布式追踪
    AlertManager,         // 告警管理
};
```

### 性能测试 (Benchmarking)

```rust
use c13_reliability::benchmarking::{
    LoadGenerator,        // 负载生成器
    LatencyAnalyzer,      // 延迟分析
    ThroughputMeter,      // 吞吐量测量
};
```

---

## 📖 快速查找

### 按功能查找

- **创建和初始化** → 各模块的 `new()` 方法
- **执行操作** → `call()`, `execute()`, `run()` 等
- **配置和设置** → `Config` 结构体和 Builder 模式
- **查询状态** → `status()`, `metrics()`, `stats()` 等

### 常用模式

**Builder 模式**:
```rust
let config = ConfigBuilder::new()
    .option1(value1)
    .option2(value2)
    .build()?;
```

**异步操作**:
```rust
let result = component.async_operation().await?;
```

**错误处理**:
```rust
use c13_reliability::error::UnifiedError;

fn my_function() -> Result<(), UnifiedError> {
    // ...
}
```

---

## 🔗 相关资源

- [使用指南](../guides/usage-guide.md) - 如何使用API
- [代码示例](../../examples/) - 实际使用示例
- [最佳实践](../guides/best-practices.md) - API使用最佳实践
- [常见问题](../reference/FAQ.md) - API相关问题

---

## 🛠️ 生成文档

生成本地 API 文档：

```bash
cargo doc --open --no-deps
```

---

**文档维护**: C13 开发团队  
**最后审核**: 2025-10-19

