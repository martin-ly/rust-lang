# 🚀 快速开始指南


## 📊 目录

- [� 快速开始指南](#-快速开始指南)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [📦 安装](#-安装)
    - [添加依赖](#添加依赖)
  - [⚡ 5个常见场景](#-5个常见场景)
    - [1. 熔断器 - 防止级联故障](#1-熔断器---防止级联故障)
    - [2. 限流器 - 控制请求速率](#2-限流器---控制请求速率)
    - [3. 指标收集 - 监控系统状态](#3-指标收集---监控系统状态)
    - [4. 分布式锁 - 协调分布式操作](#4-分布式锁---协调分布式操作)
    - [5. 性能测试 - 压力测试你的服务](#5-性能测试---压力测试你的服务)
  - [🎨 组合使用](#-组合使用)
    - [完整的服务保护方案](#完整的服务保护方案)
  - [📚 更多资源](#-更多资源)
    - [文档](#文档)
    - [代码示例](#代码示例)
    - [主要模块](#主要模块)
  - [🎯 常见模式速查](#-常见模式速查)
    - [重试策略](#重试策略)
    - [事件总线](#事件总线)
    - [服务发现](#服务发现)
    - [一致性哈希](#一致性哈希)
  - [⚡ 性能提示](#-性能提示)
  - [🐛 故障排查](#-故障排查)
    - [编译错误](#编译错误)
    - [运行时错误](#运行时错误)
  - [💬 获取帮助](#-获取帮助)
  - [🎉 下一步](#-下一步)


5分钟快速上手 c13_reliability 框架！

---

## 📋 目录

- [🚀 快速开始指南](#-快速开始指南)
  - [� 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [📦 安装](#-安装)
    - [添加依赖](#添加依赖)
  - [⚡ 5个常见场景](#-5个常见场景)
    - [1. 熔断器 - 防止级联故障](#1-熔断器---防止级联故障)
    - [2. 限流器 - 控制请求速率](#2-限流器---控制请求速率)
    - [3. 指标收集 - 监控系统状态](#3-指标收集---监控系统状态)
    - [4. 分布式锁 - 协调分布式操作](#4-分布式锁---协调分布式操作)
    - [5. 性能测试 - 压力测试你的服务](#5-性能测试---压力测试你的服务)
  - [🎨 组合使用](#-组合使用)
    - [完整的服务保护方案](#完整的服务保护方案)
  - [📚 更多资源](#-更多资源)
    - [文档](#文档)
    - [代码示例](#代码示例)
    - [主要模块](#主要模块)
  - [🎯 常见模式速查](#-常见模式速查)
    - [重试策略](#重试策略)
    - [事件总线](#事件总线)
    - [服务发现](#服务发现)
    - [一致性哈希](#一致性哈希)
  - [⚡ 性能提示](#-性能提示)
  - [🐛 故障排查](#-故障排查)
    - [编译错误](#编译错误)
    - [运行时错误](#运行时错误)
  - [💬 获取帮助](#-获取帮助)
  - [🎉 下一步](#-下一步)

## 📦 安装

### 添加依赖

```toml
[dependencies]
c13_reliability = "0.1.0"
tokio = { version = "1", features = ["full"] }
anyhow = "1.0"
```

---

## ⚡ 5个常见场景

### 1. 熔断器 - 防止级联故障

```rust
use c13_reliability::fault_tolerance::{CircuitBreaker, CircuitBreakerConfig};
use std::time::Duration;
use std::sync::Arc;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let config = CircuitBreakerConfig {
        failure_threshold: 5,
        success_threshold: 2,
        recovery_timeout: Duration::from_secs(10),
        half_open_max_requests: 3,
        sliding_window_size: Duration::from_secs(60),
        minimum_requests: 10,
    };
    
    let cb = Arc::new(CircuitBreaker::new(config));
    
    // 使用熔断器保护调用
    let result = cb.call(|| async {
        // 你的业务逻辑
        external_api_call().await
    }).await?;
    
    Ok(())
}

async fn external_api_call() -> anyhow::Result<String> {
    Ok("success".to_string())
}
```

### 2. 限流器 - 控制请求速率

```rust
use c13_reliability::fault_tolerance::rate_limiting::{TokenBucket, RateLimiter};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 每秒100个请求
    let limiter = TokenBucket::new(100, Duration::from_secs(1));
    
    // 处理请求
    if limiter.try_acquire().await {
        println!("请求通过");
        // 处理业务逻辑
    } else {
        println!("请求被限流");
    }
    
    Ok(())
}
```

### 3. 指标收集 - 监控系统状态

```rust
use c13_reliability::observability::metrics_aggregation::MetricsAggregator;
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let aggregator = MetricsAggregator::new();
    
    // 记录不同类型的指标
    aggregator.record_counter("api.requests", 1.0).await;
    aggregator.record_histogram("api.latency_ms", 42.0).await;
    aggregator.record_gauge("cpu_usage", 65.5).await;
    
    // 获取统计信息
    let stats = aggregator
        .get_histogram_stats("api.latency_ms", Duration::from_secs(60))
        .await?;
    
    println!("P95延迟: {:.2}ms", stats.p95);
    println!("P99延迟: {:.2}ms", stats.p99);
    
    Ok(())
}
```

### 4. 分布式锁 - 协调分布式操作

```rust
use c13_reliability::distributed_systems::distributed_lock::DistributedLock;
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let lock = DistributedLock::new("my_resource".to_string());
    
    // 获取锁
    if let Some(guard) = lock.try_lock(Duration::from_secs(5)).await? {
        println!("获得锁，执行关键操作");
        // 执行需要互斥的操作
        critical_operation().await?;
        // guard被drop时自动释放锁
    } else {
        println!("无法获取锁");
    }
    
    Ok(())
}

async fn critical_operation() -> anyhow::Result<()> {
    Ok(())
}
```

### 5. 性能测试 - 压力测试你的服务

```rust
use c13_reliability::benchmarking::{
    LoadGenerator, LoadConfig, LoadPattern, LatencyAnalyzer
};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 配置负载生成器
    let config = LoadConfig {
        initial_rate: 10.0,
        max_rate: 100.0,
        duration: Duration::from_secs(30),
        pattern: LoadPattern::Linear,
        max_concurrency: 50,
    };
    
    let generator = LoadGenerator::new(config);
    
    // 运行负载测试
    let results = generator
        .generate(|| async {
            // 你要测试的操作
            test_operation().await
        })
        .await?;
    
    // 分析结果
    println!("总请求: {}", results.total_requests);
    println!("成功率: {:.2}%", results.success_rate() * 100.0);
    println!("吞吐量: {:.2} req/s", results.throughput());
    println!("平均延迟: {:?}", results.average_latency());
    
    Ok(())
}

async fn test_operation() -> anyhow::Result<()> {
    tokio::time::sleep(Duration::from_millis(10)).await;
    Ok(())
}
```

---

## 🎨 组合使用

### 完整的服务保护方案

```rust
use c13_reliability::{
    fault_tolerance::{CircuitBreaker, CircuitBreakerConfig},
    fault_tolerance::rate_limiting::{TokenBucket, RateLimiter},
    observability::metrics_aggregation::MetricsAggregator,
};
use std::sync::Arc;
use std::time::{Duration, Instant};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 1. 创建熔断器
    let cb_config = CircuitBreakerConfig {
        failure_threshold: 5,
        success_threshold: 2,
        recovery_timeout: Duration::from_secs(30),
        half_open_max_requests: 3,
        sliding_window_size: Duration::from_secs(60),
        minimum_requests: 10,
    };
    let circuit_breaker = Arc::new(CircuitBreaker::new(cb_config));
    
    // 2. 创建限流器
    let rate_limiter = Arc::new(TokenBucket::new(100, Duration::from_secs(1)));
    
    // 3. 创建指标收集器
    let metrics = Arc::new(MetricsAggregator::new());
    
    // 处理请求的完整流程
    for i in 1..=10 {
        // 限流检查
        if !rate_limiter.try_acquire().await {
            println!("请求 {} 被限流", i);
            metrics.record_counter("requests.rate_limited", 1.0).await;
            continue;
        }
        
        // 使用熔断器保护
        let start = Instant::now();
        let result = circuit_breaker.call(|| async {
            // 实际的业务逻辑
            call_external_service().await
        }).await;
        
        let latency = start.elapsed();
        
        // 记录指标
        match result {
            Ok(_) => {
                metrics.record_counter("requests.success", 1.0).await;
                metrics.record_histogram("requests.latency_ms", 
                    latency.as_millis() as f64).await;
                println!("请求 {} 成功", i);
            }
            Err(e) => {
                metrics.record_counter("requests.failed", 1.0).await;
                println!("请求 {} 失败: {}", i, e);
            }
        }
    }
    
    // 查看统计
    let stats = metrics
        .get_histogram_stats("requests.latency_ms", Duration::from_secs(60))
        .await?;
    println!("\n延迟统计:");
    println!("  P50: {:.2}ms", stats.p50);
    println!("  P95: {:.2}ms", stats.p95);
    println!("  P99: {:.2}ms", stats.p99);
    
    Ok(())
}

async fn call_external_service() -> anyhow::Result<String> {
    tokio::time::sleep(Duration::from_millis(50)).await;
    Ok("success".to_string())
}
```

---

## 📚 更多资源

### 文档

- [完整README](README.md) - 项目介绍和详细说明
- [最佳实践](docs/BEST_PRACTICES.md) - 8个主题的最佳实践
- [架构决策](docs/ARCHITECTURE_DECISIONS.md) - 12个ADR
- [API参考](docs/api_reference.md) - 完整的API文档

### 代码示例

查看 `examples/` 目录获取更多示例。

### 主要模块

```rust
use c13_reliability::prelude::*;  // 常用类型
use c13_reliability::{
    fault_tolerance,        // 容错机制
    distributed_systems,    // 分布式系统
    concurrency_models,     // 并发模型
    microservices,          // 微服务架构
    observability,          // 可观测性
    benchmarking,           // 性能测试
    design_patterns,        // 设计模式
};
```

---

## 🎯 常见模式速查

### 重试策略

```rust
use c13_reliability::fault_tolerance::RetryPolicy;

// 指数退避重试
let retry = RetryPolicy::exponential_backoff(3, Duration::from_millis(100));
```

### 事件总线

```rust
use c13_reliability::design_patterns::observer::{EventBus, Event};

let bus = EventBus::new();
let event = Event { /* ... */ };
bus.publish(event).await?;
```

### 服务发现

```rust
use c13_reliability::microservices::service_discovery::ServiceRegistry;

let registry = ServiceRegistry::new();
registry.register("my-service", "http://localhost:8080", metadata).await?;
let services = registry.discover("my-service").await?;
```

### 一致性哈希

```rust
use c13_reliability::distributed_systems::consistent_hash::ConsistentHash;

let mut ch = ConsistentHash::new(150);
ch.add_node("server1");
let server = ch.get_node("key");
```

---

## ⚡ 性能提示

1. **使用Arc共享状态** - 在异步代码中
2. **合理设置阈值** - 熔断器和限流器
3. **定期清理数据** - 指标和日志
4. **避免锁内异步** - 先异步再加锁
5. **批量处理** - 提高吞吐量

---

## 🐛 故障排查

### 编译错误

```bash
# 清理并重新构建
cargo clean
cargo build
```

### 运行时错误

- 检查异步runtime是否正确初始化
- 确认所有Arc引用正确传递
- 查看tracing日志输出

---

## 💬 获取帮助

- 查看 [README](README.md)
- 阅读 [最佳实践](docs/BEST_PRACTICES.md)
- 查看测试用例作为示例
- GitHub Issues (待添加)

---

## 🎉 下一步

1. 选择一个场景试试
2. 查看完整文档
3. 阅读最佳实践
4. 根据需求定制

**开始构建可靠的Rust应用吧！** 🚀

---

**版本**: 0.1.0  
**最后更新**: 2025年10月4日  
**License**: MIT
