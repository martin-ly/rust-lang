# C13 可靠性框架: 主索引 (Master Index)

> **文档定位**: 可靠性框架学习路径总导航，涵盖容错、分布式、微服务等  
> **使用方式**: 作为学习起点，根据需求选择合适的可靠性模式  
> **相关文档**: [README](../README.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | [README](../README.md) → [快速开始](../QUICK_START.md) → 熔断器 | 基础模式 |
| **中级开发者** | 分布式系统 → 微服务 → 可观测性 | 生产实践 |
| **架构师** | 架构设计 → 性能优化 → 容量规划 | 架构决策 |
| **研究者** | 形式化验证 → 算法分类 → 理论分析 | 学术研究 |

---

## 🏗️ 核心内容结构

### 第一部分：容错机制

#### 1. 熔断器与限流

| 模式 | 说明 | 源码 |
|------|------|------|
| **熔断器** | 五状态熔断器 | `src/fault_tolerance/circuit_breaker.rs` |
| **限流器** | 令牌桶、漏桶等 | `src/fault_tolerance/rate_limiter.rs` |
| **重试** | 指数退避 | `src/fault_tolerance/retry.rs` |
| **超时** | 超时控制 | `src/fault_tolerance/timeout.rs` |

### 第二部分：分布式系统

#### 2. 共识与事务

| 功能 | 说明 | 源码 |
|------|------|------|
| **Raft** | 共识算法 | `src/distributed_systems/raft.rs` |
| **分布式事务** | 2PC/Saga | `src/distributed_systems/transactions.rs` |
| **一致性哈希** | 负载均衡 | `src/distributed_systems/consistent_hashing.rs` |

### 第三部分：并发模型

#### 3. 并发抽象

| 模型 | 说明 | 源码 |
|------|------|------|
| **Actor** | 消息传递 | `src/concurrency_models/actor.rs` |
| **CSP** | Channel通信 | `src/concurrency_models/csp.rs` |
| **STM** | 事务内存 | `src/concurrency_models/stm.rs` |

### 第四部分：微服务

#### 4. 服务治理

| 功能 | 说明 | 源码 |
|------|------|------|
| **服务发现** | 注册与发现 | `src/microservices/service_discovery.rs` |
| **API网关** | 统一入口 | `src/microservices/api_gateway.rs` |
| **负载均衡** | 多种策略 | `src/microservices/load_balancer.rs` |

### 第五部分：可观测性

#### 5. 监控与追踪

| 功能 | 说明 | 源码 |
|------|------|------|
| **指标收集** | Metrics | `src/observability/metrics.rs` |
| **分布式追踪** | Tracing | `src/observability/tracer.rs` |
| **日志聚合** | Logging | `src/observability/logger.rs` |

---

## 📖 实践示例

### 可运行示例 (examples/)

| 示例 | 说明 | 运行命令 |
|------|------|----------|
| **基础使用** | `reliability_basic_usage.rs` | `cargo run --example reliability_basic_usage` |
| **高级功能** | `advanced_usage.rs` | `cargo run --example advanced_usage` |
| **分布式微服务** | `distributed_microservices_showcase.rs` | `cargo run --example distributed_microservices_showcase` |
| **运行时环境** | `runtime_environment_example.rs` | `cargo run --example runtime_environment_example` |
| **Rust 1.90特性** | `rust_190_features_demo.rs` | `cargo run --example rust_190_features_demo` |

---

## 📚 学习路径

### 🚀 初学者路径 (1周)

1. [README](../README.md)
2. [快速开始](../QUICK_START.md)
3. 熔断器示例
4. 限流器示例

### 🎓 中级路径 (2-3周)

1. 分布式系统
2. 微服务架构
3. 可观测性
4. 性能优化

### 🔬 高级路径 (4周+)

1. 形式化验证
2. 算法分类
3. 架构设计
4. 生产部署

---

## 🎯 按场景导航

### 高可用系统

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 故障隔离 | 熔断器 | `src/fault_tolerance/` |
| 流量控制 | 限流器 | `src/fault_tolerance/` |
| 重试逻辑 | 指数退避 | `src/fault_tolerance/` |

### 分布式系统

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 一致性 | Raft | `src/distributed_systems/` |
| 事务 | 2PC/Saga | `src/distributed_systems/` |
| 负载均衡 | 一致性哈希 | `src/distributed_systems/` |

### 微服务架构

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 服务发现 | 注册中心 | `src/microservices/` |
| API网关 | 统一入口 | `src/microservices/` |
| 监控 | 指标收集 | `src/observability/` |

---

## 🔗 相关资源

### 项目文档

- [顶层 README](../README.md)
- [架构文档](./ARCHITECTURE.md)
- [最佳实践](./BEST_PRACTICES.md)
- [API参考](./api_reference.md)

### 分析文档

- [算法分类](./COMPREHENSIVE_ALGORITHM_MODEL_TAXONOMY.md)
- [架构决策](./ARCHITECTURE_DECISIONS.md)
- [运行时环境](../RUNTIME_ENVIRONMENTS_GUIDE.md)

---

## 📊 项目统计

- **容错模式**: 10+ 模式
- **分布式算法**: 5+ 算法
- **并发模型**: 3 种模型
- **示例程序**: 10+ 示例
- **测试用例**: 完整测试套件

---

## 🆕 最新更新

### 2025-10-19

- ✅ 创建主索引
- ✅ 完善导航

### 2025年

- ✅ Rust 1.90特性集成
- ✅ 分布式系统完善
- ✅ 微服务架构支持
- ✅ 运行时环境分类

---

**文档维护**: Rust 学习社区  
**文档版本**: v1.0  
**Rust 版本**: 1.90+
