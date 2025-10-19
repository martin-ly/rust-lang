# C12 模型与架构: 主索引 (Master Index)

> **文档定位**: 软件架构模型学习路径总导航，涵盖并发、分布式、AI/ML等模型  
> **使用方式**: 作为学习起点，根据需求选择合适的架构模型和设计模式  
> **相关文档**: [README](./README.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | README → 基础概念 → 并发模型 | 入门指南 |
| **中级开发者** | 分布式模型 → 微服务架构 → 性能模型 | 实践案例 |
| **架构师** | 架构设计 → 模型分类 → 系统建模 | 架构设计 |
| **研究者** | 形式化模型 → 语义分析 → AI/ML模型 | 理论研究 |

### 📚 按主题导航

| 主题 | 文档入口 | 说明 |
|------|---------|------|
| **概览** | [OVERVIEW.md](./OVERVIEW.md) | 项目概述 |
| **综合指南** | [COMPREHENSIVE_USAGE_GUIDE.md](./COMPREHENSIVE_USAGE_GUIDE.md) | 完整使用指南 |
| **模型分类** | [MODEL_COMPREHENSIVE_TAXONOMY.md](./MODEL_COMPREHENSIVE_TAXONOMY.md) | 模型分类体系 |
| **架构设计** | [MODEL_ARCHITECTURE_DESIGN.md](./MODEL_ARCHITECTURE_DESIGN.md) | 架构设计指南 |

---

## 🏗️ 核心内容结构

### 第一部分：并发模型

#### 1. 并发编程模型

**文档**: [concurrency/](./concurrency/)

| 模型 | 说明 | 源码 |
|------|------|------|
| **Actor模型** | 消息传递并发 | `src/parallel_concurrent_models.rs` |
| **CSP模型** | 通信顺序进程 | - |
| **结构化并发** | 任务层次结构 | - |

**示例**: `examples/concurrency_*.rs`

#### 2. 异步模型

**文档**: [async/](./async/)

| 主题 | 说明 |
|------|------|
| **async/await** | 异步编程语法 |
| **Future机制** | 异步计算抽象 |
| **异步递归** | 递归异步函数 |
| **同步异步等价** | 语义等价性 |

**源码**: `src/async_models.rs`, `src/async_sync_models.rs`

### 第二部分：分布式模型

#### 3. 分布式系统

**文档**: [distributed/](./distributed/)

| 模型 | 说明 | 源码 |
|------|------|------|
| **一致性模型** | CAP理论、最终一致性 | `src/distributed_models.rs` |
| **共识算法** | Raft、Paxos | - |
| **分布式事务** | 2PC、Saga | - |

#### 4. 微服务架构

**文档**: [microservices/](./architecture/)

| 模式 | 说明 | 源码 |
|------|------|------|
| **服务发现** | 服务注册与发现 | `src/microservice_models.rs` |
| **API网关** | 统一入口 | - |
| **熔断器** | 故障隔离 | - |

**示例**: `examples/tower_*.rs`

### 第三部分：性能模型

#### 5. 性能分析

**文档**: [performance/](./performance/)

| 主题 | 说明 | 源码 |
|------|------|------|
| **排队论** | 队列模型 | `src/queueing_models.rs` |
| **背压控制** | 流量控制 | - |
| **性能指标** | 延迟、吞吐量 | `src/performance_models.rs` |

**示例**: `examples/async_backpressure_*.rs`

### 第四部分：AI/ML模型

#### 6. 机器学习集成

**文档**: [ml/](./ml/)

| 主题 | 说明 | 源码 |
|------|------|------|
| **深度学习** | PyTorch集成 | `src/ml_models.rs` |
| **计算机视觉** | 图像处理 | `src/computer_vision.rs` |
| **语言模型** | NLP应用 | `src/language_models.rs` |
| **现代ML** | Rust 1.90特性 | `src/modern_ml.rs` |

**示例**: `examples/machine_learning_examples.rs`, `examples/rust_190_modern_ml_demo.rs`

### 第五部分：形式化方法

#### 7. 形式化模型

**文档**: [formal/](./formal/)

| 主题 | 说明 | 源码 |
|------|------|------|
| **类型系统** | 类型理论 | `src/formal_models.rs` |
| **语义模型** | 操作语义、指称语义 | `src/semantic_models.rs` |
| **验证方法** | 模型检测、定理证明 | - |

**示例**: `examples/formal_methods_examples.rs`

---

## 📖 实践示例

### 可运行示例 (examples/)

| 示例 | 说明 | 运行命令 |
|------|------|----------|
| **综合展示** | 模型综合演示 | `cargo run --example comprehensive_model_showcase` |
| **并发模式** | Actor/CSP/结构化 | `cargo run --example concurrency_*` |
| **背压控制** | 异步背压 | `cargo run --example async_backpressure_demo` |
| **微服务** | Tower可靠性 | `cargo run --example tower_reliability` |
| **机器学习** | ML模型应用 | `cargo run --example machine_learning_examples` |
| **Rust 1.90特性** | 最新特性演示 | `cargo run --example model_rust_190_features_demo` |

---

## 🧪 测试与验证

### 测试套件 (tests/)

| 测试 | 说明 |
|------|------|
| **背压测试** | `backpressure_tests.rs` |
| **Loom测试** | `concurrency_loom.rs`, `loom_*.rs` |

### 运行测试

```bash
cargo test -p c12_model
cargo test --test loom_minimal
```

---

## 📚 学习路径

### 🚀 初学者路径 (1-2周)

1. [README](./README.md)
2. [OVERVIEW](./OVERVIEW.md)
3. 并发模型基础
4. 运行示例

### 🎓 中级路径 (3-4周)

1. 分布式模型
2. 微服务架构
3. 性能模型
4. 实战项目

### 🔬 高级路径 (5-8周)

1. 形式化方法
2. AI/ML集成
3. 架构设计
4. 系统优化

---

## 🎯 按场景导航

### 高并发系统

| 需求 | 推荐模型 | 文档 |
|------|---------|------|
| 消息传递 | Actor | concurrency/ |
| 背压控制 | 异步背压 | examples/ |
| 负载均衡 | 微服务 | architecture/ |

### 分布式系统

| 需求 | 推荐模型 | 文档 |
|------|---------|------|
| 一致性 | Raft/Paxos | distributed/ |
| 事务 | Saga | distributed/ |
| 服务治理 | 微服务 | architecture/ |

---

## 🔗 相关资源

### 项目文档

- [顶层 README](../README.md)
- [路线图](../ROADMAP.md)
- [里程碑](../MILESTONES.md)

### 工具与配置

- **Cargo.toml**: 依赖配置
- **book.toml**: mdBook配置

---

## 📊 项目统计

- **模型实现**: 20+ 模型
- **示例程序**: 15+ 示例
- **测试用例**: 完整测试套件
- **文档**: 40+ 文档

---

## 🆕 最新更新

### 2025-10-19

- ✅ 创建主索引
- ✅ 完善导航

### 2025年

- ✅ Rust 1.90特性集成
- ✅ AI/ML模型支持
- ✅ 形式化验证框架

---

**文档维护**: Rust 学习社区  
**文档版本**: v1.0  
**Rust 版本**: 1.90+
