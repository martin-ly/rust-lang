# C09 设计模式: 主索引 (Master Index)

> **文档定位**: 设计模式学习路径总导航，快速定位所有学习资源  
> **使用方式**: 作为学习起点，根据需求选择合适的文档和代码模块  
> **相关文档**: [README](./README.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)


## 📊 目录

- [C09 设计模式: 主索引 (Master Index)](#c09-设计模式-主索引-master-index)
  - [📊 目录](#-目录)
  - [📋 快速导航](#-快速导航)
    - [🎯 按角色导航](#-按角色导航)
    - [📚 按类型导航](#-按类型导航)
  - [🏗️ 核心内容结构](#️-核心内容结构)
    - [第一部分：经典设计模式 (GoF)](#第一部分经典设计模式-gof)
      - [1. 创建型模式 (Creational Patterns)](#1-创建型模式-creational-patterns)
      - [2. 结构型模式 (Structural Patterns)](#2-结构型模式-structural-patterns)
      - [3. 行为型模式 (Behavioral Patterns)](#3-行为型模式-behavioral-patterns)
    - [第二部分：并发与异步模式](#第二部分并发与异步模式)
      - [4. 并发模式 (Concurrency Patterns)](#4-并发模式-concurrency-patterns)
      - [5. 并行模式 (Parallel Patterns)](#5-并行模式-parallel-patterns)
    - [第三部分：形式化理论与分析](#第三部分形式化理论与分析)
      - [6. 形式化文档](#6-形式化文档)
      - [7. 形式化验证代码](#7-形式化验证代码)
    - [第四部分：领域专题](#第四部分领域专题)
      - [8. 领域特定模式](#8-领域特定模式)
    - [第五部分：Rust 特性集成](#第五部分rust-特性集成)
      - [9. Rust 1.90+ 特性](#9-rust-190-特性)
  - [📖 实践示例](#-实践示例)
    - [可运行示例 (examples/)](#可运行示例-examples)
    - [性能基准测试 (benches/)](#性能基准测试-benches)
  - [🧪 测试与验证](#-测试与验证)
    - [测试套件 (tests/)](#测试套件-tests)
    - [运行测试](#运行测试)
  - [📚 学习路径](#-学习路径)
    - [🚀 初学者路径 (1-2周)](#-初学者路径-1-2周)
    - [🎓 中级路径 (3-4周)](#-中级路径-3-4周)
    - [🔬 高级路径 (5-8周)](#-高级路径-5-8周)
    - [🏆 专家路径 (持续学习)](#-专家路径-持续学习)
  - [🎯 按场景导航](#-按场景导航)
    - [性能优化场景](#性能优化场景)
    - [架构设计场景](#架构设计场景)
    - [并发编程场景](#并发编程场景)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [工具与配置](#工具与配置)
  - [📊 项目统计](#-项目统计)
    - [代码规模](#代码规模)
    - [文档规模](#文档规模)
  - [🆕 最新更新](#-最新更新)
    - [2025-10-19 - 重大更新 🎉](#2025-10-19---重大更新-)
    - [2025年9月](#2025年9月)
  - [📞 获取帮助](#-获取帮助)
    - [问题解决](#问题解决)
    - [社区支持](#社区支持)


**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+ (Edition 2024)  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | [README](./README.md) → [OVERVIEW](./OVERVIEW.md) → 创建型模式 | 基础概念、示例代码 |
| **中级开发者** | 行为型模式 → 并发模式 → 最佳实践 | 实战案例、性能优化 |
| **架构师** | [综合指南](./COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md) → 形式化理论 | 架构设计、模式组合 |
| **研究者** | 形式化文档 → 等价性分析 → 性能基准 | 理论证明、语义模型 |

### 📚 按类型导航

| 类型 | 文档/目录 | 说明 |
|------|----------|------|
| **入门指南** | [README](./README.md) | 项目概述和快速开始 |
| **概览** | [OVERVIEW](./OVERVIEW.md) | 文档结构和阅读路径 |
| **综合指南** | [COMPREHENSIVE_DESIGN_PATTERNS_GUIDE](./COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md) | 完整的模式理论与实践 |
| **知识图谱** 🆕 | [KNOWLEDGE_GRAPH](./KNOWLEDGE_GRAPH.md) | 模式关系网络与组合策略 |
| **多维矩阵** 🆕 | [MULTIDIMENSIONAL_MATRIX_COMPARISON](./MULTIDIMENSIONAL_MATRIX_COMPARISON.md) | 7维度性能对比分析 |
| **思维导图** 🆕 | [MIND_MAP](./MIND_MAP.md) | 可视化学习路径与决策树 |
| **Rust 1.90示例** 🆕 | [RUST_190_EXAMPLES](./RUST_190_EXAMPLES.md) | 最新特性完整示例集 |
| **FAQ** | [FAQ](./FAQ.md) | 常见问题解答 |
| **术语表** | [Glossary](./Glossary.md) | 核心概念快速参考 |

---

## 🏗️ 核心内容结构

### 第一部分：经典设计模式 (GoF)

#### 1. 创建型模式 (Creational Patterns)

| 模式 | 源码位置 | 说明 | 特点 |
|------|---------|------|------|
| **单例模式** | [`src/creational/singleton/`](../src/creational/singleton/) | 全局唯一实例 | `OnceLock`, 线程安全 |
| **工厂方法** | [`src/creational/factory_method/`](../src/creational/factory_method/) | 对象创建接口 | Trait + 泛型 |
| **抽象工厂** | [`src/creational/abstract_factory/`](../src/creational/abstract_factory/) | 产品族创建 | 枚举 + Trait |
| **建造者模式** | [`src/creational/builder/`](../src/creational/builder/) | 复杂对象构建 | Typestate 模式 |
| **原型模式** | [`src/creational/prototype/`](../src/creational/prototype/) | 对象克隆 | Clone trait |
| **对象池** | [`src/creational/object_pool/`](../src/creational/object_pool/) | 对象复用 | 性能优化 |
| **静态创建方法** | [`src/creational/static_creation_method/`](../src/creational/static_creation_method/) | 命名构造器 | 语义清晰 |

#### 2. 结构型模式 (Structural Patterns)

| 模式 | 源码位置 | 说明 | 特点 |
|------|---------|------|------|
| **适配器模式** | [`src/structural/adapter/`](../src/structural/adapter/) | 接口转换 | Trait 适配 |
| **桥接模式** | [`src/structural/bridge/`](../src/structural/bridge/) | 抽象与实现分离 | 泛型 + Trait |
| **组合模式** | [`src/structural/composite/`](../src/structural/composite/) | 树形结构 | 递归组合 |
| **装饰器模式** | [`src/structural/decorator/`](../src/structural/decorator/) | 动态功能扩展 | 零成本包装 |
| **外观模式** | [`src/structural/facade/`](../src/structural/facade/) | 简化接口 | 模块化设计 |
| **享元模式** | [`src/structural/flyweight/`](../src/structural/flyweight/) | 对象共享 | 内存优化 |
| **代理模式** | [`src/structural/proxy/`](../src/structural/proxy/) | 访问控制 | 智能指针 |

#### 3. 行为型模式 (Behavioral Patterns)

| 模式 | 源码位置 | 说明 | 特点 |
|------|---------|------|------|
| **责任链模式** | [`src/behavioral/chain_of_responsibility/`](../src/behavioral/chain_of_responsibility/) | 请求链式处理 | let-else |
| **命令模式** | [`src/behavioral/command/`](../src/behavioral/command/) | 请求封装 | 闭包实现 |
| **解释器模式** | [`src/behavioral/interpreter/`](../src/behavioral/interpreter/) | 语言解释 | 递归下降 |
| **迭代器模式** | [`src/behavioral/iterator/`](../src/behavioral/iterator/) | 顺序访问 | Iterator trait |
| **中介者模式** | [`src/behavioral/mediator/`](../src/behavioral/mediator/) | 对象交互 | 集中控制 |
| **备忘录模式** | [`src/behavioral/memento/`](../src/behavioral/memento/) | 状态保存 | 封装私有状态 |
| **观察者模式** | [`src/behavioral/observer/`](../src/behavioral/observer/) | 事件通知 | GATs, 零拷贝 |
| **状态模式** | [`src/behavioral/state/`](../src/behavioral/state/) | 状态转换 | 类型状态 |
| **策略模式** | [`src/behavioral/strategy/`](../src/behavioral/strategy/) | 算法切换 | 编译时/运行时多态 |
| **模板方法** | [`src/behavioral/template_method/`](../src/behavioral/template_method/) | 算法骨架 | Trait 默认方法 |
| **访问者模式** | [`src/behavioral/visitor/`](../src/behavioral/visitor/) | 操作分离 | 双重分派 |

### 第二部分：并发与异步模式

#### 4. 并发模式 (Concurrency Patterns)

| 模块 | 源码位置 | 说明 |
|------|---------|------|
| **异步模式** | [`src/concurrency/asynchronous/`](../src/concurrency/asynchronous/) | Future/async/await |
| **原生 async trait** | [`src/concurrency/asynchronous/native_async_trait/`](../src/concurrency/asynchronous/native_async_trait/) | Rust 1.90+ 特性 |
| **消息传递** | [`src/concurrency/message_passing/`](../src/concurrency/message_passing/) | Channel 通信 |
| **生产者-消费者** | [`src/concurrency/producer_consumer/`](../src/concurrency/producer_consumer/) | 队列模式 |
| **读写者** | [`src/concurrency/reader_writer/`](../src/concurrency/reader_writer/) | RwLock 模式 |
| **共享状态** | [`src/concurrency/shared_state/`](../src/concurrency/shared_state/) | Mutex/Arc |
| **任务调度** | [`src/concurrency/task_scheduling/`](../src/concurrency/task_scheduling/) | 调度策略 |

#### 5. 并行模式 (Parallel Patterns)

| 模块 | 源码位置 | 说明 |
|------|---------|------|
| **数据并行** | [`src/parallel/data_parrallelism/`](../src/parallel/data_parrallelism/) | Rayon 并行 |
| **并行归约** | [`src/parallel/parallel_reduction/`](../src/parallel/parallel_reduction/) | 规约操作 |
| **流水线** | [`src/parallel/pipeline/`](../src/parallel/pipeline/) | 流水线处理 |
| **任务分解** | [`src/parallel/task_decomposition/`](../src/parallel/task_decomposition/) | 分治策略 |
| **工作窃取** | [`src/parallel/work_stealing/`](../src/parallel/work_stealing/) | 负载均衡 |

### 第三部分：形式化理论与分析

#### 6. 形式化文档

| 文档 | 主题 | 核心内容 |
|------|------|---------|
| [异步vs同步等价性](./ASYNC_SYNC_EQUIVALENCE_THEORY.md) | 语义等价 | CPS变换, Monad, 控制流 |
| [Actor与Reactor模式](./ACTOR_REACTOR_PATTERNS.md) | 并发模型 | 消息传递, 事件驱动 |
| [CSP vs Async分析](./CSP_VS_ASYNC_ANALYSIS.md) | 模型对比 | Golang vs Rust |
| [异步递归分析](./ASYNC_RECURSION_ANALYSIS.md) | 递归优化 | Box::pin, 尾递归 |

#### 7. 形式化验证代码

| 模块 | 说明 |
|------|------|
| [`src/formal_verification_examples.rs`](../src/formal_verification_examples.rs) | 类型级状态机、终止性证明 |

### 第四部分：领域专题

#### 8. 领域特定模式

| 模块 | 源码位置 | 说明 |
|------|---------|------|
| **Web框架模式** | [`src/web_framework_patterns.rs`](../src/web_framework_patterns.rs) | HTTP, 中间件 |
| **数据库模式** | [`src/database_patterns.rs`](../src/database_patterns.rs) | 连接池, 事务 |
| **操作系统模式** | [`src/os_patterns.rs`](../src/os_patterns.rs) | 进程, 线程 |
| **游戏引擎模式** | [`src/game_engine_patterns.rs`](../src/game_engine_patterns.rs) | 实体组件系统 |

### 第五部分：Rust 特性集成

#### 9. Rust 1.90+ 特性

| 特性 | 源码位置 | 说明 |
|------|---------|------|
| **RPITIT** | [`src/rust_190_features.rs`](../src/rust_190_features.rs) | Trait 方法返回 impl Trait |
| **dyn upcasting** | [`src/rust_190_features.rs`](../src/rust_190_features.rs) | trait 对象上转型 |
| **let-else** | 多处使用 | 早退模式 |
| **OnceLock** | [`src/error_handling.rs`](../src/error_handling.rs) | 全局初始化 |

---

## 📖 实践示例

### 可运行示例 (examples/)

| 示例 | 文件 | 说明 | 运行命令 |
|------|------|------|----------|
| **事件总线** | [`event_bus_demo.rs`](../examples/event_bus_demo.rs) | 异步事件、背压控制 | `cargo run --example event_bus_demo` |
| **async trait** | [`async_trait_demo.rs`](../examples/async_trait_demo.rs) | 原生 async trait | `cargo run --example async_trait_demo` |
| **GATs观察者** | [`gats_observer_demo.rs`](../examples/gats_observer_demo.rs) | GATs 借用视图 | `cargo run --example gats_observer_demo` |
| **流水线迭代器** | [`pipeline_iter_demo.rs`](../examples/pipeline_iter_demo.rs) | RPIT + Send | `cargo run --example pipeline_iter_demo` |
| **追踪链** | [`tracing_chain.rs`](../examples/tracing_chain.rs) | 责任链 + 追踪 | `cargo run --example tracing_chain` |

### 性能基准测试 (benches/)

| 基准 | 文件 | 说明 | 运行命令 |
|------|------|------|----------|
| **异步GATs基准** | [`async_gats_benches.rs`](../benches/async_gats_benches.rs) | 异步事件总线性能 | `cargo bench` |
| **模式基准** | [`pattern_benchmarks.rs`](../benches/pattern_benchmarks.rs) | 各种模式性能对比 | `cargo bench` |
| **场景基准** | [`pattern_scenarios.rs`](../benches/pattern_scenarios.rs) | 实际场景性能 | `cargo bench` |
| **性能基准** | [`performance_benchmarks.rs`](../benches/performance_benchmarks.rs) | 综合性能测试 | `cargo bench` |

---

## 🧪 测试与验证

### 测试套件 (tests/)

| 测试 | 文件 | 说明 |
|------|------|------|
| **执行模型测试** | [`execution_model_tests.rs`](../tests/execution_model_tests.rs) | 同步/异步执行 |
| **事件单例集成** | [`integration_events_singleton.rs`](../tests/integration_events_singleton.rs) | 跨模式集成 |
| **集成测试** | [`integration_tests.rs`](../tests/integration_tests.rs) | 完整功能测试 |

### 运行测试

```bash
# 运行所有测试
cargo test -p c09_design_pattern

# 运行特定测试
cargo test -p c09_design_pattern --test integration_tests

# 运行带 Tokio 特性的测试
cargo test -p c09_design_pattern --features tokio-bench

# 运行性能基准
cargo bench -p c09_design_pattern
```

---

## 📚 学习路径

### 🚀 初学者路径 (1-2周)

1. **起步**: [README](./README.md) → [OVERVIEW](./OVERVIEW.md)
2. **基础概念**: 创建型模式 (单例、工厂、建造者)
3. **实践**: 运行 examples/ 下的基础示例
4. **巩固**: 完成 FAQ 中的练习题

**推荐阅读顺序**:

- 创建型: 单例 → 工厂 → 建造者 → 原型
- 结构型: 适配器 → 装饰器 → 代理

### 🎓 中级路径 (3-4周)

1. **深入行为型**: 观察者、策略、命令、状态
2. **并发基础**: 消息传递、共享状态、生产者-消费者
3. **异步编程**: Future/async/await 模式
4. **性能优化**: 运行基准测试，理解性能权衡

**推荐阅读顺序**:

- 行为型: 观察者 → 策略 → 命令 → 状态 → 责任链
- 并发: 消息传递 → 共享状态 → 异步模式

### 🔬 高级路径 (5-8周)

1. **形式化理论**: [异步vs同步等价性](./ASYNC_SYNC_EQUIVALENCE_THEORY.md)
2. **并发模型**: [Actor与Reactor](./ACTOR_REACTOR_PATTERNS.md)
3. **模型对比**: [CSP vs Async](./CSP_VS_ASYNC_ANALYSIS.md)
4. **深度优化**: [异步递归](./ASYNC_RECURSION_ANALYSIS.md)
5. **实战项目**: 应用到实际项目中

**推荐阅读顺序**:

- 理论: 等价性分析 → Actor/Reactor → CSP对比
- 实践: 形式化验证 → 性能优化 → 架构设计

### 🏆 专家路径 (持续学习)

1. **深度研究**: [综合指南](./COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md)
2. **源码分析**: 阅读并分析所有模式源码
3. **贡献代码**: 改进现有实现或添加新模式
4. **分享经验**: 撰写技术博客或教程

---

## 🎯 按场景导航

### 性能优化场景

| 需求 | 推荐模式 | 文档 |
|------|---------|------|
| 减少对象创建开销 | 对象池、享元 | 创建型/结构型 |
| 高并发处理 | Actor、Reactor | 并发模式文档 |
| 异步IO优化 | async/await、Future | 异步模式 |
| 内存优化 | 享元、代理 | 结构型模式 |

### 架构设计场景

| 需求 | 推荐模式 | 文档 |
|------|---------|------|
| 解耦组件 | 观察者、中介者 | 行为型模式 |
| 可扩展系统 | 策略、命令 | 行为型模式 |
| 插件系统 | 抽象工厂、代理 | 创建型/结构型 |
| 状态管理 | 状态、备忘录 | 行为型模式 |

### 并发编程场景

| 需求 | 推荐模式 | 文档 |
|------|---------|------|
| 线程通信 | 消息传递 | 并发模式 |
| 共享数据 | 读写者、共享状态 | 并发模式 |
| 任务调度 | 任务调度、工作窃取 | 并发/并行模式 |
| 异步处理 | async trait、Future | 异步模式文档 |

---

## 🔗 相关资源

### 项目文档

- [顶层 README](../README.md) - 项目概述
- [设计模式章节导引](../09_design_patterns.md) - 章节说明
- [Rust 1.89 分析](../RUST_189_DESIGN_PATTERNS_ANALYSIS.md) - 版本对齐
- [项目完成报告](../PROJECT_COMPLETION_REPORT.md) - 项目状态
- [实施路线图](../IMPLEMENTATION_ROADMAP.md) - 未来规划

### 工具与配置

- **Cargo.toml**: 依赖配置和特性门控
- **clippy.toml**: 代码质量配置
- **rustfmt.toml**: 代码格式化配置

---

## 📊 项目统计

### 代码规模

- **创建型模式**: 7 个模式
- **结构型模式**: 7 个模式
- **行为型模式**: 11 个模式
- **并发模式**: 6 个子模块
- **并行模式**: 5 个子模块
- **示例程序**: 5+ 个可运行示例
- **基准测试**: 4 个性能基准套件
- **测试用例**: 3 个集成测试套件

### 文档规模

- **核心文档**: 9 个主要文档
- **形式化文档**: 4 个理论分析文档
- **README文档**: 多个子模块 README
- **代码注释**: 完整的文档注释

---

## 🆕 最新更新

### 2025-10-19 - 重大更新 🎉

- ✅ **新增知识图谱文档** (KNOWLEDGE_GRAPH.md) - 展示模式关系网络
- ✅ **新增多维矩阵对比文档** (MULTIDIMENSIONAL_MATRIX_COMPARISON.md) - 7维度全面对比
- ✅ **新增思维导图文档** (MIND_MAP.md) - 可视化学习路径
- ✅ **新增Rust 1.90示例集** (RUST_190_EXAMPLES.md) - 100+完整示例
- ✅ **新增综合增强报告** (C09_COMPREHENSIVE_ENHANCEMENT_REPORT_2025_10_19.md)
- ✅ **50+个Mermaid可视化图表**
- ✅ 创建主索引文档
- ✅ 完善文档导航结构
- ✅ 添加学习路径指导

### 2025年9月

- ✅ 集成 Rust 1.90 特性
- ✅ 实现原生 async trait
- ✅ 添加 GATs 示例
- ✅ 完善形式化理论文档

---

## 📞 获取帮助

### 问题解决

1. **查看 FAQ**: [FAQ.md](./FAQ.md) - 常见问题解答
2. **查看术语表**: [Glossary.md](./Glossary.md) - 核心概念定义
3. **查看示例**: examples/ - 可运行的示例代码
4. **运行测试**: `cargo test` - 验证功能

### 社区支持

- **GitHub Issues**: 报告问题和建议
- **代码审查**: 提交 PR 获得反馈
- **技术讨论**: 参与社区讨论

---

**文档维护**: Rust 学习社区  
**更新频率**: 跟随项目进度持续更新  
**文档版本**: v1.0  
**Rust 版本**: 1.90+ (Edition 2024)
