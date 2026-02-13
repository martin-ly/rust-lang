# 🦀 Rust设计模式综合学习模块

> **模块类型**: 设计模式学习模块 | ⭐ 质量评分: **95/100**
> **Rust版本**: 1.93.0+ | 📊 完成度: **100% 完成** ✅
> **学习重点**: GoF设计模式、并发模式、Rust特有模式、形式化验证
> **适用对象**: Rust中级到高级开发者、架构师
> **最后更新**: 2025-12-25 | 🔄 维护模式: Rust 1.93.0 特性更新完成，Tier 1 文档完善完成

## 目录

- [🦀 Rust设计模式综合学习模块](#-rust设计模式综合学习模块)
  - [目录](#目录)
  - [🎯 最新更新 (2025-12-25) ✨](#-最新更新-2025-12-25-)
    - [🎉 组合模式工程案例完成](#-组合模式工程案例完成)
    - [📖 Tier 3 文档完善 🎉](#-tier-3-文档完善-)
    - [📖 Tier 1 文档完善 🎉](#-tier-1-文档完善-)
  - [🎯 最新更新 (2025-11-15) ✨](#-最新更新-2025-11-15-)
  - [🎯 2025-10-22 文档标准化完成 ✨](#-2025-10-22-文档标准化完成-)
    - [📖 新版文档导航](#-新版文档导航)
  - [🌟 2025-10-20 核心增强更新](#-2025-10-20-核心增强更新)
  - [📋 模块概述](#-模块概述)
    - [🎯 学习目标](#-学习目标)
  - [🚀 核心学习内容](#-核心学习内容)
    - [第一部分：经典设计模式 (GoF)](#第一部分经典设计模式-gof)
      - [创建型模式 (Creational)](#创建型模式-creational)
      - [结构型模式 (Structural)](#结构型模式-structural)
      - [行为型模式 (Behavioral)](#行为型模式-behavioral)
    - [第二部分：并发与异步模式](#第二部分并发与异步模式)
      - [异步原语](#异步原语)
      - [高级并发模型](#高级并发模型)
    - [第三部分：形式化理论 🔬](#第三部分形式化理论-)
      - [类型系统与证明](#类型系统与证明)
      - [语义模型与等价关系](#语义模型与等价关系)
      - [形式化验证实践](#形式化验证实践)
    - [第四部分：Rust特有模式](#第四部分rust特有模式)
  - [📚 学习资源与文档](#-学习资源与文档)
    - [核心文档 📖](#核心文档-)
    - [形式化理论文档 🔬](#形式化理论文档-)
      - [本模块形式化文档](#本模块形式化文档)
      - [🔬 形式化工程系统理论](#-形式化工程系统理论)
    - [代码示例与实现](#代码示例与实现)
      - [经典模式示例](#经典模式示例)
      - [并发模式示例](#并发模式示例)
      - [形式化验证示例](#形式化验证示例)
      - [可运行示例](#可运行示例)
    - [性能基准测试](#性能基准测试)
  - [🚀 快速开始](#-快速开始)
    - [运行示例](#运行示例)
    - [阅读建议路径](#阅读建议路径)
  - [🛠️ 实践练习](#️-实践练习)
    - [Level 1：基础掌握 ⭐](#level-1基础掌握-)
    - [Level 2：并发进阶 ⭐⭐](#level-2并发进阶-)
    - [Level 3：形式化验证 ⭐⭐⭐](#level-3形式化验证-)
    - [Level 4：实战项目 ⭐⭐⭐⭐](#level-4实战项目-)
  - [📖 学习路径](#-学习路径)
    - [第1周：创建型模式](#第1周创建型模式)
    - [第2周：结构型模式](#第2周结构型模式)
    - [第3周：行为型模式](#第3周行为型模式)
    - [第4周：Rust特有模式](#第4周rust特有模式)
  - [🎯 实践项目](#-实践项目)
    - [初级项目](#初级项目)
    - [中级项目](#中级项目)
    - [高级项目](#高级项目)
  - [🔍 常见问题](#-常见问题)
    - [设计模式问题](#设计模式问题)
    - [并发模式问题](#并发模式问题)
    - [性能问题](#性能问题)
  - [📊 学习进度](#-学习进度)
    - [基础掌握 (第1-2周)](#基础掌握-第1-2周)
    - [进阶掌握 (第3-4周)](#进阶掌握-第3-4周)
    - [高级应用 (第5-8周)](#高级应用-第5-8周)
  - [🤝 社区支持](#-社区支持)
    - [获取帮助](#获取帮助)
    - [贡献方式](#贡献方式)
  - [📞 联系信息](#-联系信息)
    - [项目维护](#项目维护)
    - [学习支持](#学习支持)
  - [🆕 Rust 1.93.0 / Edition 2024 采用情况](#-rust-1920--edition-2024-采用情况)
    - [示例入口与用法](#示例入口与用法)
    - [运行 examples](#运行-examples)
    - [Benchmark（Criterion）](#benchmarkcriterion)
    - [新增示例与基准索引](#新增示例与基准索引)
      - [异步事件总线用法提示](#异步事件总线用法提示)

## 🎯 最新更新 (2025-12-25) ✨

> **文档状态**: ✅ **100% 标准化完成**
> **框架结构**: ✅ **4-Tier 架构**
> **文档总数**: **43+ 篇**
> **质量评分**: **95/100**
> **Rust版本**: 1.93.0+ (Edition 2024)
> **Tier 1 完成度**: ✅ **100%** (4/4 文档全部完成)
> **Tier 3 完成度**: ✅ **100%** (6/6 文档全部完成)

### 🎉 组合模式工程案例完成

- ✅ **Web 服务案例** (`src/pattern_combinations.rs`)
  - 组合：Facade + Builder + Strategy + Circuit Breaker
  - 完整实现和集成测试
  - 并发安全验证

- ✅ **游戏引擎子系统案例** (`src/pattern_combinations.rs`)
  - 组合：Observer + Command + State
  - 完整实现和集成测试
  - 性能测试支持

### 📖 Tier 3 文档完善 🎉

- ✅ **新增模式使用快速参考** ([tier*03_references/06*模式使用快速参考.md](./docs/tier_03_references/06_模式使用快速参考.md))
  - 为每个模式提供：何时使用/避免、复杂度、线程安全性
  - 覆盖所有 GoF 模式、并发模式和 Rust 特有模式
  - 包含 Rust 特性说明和实现要点

### 📖 Tier 1 文档完善 🎉

- ✅ **新增 Tier 1 术语表** ([tier*01_foundations/03*术语表.md](./docs/tier_01_foundations/03_术语表.md)) - 核心术语快速参考
- ✅ **新增 Tier 1 常见问题** ([tier*01_foundations/04*常见问题.md](./docs/tier_01_foundations/04_常见问题.md)) - 新手常见问题解答
- ✅ **完善 Tier 1 基础层** - 4个文档全部完成
- ✅ **更新文档链接** - 所有交叉引用已更新

## 🎯 最新更新 (2025-11-15) ✨

> **文档状态**: ✅ **100% 标准化完成**
> **框架结构**: ✅ **4-Tier 架构**
> **文档总数**: **40+ 篇**
> **质量评分**: **95/100**
> **Rust版本**: 1.93.0+ (Edition 2024)

## 🎯 2025-10-22 文档标准化完成 ✨

> **文档状态**: ✅ **100% 标准化完成**
> **框架结构**: ✅ **4-Tier 架构**
> **文档总数**: **27+ 篇**
> **质量评分**: **95/100**

### 📖 新版文档导航

**从这里开始学习** ⭐:

- 🎯 [项目概览](./docs/tier_01_foundations/01_项目概览.md) - 快速了解设计模式
- 🗺️ [主索引导航](./docs/tier_01_foundations/02_主索引导航.md) - 找到适合你的学习路径
- 📖 [术语表](./docs/tier_01_foundations/03_术语表.md) - 核心术语速查
- ❓ [常见问题](./docs/tier_01_foundations/04_常见问题.md) - 解决常见疑问

**文档层级结构**:

- 📚 [Tier 1: 基础层](./docs/tier_01_foundations/) - 快速入门 (2-4小时)
- 📝 [Tier 2: 实践层](./docs/tier_02_guides/) - 实战指南 (10-20小时)
- 📖 [Tier 3: 参考层](./docs/tier_03_references/) - 技术参考 (按需查阅)
- 🚀 [Tier 4: 高级层](./docs/tier_04_advanced/) - 形式化理论 (20-30小时)

**标准化报告**: [C09_STANDARDIZATION_FINAL_2025_10_22.md](./docs/reports/C09_STANDARDIZATION_FINAL_2025_10_22.md)

---

## 🌟 2025-10-20 核心增强更新

- **📊 [知识图谱与概念关系](./docs/theory_enhanced/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)** - 设计模式完整体系
- **📐 [多维矩阵对比分析](./docs/theory_enhanced/MULTI_DIMENSIONAL_COMPARISON_MATRIX.md)** - GoF/并发模式全面对比
- **🗺️ [Rust 1.93.0 设计模式改进与思维导图](./docs/RUST_192_DESIGN_PATTERN_IMPROVEMENTS.md)** ⭐ NEW!
  - GoF模式/并发模式/Rust特有模式 | 3级学习路径(1-6周)
- **💻 [Rust 实战示例集](./docs/RUST_190_EXAMPLES_COLLECTION.md)** ⭐ NEW!
  - 800+行代码 | Builder/Factory/Strategy/Observer/Actor/Type State

**完整度**: 📊 知识图谱 + 📐 多维矩阵 + 🗺️ 思维导图 + 💻 实战示例 = **100%** ✨

---

**模块类型**: 高级学习模块 + 形式化验证
**学习重点**: Rust设计模式、GoF模式、并发模式、形式化理论
**适用对象**: Rust中级到高级开发者、系统架构师
**Rust版本**: 1.93.0+ (Edition 2024)

---

## 📋 模块概述

本模块提供**最全面**的Rust设计模式学习资源，涵盖：

1. **经典设计模式**：GoF 23种模式的现代Rust实现
2. **并发与异步模式**：Actor、Reactor、CSP等高级并发模型
3. **形式化理论**：类型系统证明、语义模型、等价关系分析
4. **实践指南**：性能优化、最佳实践、选型决策

### 🎯 学习目标

- ✅ 理解经典设计模式在Rust中的实现与优化
- ✅ 掌握Rust特有的并发、异步、所有权模式
- ✅ 学会在项目中应用适当的设计模式
- ✅ 理解模式之间的组合和协作
- ✅ 掌握异步编程的语义模型与等价关系
- ✅ 理解Actor/Reactor调度机制与CSP模型
- ✅ 学会形式化验证设计模式的正确性

---

## 🚀 核心学习内容

### 第一部分：经典设计模式 (GoF)

#### 创建型模式 (Creational)

- **单例模式** (`OnceLock`): 线程安全的单例实现，Rust 1.93.0 支持（自 Rust 1.70 引入，1.92.0 增强）
- **工厂模式** (Generic): 使用trait和泛型的工厂设计，零成本抽象
- **建造者模式** (Typestate): 类型状态模式，编译时保证完整性
- **原型模式** (Clone): Clone trait的使用和深拷贝策略

#### 结构型模式 (Structural)

- **适配器模式**: trait适配和类型转换，接口兼容性
- **装饰器模式**: 使用组合和trait扩展功能，零成本包装
- **代理模式**: 智能指针（`Arc`, `Box`, `Rc`）和代理实现
- **外观模式**: 简化复杂子系统接口，模块化设计

#### 行为型模式 (Behavioral)

- **观察者模式** (GATs): 事件驱动和回调机制，支持借用视图（零拷贝）
- **策略模式**: trait对象和泛型，编译时vs运行时多态
- **命令模式**: 闭包和命令队列，函数式风格
- **状态模式**: 状态机和状态转换，类型级状态

### 第二部分：并发与异步模式

#### 异步原语

- **Future/Poll机制**: 状态机变换，零成本抽象
- **async/await**: 协作式调度，编译器魔法
- **Channel通信**: mpsc, broadcast, oneshot语义对比
- **Select多路复用**: 非确定性选择，事件驱动

#### 高级并发模型

- **Actor模式**: 消息传递并发，隔离性保证
- **Reactor模式**: 事件驱动IO，单线程高并发
- **CSP模型**: 类似Golang的通信顺序进程
- **生产者-消费者**: 背压控制，流量管理

### 第三部分：形式化理论 🔬

#### 类型系统与证明

- **Curry-Howard同构**: 类型即命题，程序即证明
- **线性类型**: Rust所有权系统的理论基础
- **Hoare逻辑**: 前置/后置条件，不变量证明
- **会话类型**: 协议正确性的编译时保证

#### 语义模型与等价关系

- **异步vs同步等价性**: CPS变换，Monad语义
- **控制流分析**: CFG构建，数据依赖分析
- **Actor-Reactor关系**: 双模拟证明，语义等价
- **CSP vs Async**: 轨迹语义，失败语义对比

#### 形式化验证实践

- **类型级状态机**: 编译时状态验证
- **终止性证明**: 递归算法的收敛性
- **并发安全性**: 数据竞争自由证明
- **死锁检测**: 资源排序，环路分析

### 第四部分：Rust特有模式

- **所有权模式**: 移动语义、借用模式、生命周期
- **错误处理模式**: `Result<T,E>`、`?`运算符、自定义错误类型
- **零成本抽象**: 泛型单态化、内联优化、LLVM优化
- **新型类型**: 类型安全的领域建模

---

## 📚 学习资源与文档

### 核心文档 📖

| 文档                                                                                    | 内容                                             | 难度       |
| --------------------------------------------------------------------------------------- | ------------------------------------------------ | ---------- |
| [`COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md`](docs/COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md) | 🌟**综合指南**：所有模式的理论、实践、形式化验证 | ⭐⭐⭐⭐⭐ |
| [`09_design_patterns.md`](09_design_patterns.md)                                        | 设计模式定义、数学表示、伪代码索引               | ⭐⭐⭐     |
| [`IMPLEMENTATION_ROADMAP.md`](IMPLEMENTATION_ROADMAP.md)                                | Rust 1.93.0对齐路线图与实施计划                  | ⭐⭐⭐⭐   |
| [`PROJECT_COMPLETION_REPORT.md`](PROJECT_COMPLETION_REPORT.md)                          | 项目完成状态与1.90特性集成报告                   | ⭐⭐⭐     |

### 形式化理论文档 🔬

#### 本模块形式化文档

| 文档                                                                             | 主题                   | 核心内容                                       |
| -------------------------------------------------------------------------------- | ---------------------- | ---------------------------------------------- |
| [`docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md`](docs/ASYNC_SYNC_EQUIVALENCE_THEORY.md) | **异步vs同步等价性**   | CPS变换、Monad语义、控制流分析、性能对比       |
| [`docs/ACTOR_REACTOR_PATTERNS.md`](docs/ACTOR_REACTOR_PATTERNS.md)               | **Actor与Reactor模式** | 消息传递、事件驱动、调度机制、形式化证明       |
| [`docs/CSP_VS_ASYNC_ANALYSIS.md`](docs/CSP_VS_ASYNC_ANALYSIS.md)                 | **CSP vs Rust Async**  | Golang对比、Channel语义、调度模型、性能分析    |
| [`docs/ASYNC_RECURSION_ANALYSIS.md`](docs/ASYNC_RECURSION_ANALYSIS.md)           | **异步递归**           | Box::pin原理、尾递归优化、性能分析、形式化证明 |

#### 🔬 形式化工程系统理论

深入学习设计模式的形式化理论基础：

- 📐 **[设计模式形式化理论](../../docs/rust-formal-engineering-system/03_design_patterns/)** - 完整的模式定义和类型规则
- 🔬 **[形式化验证理论](../../docs/rust-formal-engineering-system/01_theoretical_foundations/09_formal_verification/)** - 形式化验证方法
- 🎯 **[类型系统理论](../../docs/rust-formal-engineering-system/01_theoretical_foundations/01_type_system/)** - 设计模式中的类型系统应用
- 🧮 **[数学基础](../../docs/rust-formal-engineering-system/01_theoretical_foundations/10_mathematical_foundations/)** - 模式背后的数学理论

**学习路径**: 实践代码 → 形式化理论 → 深入理解

### 代码示例与实现

#### 经典模式示例

- `src/creational/` - 创建型模式（单例、工厂、建造者等）
- `src/structural/` - 结构型模式（适配器、装饰器、代理等）
- `src/behavioral/` - 行为型模式（观察者、策略、命令等）

#### 并发模式示例

- `src/concurrency/` - 并发与并行模式
  - `asynchronous/` - 异步模式（Future、Actor、Reactor）
  - `message_passing/` - 消息传递（Channel、EventBus）
  - `shared_state/` - 共享状态（Mutex、RwLock）

#### 形式化验证示例

- `src/formal_verification_examples.rs` - 类型级状态机、终止性证明、并发安全性

#### 可运行示例

- `examples/` - 独立可运行示例
  - `event_bus_demo.rs` - 事件总线演示（背压、取消、超时）
  - `actor_demo.rs` - Actor模型演示
  - `reactor_demo.rs` - Reactor模式演示

### 性能基准测试

- `benches/` - Criterion基准测试
  - 同步vs异步性能对比
  - Channel吞吐量测试
  - 模式实现开销分析

---

## 🚀 快速开始

### 运行示例

```bash
# 1. 进入模块目录
cd crates/c09_design_pattern

# 2. 运行事件总线示例（异步、背压控制）
cargo run --example event_bus_demo

# 3. 运行形式化验证测试
cargo test --lib formal_verification_examples

# 4. 运行所有测试
cargo test --all-features

# 5. 运行性能基准测试
cargo bench
```

### 阅读建议路径

```text
第一阶段：入门（1-2周）
├─ 阅读 COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md 第一部分
├─ 运行 examples/ 下的基础示例
└─ 学习 src/creational/ 和 src/behavioral/ 的实现

第二阶段：并发与异步（3-4周）
├─ 阅读 ASYNC_SYNC_EQUIVALENCE_THEORY.md
├─ 阅读 ACTOR_REACTOR_PATTERNS.md
├─ 学习 src/concurrency/ 的实现
└─ 对比 CSP_VS_ASYNC_ANALYSIS.md

第三阶段：形式化理论（5-8周）
├─ 阅读 COMPREHENSIVE_DESIGN_PATTERNS_GUIDE.md 第三部分
├─ 学习 formal_verification_examples.rs
├─ 阅读 ASYNC_RECURSION_ANALYSIS.md
└─ 实践类型级状态机

第四阶段：实战项目（9-12周）
├─ 在实际项目中应用设计模式
├─ 性能优化与基准测试
├─ 贡献新的模式实现
└─ 撰写技术博客分享经验
```

---

## 🛠️ 实践练习

### Level 1：基础掌握 ⭐

1. **单例模式** - 使用`OnceLock`实现线程安全的全局配置
2. **建造者模式** - 实现类型状态Builder，编译时保证必填字段
3. **观察者模式** - 实现事件通知系统（使用Channel）
4. **策略模式** - 实现可插拔的排序算法（泛型vs trait对象性能对比）

### Level 2：并发进阶 ⭐⭐

1. **Actor模式** - 实现简单的Actor系统（消息传递、生命周期管理）
2. **Reactor模式** - 实现事件循环和回调注册机制
3. **生产者-消费者** - 实现带背压控制的异步管道
4. **EventBus系统** - 扩展`event_bus_demo.rs`，支持多种事件类型

### Level 3：形式化验证 ⭐⭐⭐

1. **类型级状态机** - 为数据库连接/文件IO实现类型状态
2. **终止性证明** - 为递归算法添加形式化注释
3. **并发安全证明** - 使用`crossbeam`实现无锁数据结构并证明安全性
4. **会话类型** - 实现编译时协议验证（如HTTP状态机）

### Level 4：实战项目 ⭐⭐⭐⭐

1. **异步Web框架** - 组合Actor+Reactor实现高性能HTTP服务器
2. **插件系统** - 使用动态加载和trait object实现插件架构
3. **分布式系统** - 实现基于Actor的简单分布式计算框架
4. **性能分析工具** - 对比不同设计模式的性能开销

---

## 📖 学习路径

### 第1周：创建型模式

- 学习单例、工厂、建造者模式
- 理解Rust中的对象创建策略
- 练习使用trait和泛型

### 第2周：结构型模式

- 学习适配器、装饰器、代理模式
- 理解组合和继承的区别
- 练习使用智能指针

### 第3周：行为型模式

- 学习观察者、策略、命令模式
- 理解事件驱动编程
- 练习使用闭包和回调

### 第4周：Rust特有模式

- 学习所有权和借用模式
- 理解错误处理模式
- 练习异步和并发模式

---

## 🎯 实践项目

### 初级项目

- **简单工厂**: 实现一个简单的对象工厂
- **观察者系统**: 实现一个事件通知系统
- **策略排序**: 实现可插拔的排序算法

### 中级项目

- **命令模式**: 实现一个可撤销的操作系统
- **状态机**: 实现一个状态转换系统
- **代理模式**: 实现一个缓存代理

### 高级项目

- **异步消息系统**: 实现异步的消息处理系统
- **插件架构**: 实现可扩展的插件系统
- **分布式模式**: 实现分布式系统的设计模式

---

## 🔍 常见问题

### 设计模式问题

- **Q: 什么时候使用设计模式？**
- **A: 当遇到重复出现的设计问题时，使用相应的模式可以提高代码的可维护性和可扩展性。**

- **Q: Rust中的设计模式有什么特点？**
- **A: Rust中的设计模式需要考虑所有权、生命周期和类型安全，通常使用trait和泛型来实现。**

### 并发模式问题

- **Q: 如何在Rust中实现线程安全的单例？**
- **A: 可以使用OnceCell、LazyStatic或者std::sync::Once来实现。**

- **Q: 异步模式与同步模式有什么区别？**
- **A: 异步模式使用Future和async/await，可以处理大量并发连接，而同步模式使用线程和锁。**

### 性能问题

- **Q: 设计模式会影响性能吗？**
- **A: 在Rust中，零成本抽象使得很多设计模式在编译时被优化掉，对运行时性能影响很小。**

- **Q: 如何选择高性能的设计模式？**
- **A: 优先考虑零成本抽象、编译时多态和所有权转移，避免运行时开销。**

---

## 📊 学习进度

### 基础掌握 (第1-2周)

- [ ] 理解创建型和结构型模式
- [ ] 掌握trait和泛型的使用
- [ ] 学会使用智能指针
- [ ] 理解组合优于继承

### 进阶掌握 (第3-4周)

- [ ] 掌握行为型模式
- [ ] 理解事件驱动编程
- [ ] 学会使用闭包和回调
- [ ] 掌握Rust特有模式

### 高级应用 (第5-8周)

- [ ] 在复杂项目中使用设计模式
- [ ] 实现高性能的异步模式
- [ ] 掌握模式组合和协作
- [ ] 能够设计新的模式

---

## 🤝 社区支持

### 获取帮助

- **技术问题**: 通过GitHub Issues反馈
- **学习问题**: 通过社区讨论区提问
- **代码审查**: 请求代码审查和建议
- **项目讨论**: 参与项目相关讨论

### 贡献方式

- **代码贡献**: 提交改进的示例代码
- **文档贡献**: 改进文档和注释
- **测试贡献**: 添加测试用例
- **问题反馈**: 报告发现的问题

---

## 📞 联系信息

### 项目维护

- **维护者**: Rust学习社区
- **更新频率**: 跟随学习进度
- **质量保证**: 持续改进中

### 学习支持

- **学习指导**: 提供学习路径指导
- **问题解答**: 解答学习过程中的问题
- **资源推荐**: 推荐相关学习资源
- **经验分享**: 分享学习经验

---

**模块状态**: 🔄 持续开发中
**最后更新**: 2025年9月25日
**适用版本**: Rust 1.93.0，Edition 2024

---

*本模块专注于Rust设计模式的学习，提供系统性的学习路径和实践示例。如有任何问题或建议，欢迎反馈。*

---

## 🆕 Rust 1.93.0 / Edition 2024 采用情况

- let-else：
  - `behavioral/chain_of_responsibility/define.rs` 的 `handle` 方法使用 `let Some(..) else { .. }` 做早退分支。
- return-position impl Trait：
  - `structural/flyweight/define.rs` 的 `OptimizedFlyweightFactory::iter_ids` 返回 `impl Iterator<Item = u32>`。
- RPITIT（trait 方法返回 impl Trait）：
  - `src/rust_190_features.rs::rpitit_demo::TextSource::words` 展示在 trait 方法中返回 `impl Iterator` 的用法。
- dyn 上行转型（dyn upcasting）：
  - `src/rust_190_features.rs::dyn_upcasting_demo` 展示 `&mut dyn Sub` 到 `&mut dyn Super` 的隐式上转型调用场景。
- 其他：
  - 错误处理工具 `error_handling.rs::utils::validate_input` 使用 `let-else` 提升可读性。
  - 全局初始化从 `lazy_static` 迁移为 `std::sync::OnceLock`（见 `error_handling.rs::global_error_monitor`）。

### 示例入口与用法

- 原生 async fn in trait：
  - 模块：`concurrency/asynchronous/native_async_trait`
  - 运行思路：该示例带有单元测试（纯 Rust 栈内 `block_on`），可通过 `cargo test -p c09_design_pattern native_async_trait` 触发。
  - 可选 Tokio 门控：启用 `--features tokio-bench` 可运行基于 Tokio 的延迟处理测试。
- 1.90 汇总示例：
  - 模块：`rust_190_features`
  - API：`highlights::terminate_with_panic() -> !`、`highlights::if_let_chain(..)`、`rpitit_demo::TextSource::words(..)`、`dyn_upcasting_demo`
  - 用途：演示 never 类型与 if-let 链式匹配；可在任意示例/测试中直接调用。
- GATs 借用视图：
  - 模块：`behavioral/observer/define.rs`
  - 类型：`ObserverRef`、`BorrowingObserver`、`BorrowingSubjectString`
  - 要点：通知时借用数据，避免多次克隆，用以展示 GATs 的借用返回。
- 并行流水线（返回位 impl Trait）：
  - 模块：`parallel/pipeline/define.rs`
  - API：`make_pipeline_iter(&[i32]) -> impl Iterator<Item=i32> + Send`
  - 要点：组合 map/filter/map，返回位 impl Trait + Send。

### 运行 examples

```bash
# async trait 示例
cargo run -p c09_design_pattern --example async_trait_demo

# 异步事件总线（背压/取消/超时近似/批处理）
cargo run -p c09_design_pattern --example event_bus_demo

# GATs 观察者示例
cargo run -p c09_design_pattern --example gats_observer_demo

# 流水线迭代器示例
cargo run -p c09_design_pattern --example pipeline_iter_demo

# 启用 Tokio 门控并运行测试
cargo test -p c09_design_pattern --features tokio-bench
```

### Benchmark（Criterion）

```bash
# 运行全部基准
cargo bench -p c09_design_pattern

# 仅运行某组或某项（支持正则）
cargo bench -p c09_design_pattern -- flyweight
cargo bench -p c09_design_pattern -- proxy_request

# 保存当前结果为基线
cargo bench -p c09_design_pattern -- --save-baseline main

# 与已保存的基线对比
cargo bench -p c09_design_pattern -- --baseline main
```

### 新增示例与基准索引

- 示例：
  - `event_bus_demo`: 异步事件总线（async trait + GATs）
  - `async_trait_demo`: 原生 async trait 最小示例
  - `gats_observer_demo`: GATs 借用观察者
  - `pipeline_iter_demo`: 返回位 impl Trait 的流水线

#### 异步事件总线用法提示

- 背压策略：`DropOldest`（保留最新一半示例）、`Block`（逐条处理）、`Batch(n)`（按批处理）
- 取消/超时近似：`run_until_cancel(..., true)`、`run_with_timeout_like(events, max_events)`

示例调用（详见 `examples/event_bus_demo.rs`）：

```rust
let bus = EventBusString::new(StringEventHandler);
let events: Vec<String> = (0..5).map(|i| format!("demo-{}", i)).collect();
block_on(bus.run_with_backpressure(&events));
block_on(bus.run_until_cancel(&events, true));
block_on(bus.run_with_strategy(&events, BackpressureStrategy::Block));
block_on(bus.run_with_strategy(&events, BackpressureStrategy::DropOldest));
block_on(bus.run_with_strategy(&events, BackpressureStrategy::Batch(2)));
block_on(bus.run_with_timeout_like(&events, 3));
```

- 基准：
  - `benches/async_gats_benches.rs`: 异步事件总线与 GATs 观察者基准

后续规划：在不破坏稳定 API 的前提下，逐步引入原生 `async fn` in trait、GATs 等更高级特性到并发与异步子模块（视适用性与依赖生态兼容性推进）。
