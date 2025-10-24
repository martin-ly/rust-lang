# C05 线程编程 - 主索引

> **文档定位**: 本文档是C05线程编程模块的完整索引系统，提供所有文档的分类导航、学习路径和快速查找。初次访问建议从 [README.md](./README.md) 开始。

## 📊 目录

- [C05 线程编程 - 主索引](#c05-线程编程---主索引)
  - [📊 目录](#-目录)
  - [📚 文档导航总览](#-文档导航总览)
  - [🎯 快速开始](#-快速开始)
    - [新手入门](#新手入门)
    - [进阶学习](#进阶学习)
  - [📂 文档分类索引](#-文档分类索引)
    - [1️⃣ 基础入门文档](#1️⃣-基础入门文档)
      - [核心概念](#核心概念)
      - [并发范式](#并发范式)
    - [2️⃣ 进阶主题文档](#2️⃣-进阶主题文档)
      - [并行与性能](#并行与性能)
      - [高级编程](#高级编程)
    - [3️⃣ 参考文档](#3️⃣-参考文档)
      - [学习辅助](#学习辅助)
      - [版本特性](#版本特性)
  - [🎓 推荐学习路径](#-推荐学习路径)
    - [路径 1: 快速入门 (3-5 天)](#路径-1-快速入门-3-5-天)
    - [路径 2: 系统学习 (1-2 周)](#路径-2-系统学习-1-2-周)
    - [路径 3: 专家进阶 (持续学习)](#路径-3-专家进阶-持续学习)
  - [📊 文档统计](#-文档统计)
    - [文档数量](#文档数量)
    - [文档质量](#文档质量)
  - [🔍 快速查找](#-快速查找)
    - [按关键词查找](#按关键词查找)
    - [按问题查找](#按问题查找)
  - [🔗 相关资源](#-相关资源)
    - [项目资源](#项目资源)
    - [相关模块](#相关模块)
    - [外部资源](#外部资源)
  - [💡 使用建议](#-使用建议)
    - [新用户必读](#新用户必读)
    - [重要概念](#重要概念)
  - [📝 文档维护](#-文档维护)
    - [待完成工作](#待完成工作)
  - [⚠️ 当前状态说明](#️-当前状态说明)
  - [📞 反馈与支持](#-反馈与支持)
    - [发现问题？](#发现问题)
    - [需要帮助？](#需要帮助)

## 📚 文档导航总览

本索引提供 `c05_threads` 模块所有文档的快速访问入口，帮助您快速找到所需的学习资源和参考文档。

**最后更新**: 2025-10-19  
**文档版本**: v1.0  
**Rust 版本**: 1.89+ (推荐 1.90+)  
**文档状态**: 🔧 整理中

---

## 🎯 快速开始

### 新手入门

如果您是第一次学习 Rust 并发编程，推荐按以下顺序阅读：

1. 📖 [README](./README.md) - 模块概览和快速导航
2. 📖 [01_threads_and_ownership](./01_threads_and_ownership.md) - 线程与所有权基础
3. 📖 [02_message_passing](./02_message_passing.md) - 消息传递并发
4. 📖 [03_synchronization_primitives](./03_synchronization_primitives.md) - 同步原语

### 进阶学习

已经掌握基础？继续深入学习：

1. 📖 [04_parallelism_and_beyond](./04_parallelism_and_beyond.md) - 并发vs并行
2. 📖 [05_advanced_topics_and_summary](./05_advanced_topics_and_summary.md) - 高级主题
3. 📖 [06_parallel_algorithms](./06_parallel_algorithms.md) - 并行算法
4. 📖 [04_lock_free_programming](./04_lock_free_programming.md) - 无锁编程

---

## 📂 文档分类索引

### 1️⃣ 基础入门文档

#### 核心概念

- 📖 **[README.md](./README.md)** - 模块总览和导航指南
- 📖 **[01_threads_and_ownership.md](./01_threads_and_ownership.md)** - 线程与所有权 (原理文档)
- 📖 **[01_basic_threading.md](./01_basic_threading.md)** - 基础线程操作 (实践文档)

> **注意**: 两个01文档内容互补，前者侧重原理，后者侧重实践操作

#### 并发范式

- 📖 **[02_message_passing.md](./02_message_passing.md)** - 消息传递并发 (原理文档)
- 📖 **[02_thread_synchronization.md](./02_thread_synchronization.md)** - 线程同步 (实践文档)
- 📖 **[03_synchronization_primitives.md](./03_synchronization_primitives.md)** - 同步原语详解
- 📖 **[03_concurrency_patterns.md](./03_concurrency_patterns.md)** - 并发模式

### 2️⃣ 进阶主题文档

#### 并行与性能

- 📄 [04_parallelism_and_beyond.md](./04_parallelism_and_beyond.md) - 并发与并行的区别
- 📄 [06_parallel_algorithms.md](./06_parallel_algorithms.md) - 并行算法详解
- 📄 [advanced_concurrency_optimization.md](./advanced_concurrency_optimization.md) - 高级并发优化

#### 高级编程

- 📄 [04_lock_free_programming.md](./04_lock_free_programming.md) - 无锁编程
- 📄 [05_advanced_topics_and_summary.md](./05_advanced_topics_and_summary.md) - 高级主题总结
- 📄 [05_message_passing.md](./05_message_passing.md) - 高级消息传递

### 3️⃣ 参考文档

#### 学习辅助

- 📖 **[Glossary.md](./Glossary.md)** - 并发术语表
- 📖 **[FAQ.md](./FAQ.md)** - 常见问题解答

#### 版本特性

- 🚀 **[rust_189_features_analysis.md](./rust_189_features_analysis.md)** - Rust 1.89特性分析

---

## 🎓 推荐学习路径

### 路径 1: 快速入门 (3-5 天)

**目标**: 快速掌握基本并发编程，能够编写简单的多线程程序

**Day 1**: 基础概念

- [README](./README.md)
- [01_threads_and_ownership](./01_threads_and_ownership.md)
- [01_basic_threading](./01_basic_threading.md)

**Day 2**: 并发范式 - 消息传递

- [02_message_passing](./02_message_passing.md)

**Day 3**: 并发范式 - 共享状态

- [03_synchronization_primitives](./03_synchronization_primitives.md)
- [02_thread_synchronization](./02_thread_synchronization.md)

**Day 4-5**: 实践练习

- 查看 [`examples/`](../examples/) 中的示例
- 运行测试: `cargo test -p c05_threads`

### 路径 2: 系统学习 (1-2 周)

**目标**: 系统掌握并发编程，理解各种并发特性和模式

**第 1 周**: 基础到进阶

1. 基础文档 (Day 1-2)
   - 01系列 - 线程基础
   - 02系列 - 并发范式

2. 并发模式 (Day 3-4)
   - [03_concurrency_patterns](./03_concurrency_patterns.md)
   - [03_synchronization_primitives](./03_synchronization_primitives.md)

3. 并发与并行 (Day 5-7)
   - [04_parallelism_and_beyond](./04_parallelism_and_beyond.md)
   - [06_parallel_algorithms](./06_parallel_algorithms.md)

**第 2 周**: 高级主题

1. 高级编程 (Day 1-3)
   - [04_lock_free_programming](./04_lock_free_programming.md)
   - [05_advanced_topics_and_summary](./05_advanced_topics_and_summary.md)

2. 性能优化 (Day 4-5)
   - [advanced_concurrency_optimization](./advanced_concurrency_optimization.md)

3. 项目实践 (Day 6-7)
   - 学习示例代码
   - 完成实践项目

### 路径 3: 专家进阶 (持续学习)

**目标**: 精通并发编程，能够设计复杂的并发系统

1. **深度理解**
   - 研读所有文档
   - 理解底层原理
   - 分析性能特征

2. **高级应用**
   - 无锁数据结构
   - 高性能并发算法
   - 实时系统设计

3. **持续更新**
   - 关注 Rust 版本更新
   - 学习最新并发特性
   - 参与社区讨论

---

## 📊 文档统计

### 文档数量

| 类别 | 数量 | 总行数 |
|------|------|--------|
| **基础文档** | 6 | ~2,000+ |
| **进阶文档** | 7 | ~3,000+ |
| **参考文档** | 3 | ~500+ |
| **总计** | 16 | ~5,500+ |

### 文档质量

- 🔧 **完整性**: 80%+ 覆盖率 (整理中)
- ⚠️ **准确性**: 需要验证版本信息
- ✅ **可读性**: 中文详细注释
- 🔧 **一致性**: 格式统一中

---

## 🔍 快速查找

### 按关键词查找

**线程基础**:

- 线程创建 → [01_basic_threading](./01_basic_threading.md)
- 线程所有权 → [01_threads_and_ownership](./01_threads_and_ownership.md)
- 线程句柄 → [01_basic_threading](./01_basic_threading.md#22-线程句柄管理)

**并发模式**:

- 消息传递 → [02_message_passing](./02_message_passing.md)
- 共享状态 → [03_synchronization_primitives](./03_synchronization_primitives.md)
- 并发模式 → [03_concurrency_patterns](./03_concurrency_patterns.md)

**同步原语**:

- Mutex → [03_synchronization_primitives](./03_synchronization_primitives.md)
- Arc → [03_synchronization_primitives](./03_synchronization_primitives.md)
- RwLock → [03_synchronization_primitives](./03_synchronization_primitives.md)
- Channel → [02_message_passing](./02_message_passing.md)

**高级特性**:

- 并行计算 → [04_parallelism_and_beyond](./04_parallelism_and_beyond.md)
- 无锁编程 → [04_lock_free_programming](./04_lock_free_programming.md)
- 并行算法 → [06_parallel_algorithms](./06_parallel_algorithms.md)
- 原子操作 → [05_advanced_topics_and_summary](./05_advanced_topics_and_summary.md)

**性能优化**:

- 并发优化 → [advanced_concurrency_optimization](./advanced_concurrency_optimization.md)
- 工作窃取 → [06_parallel_algorithms](./06_parallel_algorithms.md)

### 按问题查找

**我想学习...**:

- 并发基础 → [01_threads_and_ownership](./01_threads_and_ownership.md)
- 线程操作 → [01_basic_threading](./01_basic_threading.md)
- 消息传递 → [02_message_passing](./02_message_passing.md)
- 共享内存 → [03_synchronization_primitives](./03_synchronization_primitives.md)

**我想了解...**:

- 并发vs并行 → [04_parallelism_and_beyond](./04_parallelism_and_beyond.md)
- Send/Sync → [FAQ](./FAQ.md#q1-send-和-sync-到底有什么区别我总是搞混)
- `Arc<Mutex<T>>` → [FAQ](./FAQ.md#q3-arcmutext-看起来很笨重它到底是怎么工作的)

**我遇到问题...**:

- 常见问题 → [FAQ](./FAQ.md)
- 术语不懂 → [Glossary](./Glossary.md)
- 死锁问题 → [Glossary](./Glossary.md#deadlock-死锁)

---

## 🔗 相关资源

### 项目资源

- [主 README](../README.md) - 项目主页
- [示例代码](../examples/) - 完整示例
- [源代码](../src/) - 模块源代码
- [测试用例](../tests/) - 测试代码
- [基准测试](../benches/) - 性能测试

### 相关模块

- [c04_generic](../../c04_generic/docs/00_MASTER_INDEX.md) - 泛型编程
- [c06_async](../../c06_async/) - 异步编程
- [c07_process](../../c07_process/) - 进程管理

### 外部资源

- [Rust 官方文档](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Rust Reference - Concurrency](https://doc.rust-lang.org/reference/types/function-item.html)
- [The Rustonomicon - Concurrency](https://doc.rust-lang.org/nomicon/concurrency.html)

---

## 💡 使用建议

### 新用户必读

1. **首次访问**: 从 [README](./README.md) 开始
2. **基础学习**: 按照推荐学习路径
3. **快速查找**: 使用本索引的分类和搜索
4. **深入研究**: 结合源代码和示例学习

### 重要概念

**核心概念**:

- **Send**: 类型可以安全地在线程间传递所有权
- **Sync**: 类型可以安全地在线程间共享引用
- **所有权**: Rust的核心安全保障
- **借用检查**: 编译时的安全验证

**并发模式**:

- **消息传递**: 通过通道通信，不共享内存
- **共享状态**: 使用Mutex/RwLock保护共享数据
- **无锁编程**: 使用原子操作避免锁开销

---

## 📝 文档维护

**维护状态**: 🔧 活跃整理中  
**更新频率**: 跟随 Rust 版本更新  
**最后整理**: 2025-10-19

### 待完成工作

- [ ] 统一所有文档格式
- [ ] 验证Rust版本信息准确性
- [ ] 处理重复编号文档
- [ ] 添加更多代码示例
- [ ] 创建实践指南

---

## ⚠️ 当前状态说明

本文档索引是在2025-10-19创建的，目前c05_threads模块正在进行文档梳理：

**已发现的问题**:

1. 存在重复编号的文档（需要整合）
2. 文档格式不统一（正在统一）
3. 部分文档需要验证版本信息

**整理进度**: 10% ✅

---

## 📞 反馈与支持

### 发现问题？

- **文档错误**: 请查看最新版本
- **内容建议**: 欢迎提出改进意见
- **学习困难**: 参考FAQ和Glossary

### 需要帮助？

- **学习指导**: 从 [README](./README.md) 开始
- **快速查找**: 使用本索引查找
- **术语查询**: 查看 [Glossary](./Glossary.md)
- **常见问题**: 查看 [FAQ](./FAQ.md)

---

**文档版本**: v1.0  
**创建日期**: 2025-10-19  
**维护状态**: 🔧 整理中

🚀 **文档梳理工作正在进行中，敬请期待！**
