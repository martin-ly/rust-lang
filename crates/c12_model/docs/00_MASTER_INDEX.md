# C12 模型与架构：主索引 (Master Index)

> **文档定位**: 软件建模与形式方法学习路径总导航  
> **使用方式**: 作为学习起点，根据需求选择合适的模型和方法  
> **相关文档**: [README](./README.md) | [FAQ](./FAQ.md) | [术语表](./Glossary.md)

## 📊 目录

- [C12 模型与架构：主索引 (Master Index)](#c12-模型与架构主索引-master-index)
  - [📊 目录](#-目录)
  - [📋 快速导航](#-快速导航)
    - [🎯 按角色导航](#-按角色导航)
    - [📚 按主题导航](#-按主题导航)
  - [🏗️ 文档结构](#️-文档结构)
    - [📖 核心文档层](#-核心文档层)
    - [📚 内容文档层](#-内容文档层)
      - [1. 核心概念 (core/)](#1-核心概念-core)
      - [2. 并发模型 (concurrency/)](#2-并发模型-concurrency)
      - [3. 分布式系统 (distributed/)](#3-分布式系统-distributed)
      - [4. 架构设计 (architecture/)](#4-架构设计-architecture)
      - [5. 形式化方法 (formal/)](#5-形式化方法-formal)
      - [6. 使用指南 (guides/)](#6-使用指南-guides)
      - [7. 教程 (tutorials/)](#7-教程-tutorials)
      - [8. API 参考 (api/)](#8-api-参考-api)
      - [9. 示例 (examples/)](#9-示例-examples)
      - [10. 设计模式 (patterns/)](#10-设计模式-patterns)
      - [11. 领域应用 (domain/)](#11-领域应用-domain)
      - [12. 开发指南 (development/)](#12-开发指南-development)
      - [13. 高级主题 (advanced/)](#13-高级主题-advanced)
      - [14. 归档文档 (archives/)](#14-归档文档-archives)
  - [📚 学习路径](#-学习路径)
    - [🚀 初学者路径 (1-2周)](#-初学者路径-1-2周)
    - [🎓 中级路径 (3-6周)](#-中级路径-3-6周)
    - [🔬 高级路径 (7-12周)](#-高级路径-7-12周)
  - [🎯 按场景导航](#-按场景导航)
    - [高并发系统开发](#高并发系统开发)
    - [分布式系统设计](#分布式系统设计)
    - [微服务架构](#微服务架构)
    - [形式化验证](#形式化验证)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [源码与示例](#源码与示例)
    - [配置文件](#配置文件)
  - [📊 文档统计](#-文档统计)
  - [🆕 最近更新](#-最近更新)
    - [2025-10-19](#2025-10-19)
    - [历史更新](#历史更新)
  - [💡 使用建议](#-使用建议)
  - [📞 支持与反馈](#-支持与反馈)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | README → 教程 → 核心概念 | [快速开始](./tutorials/quick-start.md) |
| **中级开发者** | 并发模型 → 分布式系统 → 架构设计 | [使用指南](./guides/) |
| **架构师** | 架构设计 → 模型分类 → 高级主题 | [架构设计](./architecture/) |
| **研究者** | 形式化方法 → 语义模型 → 算法理论 | [形式化方法](./formal/) |

### 📚 按主题导航

| 主题 | 文档入口 | 说明 |
|------|---------|------|
| **概览** | [OVERVIEW.md](./OVERVIEW.md) | 项目整体概述 |
| **核心概念** | [core/](./core/) | 建模基础理论 |
| **并发模型** | [concurrency/](./concurrency/) | 并发与异步模型 |
| **分布式系统** | [distributed/](./distributed/) | 分布式共识与算法 |
| **架构设计** | [architecture/](./architecture/) | 软件架构模式 |
| **形式化方法** | [formal/](./formal/) | 语义与验证 |

---

## 🏗️ 文档结构

### 📖 核心文档层

```text
docs/
├── 00_MASTER_INDEX.md          # 本文档 - 主导航索引
├── README.md                    # 文档中心首页
├── OVERVIEW.md                  # 项目概述
├── FAQ.md                       # 常见问题
├── Glossary.md                  # 术语表
└── SUMMARY.md                   # 文档结构总览
```

### 📚 内容文档层

#### 1. 核心概念 (core/)

基础理论和概念，建模入门必读

| 文档 | 说明 |
|------|------|
| [modeling-overview.md](./core/modeling-overview.md) | 建模概述 |
| [algorithm-models.md](./core/algorithm-models.md) | 算法模型基础 |

**适合人群**: 初学者、需要理论基础的开发者

#### 2. 并发模型 (concurrency/)

并发、异步、背压控制等并发编程模型

| 文档 | 说明 |
|------|------|
| [README.md](./concurrency/README.md) | 并发模型总览 |
| [models.md](./concurrency/models.md) | 并发模型分类 |
| [async-sync-classification.md](./concurrency/async-sync-classification.md) | 异步同步分类 |
| [async-recursion.md](./concurrency/async-recursion.md) | 异步递归模型 |
| [backpressure-models.md](./concurrency/backpressure-models.md) | 背压控制模型 |
| [concurrency-models-deep-dive.md](./concurrency/concurrency-models-deep-dive.md) | 并发模型深度分析 |
| [engineering.md](./concurrency/engineering.md) | 并发工程实践 |
| [rust189.md](./concurrency/rust189.md) | Rust 1.89 并发特性 |

**适合人群**: 中高级开发者、并发系统设计者

#### 3. 分布式系统 (distributed/)

分布式共识、快照、一致性模型

| 文档 | 说明 |
|------|------|
| [raft-consensus-comprehensive.md](./distributed/raft-consensus-comprehensive.md) | Raft共识算法完整实现 |
| [distributed-snapshot-comprehensive.md](./distributed/distributed-snapshot-comprehensive.md) | 分布式快照算法 |

**适合人群**: 分布式系统开发者、架构师

#### 4. 架构设计 (architecture/)

软件架构模式、微服务设计

| 文档 | 说明 |
|------|------|
| [README.md](./architecture/README.md) | 架构设计总览 |
| [design-models.md](./architecture/design-models.md) | 设计模型 |
| [distributed-design.md](./architecture/distributed-design.md) | 分布式架构设计 |
| [software-design-models-comprehensive.md](./architecture/software-design-models-comprehensive.md) | 软件设计模型综合 |
| [microservices-mechanisms.md](./architecture/microservices-mechanisms.md) | 微服务机制 |

**适合人群**: 架构师、系统设计者

#### 5. 形式化方法 (formal/)

语义模型、形式化验证

| 文档 | 说明 |
|------|------|
| [README.md](./formal/README.md) | 形式化方法总览 |
| [language-semantics.md](./formal/language-semantics.md) | 语言语义学 |
| [semantic-models-comprehensive.md](./formal/semantic-models-comprehensive.md) | 语义模型综合 |

**适合人群**: 研究者、编译器开发者、形式化验证工程师

#### 6. 使用指南 (guides/)

实践指南和最佳实践

| 文档 | 说明 |
|------|------|
| [README.md](./guides/README.md) | 指南总览 |
| [comprehensive-usage-guide.md](./guides/comprehensive-usage-guide.md) | 综合使用指南 |
| [system-modeling.md](./guides/system-modeling.md) | 系统建模指南 |
| [machine-learning.md](./guides/machine-learning.md) | 机器学习集成 |
| [ml-preprocess-eval.md](./guides/ml-preprocess-eval.md) | ML预处理与评估 |
| [fsm-to-protocol.md](./guides/fsm-to-protocol.md) | 从状态机到协议 |

**适合人群**: 所有开发者

#### 7. 教程 (tutorials/)

分步教程和快速入门

| 文档 | 说明 |
|------|------|
| [README.md](./tutorials/README.md) | 教程总览 |
| [installation.md](./tutorials/installation.md) | 安装配置 |
| [quick-start.md](./tutorials/quick-start.md) | 快速开始 |

**适合人群**: 初学者

#### 8. API 参考 (api/)

API 文档和接口说明

| 文档 | 说明 |
|------|------|
| [README.md](./api/README.md) | API 总览 |
| [formal-models.md](./api/formal-models.md) | 形式化模型 API |
| [ml-models.md](./api/ml-models.md) | 机器学习模型 API |
| [queueing-models.md](./api/queueing-models.md) | 排队论模型 API |

**适合人群**: API 使用者

#### 9. 示例 (examples/)

代码示例和演示

| 文档 | 说明 |
|------|------|
| [README.md](./examples/README.md) | 示例总览 |

**适合人群**: 所有开发者

#### 10. 设计模式 (patterns/)

设计模式和最佳实践

| 文档 | 说明 |
|------|------|
| [README.md](./patterns/README.md) | 模式总览 |

**适合人群**: 中高级开发者

#### 11. 领域应用 (domain/)

特定领域的应用

| 文档 | 说明 |
|------|------|
| [README.md](./domain/README.md) | 领域应用总览 |

**适合人群**: 特定领域开发者

#### 12. 开发指南 (development/)

贡献指南和开发规范

| 文档 | 说明 |
|------|------|
| [README.md](./development/README.md) | 开发指南总览 |
| [contributing.md](./development/contributing.md) | 贡献指南 |

**适合人群**: 贡献者

#### 13. 高级主题 (advanced/)

高级理论和深度分析

| 文档 | 说明 |
|------|------|
| [MODEL_COMPREHENSIVE_TAXONOMY.md](./advanced/MODEL_COMPREHENSIVE_TAXONOMY.md) | 模型分类体系 |
| [MODEL_RELATIONSHIPS_COMPREHENSIVE.md](./advanced/MODEL_RELATIONSHIPS_COMPREHENSIVE.md) | 模型关系综合分析 |
| [MODEL_RELATIONSHIPS_AND_SEMANTICS.md](./advanced/MODEL_RELATIONSHIPS_AND_SEMANTICS.md) | 模型关系与语义 |
| [MODEL_ARCHITECTURE_DESIGN.md](./advanced/MODEL_ARCHITECTURE_DESIGN.md) | 模型架构设计 |

**适合人群**: 高级开发者、研究者

#### 14. 归档文档 (archives/)

历史文档和报告

包含项目开发过程中的各类报告、总结和历史文档，供参考使用。

---

## 📚 学习路径

### 🚀 初学者路径 (1-2周)

1. **入门** → [README](./README.md) + [OVERVIEW](./OVERVIEW.md)
2. **教程** → [快速开始](./tutorials/quick-start.md) + [安装配置](./tutorials/installation.md)
3. **核心** → [建模概述](./core/modeling-overview.md)
4. **实践** → [示例代码](./examples/)

### 🎓 中级路径 (3-6周)

1. **并发** → [并发模型](./concurrency/)
2. **分布式** → [分布式系统](./distributed/)
3. **架构** → [架构设计](./architecture/)
4. **指南** → [使用指南](./guides/)

### 🔬 高级路径 (7-12周)

1. **形式化** → [形式化方法](./formal/)
2. **深入** → [高级主题](./advanced/)
3. **模式** → [设计模式](./patterns/)
4. **领域** → [领域应用](./domain/)

---

## 🎯 按场景导航

### 高并发系统开发

| 需求 | 推荐文档 | 路径 |
|------|---------|------|
| 并发模型 | [并发模型分类](./concurrency/models.md) | concurrency/ |
| 背压控制 | [背压模型](./concurrency/backpressure-models.md) | concurrency/ |
| 异步编程 | [异步同步分类](./concurrency/async-sync-classification.md) | concurrency/ |

### 分布式系统设计

| 需求 | 推荐文档 | 路径 |
|------|---------|------|
| 共识算法 | [Raft共识](./distributed/raft-consensus-comprehensive.md) | distributed/ |
| 快照机制 | [分布式快照](./distributed/distributed-snapshot-comprehensive.md) | distributed/ |
| 架构设计 | [分布式架构](./architecture/distributed-design.md) | architecture/ |

### 微服务架构

| 需求 | 推荐文档 | 路径 |
|------|---------|------|
| 架构模式 | [架构设计](./architecture/design-models.md) | architecture/ |
| 微服务机制 | [微服务机制](./architecture/microservices-mechanisms.md) | architecture/ |
| 系统建模 | [系统建模指南](./guides/system-modeling.md) | guides/ |

### 形式化验证

| 需求 | 推荐文档 | 路径 |
|------|---------|------|
| 语义模型 | [语义模型](./formal/semantic-models-comprehensive.md) | formal/ |
| 语言语义 | [语言语义学](./formal/language-semantics.md) | formal/ |
| 状态机 | [状态机到协议](./guides/fsm-to-protocol.md) | guides/ |

---

## 🔗 相关资源

### 项目文档

- [项目 README](../README.md) - 项目总览
- [路线图](../ROADMAP.md) - 开发路线图
- [里程碑](../MILESTONES.md) - 项目里程碑
- [更新日志](../CHANGELOG.md) - 版本更新记录

### 源码与示例

- [源码实现](../src/) - 核心实现代码
- [示例程序](../examples/) - 完整示例代码
- [测试用例](../tests/) - 测试代码
- [基准测试](../benches/) - 性能基准

### 配置文件

- [Cargo.toml](../Cargo.toml) - 项目配置
- [book.toml](./book.toml) - mdBook 配置

---

## 📊 文档统计

- **文档总数**: 50+ 篇
- **核心文档**: 6 个类别
- **教程文档**: 3 篇
- **API 文档**: 4 篇
- **示例代码**: 15+ 个

---

## 🆕 最近更新

### 2025-10-19

- ✅ 重组文档结构
- ✅ 合并重复目录 (concurrent → concurrency)
- ✅ 创建清晰的分类体系
- ✅ 添加学习路径指引
- ✅ 完善导航索引

### 历史更新

详见 [归档文档](./archives/) 和 [更新日志](../CHANGELOG.md)

---

## 💡 使用建议

1. **首次使用**: 从 [README](./README.md) 和 [OVERVIEW](./OVERVIEW.md) 开始
2. **快速入门**: 直接查看 [快速开始](./tutorials/quick-start.md)
3. **深入学习**: 按照学习路径逐步推进
4. **问题解决**: 查看 [FAQ](./FAQ.md) 或搜索相关文档
5. **术语查询**: 使用 [术语表](./Glossary.md)

---

## 📞 支持与反馈

- 问题报告: [GitHub Issues](https://github.com/rust-lang/rust-lang/issues)
- 文档改进: 欢迎提交 Pull Request
- 讨论交流: [GitHub Discussions](https://github.com/rust-lang/rust-lang/discussions)

---

**文档维护**: Rust 学习社区  
**文档版本**: v2.0  
**Rust 版本**: 1.90+
