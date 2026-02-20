# C03 控制流与函数: 主索引 (Master Index)

> **文档定位**: 控制流与函数学习路径总导航，涵盖条件、循环、模式匹配、闭包等
> **使用方式**: 作为学习起点，根据需求选择合适的学习路径和文档
> **相关文档**: [README](../README.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

**最后更新**: 2026-02-14
**适用版本**: Rust 1.93.0+
**文档类型**: 📚 导航索引
**English**: [00_MASTER_INDEX.en.md](./00_MASTER_INDEX.en.md)

---

## 📊 目录

- [C03 控制流与函数: 主索引 (Master Index)](#c03-控制流与函数-主索引-master-index)
  - [📊 目录](#-目录)
  - [📚 官方资源映射](#-官方资源映射)
  - [📋 快速导航](#-快速导航)
    - [🎯 按角色导航](#-按角色导航)
    - [📚 按主题导航](#-按主题导航)
    - [🎨 可视化学习](#-可视化学习)
  - [🏗️ 核心内容结构](#️-核心内容结构)
    - [第一部分：理论基础](#第一部分理论基础)
      - [1. 理论基础 (tier\_01\_foundations/)](#1-理论基础-tier_01_foundations)
    - [第二部分：基础知识](#第二部分基础知识)
      - [2. 基础控制流 (tier\_02\_guides/)](#2-基础控制流-tier_02_guides)
    - [第三部分：高级主题](#第三部分高级主题)
      - [3. 高级控制流 (tier\_04\_advanced/)](#3-高级控制流-tier_04_advanced)
    - [第四部分：实践应用](#第四部分实践应用)
      - [4. 实践指南 (tier\_02\_guides/ + tier\_04\_advanced/)](#4-实践指南-tier_02_guides--tier_04_advanced)
    - [第五部分：Rust 特性](#第五部分rust-特性)
      - [5. 版本特性](#5-版本特性)
  - [📖 实践示例](#-实践示例)
    - [可运行示例 (examples/)](#可运行示例-examples)
  - [🧪 测试与验证](#-测试与验证)
    - [测试套件 (tests/)](#测试套件-tests)
  - [📚 学习路径](#-学习路径)
    - [🚀 初学者路径 (2-3周)](#-初学者路径-2-3周)
    - [🎓 中级路径 (3-4周)](#-中级路径-3-4周)
    - [🔬 高级路径 (4-6周)](#-高级路径-4-6周)
  - [🎯 按场景导航](#-按场景导航)
    - [控制流选择](#控制流选择)
    - [函数编程](#函数编程)
  - [🔗 相关资源](#-相关资源)
    - [项目文档](#项目文档)
    - [工具与配置](#工具与配置)
  - [📊 项目统计](#-项目统计)
    - [文档规模](#文档规模)
    - [内容覆盖](#内容覆盖)
  - [🆕 最新更新](#-最新更新)
    - [2025-12-11](#2025-12-11)
    - [Rust 1.92.0 特性](#rust-1920-特性)
  - [📞 获取帮助](#-获取帮助)
    - [问题解决](#问题解决)
    - [社区支持](#社区支持)

## 📚 官方资源映射

| 官方资源 | 链接 | 与本模块对应 |
| :--- | :--- | :--- || **The Rust Book** | [Ch. 3 Common Programming Concepts](https://doc.rust-lang.org/book/ch03-00-comments.html), [Ch. 6 Enums and Pattern Matching](https://doc.rust-lang.org/book/ch06-00-enums.html) | 控制流、模式匹配 |
| **RBE 练习** | [Flow Control](https://doc.rust-lang.org/rust-by-example/flow_control.html) · [Option](https://doc.rust-lang.org/rust-by-example/std/option.html) · [Error](https://doc.rust-lang.org/rust-by-example/error.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html) · [Closures](https://doc.rust-lang.org/rust-by-example/fn/closures.html) | 条件、循环、Option、错误处理、迭代器实践 |
| **Rust Reference** | [Expressions](https://doc.rust-lang.org/reference/expressions.html) | 表达式、控制流规范 |

**Rust 1.93 兼容性**: [兼容性注意事项](../../../docs/06_toolchain/06_rust_1.93_compatibility_notes.md) | [深度解析](../../../docs/06_toolchain/09_rust_1.93_compatibility_deep_dive.md)

**一页纸总结**: [ONE_PAGE_SUMMARY.md](./ONE_PAGE_SUMMARY.md) — 核心概念、常见坑、速选表

## 📋 快速导航

### 🎯 按角色导航

| 角色           | 推荐路径                           | 关键文档                                     |
| :--- | :--- | :--- || **初学者**     | 基础控制流 → 条件表达式 → 循环结构 | [tier_02_guides/](./tier_02_guides/)         |
| **中级开发者** | 模式匹配 → 闭包 → 错误处理         | [tier_04_advanced/](./tier_04_advanced/)     |
| **架构师**     | 高级控制流 → 性能优化 → 设计模式   | [tier_04_advanced/](./tier_04_advanced/)     |
| **研究者**     | 理论基础 → 类型系统 → Rust特性     | [tier_03_references/](./tier_03_references/) |

### 📚 按主题导航

| 主题       | 文档入口                                           | 说明         |
| :--- | :--- | :--- || **概览**   | [DOCUMENTATION_INDEX.md](./DOCUMENTATION_INDEX.md) | 完整文档索引 |
| **FAQ**    | [FAQ.md](./FAQ.md)                                 | 常见问题解答 |
| **术语表** | [Glossary.md](./Glossary.md)                       | 核心概念速查 |

### 🎨 可视化学习

| 类型             | 文档入口                                                             | 说明                |
| :--- | :--- | :--- || **知识体系**     | [KNOWLEDGE_GRAPH.md](./KNOWLEDGE_GRAPH.md)                           | 🔥 完整知识工程体系 |
| **知识图谱**     | [KNOWLEDGE_GRAPH.md](./KNOWLEDGE_GRAPH.md)                           | 概念关系可视化      |
| **多维矩阵**     | [MULTIDIMENSIONAL_MATRIX.md](./MULTIDIMENSIONAL_MATRIX.md)           | 多维度对比分析      |
| **思维导图**     | [MIND_MAP.md](./MIND_MAP.md)                                         | 学习路径导航        |
| **概念关系网络** | [CONCEPT_RELATIONSHIP_NETWORK.md](./CONCEPT_RELATIONSHIP_NETWORK.md) | 深度关系分析        |

---

## 🏗️ 核心内容结构

### 第一部分：理论基础

#### 1. 理论基础 (tier_01_foundations/)

| 文档                                                 | 说明           |
| :--- | :--- || [项目概览](./tier_01_foundations/01_项目概览.md)     | 项目概述和结构 |
| [主索引导航](./tier_01_foundations/02_主索引导航.md) | 完整导航索引   |
| [术语表](./tier_01_foundations/03_术语表.md)         | 术语定义       |
| [常见问题](./tier_01_foundations/04_常见问题.md)     | 常见问题解答   |

### 第二部分：基础知识

#### 2. 基础控制流 (tier_02_guides/)

| 文档                                                | 说明                  |
| :--- | :--- || [条件语句指南](./tier_02_guides/01_条件语句指南.md) | if/else 详解          |
| [循环结构指南](./tier_02_guides/02_循环结构指南.md) | loop/while/for        |
| [函数系统指南](./tier_02_guides/03_函数系统指南.md) | 函数定义与闭包基础    |
| [模式匹配指南](./tier_02_guides/04_模式匹配指南.md) | match 详解            |
| [错误处理指南](./tier_02_guides/05_错误处理指南.md) | Result/Option/?运算符 |
| [代码示例集合](./tier_02_guides/06_代码示例集合.md) | 完整代码示例          |
| [实战项目集](./tier_02_guides/07_实战项目集.md)     | 实战项目              |

### 第三部分：高级主题

#### 3. 高级控制流 (tier_04_advanced/)

| 文档                                                  | 说明           | Rust版本 |
| :--- | :--- | :--- || [高级模式匹配](./tier_04_advanced/01_高级模式匹配.md) | match 深度使用 | 1.92.0+  |
| [闭包深入](./tier_04_advanced/02_闭包深入.md)         | 闭包深入       | 1.92.0+  |
| [函数式编程](./tier_04_advanced/03_函数式编程.md)     | 函数式编程     | 1.92.0+  |
| [错误处理进阶](./tier_04_advanced/04_错误处理进阶.md) | 错误处理进阶   | 1.92.0+  |
| [性能优化](./tier_04_advanced/05_性能优化.md)         | 性能优化       | 1.92.0+  |

### 第四部分：实践应用

#### 4. 实践指南 (tier_02_guides/ + tier_04_advanced/)

| 文档                                                | 说明         |
| :--- | :--- || [代码示例集合](./tier_02_guides/06_代码示例集合.md) | 完整代码示例 |
| [实战项目集](./tier_02_guides/07_实战项目集.md)     | 实战项目     |
| [性能优化](./tier_04_advanced/05_性能优化.md)       | 性能优化     |
| [常见问题](./tier_01_foundations/04_常见问题.md)    | 常见问题解答 |

### 第五部分：Rust 特性

#### 5. 版本特性

| 文档                                                               | 版本   | 说明        |
| :--- | :--- | :--- || [Rust 1.92.0 控制流改进](../RUST_192_CONTROL_FLOW_IMPROVEMENTS.md) | 1.92.0 | 最新特性 🆕 |
| [Rust 1.92.0 控制流改进](../RUST_192_CONTROL_FLOW_IMPROVEMENTS.md) | 1.92.0 | 最新版本    |
| [Rust 1.91 控制流改进](../RUST_191_CONTROL_FLOW_IMPROVEMENTS.md)   | 1.91   | 历史版本    |
| [Rust 1.92.0 控制流改进](../RUST_192_CONTROL_FLOW_IMPROVEMENTS.md) | 1.92.0 | 最新特性 🆕 |

---

## 📖 实践示例

### 可运行示例 (examples/)

```bash
# 查看示例目录
cd crates/c03_control_fn/examples

# 运行控制流示例
cargo run --example control_flow_demo

# 运行闭包示例
cargo run --example closure_demo
```

---

## 🧪 测试与验证

### 测试套件 (tests/)

```bash
# 运行所有测试
cargo test -p c03_control_fn

# 运行特定测试
cargo test --test control_flow_tests
```

---

## 📚 学习路径

### 🚀 初学者路径 (2-3周)

**Week 1: 基础概念**:

1. [条件语句指南](./tier_02_guides/01_条件语句指南.md)
2. [循环结构指南](./tier_02_guides/02_循环结构指南.md)
3. [函数系统指南](./tier_02_guides/03_函数系统指南.md)

**Week 2: 函数与错误**:

1. [函数系统指南](./tier_02_guides/03_函数系统指南.md)
2. [错误处理指南](./tier_02_guides/05_错误处理指南.md)

**Week 3: 新特性与实践**:

1. [Rust 1.92.0 控制流改进](../RUST_192_CONTROL_FLOW_IMPROVEMENTS.md) 🆕
2. [代码示例集合](./tier_02_guides/06_代码示例集合.md)

### 🎓 中级路径 (3-4周)

**Week 1-2: 高级控制流**:

1. [高级模式匹配](./tier_04_advanced/01_高级模式匹配.md)
2. [模式匹配指南](./tier_02_guides/04_模式匹配指南.md)
3. [闭包深入](./tier_04_advanced/02_闭包深入.md)
4. [函数式编程](./tier_04_advanced/03_函数式编程.md)

**Week 3: 函数特性**:

1. [闭包深入](./tier_04_advanced/02_闭包深入.md)
2. [迭代器参考](./tier_03_references/02_迭代器参考.md)

**Week 4: 特殊类型**:

1. [错误处理进阶](./tier_04_advanced/04_错误处理进阶.md)
2. [性能优化](./tier_04_advanced/05_性能优化.md)

### 🔬 高级路径 (4-6周)

**理论与实践**:

1. [基础层](./tier_01_foundations/) - 所有基础文档
2. [高级主题](./tier_04_advanced/) - 所有高级文档
3. [实践指南](./tier_02_guides/) - 所有实践文档
4. [性能优化](./tier_04_advanced/05_性能优化.md)

---

## 🎯 按场景导航

### 控制流选择

| 需求     | 推荐方案         | 文档                                                |
| :--- | :--- | :--- || 条件分支 | if/else、match   | [条件语句指南](./tier_02_guides/01_条件语句指南.md) |
| 循环迭代 | for、while、loop | [循环结构指南](./tier_02_guides/02_循环结构指南.md) |
| 模式匹配 | match、if let    | [模式匹配指南](./tier_02_guides/04_模式匹配指南.md) |
| 错误处理 | Result、?运算符  | [错误处理指南](./tier_02_guides/05_错误处理指南.md) |

### 函数编程

| 需求     | 推荐方案         | 文档                                                |
| :--- | :--- | :--- || 高阶函数 | 闭包、Fn traits  | [闭包深入](./tier_04_advanced/02_闭包深入.md)       |
| 函数组合 | 组合子、链式调用 | [代码示例集合](./tier_02_guides/06_代码示例集合.md) |
| 惰性求值 | 迭代器           | [迭代器参考](./tier_03_references/02_迭代器参考.md) |

---

## 🔗 相关资源

### 项目文档

- [顶层 README](../README.md) - 项目概述
- [文档标准](./DOCUMENTATION_STANDARD.md) - 文档规范
- [文档索引](./DOCUMENTATION_INDEX.md) - 详细索引

### 工具与配置

- **Cargo.toml**: 依赖配置
- **examples/**: 示例代码
- **tests/**: 测试用例

---

## 📊 项目统计

### 文档规模

- **理论文档**: 3 个
- **基础文档**: 6 个
- **高级文档**: 10 个
- **实践文档**: 5 个
- **特性文档**: 4+ 个

### 内容覆盖

- **控制流结构**: if/match/loop/for/while
- **函数特性**: 闭包、高阶函数、Fn traits
- **错误处理**: Result/Option/?运算符
- **Rust 1.92.0**: 改进的自动特征和 `Sized` 边界处理、增强的高阶生命周期区域处理、改进的 `unused_must_use` Lint 行为

---

## 🆕 最新更新

### 2025-12-11

- ✅ 更新到 Rust 1.92.0
- ✅ 完善导航结构
- ✅ 统一文档格式

### Rust 1.92.0 特性

- ✅ `MaybeUninit` 表示和有效性文档化
- ✅ 联合体字段的原始引用安全访问
- ✅ 改进的自动特征和 `Sized` 边界处理
- ✅ 零大小数组的优化处理
- ✅ `#[track_caller]` 和 `#[no_mangle]` 的组合使用
- ✅ 更严格的 Never 类型 Lint
- ✅ 关联项的多个边界
- ✅ 增强的高阶生命周期区域处理
- ✅ 改进的 `unused_must_use` Lint 行为

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
**Rust 版本**: 1.92.0+
