# 📖 C11宏系统 - 主索引

> **学习导航**: C11宏系统模块的完整学习路径和资源导航
> **最后更新**: 2026-03-13
> **适用版本**: Rust 1.94.0+

📄 **一页纸总结**: [ONE_PAGE_SUMMARY](./ONE_PAGE_SUMMARY.md) - 核心概念、常见坑、速选表、学习路径

## 📚 官方资源映射

| 官方资源 | 链接 | 与本模块对应 |
| :--- | :--- | :--- || **The Rust Book** | [Ch. 19.5 Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) | 宏基础 |
| **RBE 练习** | [Macros](https://doc.rust-lang.org/rust-by-example/macros.html) | 声明宏实践 |
| **Rust Reference** | [Macros](https://doc.rust-lang.org/reference/macros.html) | 宏规范 |
| **The Little Book of Rust Macros** | [dtolnay/rust-macros](https://danielkeep.github.io/tlborm/book/) | 宏深入 |

---

## 📋 目录

- [📖 C11宏系统 - 主索引](#-c11宏系统---主索引)
  - [📚 官方资源映射](#-官方资源映射)
  - [📋 目录](#-目录)
  - [🎯 模块概述](#-模块概述)
    - [学习目标](#学习目标)
  - [📚 学习路径](#-学习路径)
    - [🌱 初学者路径 (2-3周)](#-初学者路径-2-3周)
      - [Week 1: 宏基础](#week-1-宏基础)
      - [Week 2-3: 递归宏与实践](#week-2-3-递归宏与实践)
    - [🚀 进阶路径 (3-4周)](#-进阶路径-3-4周)
      - [Week 4-5: 过程宏](#week-4-5-过程宏)
      - [Week 6-7: 高级应用](#week-6-7-高级应用)
      - [Week 8: Rust 1.92.0特性（自 Rust 1.90 引入）](#week-8-rust-1920特性自-rust-190-引入)
  - [📖 文档结构](#-文档结构)
    - [tier\_01\_foundations / tier\_02\_guides - 基础与指南](#tier_01_foundations--tier_02_guides---基础与指南)
    - [tier\_02\_guides - 声明宏与过程宏](#tier_02_guides---声明宏与过程宏)
    - [tier\_03\_references - 参考](#tier_03_references---参考)
    - [tier\_04\_advanced - 高级主题](#tier_04_advanced---高级主题)
    - [📦 Rust 1.92.0 宏特性](#-rust-1920-宏特性)
    - [🧠 思维表征 (docs/04\_thinking)](#-思维表征-docs04_thinking)
  - [💻 代码示例](#-代码示例)
    - [运行示例](#运行示例)
    - [示例列表](#示例列表)
  - [🎓 按角色导航](#-按角色导航)
    - [我是新手](#我是新手)
    - [我有Rust基础](#我有rust基础)
    - [我想深入理解](#我想深入理解)
  - [🔍 按主题导航](#-按主题导航)
    - [声明宏 (macro\_rules!)](#声明宏-macro_rules)
    - [过程宏 (Procedural Macros)](#过程宏-procedural-macros)
    - [Rust 1.92.0特性](#rust-1920特性)
    - [DSL与代码生成](#dsl与代码生成)
  - [🛠️ 工具与资源](#️-工具与资源)
    - [开发工具](#开发工具)
    - [调试工具](#调试工具)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [社区资源](#社区资源)
    - [本模块资源](#本模块资源)
    - [深度学习资源 ⭐](#深度学习资源-)
  - [✅ 学习检查清单](#-学习检查清单)
    - [基础知识 (必须掌握)](#基础知识-必须掌握)
    - [进阶技能 (建议掌握)](#进阶技能-建议掌握)
    - [高级能力 (深入方向)](#高级能力-深入方向)
  - [🎯 下一步](#-下一步)

## 🎯 模块概述

Rust宏系统是一个强大的元编程框架，允许在编译期进行代码生成和转换。本模块提供从基础到高级的系统化学习内容。

### 学习目标

完成本模块后，你将能够：

- ✅ 理解宏的基本概念和工作原理
- ✅ 使用`macro_rules!`编写声明宏
- ✅ 实现三种类型的过程宏
- ✅ 构建领域特定语言(DSL)
- ✅ 调试和优化宏性能

---

## 📚 学习路径

### 🌱 初学者路径 (2-3周)

#### Week 1: 宏基础

**第1天-2天: 理论基础**:

- [ ] [宏基础理论](./tier_02_guides/01_声明宏实践指南.md)
- [ ] [卫生宏与作用域](./tier_03_references/04_宏卫生性参考.md)
- [ ] 运行示例: `01_macro_rules_basics.rs`

**第3天-4天: 声明宏入门**:

- [ ] [macro_rules!基础](./tier_02_guides/01_声明宏实践指南.md)
- [ ] [模式匹配](./tier_03_references/01_声明宏完整参考.md)
- [ ] 运行示例: `02_pattern_matching.rs`

**第5天-7天: 声明宏进阶**:

- [ ] [重复语法](./tier_03_references/01_声明宏完整参考.md)
- [ ] [高级模式](./tier_03_references/01_声明宏完整参考.md)
- [ ] 运行示例: `03_repetition.rs`

#### Week 2-3: 递归宏与实践

**Week 2**:

- [ ] [递归宏](./tier_02_guides/01_声明宏实践指南.md)
- [ ] 运行示例: `04_recursive_macros.rs`
- [ ] 完成练习: 实现5个自定义宏

**Week 3**:

- [ ] [常用模式](./tier_04_advanced/05_生产级宏开发.md)
- [ ] [最佳实践](./tier_04_advanced/05_生产级宏开发.md)
- [ ] 项目实战: 创建宏库

### 🚀 进阶路径 (3-4周)

#### Week 4-5: 过程宏

**派生宏 (Derive Macros)**:

- [ ] [过程宏基础](./tier_02_guides/02_Derive宏开发指南.md)
- [ ] [派生宏](./tier_02_guides/02_Derive宏开发指南.md)
- [ ] 实践: 实现Builder派生宏

**属性宏 (Attribute Macros)**:

- [ ] [属性宏](./tier_02_guides/03_属性宏开发指南.md)
- [ ] 实践: 实现路由属性宏

**函数式宏 (Function-like Macros)**:

- [ ] [函数式宏](./tier_02_guides/04_函数宏开发指南.md)
- [ ] 实践: 实现SQL查询宏

**Token流处理**:

- [ ] [Token流](./tier_03_references/02_过程宏API参考.md)

#### Week 6-7: 高级应用

**DSL构建**:

- [ ] [DSL构建技术](./tier_04_advanced/02_DSL构建实践.md)
- [ ] 实践: 实现配置DSL

**代码生成**:

- [ ] [代码生成](./tier_04_advanced/03_代码生成优化.md)
- [ ] [性能考量](./tier_04_advanced/03_代码生成优化.md)

**调试与测试**:

- [ ] [宏调试](./tier_04_advanced/04_宏调试深化.md)
- [ ] [宏测试](./tier_02_guides/05_宏调试与测试.md)

#### Week 8: Rust 1.92.0特性（自 Rust 1.90 引入）

**版本特性掌握**:

- [ ] [Rust 1.92.0特性总览](./RUST_192_MACRO_IMPROVEMENTS.md)
- [ ] [完整特性清单](./RUST_192_MACRO_IMPROVEMENTS.md)
- [ ] [实例代码学习](./RUST_192_MACRO_IMPROVEMENTS.md)
- [ ] 实践: 使用最新特性重构现有宏

---

## 📖 文档结构

### tier_01_foundations / tier_02_guides - 基础与指南

| 文档                                                               | 难度   | 预计时间 |
| :--- | :--- | :--- || [01_声明宏实践指南](./tier_02_guides/01_声明宏实践指南.md)         | ⭐     | 2小时    |
| [04_宏卫生性参考](./tier_03_references/04_宏卫生性参考.md)         | ⭐⭐   | 2小时    |
| [01_声明宏完整参考](./tier_03_references/01_声明宏完整参考.md)     | ⭐⭐   | 3小时    |
| [01_宏元编程](./tier_04_advanced/01_宏元编程.md)                   | ⭐⭐⭐ | 4小时    |

### tier_02_guides - 声明宏与过程宏

| 文档                                                                  | 难度   | 预计时间 |
| :--- | :--- | :--- || [01_声明宏实践指南](./tier_02_guides/01_声明宏实践指南.md)            | ⭐     | 2小时    |
| [02_Derive宏开发指南](./tier_02_guides/02_Derive宏开发指南.md)       | ⭐⭐⭐ | 5小时    |
| [03_属性宏开发指南](./tier_02_guides/03_属性宏开发指南.md)           | ⭐⭐⭐ | 5小时    |
| [04_函数宏开发指南](./tier_02_guides/04_函数宏开发指南.md)           | ⭐⭐⭐ | 5小时    |
| [05_宏调试与测试](./tier_02_guides/05_宏调试与测试.md)                | ⭐⭐   | 4小时    |

### tier_03_references - 参考

| 文档                                                               | 难度     | 预计时间 |
| :--- | :--- | :--- || [01_声明宏完整参考](./tier_03_references/01_声明宏完整参考.md)      | ⭐⭐     | 3小时    |
| [02_过程宏API参考](./tier_03_references/02_过程宏API参考.md)       | ⭐⭐⭐   | 5小时    |
| [04_宏卫生性参考](./tier_03_references/04_宏卫生性参考.md)          | ⭐⭐     | 2小时    |

### tier_04_advanced - 高级主题

| 文档                                                                  | 难度       | 预计时间 |
| :--- | :--- | :--- || [01_宏元编程](./tier_04_advanced/01_宏元编程.md)                       | ⭐⭐⭐⭐   | 6小时    |
| [02_DSL构建实践](./tier_04_advanced/02_DSL构建实践.md)                 | ⭐⭐⭐⭐⭐ | 8小时    |
| [03_代码生成优化](./tier_04_advanced/03_代码生成优化.md)               | ⭐⭐⭐⭐   | 6小时    |
| [04_宏调试深化](./tier_04_advanced/04_宏调试深化.md)                   | ⭐⭐⭐     | 4小时    |
| [05_生产级宏开发](./tier_04_advanced/05_生产级宏开发.md)              | ⭐⭐⭐     | 4小时    |

### 📦 Rust 1.92.0 宏特性

| 文档                                                                          | 难度     | 预计时间 |
| :--- | :--- | :--- || [RUST_192_MACRO_IMPROVEMENTS](./RUST_192_MACRO_IMPROVEMENTS.md)               | ⭐       | 30分钟   |
| [RUST_192_MACRO_IMPROVEMENTS](./RUST_192_MACRO_IMPROVEMENTS.md)                | ⭐⭐⭐⭐ | 4小时    |

### 🧠 思维表征 (docs/04_thinking)

| 文档                                                                                                      | 难度     | 预计时间 |
| :--- | :--- | :--- || [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../../docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md)             | ⭐⭐⭐   | 2小时    |
| [MIND_MAP_COLLECTION](../../docs/04_thinking/MIND_MAP_COLLECTION.md)                                      | ⭐⭐     | 1.5小时  |

---

## 💻 代码示例

### 运行示例

```bash
# 查看所有示例
cargo run --example --list

# 运行特定示例
cargo run --example 01_macro_rules_basics
cargo run --example 02_pattern_matching
cargo run --example 03_repetition
cargo run --example 04_recursive_macros
```

### 示例列表

| 示例                         | 主题       | 难度     |
| :--- | :--- | :--- || `01_macro_rules_basics.rs`   | 声明宏基础 | ⭐       |
| `02_pattern_matching.rs`     | 模式匹配   | ⭐⭐     |
| `03_repetition.rs`           | 重复语法   | ⭐⭐     |
| `04_recursive_macros.rs`     | 递归宏     | ⭐⭐⭐   |
| `05_derive_macro_demo.rs`    | 派生宏     | ⭐⭐⭐   |
| `06_attribute_macro_demo.rs` | 属性宏     | ⭐⭐⭐   |
| `07_function_macro_demo.rs`  | 函数式宏   | ⭐⭐⭐   |
| `08_dsl_example.rs`          | DSL构建    | ⭐⭐⭐⭐ |

---

## 🎓 按角色导航

### 我是新手

**学习顺序**:

1. 从[宏基础理论](./tier_02_guides/01_声明宏实践指南.md)开始
2. 学习[macro_rules!基础](./tier_02_guides/01_声明宏实践指南.md)
3. 运行示例 `01_macro_rules_basics.rs`
4. 查看[FAQ](./FAQ.md)解答疑惑

**推荐资源**:

- [快速参考](../README.md#快速参考)
- [术语表](./Glossary.md)

### 我有Rust基础

**快速通道**:

1. 浏览[理论文档](./tier_02_guides/01_声明宏实践指南.md)
2. 直接学习[声明宏](./tier_02_guides/01_声明宏实践指南.md)
3. 完成所有基础示例
4. 进入[过程宏](./tier_02_guides/02_Derive宏开发指南.md)学习

### 我想深入理解

**深度路径**:

1. 详细学习[宏理论](./tier_04_advanced/01_宏元编程.md)
2. 研究[展开机制](./tier_03_references/01_声明宏完整参考.md)
3. 掌握[Token流](./tier_03_references/02_过程宏API参考.md)
4. 实践[DSL构建](./tier_04_advanced/02_DSL构建实践.md)

---

## 🔍 按主题导航

### 声明宏 (macro_rules!)

**核心文档**:

- [基础语法](./tier_02_guides/01_声明宏实践指南.md)
- [模式匹配](./tier_03_references/01_声明宏完整参考.md)
- [递归实现](./tier_02_guides/01_声明宏实践指南.md)

**示例**:

- `01_macro_rules_basics.rs`
- `04_recursive_macros.rs`

### 过程宏 (Procedural Macros)

**三种类型**:

1. [派生宏](./tier_02_guides/02_Derive宏开发指南.md) - `#[derive(Trait)]`
2. [属性宏](./tier_02_guides/03_属性宏开发指南.md) - `#[attribute]`
3. [函数式宏](./tier_02_guides/04_函数宏开发指南.md) - `macro!()`

**示例**:

- `05_derive_macro_demo.rs`
- `06_attribute_macro_demo.rs`
- `07_function_macro_demo.rs`

### Rust 1.92.0特性

**核心文档**:

- [RUST_192_MACRO_IMPROVEMENTS](./RUST_192_MACRO_IMPROVEMENTS.md) ⭐ 起点
- [RUST_192_MACRO_IMPROVEMENTS](./RUST_192_MACRO_IMPROVEMENTS.md) - 10大特性板块

**学习重点**:

- 13种片段说明符
- 过程宏完整API
- TokenStream优化
- 宏卫生性增强
- 诊断与错误报告

### DSL与代码生成

**核心主题**:

- [DSL构建](./tier_04_advanced/02_DSL构建实践.md)
- [代码生成](./tier_04_advanced/03_代码生成优化.md)

**示例**:

- `08_dsl_example.rs`
- `09_code_generation.rs`

---

## 🛠️ 工具与资源

### 开发工具

**cargo-expand** - 查看宏展开

```bash
cargo install cargo-expand
cargo expand --example 01_macro_rules_basics
```

**rust-analyzer** - IDE支持

- VSCode插件
- 宏展开提示
- 语法高亮

### 调试工具

**trace_macros** - 跟踪宏展开

```rust
#![feature(trace_macros)]
trace_macros!(true);
```

**log_syntax** - 打印语法

```rust
#![feature(log_syntax)]
```

---

## 📚 相关资源

### 官方文档

- [The Rust Book - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [The Rust Reference](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)

### 社区资源

- [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop)
- [syn](https://docs.rs/syn/) - 语法解析
- [quote](https://docs.rs/quote/) - 代码生成

### 本模块资源

- [README](../README.md) - 模块总览
- [FAQ](./FAQ.md) - 常见问题
- [Glossary](./Glossary.md) - 术语表

### 深度学习资源 ⭐

- [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../../docs/04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md) - 系统化知识体系
- [MIND_MAP_COLLECTION](../../docs/04_thinking/MIND_MAP_COLLECTION.md) - 可视化学习

---

## ✅ 学习检查清单

### 基础知识 (必须掌握)

- [ ] 理解宏与函数的区别
- [ ] 掌握`macro_rules!`基本语法
- [ ] 了解宏卫生(Hygiene)
- [ ] 能够编写简单的声明宏
- [ ] 理解模式匹配规则

### 进阶技能 (建议掌握)

- [ ] 实现递归宏
- [ ] 使用重复语法`$(...)*`
- [ ] 理解Token流概念
- [ ] 创建派生宏
- [ ] 实现属性宏

### 高级能力 (深入方向)

- [ ] 构建DSL
- [ ] 优化宏性能
- [ ] 掌握Rust 1.92.0最新特性
- [ ] 理解TokenStream优化
- [ ] 调试复杂宏
- [ ] 设计宏API
- [ ] 在生产环境使用宏

---

## 🎯 下一步

根据你的学习目标选择：

1. **系统学习** → 按[初学者路径](#-初学者路径-2-3周)开始
2. **快速上手** → 直接运行[示例代码](#运行示例)
3. **解决问题** → 查看[FAQ](./FAQ.md)
4. **深入理解** → 阅读[理论文档](./tier_02_guides/01_声明宏实践指南.md)

---

**开始学习！** 🚀

从第一个示例开始：

```bash
cargo run --example 01_macro_rules_basics
```

**最后更新**: 2025-12-11
**维护者**: Rust学习社区
