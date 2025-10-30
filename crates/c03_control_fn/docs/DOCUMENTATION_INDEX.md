# 📚 C03 控制流与函数 - 完整文档索引

## 📊 目录

- [📚 C03 控制流与函数 - 完整文档索引](#-c03-控制流与函数---完整文档索引)
  - [📊 目录](#-目录)
  - [📖 文档组织结构](#-文档组织结构)
  - [🎯 学习路径导航](#-学习路径导航)
    - [🚀 初学者路径（2-3周）](#-初学者路径2-3周)
    - [🎓 进阶路径（3-4周）](#-进阶路径3-4周)
    - [🔬 专家路径（4-6周）](#-专家路径4-6周)
  - [📂 分类索引](#-分类索引)
    - [01. 理论基础 (Theory)](#01-理论基础-theory)
    - [02. 基础知识 (Basics)](#02-基础知识-basics)
    - [03. 高级主题 (Advanced)](#03-高级主题-advanced)
    - [04. 实践应用 (Practice)](#04-实践应用-practice)
    - [05. Rust 版本特性 (Rust Features)](#05-rust-版本特性-rust-features)
    - [06. 参考资料 (References)](#06-参考资料-references)
  - [🔍 按主题查找](#-按主题查找)
    - [条件控制](#条件控制)
    - [循环与迭代](#循环与迭代)
    - [函数与闭包](#函数与闭包)
    - [错误处理](#错误处理)
    - [性能优化](#性能优化)
    - [设计模式](#设计模式)
  - [💻 代码示例](#-代码示例)
  - [📊 学习建议](#-学习建议)
    - [时间规划](#时间规划)
    - [学习方法](#学习方法)
    - [检查清单](#检查清单)
  - [🔗 外部资源](#-外部资源)
    - [官方资源](#官方资源)
    - [相关模块](#相关模块)
  - [📝 文档贡献](#-文档贡献)
  - [📞 获取帮助](#-获取帮助)

本文档提供 c03_control_fn 模块所有文档的完整索引和导航指南。

## 📖 文档组织结构

文档按照难度和主题分为六个主要部分：

```text
docs/
├── 01_theory/          # 理论基础
├── 02_basics/          # 基础知识
├── 03_advanced/        # 高级主题
├── 04_practice/        # 实践应用
├── 05_rust_features/   # Rust 版本特性
└── 06_references/      # 参考资料
```

## 🎯 学习路径导航

### 🚀 初学者路径（2-3周）

从零开始学习 Rust 控制流：

1. **Week 1：基础概念**
   - [控制流基础概念](02_basics/01_control_flow_fundamentals.md)
   - [条件表达式](02_basics/02_conditional_expressions.md)
   - [迭代结构](02_basics/03_iterative_constructs.md)

2. **Week 2：函数与错误**
   - [函数与闭包](02_basics/04_functions_and_closures.md)
   - [错误处理控制流](02_basics/05_error_handling_as_control_flow.md)

3. **Week 3：新特性与实践**
   - [控制流总览（Rust 1.90）](02_basics/06_control_flow_overview_1_90.md)
   - [函数与闭包实践](04_practice/01_functions_closures_practice.md)

### 🎓 进阶路径（3-4周）

深入学习高级特性：

1. **Week 1-2：高级控制流**
   - [高级控制流技术](03_advanced/01_advanced_control_flow.md)
   - [高级模式匹配](03_advanced/02_pattern_matching_advanced_1_90.md)
   - [Match 人体工程学](03_advanced/03_match_ergonomics_and_binding_1_90.md)
   - [Let-Else 模式](03_advanced/04_let_else_patterns_handbook_1_90.md)
   - [标签块与 Break 值](03_advanced/05_labeled_blocks_and_break_values_1_90.md)

2. **Week 3：函数特性**
   - [闭包与 Fn Traits](03_advanced/06_closures_and_fn_traits_1_90.md)
   - [循环与迭代器控制](03_advanced/07_loops_and_iterators_control_1_90.md)

3. **Week 4：特殊类型**
   - [Never 类型实践](03_advanced/08_never_type_practices_1_90.md)
   - [Try 块高级用法](03_advanced/09_try_blocks_advanced_1_90.md)
   - [While If Let 链](03_advanced/10_while_if_let_chains_1_90.md)

### 🔬 专家路径（4-6周）

理论与实践结合：

1. **理论深入**
   - [控制流形式化基础](01_theory/01_control_flow_foundations.md)
   - [类型系统与控制流](01_theory/02_type_system_integration.md)
   - [所有权与控制流](01_theory/03_ownership_control_flow.md)

2. **实践应用**
   - [错误处理实践](04_practice/02_error_handling_practice.md)
   - [控制流性能实践](04_practice/03_control_flow_performance_practices_1_90.md)
   - [控制流设计模式](04_practice/04_control_flow_design_patterns.md)
   - [常见陷阱与解决方案](04_practice/05_common_pitfalls.md)

3. **版本特性**
   - [Rust 1.89 特性汇总](05_rust_features/)

## 📂 分类索引

### 01. 理论基础 (Theory)

深入理解控制流的理论基础：

| 文档 | 难度 | 主题 | 推荐读者 |
|------|------|------|---------|
| [01_control_flow_foundations.md](01_theory/01_control_flow_foundations.md) | ⭐⭐ | 形式化语义、设计哲学 | 所有开发者 |
| [02_type_system_integration.md](01_theory/02_type_system_integration.md) | ⭐⭐⭐ | 类型检查、穷尽性 | 中级以上 |
| [03_ownership_control_flow.md](01_theory/03_ownership_control_flow.md) | ⭐⭐⭐⭐ | 借用检查器、生命周期 | 中级以上 |

**何时阅读**：

- 想深入理解 Rust 设计原理
- 需要理解编译器错误的根源
- 准备贡献 Rust 编译器或工具

### 02. 基础知识 (Basics)

掌握控制流的基本使用：

| 文档 | 难度 | 核心内容 | 预计时间 |
|------|------|---------|---------|
| [01_control_flow_fundamentals.md](02_basics/01_control_flow_fundamentals.md) | ⭐ | if/match/loop/异步 | 2-3h |
| [02_conditional_expressions.md](02_basics/02_conditional_expressions.md) | ⭐ | if/match 详解 | 1-2h |
| [03_iterative_constructs.md](02_basics/03_iterative_constructs.md) | ⭐⭐ | loop/while/for | 2-3h |
| [04_functions_and_closures.md](02_basics/04_functions_and_closures.md) | ⭐⭐ | 函数/闭包基础 | 3-4h |
| [05_error_handling_as_control_flow.md](02_basics/05_error_handling_as_control_flow.md) | ⭐⭐⭐ | Result/Option/? | 3-4h |
| [06_control_flow_overview_1_90.md](02_basics/06_control_flow_overview_1_90.md) | ⭐⭐ | Rust 1.90 特性 | 2h |

**何时阅读**：

- Rust 初学者
- 需要快速入门控制流
- 作为参考手册查阅

### 03. 高级主题 (Advanced)

掌握高级特性和技巧：

| 文档 | 难度 | 核心内容 | Rust 版本 |
|------|------|---------|-----------|
| [01_advanced_control_flow.md](03_advanced/01_advanced_control_flow.md) | ⭐⭐⭐ | 复杂控制流技巧 | All |
| [02_pattern_matching_advanced_1_90.md](03_advanced/02_pattern_matching_advanced_1_90.md) | ⭐⭐⭐⭐ | 高级模式匹配 | 1.90+ |
| [03_match_ergonomics_and_binding_1_90.md](03_advanced/03_match_ergonomics_and_binding_1_90.md) | ⭐⭐⭐ | Match 人体工程学 | 1.90+ |
| [04_let_else_patterns_handbook_1_90.md](03_advanced/04_let_else_patterns_handbook_1_90.md) | ⭐⭐⭐ | let-else 语法 | 1.90+ |
| [05_labeled_blocks_and_break_values_1_90.md](03_advanced/05_labeled_blocks_and_break_values_1_90.md) | ⭐⭐⭐ | 标签与 break 值 | 1.90+ |
| [06_closures_and_fn_traits_1_90.md](03_advanced/06_closures_and_fn_traits_1_90.md) | ⭐⭐⭐⭐ | 闭包特征系统 | 1.90+ |
| [07_loops_and_iterators_control_1_90.md](03_advanced/07_loops_and_iterators_control_1_90.md) | ⭐⭐⭐⭐ | 迭代器高级应用 | 1.90+ |
| [08_never_type_practices_1_90.md](03_advanced/08_never_type_practices_1_90.md) | ⭐⭐⭐⭐ | ! 类型应用 | 1.90+ |
| [09_try_blocks_advanced_1_90.md](03_advanced/09_try_blocks_advanced_1_90.md) | ⭐⭐⭐ | try 块语法 | 1.90+ |
| [10_while_if_let_chains_1_90.md](03_advanced/10_while_if_let_chains_1_90.md) | ⭐⭐⭐ | 模式匹配链 | 1.90+ |

**何时阅读**：

- 已掌握基础知识
- 需要使用 Rust 1.90 新特性
- 优化现有代码

### 04. 实践应用 (Practice)

工程实践和最佳实践：

| 文档 | 难度 | 核心内容 | 适用场景 |
|------|------|---------|---------|
| [01_functions_closures_practice.md](04_practice/01_functions_closures_practice.md) | ⭐⭐⭐ | 函数设计、API 设计 | 库开发 |
| [02_error_handling_practice.md](04_practice/02_error_handling_practice.md) | ⭐⭐⭐ | 错误处理策略 | 所有项目 |
| [03_control_flow_performance_practices_1_90.md](04_practice/03_control_flow_performance_practices_1_90.md) | ⭐⭐⭐⭐ | 性能优化 | 高性能应用 |
| [04_control_flow_design_patterns.md](04_practice/04_control_flow_design_patterns.md) | ⭐⭐⭐⭐ | 设计模式 | 架构设计 |
| [05_common_pitfalls.md](04_practice/05_common_pitfalls.md) | ⭐⭐⭐ | 常见错误避免 | 所有开发者 |

**何时阅读**：

- 开始实际项目开发
- 代码审查时参考
- 遇到性能问题时

### 05. Rust 版本特性 (Rust Features)

Rust 1.89 版本特性文档：

| 文档 | 内容概述 |
|------|---------|
| `RUST_189_FEATURES_SUMMARY.md` | 特性总结 |
| `RUST_189_ENHANCED_FEATURES.md` | 增强特性详解 |
| `RUST_189_COMPREHENSIVE_FEATURES.md` | 全面特性分析 |
| `RUST_189_MIGRATION_GUIDE.md` | 版本迁移指南 |
| `RUST_189_PRACTICAL_GUIDE.md` | 实践应用指南 |
| `RUST_189_BASIC_SYNTAX_COMPREHENSIVE_GUIDE.md` | 基础语法指南 |
| `RUST_189_CONTROL_FLOW_FUNCTIONS_FULL_GUIDE.md` | 控制流完整指南 |

### 06. 参考资料 (References)

快速参考和辅助材料：

| 文档 | 用途 |
|------|------|
| `FAQ.md` | 常见问题解答 |
| `Glossary.md` | 术语表 |
| `view01.md` | 控制流基础视图 |
| `view02.md` | 控制流高级视图 |

## 🔍 按主题查找

### 条件控制

- [条件表达式](02_basics/02_conditional_expressions.md)
- [高级模式匹配](03_advanced/02_pattern_matching_advanced_1_90.md)
- [Match 人体工程学](03_advanced/03_match_ergonomics_and_binding_1_90.md)
- [Let-Else 模式](03_advanced/04_let_else_patterns_handbook_1_90.md)

### 循环与迭代

- [迭代结构](02_basics/03_iterative_constructs.md)
- [标签块与 Break 值](03_advanced/05_labeled_blocks_and_break_values_1_90.md)
- [循环与迭代器控制](03_advanced/07_loops_and_iterators_control_1_90.md)

### 函数与闭包

- [函数与闭包基础](02_basics/04_functions_and_closures.md)
- [闭包与 Fn Traits](03_advanced/06_closures_and_fn_traits_1_90.md)
- [函数与闭包实践](04_practice/01_functions_closures_practice.md)

### 错误处理

- [错误处理控制流](02_basics/05_error_handling_as_control_flow.md)
- [Try 块高级用法](03_advanced/09_try_blocks_advanced_1_90.md)
- [错误处理实践](04_practice/02_error_handling_practice.md)

### 性能优化

- [控制流性能实践](04_practice/03_control_flow_performance_practices_1_90.md)
- [常见陷阱](04_practice/05_common_pitfalls.md)

### 设计模式

- [控制流设计模式](04_practice/04_control_flow_design_patterns.md)
- [高级控制流技术](03_advanced/01_advanced_control_flow.md)

## 💻 代码示例

每个文档都包含可运行的代码示例。运行示例：

```bash
# 查看所有示例
ls examples/

# 运行特定示例
cargo run --example control_flow_example
cargo run --example pattern_matching_advanced
cargo run --example closures_and_fn_traits

# 运行所有测试
cargo test

# 运行性能测试
cargo bench
```

## 📊 学习建议

### 时间规划

| 级别 | 推荐时间 | 学习内容 |
|------|---------|---------|
| 初学者 | 2-3周 | 基础知识全部 |
| 进阶者 | 3-4周 | 高级主题全部 |
| 专家级 | 4-6周 | 理论+实践+特性 |

### 学习方法

1. **循序渐进**：按照推荐路径学习
2. **动手实践**：运行并修改示例代码
3. **深入理解**：阅读理论部分理解原理
4. **项目应用**：在实际项目中应用所学
5. **持续更新**：关注 Rust 新版本特性

### 检查清单

- [ ] 完成基础知识部分所有文档
- [ ] 运行所有基础示例代码
- [ ] 完成高级主题部分所有文档
- [ ] 理解所有设计模式
- [ ] 能够避免常见陷阱
- [ ] 完成至少一个实战项目
- [ ] 能够优化控制流性能
- [ ] 理解 Rust 1.90 新特性

## 🔗 外部资源

### 官方资源

- [Rust Book - Control Flow](https://doc.rust-lang.org/book/ch03-05-control-flow.html)
- [Rust Reference - Expressions](https://doc.rust-lang.org/reference/expressions.html)
- [Rust by Example - Flow Control](https://doc.rust-lang.org/rust-by-example/flow_control.html)

### 相关模块

- `c01_ownership_borrow_scope` - 所有权与借用
- `c02_type_system` - 类型系统
- `c06_async` - 异步编程
- `c09_design_pattern` - 设计模式

## 📝 文档贡献

欢迎对文档进行改进：

1. 发现错误 → 提交 Issue
2. 改进文档 → 提交 Pull Request
3. 添加示例 → 贡献代码
4. 翻译文档 → 提供多语言版本

## 📞 获取帮助

- **文档问题**：查看 [FAQ](06_references/FAQ.md)
- **代码问题**：查看 [常见陷阱](04_practice/05_common_pitfalls.md)
- **术语疑问**：查看 [术语表](06_references/Glossary.md)
- **学习指导**：参考学习路径

---

*最后更新：2025年1月*
*文档版本：v2.0*
*Rust 版本：1.90+*
*总文档数：30+*
