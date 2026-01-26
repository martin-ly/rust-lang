# 🔗 文档交叉引用指南

> **文档类型**: 文档管理指南
> **最后更新**: 2026-01-27
> **适用版本**: Rust 1.93.0+

---

## 📋 目录

- [🔗 文档交叉引用指南](#-文档交叉引用指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
  - [交叉引用结构](#交叉引用结构)
    - [文档层级](#文档层级)
  - [核心模块文档链接](#核心模块文档链接)
    - [C01 - 所有权与借用](#c01---所有权与借用)
    - [C02 - 类型系统](#c02---类型系统)
    - [C03 - 控制流与函数](#c03---控制流与函数)
    - [C04 - 泛型编程](#c04---泛型编程)
    - [C05 - 线程与并发](#c05---线程与并发)
    - [C06 - 异步编程](#c06---异步编程)
    - [C07 - 进程管理](#c07---进程管理)
    - [C08 - 算法与数据结构](#c08---算法与数据结构)
    - [C09 - 设计模式](#c09---设计模式)
    - [C10 - 网络编程](#c10---网络编程)
    - [C11 - 宏系统](#c11---宏系统)
    - [C12 - WASM](#c12---wasm)
  - [快速参考链接](#快速参考链接)
    - [所有速查卡](#所有速查卡)
  - [研究笔记链接](#研究笔记链接)
    - [形式化方法研究](#形式化方法研究)
    - [类型理论研究](#类型理论研究)
  - [最佳实践](#最佳实践)
    - [1. 使用相对路径](#1-使用相对路径)
    - [2. 提供描述性链接文本](#2-提供描述性链接文本)
    - [3. 维护链接完整性](#3-维护链接完整性)
  - [📚 相关资源](#-相关资源)
    - [核心文档](#核心文档)
    - [高级文档](#高级文档)

---

## 概述

本文档提供项目中所有文档的交叉引用指南，帮助开发者快速找到相关文档。

---

## 交叉引用结构

### 文档层级

```
项目根目录
├── README.md (主入口)
├── docs/
│   ├── README.md (文档中心)
│   ├── quick_reference/ (19个速查卡)
│   ├── research_notes/ (研究笔记系统)
│   ├── ADVANCED_TOPICS_DEEP_DIVE.md (高级主题)
│   ├── COMPREHENSIVE_BEST_PRACTICES.md (最佳实践)
│   └── PERFORMANCE_TESTING_REPORT.md (性能测试)
└── crates/
    └── c##_module_name/
        ├── README.md
        └── docs/
            └── tier_01_foundations/
                └── 02_主索引导航.md
```

---

## 核心模块文档链接

### C01 - 所有权与借用

- **主索引**: [c01_ownership_borrow_scope/docs/tier_01_foundations/02_主索引导航.md](../crates/c01_ownership_borrow_scope/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [ownership_cheatsheet.md](./quick_reference/ownership_cheatsheet.md)
- **研究笔记**: [ownership_model.md](./research_notes/formal_methods/ownership_model.md)

### C02 - 类型系统

- **主索引**: [c02_type_system/docs/tier_01_foundations/02_主索引导航.md](../crates/c02_type_system/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [type_system.md](./quick_reference/type_system.md)
- **研究笔记**: [type_system_foundations.md](./research_notes/type_theory/type_system_foundations.md)

### C03 - 控制流与函数

- **主索引**: [c03_control_fn/docs/tier_01_foundations/02_主索引导航.md](../crates/c03_control_fn/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [control_flow_functions_cheatsheet.md](./quick_reference/control_flow_functions_cheatsheet.md)

### C04 - 泛型编程

- **主索引**: [c04_generic/docs/tier_01_foundations/02_主索引导航.md](../crates/c04_generic/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [generics_cheatsheet.md](./quick_reference/generics_cheatsheet.md)

### C05 - 线程与并发

- **主索引**: [c05_threads/docs/tier_01_foundations/02_主索引导航.md](../crates/c05_threads/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [threads_concurrency_cheatsheet.md](./quick_reference/threads_concurrency_cheatsheet.md)

### C06 - 异步编程

- **主索引**: [c06_async/docs/tier_01_foundations/02_主索引导航.md](../crates/c06_async/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [async_patterns.md](./quick_reference/async_patterns.md)
- **研究笔记**: [async_state_machine.md](./research_notes/formal_methods/async_state_machine.md)

### C07 - 进程管理

- **主索引**: [c07_process/docs/tier_01_foundations/02_主索引导航.md](../crates/c07_process/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [process_management_cheatsheet.md](./quick_reference/process_management_cheatsheet.md)

### C08 - 算法与数据结构

- **主索引**: [c08_algorithms/docs/tier_01_foundations/02_主索引导航.md](../crates/c08_algorithms/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [algorithms_cheatsheet.md](./quick_reference/algorithms_cheatsheet.md)

### C09 - 设计模式

- **主索引**: [c09_design_pattern/docs/tier_01_foundations/02_主索引导航.md](../crates/c09_design_pattern/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [design_patterns_cheatsheet.md](./quick_reference/design_patterns_cheatsheet.md)

### C10 - 网络编程

- **主索引**: [c10_networks/docs/tier_01_foundations/02_主索引导航.md](../crates/c10_networks/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [network_programming_cheatsheet.md](./quick_reference/network_programming_cheatsheet.md)

### C11 - 宏系统

- **主索引**: [c11_macro_system/README.md](../crates/c11_macro_system/README.md)
- **速查卡**: [macros_cheatsheet.md](./quick_reference/macros_cheatsheet.md)

### C12 - WASM

- **主索引**: [c12_wasm/docs/tier_01_foundations/02_主索引导航.md](../crates/c12_wasm/docs/tier_01_foundations/02_主索引导航.md)
- **速查卡**: [wasm_cheatsheet.md](./quick_reference/wasm_cheatsheet.md)

---

## 快速参考链接

### 所有速查卡

1. [类型系统速查卡](./quick_reference/type_system.md)
2. [所有权系统速查卡](./quick_reference/ownership_cheatsheet.md)
3. [异步编程速查卡](./quick_reference/async_patterns.md)
4. [泛型编程速查卡](./quick_reference/generics_cheatsheet.md)
5. [错误处理速查卡](./quick_reference/error_handling_cheatsheet.md)
6. [线程与并发速查卡](./quick_reference/threads_concurrency_cheatsheet.md)
7. [宏系统速查卡](./quick_reference/macros_cheatsheet.md)
8. [测试速查卡](./quick_reference/testing_cheatsheet.md)
9. [控制流与函数速查卡](./quick_reference/control_flow_functions_cheatsheet.md)
10. [集合与迭代器速查卡](./quick_reference/collections_iterators_cheatsheet.md)
11. [智能指针速查卡](./quick_reference/smart_pointers_cheatsheet.md)
12. [模块系统速查卡](./quick_reference/modules_cheatsheet.md)
13. [字符串与格式化速查卡](./quick_reference/strings_formatting_cheatsheet.md)
14. [Cargo 速查卡](./quick_reference/cargo_cheatsheet.md)
15. [进程管理速查卡](./quick_reference/process_management_cheatsheet.md)
16. [网络编程速查卡](./quick_reference/network_programming_cheatsheet.md)
17. [算法与数据结构速查卡](./quick_reference/algorithms_cheatsheet.md)
18. [设计模式速查卡](./quick_reference/design_patterns_cheatsheet.md)
19. [WASM 速查卡](./quick_reference/wasm_cheatsheet.md)

**完整索引**: [quick_reference/README.md](./quick_reference/README.md)

---

## 研究笔记链接

### 形式化方法研究

- [所有权模型形式化](./research_notes/formal_methods/ownership_model.md)
- [借用检查器证明](./research_notes/formal_methods/borrow_checker_proof.md)
- [生命周期形式化](./research_notes/formal_methods/lifetime_formalization.md)
- [异步状态机形式化](./research_notes/formal_methods/async_state_machine.md)

### 类型理论研究

- [类型系统基础](./research_notes/type_theory/type_system_foundations.md)
- [Trait系统形式化](./research_notes/type_theory/trait_system_formalization.md)
- [高级类型特性](./research_notes/type_theory/advanced_types.md)

**完整索引**: [research_notes/README.md](./research_notes/README.md)

---

## 最佳实践

### 1. 使用相对路径

**✅ 正确**:

```markdown
[类型系统速查卡](./quick_reference/type_system.md)
[所有权模型形式化](./research_notes/formal_methods/ownership_model.md)
```

**❌ 错误**:

```markdown
[类型系统速查卡](/docs/quick_reference/type_system.md)
```

### 2. 提供描述性链接文本

**✅ 正确**:

```markdown
查看 [类型系统速查卡](./quick_reference/type_system.md) 了解类型系统
```

**❌ 错误**:

```markdown
点击 [这里](./quick_reference/type_system.md)
```

### 3. 维护链接完整性

- 定期检查链接有效性
- 更新过时的链接
- 修复断开的链接

---

## 📚 相关资源

### 核心文档

- [文档中心主索引](./README.md)
- [快速参考索引](./quick_reference/README.md)
- [研究笔记索引](./research_notes/README.md)

### 高级文档

- [高级主题深度指南](./ADVANCED_TOPICS_DEEP_DIVE.md)
- [综合最佳实践指南](./COMPREHENSIVE_BEST_PRACTICES.md)
- [性能测试报告](./PERFORMANCE_TESTING_REPORT.md)
- [跨模块集成示例](../CROSS_MODULE_INTEGRATION_EXAMPLES.md)

---

**报告日期**: 2026-01-27
**维护者**: Rust 项目推进团队
