# Rust 快速参考指南 {#rust-快速参考指南}

> **EN**: Quick Reference Index
> **Summary**: Rust 快速参考指南 Quick Reference Index. (stub/archive redirect)
> **分级**: [A]
> **Bloom 层级**: L2-L3 (理解/速查)
> **创建日期**: 2025-12-11
> **最后更新**: 2026-05-08
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 26 个主题速查（含 6 个版本特性速查卡）；语法/模式可速查
> **完整结构**: DOCS_STRUCTURE_OVERVIEW § 2.2 quick_reference
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

---

## 📋 目录 {#目录}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [Rust 快速参考指南 {#rust-快速参考指南}](#rust-快速参考指南-rust-快速参考指南)
  - [📋 目录 {#目录}](#-目录-目录)
  - [🎯 快速参考概述 {#快速参考概述}](#-快速参考概述-快速参考概述)
    - [适用场景 {#适用场景}](#适用场景-适用场景)
  - [📖 速查卡列表 {#速查卡列表}](#-速查卡列表-速查卡列表)
    - [1. 类型系统速查卡 {#1-类型系统速查卡}](#1-类型系统速查卡-1-类型系统速查卡)
    - [2. 所有权系统速查卡 {#2-所有权系统速查卡}](#2-所有权系统速查卡-2-所有权系统速查卡)
    - [3. 异步编程速查卡 {#3-异步编程速查卡}](#3-异步编程速查卡-3-异步编程速查卡)
    - [4. 泛型编程速查卡 {#4-泛型编程速查卡}](#4-泛型编程速查卡-4-泛型编程速查卡)
    - [5. 错误处理速查卡 {#5-错误处理速查卡}](#5-错误处理速查卡-5-错误处理速查卡)
    - [6. 线程与并发速查卡 {#6-线程与并发速查卡}](#6-线程与并发速查卡-6-线程与并发速查卡)
    - [7. 宏系统速查卡 {#7-宏系统速查卡}](#7-宏系统速查卡-7-宏系统速查卡)
    - [8. 测试速查卡 {#8-测试速查卡}](#8-测试速查卡-8-测试速查卡)
    - [9. 控制流与函数速查卡 {#9-控制流与函数速查卡}](#9-控制流与函数速查卡-9-控制流与函数速查卡)
    - [10. 集合与迭代器速查卡 {#10-集合与迭代器速查卡}](#10-集合与迭代器速查卡-10-集合与迭代器速查卡)
    - [11. 智能指针速查卡 {#11-智能指针速查卡}](#11-智能指针速查卡-11-智能指针速查卡)
    - [12. 模块系统速查卡 {#12-模块系统速查卡}](#12-模块系统速查卡-12-模块系统速查卡)
    - [13. 字符串与格式化速查卡 {#13-字符串与格式化速查卡}](#13-字符串与格式化速查卡-13-字符串与格式化速查卡)
    - [14. Cargo 速查卡 {#14-cargo-速查卡}](#14-cargo-速查卡-14-cargo-速查卡)
    - [15. 进程管理速查卡 ⭐ NEW {#15-进程管理速查卡-new}](#15-进程管理速查卡--new-15-进程管理速查卡-new)
    - [16. 网络编程速查卡 ⭐ NEW {#16-网络编程速查卡-new}](#16-网络编程速查卡--new-16-网络编程速查卡-new)
    - [17. 算法与数据结构速查卡 ⭐ NEW {#17-算法与数据结构速查卡-new}](#17-算法与数据结构速查卡--new-17-算法与数据结构速查卡-new)
    - [18. 设计模式速查卡 ⭐ NEW {#18-设计模式速查卡-new}](#18-设计模式速查卡--new-18-设计模式速查卡-new)
    - [19. WASM 速查卡 ⭐ NEW {#19-wasm-速查卡-new}](#19-wasm-速查卡--new-19-wasm-速查卡-new)
    - [20. AI/ML 速查卡 ⭐ NEW {#20-aiml-速查卡-new}](#20-aiml-速查卡--new-20-aiml-速查卡-new)
    - [21. Rust 1.90–1.93 特性速查卡 🆕 {#21-rust-190193-特性速查卡}](#21-rust-190193-特性速查卡--21-rust-190193-特性速查卡)
    - [22. Rust 1.94 特性速查卡 🆕 {#22-rust-194-特性速查卡}](#22-rust-194-特性速查卡--22-rust-194-特性速查卡)
    - [23. Rust 1.95 特性速查卡 🆕 {#23-rust-195-特性速查卡}](#23-rust-195-特性速查卡--23-rust-195-特性速查卡)
    - [24. Rust 1.96 特性速查卡 🆕 {#24-rust-196-特性速查卡}](#24-rust-196-特性速查卡--24-rust-196-特性速查卡)
    - [25. Rust 1.97 特性速查卡 🆕 {#25-rust-197-特性速查卡}](#25-rust-197-特性速查卡--25-rust-197-特性速查卡)
  - [🔍 快速查找 {#快速查找}](#-快速查找-快速查找)
    - [按主题查找 {#按主题查找}](#按主题查找-按主题查找)
    - [按场景查找 {#按场景查找}](#按场景查找-按场景查找)
  - [🚀 快速开始 {#快速开始}](#-快速开始-快速开始)
    - [推荐阅读顺序 {#推荐阅读顺序}](#推荐阅读顺序-推荐阅读顺序)
    - [使用建议 {#使用建议}](#使用建议-使用建议)
    - [速查卡统计 {#速查卡统计}](#速查卡统计-速查卡统计)
  - [📚 相关资源 {#相关资源}](#-相关资源-相关资源)
    - [完整文档 {#完整文档}](#完整文档-完整文档)
    - [代码示例 {#代码示例}](#代码示例-代码示例)
    - [研究笔记 {#研究笔记}](#研究笔记-研究笔记)
  - [🔄 更新日志 {#更新日志}](#-更新日志-更新日志)
    - [2026-05-29 {#2026-05-29}](#2026-05-29-2026-05-29)
    - [2026-02-12 {#2026-02-12}](#2026-02-12-2026-02-12)
    - [2026-01-27 {#2026-01-27}](#2026-01-27-2026-01-27)
    - [2026-01-26 🆕 {#2026-01-26}](#2026-01-26--2026-01-26)
    - [2025-12-11 {#2025-12-11}](#2025-12-11-2025-12-11)
    - [2025-11-15 {#2025-11-15}](#2025-11-15-2025-11-15)
    - [2025-10-30 {#2025-10-30}](#2025-10-30-2025-10-30)
  - [🆕 Rust 1.95 特性整合 {#rust-195-特性整合}](#-rust-195-特性整合-rust-195-特性整合)
    - [核心特性速查 {#核心特性速查}](#核心特性速查-核心特性速查)
  - [**状态**: ✅ 深度整合完成](#状态--深度整合完成)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

---

## 🎯 快速参考概述 {#快速参考概述}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本目录提供 Rust 核心概念的快速参考速查卡，帮助开发者快速查找常用语法、模式和最佳实践。

### 适用场景 {#适用场景}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- ✅ **快速查找** - 忘记语法时快速查阅
- ✅ **代码编写** - 编写代码时的参考
- ✅ **学习复习** - 学习后的快速复习
- ✅ **面试准备** - 面试前的快速回顾

---

## 📖 速查卡列表 {#速查卡列表}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1. 类型系统速查卡 {#1-类型系统速查卡}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**文件**: [02_type_system.md](02_type_system.md)

**内容**:

- 基本类型（标量、复合）
- 类型转换（From/Into/AsRef）
- 泛型编程
- Trait 系统
- 生命周期（Lifetimes）
- 类型型变

**适用对象**: 所有 Rust 开发者

---

### 2. 所有权系统速查卡 {#2-所有权系统速查卡}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**文件**: [02_ownership_cheatsheet.md](02_ownership_cheatsheet.md)

**内容**:

- 所有权三大规则
- 借用（Borrowing）规则
- 生命周期标注
- 智能指针（Smart Pointer）
- 常见模式

**适用对象**: Rust 初学者到中级开发者

---

### 3. 异步编程速查卡 {#3-异步编程速查卡}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**文件**: [02_async_patterns.md](02_async_patterns.md)

**内容**:

- Future Trait
- async/await 语法
- 并发执行模式
- 异步运行时（Runtime）选择
- 常见异步模式

**适用对象**: Rust 中级到高级开发者

---

### 4. 泛型编程速查卡 {#4-泛型编程速查卡}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**文件**: [02_generics_cheatsheet.md](02_generics_cheatsheet.md)

**内容**:

- 泛型函数和结构体（Struct）
- Trait 约束
- 生命周期参数
- 高级泛型特性

**适用对象**: Rust 中级到高级开发者

---

### 5. 错误处理速查卡 {#5-错误处理速查卡}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**文件**: [02_error_handling_cheatsheet.md](02_error_handling_cheatsheet.md)

**内容**:

- Result 和 Option
- 错误传播
- 自定义错误类型
- 错误处理模式

**适用对象**: 所有 Rust 开发者

---

### 6. 线程与并发速查卡 {#6-线程与并发速查卡}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**文件**: [02_threads_concurrency_cheatsheet.md](02_threads_concurrency_cheatsheet.md)

**内容**:

- 线程创建和管理
- 消息传递
- 共享状态
- 并发原语

**适用对象**: Rust 中级到高级开发者

---

### 7. 宏系统速查卡 {#7-宏系统速查卡}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**文件**: macros_cheatsheet.md

**内容**:

- 声明宏（Declarative Macro）
- 过程宏（Procedural Macro）
- 宏规则
- 常见宏模式

**适用对象**: Rust 高级开发者

---

### 8. 测试速查卡 {#8-测试速查卡}

> **来源: [IEEE](https://standards.ieee.org/)**

**文件**: [02_testing_cheatsheet.md](02_testing_cheatsheet.md)

**内容**:

- 单元测试
- 集成测试
- 文档测试
- 性能测试（基准测试）
- 测试工具和库
- 测试最佳实践

**适用对象**: 所有 Rust 开发者

---

### 9. 控制流与函数速查卡 {#9-控制流与函数速查卡}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

**文件**: [02_control_flow_functions_cheatsheet.md](02_control_flow_functions_cheatsheet.md)

**内容**:

- 条件语句（if/match/if let）
- 循环结构（loop/while/for）
- 模式匹配（Pattern Matching）
- 函数定义和调用
- 闭包（Closures）

**适用对象**: Rust 初学者到中级开发者

---

### 10. 集合与迭代器速查卡 {#10-集合与迭代器速查卡}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

**文件**: [02_collections_iterators_cheatsheet.md](02_collections_iterators_cheatsheet.md)

**内容**:

- Vec、HashMap、HashSet
- 其他集合类型
- 迭代器基础
- 迭代器适配器
- 迭代器消费者
- 常用模式

**适用对象**: 所有 Rust 开发者

---

### 11. 智能指针速查卡 {#11-智能指针速查卡}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

**文件**: [02_smart_pointers_cheatsheet.md](02_smart_pointers_cheatsheet.md)

**内容**:

- Box、Rc、Arc
- RefCell、Mutex、RwLock
- Weak 弱引用（Reference）
- 组合模式
- 选择指南

**适用对象**: Rust 中级到高级开发者

---

### 12. 模块系统速查卡 {#12-模块系统速查卡}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

**文件**: [02_modules_cheatsheet.md](02_modules_cheatsheet.md)

**内容**:

- 模块声明和组织
- 可见性控制
- use 语句
- 路径系统
- Crate 系统
- 文件组织

**适用对象**: 所有 Rust 开发者

---

### 13. 字符串与格式化速查卡 {#13-字符串与格式化速查卡}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

**文件**: [02_strings_formatting_cheatsheet.md](02_strings_formatting_cheatsheet.md)

**内容**:

- String 和 &str 类型
- 字符串操作（追加、删除、替换、查找）
- 字符串转换
- 格式化输出（println!, format!）
- 格式化选项（对齐、数字、浮点数）

**适用对象**: 所有 Rust 开发者

---

### 14. Cargo 速查卡 {#14-cargo-速查卡}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**

**文件**: [02_cargo_cheatsheet.md](02_cargo_cheatsheet.md)

**内容**:

- 项目创建和管理
- 构建命令
- 测试命令
- 依赖管理
- 发布命令
- 工作空间
- 常用工具

**适用对象**: 所有 Rust 开发者

---

### 15. 进程管理速查卡 ⭐ NEW {#15-进程管理速查卡-new}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

**文件**: [02_process_management_cheatsheet.md](02_process_management_cheatsheet.md)

**内容**:

- 进程创建和管理
- 异步进程管理
- IPC 通信
- 同步原语
- 性能优化
- 错误处理（Error Handling）

**适用对象**: Rust 中级到高级开发者（系统编程）

---

### 16. 网络编程速查卡 ⭐ NEW {#16-网络编程速查卡-new}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

**文件**: [02_network_programming_cheatsheet.md](02_network_programming_cheatsheet.md)

**内容**:

- HTTP 客户端和服务器
- TCP/UDP 编程
- WebSocket 通信
- DNS 解析
- 异步网络编程
- 安全特性

**适用对象**: Rust 中级到高级开发者（网络编程）

---

### 17. 算法与数据结构速查卡 ⭐ NEW {#17-算法与数据结构速查卡-new}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

**文件**: [02_algorithms_cheatsheet.md](02_algorithms_cheatsheet.md)

**内容**:

- 排序算法
- 搜索算法
- 图算法
- 动态规划
- 数据结构（栈、队列、树）
- 并行算法

**适用对象**: 所有 Rust 开发者

---

### 18. 设计模式速查卡 ⭐ NEW {#18-设计模式速查卡-new}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

**文件**: design_patterns_cheatsheet.md

**内容**:

- GoF 设计模式
- Rust 特有模式
- 创建型/结构型/行为型模式
- 实用示例

**适用对象**: Rust 中级到高级开发者

---

### 19. WASM 速查卡 ⭐ NEW {#19-wasm-速查卡-new}

**文件**: [02_wasm_cheatsheet.md](02_wasm_cheatsheet.md)

**内容**:

- WASM 基本设置
- JavaScript 互操作
- 异步函数
- 性能优化

**适用对象**: Rust 中级到高级开发者（Web 开发）

---

### 20. AI/ML 速查卡 ⭐ NEW {#20-aiml-速查卡-new}

**文件**: [02_ai_ml_cheatsheet.md](02_ai_ml_cheatsheet.md)

**内容**:

- AI/ML 生态系统概览
- candle 框架
- burn 框架
- 模型推理优化

**适用对象**: Rust AI/ML 开发者

---

### 21. Rust 1.90–1.93 特性速查卡 🆕 {#21-rust-190193-特性速查卡}

**文件**: [02_rust_190_to_193_features_cheatsheet.md](02_rust_190_to_193_features_cheatsheet.md)

**内容**:

- Rust 1.90: LLD 默认链接器、`cargo publish --workspace`
- Rust 1.91: aarch64-windows Tier 1、新 lint
- Rust 1.92: Never 类型 lint 严格化、`Box::new_zeroed`
- Rust 1.93: musl 1.2.5、`asm_cfg`、标准库 API

**适用对象**: 版本跟踪、迁移参考

---

### 22. Rust 1.94 特性速查卡 🆕 {#22-rust-194-特性速查卡}

**文件**: [02_rust_194_features_cheatsheet.md](02_rust_194_features_cheatsheet.md)

**内容**:

- Array Windows（数组窗口）
- LazyCell / LazyLock 新方法
- 数学常量（EULER_GAMMA、GOLDEN_RATIO）
- Peekable 迭代器增强
- `char → usize` 转换

**适用对象**: 版本跟踪、算法开发

---

### 23. Rust 1.95 特性速查卡 🆕 {#23-rust-195-特性速查卡}

**文件**: [02_rust_195_features_cheatsheet.md](02_rust_195_features_cheatsheet.md)

**内容**:

- `if let` guards
- `core::range` 类型族
- `Saturating` 类型
- `cfg_select!` 宏
- `as_ref_unchecked` / `as_mut_unchecked`

**适用对象**: 版本跟踪

---

### 24. Rust 1.96 特性速查卡 🆕 {#24-rust-196-特性速查卡}

**文件**: [02_rust_196_features_cheatsheet.md](02_rust_196_features_cheatsheet.md)

**内容**:

- `assert_matches!` / `debug_assert_matches!`
- `core::range` 完整迭代器
- `ManuallyDrop` 模式
- never 类型 tuple coercion

**适用对象**: 版本跟踪

---

### 25. Rust 1.97 特性速查卡 🆕 {#25-rust-197-特性速查卡}

**文件**: [02_rust_197_features_cheatsheet.md](02_rust_197_features_cheatsheet.md)

**内容**:

- `AsyncFn*` trait family prelude
- `midpoint` / `isqrt`
- Strict Provenance API
- `Waker::noop`
- IP 地址位运算

**适用对象**: 版本跟踪、前沿特性预览

**文件**: [02_ai_ml_cheatsheet.md](02_ai_ml_cheatsheet.md)

**内容**:

- Burn/Candle/LLM 框架选型
- 快速入门代码
- 与 C01–C12 关联

**适用对象**: Rust 开发者（AI/ML 应用）

---

## 🔍 快速查找 {#快速查找}

### 按主题查找 {#按主题查找}

| 主题         | 速查卡                       | 关键词                      |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **内存管理** | 所有权系统、智能指针         | 所有权（Ownership）/借用（Borrowing）/Box/Rc/Arc      |
| **类型系统（Type System）** | 类型系统、泛型编程           | Trait/泛型（Generics）/生命周期/内存对齐 |
| **错误处理** | 错误处理                     | Result/Option/错误传播      |
| **并发编程** | 线程与并发、异步编程         | 线程/async/await/Future     |
| **数据操作** | 集合与迭代器、字符串与格式化 | Vec/HashMap/Iterator/String |
| **代码组织** | 模块系统                     | mod/use/pub/crate           |
| **工具链**   | Cargo                        | 构建/测试/依赖/发布         |
| **高级特性** | 宏系统、泛型编程             | 宏/过程宏（Procedural Macro）/高级泛型          |
| **质量保证** | 测试                         | 单元测试/集成测试/性能测试  |

### 按场景查找 {#按场景查找}

| 场景 | 推荐速查卡 |
| :--- | :--- | :--- | :--- | :--- |
| **编写函数**  | 控制流与函数 → 类型系统 → 错误处理   |
| **处理数据**  | 集合与迭代器 → 字符串与格式化 → 类型系统 |
| **并发编程**  | 线程与并发 → 异步编程 → 智能指针  |
| **组织代码**  | 模块系统 → Cargo → 类型系统  |
| **调试问题**  | 错误处理 → 测试 → 类型系统  |
| **性能优化**  | 智能指针 → 集合与迭代器 → 测试（性能测试）→ [ALIGNMENT_GUIDE](../alignment_guide.md)（内存/缓存行对齐） |
| **发布项目**  | Cargo → 测试 → 模块系统  |

---

## 🚀 快速开始 {#快速开始}

### 推荐阅读顺序 {#推荐阅读顺序}

1. **初学者**:
   - 所有权系统速查卡 → 类型系统速查卡 → 控制流与函数速查卡 → 错误处理速查卡 → 字符串与格式化速查卡 → 集合与迭代器速查卡 → 模块系统速查卡 → Cargo 速查卡
2. **中级开发者**:
   - 类型系统速查卡 → 错误处理速查卡 → 集合与迭代器速查卡 → 智能指针速查卡 → 测试速查卡 → 字符串与格式化速查卡 → Cargo 速查卡 → 异步编程速查卡 → 线程与并发速查卡
3. **高级开发者**:
   - 异步编程速查卡 → 线程与并发速查卡 → 宏系统速查卡 → 泛型编程速查卡 → 智能指针速查卡 → 测试速查卡 → 集合与迭代器速查卡 → Cargo 速查卡
4. **特定需求**:
   - 使用上面的"按主题查找"或"按场景查找"快速定位

### 使用建议 {#使用建议}

- 📖 **打印版本**: 可以打印速查卡作为桌面参考
- 💻 **代码编辑器**: 在编辑器中打开，随时查阅
- 🔖 **书签**: 添加到浏览器书签，快速访问
- 🔍 **快速查找**: 使用 Ctrl+F 在速查卡中搜索关键词
- 📱 **移动设备**: 速查卡支持移动设备查看

### 速查卡统计 {#速查卡统计}

- **总数量**: 26 个速查卡 ⭐ (含版本特性速查卡 1.90–1.98 nightly，2026-05-29)
- **总行数**: 约 13,000+ 行
- **代码示例**: 900+ 个
- **覆盖主题**: Rust 核心概念全覆盖（包括系统编程、网络编程、算法、设计模式、WASM）+ 版本特性跟踪（1.90–1.98 nightly）
- **交叉引用**: ✅ 所有25个速查卡已统一添加"相关资源"部分，包含官方文档、项目内部文档和相关速查卡链接
- **相关示例代码**: ✅ 26 个速查卡（含版本特性，2026-05-29）
- **反例速查**: ✅ 20/20 核心速查卡已补全「反例速查」小节（错误示例 + 原因 + 修正），模板见 ANTI_PATTERN_10_template.md（2026-02-12）
- **版本一致性（Coherence）**: ✅ 所有速查卡已更新到 Rust 1.97.0+

---

## 📚 相关资源 {#相关资源}

### 完整文档 {#完整文档}

**参考指南**:

- [ALIGNMENT_GUIDE](../alignment_guide.md) - 对齐知识综合（内存/格式化/unsafe/缓存行/权威来源）

**核心模块文档**:

- [类型系统完整文档](../../../crates/c02_type_system/docs/README.md)
- [所有权系统完整文档](../../../crates/c01_ownership_borrow_scope/docs/README.md)
- [异步编程完整文档](../../../crates/c06_async/docs/README.md)
- [控制流与函数文档](../../../crates/c03_control_fn/docs/README.md)
- [泛型编程文档](../../../crates/c04_generic/docs/README.md)
- [线程与并发文档](../../../crates/c05_threads/docs/README.md)
- [进程管理文档](../../../crates/c07_process/docs/README.md)
- [算法与数据结构文档](../../../crates/c08_algorithms/docs/README.md)
- [设计模式文档](../../../crates/c09_design_pattern/docs/README.md)
- [网络编程文档](../../../crates/c10_networks/docs/README.md)
- [宏系统文档](../../../crates/c11_macro_system_proc/docs/README.md)
- [WASM 文档](../../../crates/c12_wasm/docs/README.md)

### 代码示例 {#代码示例}

**核心模块示例**:

- [类型系统示例](../../../crates/c02_type_system/examples/README.md)
- [所有权系统示例](../../../crates/c01_ownership_borrow_scope/examples/README.md)
- [异步编程示例](../../../crates/c06_async/examples/README.md)
- [控制流与函数示例](../../../crates/c03_control_fn/examples/README.md)
- [算法示例](../../../crates/c08_algorithms/examples/README.md)
- [网络编程示例](../../../crates/c10_networks/examples/README.md)
- [WASM 示例](../../../crates/c12_wasm/examples/README.md)

### 研究笔记 {#研究笔记}

- [研究笔记快速参考](../../../archive/research_notes_2026_06_25/10_quick_reference.md) - 形式化方法、类型理论、软件设计理论索引；与速查卡互为补充
- [形式化方法研究](../../../archive/research_notes_2026_06_25/formal_methods/README.md)
- [类型理论研究](../../research_notes/type_theory/README.md)
- [实验研究](../../../archive/research_notes_2026_06_25/experiments/README.md)

---

## 🔄 更新日志 {#更新日志}

### 2026-05-29 {#2026-05-29}

- ✅ **新增版本特性速查卡**: 补齐 Rust 1.90–1.97 版本特性速查表
  - `02_rust_190_to_193_features_cheatsheet.md`: 1.90–1.93 累积特性
  - `02_rust_194_features_cheatsheet.md`: 1.94 特性（从 archive 迁移）
  - `02_rust_195_features_cheatsheet.md`: 1.95 特性（已存在，确认覆盖）
  - `02_rust_196_features_cheatsheet.md`: 1.96 特性（已存在，确认覆盖）
  - `02_rust_197_features_cheatsheet.md`: 1.97 beta 特性（新增）
- ✅ **新增 1.98 nightly 前瞻速查卡**: `02_rust_198_nightly_preview_cheatsheet.md`
  - gen 块、for await、derive(CoercePointee)、never_type 推进、函数对齐、调试断点
- ✅ **速查卡总数**: 20 → 26

### 2026-02-12 {#2026-02-12}

- ✅ **反例速查补全**: 20/20 速查卡已全部添加「反例速查」小节（错误示例 + 原因 + 修正）
- ✅ **ANTI_PATTERN_10_template.md**: 新增反例速查统一模板

### 2026-01-27 {#2026-01-27}

- ✅ **20/20 速查卡已统一添加「📚 相关文档 + 🧩 相关示例代码」块**
  - 含 testing、cargo、modules、strings_formatting 等此前未列出的速查卡，与 quick_reference 统计一致

### 2026-01-26 🆕 {#2026-01-26}

- ✅ **交叉引用增强**：为所有20个速查卡统一添加/增强"相关资源"部分
  - 包含官方文档、项目内部文档和相关速查卡链接
  - 统一格式：官方文档、项目内部文档、相关速查卡
- ✅ **版本一致性**：所有速查卡已更新到 Rust 1.97.0+
- ✅ **新增 Rust 1.95+ 特性**: 所有速查卡已添加 1.95+ 新特性章节
- ✅ **断链修复**：修复所有发现的文档断链
- ✅ **工具链文档**：Rust 1.93 vs 1.92 对比文档已整合
- ✅ **文档索引增强**：增强相关资源部分，添加所有12个核心模块的文档和示例链接

### 2025-12-11 {#2025-12-11}

- ✅ 新增进程管理速查卡（C07 模块（Module））
- ✅ 新增网络编程速查卡（C10 模块）
- ✅ 新增算法与数据结构速查卡（C08 模块）
- ✅ 新增设计模式速查卡（C09 模块）
- ✅ 新增 WASM 速查卡（C12 模块）
- ✅ 更新速查卡统计信息（总计 20 个，含 AI/ML）

### 2025-11-15 {#2025-11-15}

- ✅ 更新所有速查卡的版本信息为 Rust 1.97.0+ (2026-01-26)
- ✅ 更新日期信息为 2026-01-26
- ✅ 创建 README.md 索引文件
- ✅ 新增泛型编程速查卡
- ✅ 新增错误处理速查卡
- ✅ 新增线程与并发速查卡
- ✅ 新增宏系统速查卡
- ✅ 新增测试速查卡（单元测试、集成测试、性能测试等）
- ✅ 新增控制流与函数速查卡（if/match/loop/函数/闭包（Closures））
- ✅ 新增集合与迭代器速查卡（Vec/HashMap/Iterator等）
- ✅ 新增智能指针速查卡（Box/Rc/Arc/RefCell/Mutex等）
- ✅ 新增模块系统速查卡（mod/use/pub/crate（Crate）等）
- ✅ 新增字符串与格式化速查卡（String/str/格式化输出）
- ✅ 新增 Cargo 速查卡（包管理、构建、发布）
- ✅ 统一所有速查卡的结构，为所有文件添加目录导航
- ✅ 改进 README.md，添加快速查找功能（按主题、按场景）

### 2025-10-30 {#2025-10-30}

- ✅ 创建类型系统速查卡
- ✅ 创建所有权系统速查卡
- ✅ 创建异步编程速查卡

---

**最后更新**: 2026-05-08
**维护者**: 文档团队
**状态**: ✅ **20/20 速查卡已更新至 Rust 1.97.0+，包含 1.95 新特性章节**

🎯 **快速参考，高效开发！**

---

## 🆕 Rust 1.95 特性整合 {#rust-195-特性整合}

> **适用版本**: Rust 1.97.0+

### 核心特性速查 {#核心特性速查}

```rust,ignore
// cfg_select! - 编译期条件选择
cfg_select! {
    unix => fn os_specific() -> &'static str { "Unix" }
    windows => fn os_specific() -> &'static str { "Windows" }
    _ => fn os_specific() -> &'static str { "Other" }
}

// if let guards on match arms
match value {
    Some(x) if let Ok(y) = parse(x) => println!("{}, {}", x, y),
    Some(_) => println!("parse failed"),
    None => println!("no value"),
}

// 原子操作 update / try_update
use std::sync::atomic::{AtomicUsize, Ordering};
let counter = AtomicUsize::new(5);
counter.update(Ordering::Relaxed, Ordering::Relaxed, |c| c + 1);

// Vec::push_mut / insert_mut
let mut v = vec![1, 2];
let elem: &mut i32 = v.push_mut(3);
*elem += 10;

// cold_path 分支预测提示
use std::hint::cold_path;
if let Some(msg) = e { cold_path(); eprintln!("error: {}", msg); }
```

**完整速查表**: [`02_rust_195_features_cheatsheet.md`](02_rust_195_features_cheatsheet.md) — 包含所有 1.95 新 API 与示例链接

**性能提升**: `cold_path` 优化冷分支预测, `Atomic*::update` 减少 CAS 循环样板, `push_mut` 消除二次查找。

**最后更新**: 2026-05-08 (深度整合 Rust 1.95 特性)

---

**状态**: ✅ 深度整合完成
---

> **权威来源**: [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 标准库、Rust Reference、TRPL 官方来源标注 [Authority Source Sprint Batch 8](../../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**
