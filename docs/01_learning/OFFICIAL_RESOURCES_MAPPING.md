# 本项目概念与官方资源映射表

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 本项目概念/模块 ↔ The Rust Book / Reference / Rust by Example

---

## 官方资源入口

| 资源 | URL | 说明 |
| :--- | :--- | :--- || **The Rust Book** | <https://doc.rust-lang.org/book/> | 官方入门与进阶教程 |
| **Rust Reference** | <https://doc.rust-lang.org/reference/> | 语言规范 |
| **Rust by Example** | <https://doc.rust-lang.org/rust-by-example/> | 示例驱动学习 |
| **Standard Library** | <https://doc.rust-lang.org/std/> | 标准库 API |
| **Rust releases** | <https://releases.rs/> | 版本 changelog |
| **Brown 交互版 Book** | <https://rust-book.cs.brown.edu/> | 测验、可视化、高亮（Rust Book 交互版） |
| **Rustlings** | <https://github.com/rust-lang/rustlings> | 命令行交互式习题 |
| **Compiler Error Index** | <https://doc.rust-lang.org/error-index.html> | 编译器错误详解 |
| **Command Line Book** | <https://rust-cli.github.io/book/> | CLI 应用开发 |
| **Embedded Rust Book** | <https://doc.rust-lang.org/embedded-book/> | 嵌入式开发 |

---

## 模块 → 官方章节映射

| 项目模块 | 本项目路径 | The Rust Book | RBE 练习（可点击） | Reference |
| :--- | :--- | :--- | :--- | :--- || **C01 所有权** | crates/c01_ownership_borrow_scope | Ch 4 Understanding Ownership | [Scope](https://doc.rust-lang.org/rust-by-example/scope.html) · [Move](https://doc.rust-lang.org/rust-by-example/scope/move.html) · [Borrow](https://doc.rust-lang.org/rust-by-example/scope/borrow.html) · [Lifetime](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html) | [Ownership](https://doc.rust-lang.org/reference/ownership.html) |
| **C02 类型系统** | crates/c02_type_system | Ch 3 Types, Ch 10 Traits | [Custom Types](https://doc.rust-lang.org/rust-by-example/custom_types.html) · [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) · [Conversion](https://doc.rust-lang.org/rust-by-example/conversion.html) | [Types](https://doc.rust-lang.org/reference/types.html) |
| **C03 控制流** | crates/c03_control_fn | Ch 3 Control Flow, Ch 6 Enums | [Flow Control](https://doc.rust-lang.org/rust-by-example/flow_control.html) · [Option](https://doc.rust-lang.org/rust-by-example/std/option.html) · [Error](https://doc.rust-lang.org/rust-by-example/error.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html) | [Statements](https://doc.rust-lang.org/reference/statements.html) |
| **C04 泛型** | crates/c04_generic | Ch 10 Generic Types, Traits | [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) | [Items](https://doc.rust-lang.org/reference/items/generics.html) |
| **C05 线程** | crates/c05_threads | Ch 16 Fearless Concurrency | [Threads](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html) | [Send/Sync](https://doc.rust-lang.org/reference/special-types-and-traits.html) |
| **C06 异步** | crates/c06_async | Ch 16 Async | [Async](https://doc.rust-lang.org/rust-by-example/async.html) | [Coroutines](https://doc.rust-lang.org/reference/items/coroutines.html) |
| **C07 进程** | crates/c07_process | - | [Process](https://doc.rust-lang.org/rust-by-example/std_misc/process.html) | [Process](https://doc.rust-lang.org/std/process/) |
| **C08 算法** | crates/c08_algorithms | - | [Vectors](https://doc.rust-lang.org/rust-by-example/std/vec.html) · [HashMap](https://doc.rust-lang.org/rust-by-example/std/hash.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html) | [Iterator](https://doc.rust-lang.org/std/iter/) |
| **C09 设计模式** | crates/c09_design_pattern | Ch 17 OOP | [Functional](https://doc.rust-lang.org/rust-by-example/fn.html) · [Structs](https://doc.rust-lang.org/rust-by-example/custom_types/structs.html) · [Enums](https://doc.rust-lang.org/rust-by-example/custom_types/enum.html) | - |
| **C10 网络** | crates/c10_networks | - | [TCP](https://doc.rust-lang.org/rust-by-example/std_misc/net.html) | [net](https://doc.rust-lang.org/std/net/) |
| **C11 宏** | crates/c11_macro_system | Ch 19 Macros | [Macros](https://doc.rust-lang.org/rust-by-example/macros.html) | [Macros](https://doc.rust-lang.org/reference/macros.html) |
| **C12 WASM** | crates/c12_wasm | - | - | [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/) |

---

## 小节级映射与「本项目补充」

| 官方章节 | 小节 | 本项目补充内容 |
| :--- | :--- | :--- || **Book Ch 4** | 4.1-4.3 Ownership, Borrowing, Slices | 思维导图、决策树、证明树（[THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md)）；边界特例（[EDGE_CASES](../02_reference/EDGE_CASES_AND_SPECIAL_CASES.md)） |
| **Book Ch 10** | 10.1-10.3 Traits, Lifetimes | 型变理论、生命周期形式化（[research_notes](../research_notes/)）；转换树 |
| **Reference** | Types, Ownership, Special Types | 形式化工程系统（[rust-formal-engineering-system](../rust-formal-engineering-system/)）；variance 专项 |
| **Reference** | Macros by Example, Procedural Macros | 宏系统决策树、反例（[macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md)） |
| **Book Ch 16** | 16.1-16.3 Async | 空 Future、持锁跨 await 反例（[async_patterns](../02_reference/quick_reference/async_patterns.md)）；EDGE_CASES |
| **Book Ch 3** | 3.1-3.5 Types, Control Flow | 控制流（[C03](../../crates/c03_control_fn/docs/)）；模式匹配决策树 |
| **Book Ch 9** | 9.1-9.3 Error Handling | 错误传播转换树（[THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md)）；[error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| **Book Ch 11** | 11.1-11.3 Testing | [testing_cheatsheet](../02_reference/quick_reference/testing_cheatsheet.md)；#[test] 1.93 严格化（[09_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md)） |
| **Reference** | Attributes, Macros | offset_of! 类型检查（1.93）；[macros_cheatsheet](../02_reference/quick_reference/macros_cheatsheet.md) |
| **Reference** | Type system, Variance | [variance_theory](../research_notes/type_theory/variance_theory.md)；[PROOF_INDEX](../research_notes/PROOF_INDEX.md) |
| **releases.rs** | 1.93 Language/Libraries | [09_rust_1.93_compatibility_deep_dive](../06_toolchain/09_rust_1.93_compatibility_deep_dive.md)；[07_full_changelog](../06_toolchain/07_rust_1.93_full_changelog.md) |

> 标注「本项目补充」表示官方资源未覆盖或简略，本项目提供额外深度。

---

## 核心概念映射

| 概念 | 本项目速查卡 | Book 章节 | RBE |
| :--- | :--- | :--- | :--- || 所有权 | ownership_cheatsheet | Ch 4.1 | [Move](https://doc.rust-lang.org/rust-by-example/scope/move.html) |
| 借用 | ownership_cheatsheet | Ch 4.2 | [Borrow](https://doc.rust-lang.org/rust-by-example/scope/borrow.html) |
| 生命周期 | type_system | Ch 10.3 | [Lifetime](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html) |
| Trait | type_system | Ch 10 | [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) |
| 错误处理 | error_handling_cheatsheet | Ch 9 | [Error](https://doc.rust-lang.org/rust-by-example/error.html) |
| 泛型 | generics_cheatsheet | Ch 10.1 | [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) |
| 异步 | async_patterns | Ch 16 | [Async](https://doc.rust-lang.org/rust-by-example/async.html) |
| 测试 | testing_cheatsheet | Ch 11 | [Testing](https://doc.rust-lang.org/rust-by-example/testing.html) |

---

## RBE 练习与 Rustlings 映射

- **RBE 练习**：上表「RBE 练习（可点击）」列提供各模块对应的 RBE 章节链接，可直接点击进入练习
- **Rustlings 模块映射**：[exercises/RUSTLINGS_MAPPING.md](../../exercises/RUSTLINGS_MAPPING.md) — C01–C12 与 Rustlings 习题主题对应表（含可点击 GitHub 链接）

---

## 📋 官方资源使用场景指南

### 学习场景对照表

| 你的情况 | 推荐资源 | 使用方式 |
| :--- | :--- | :--- |
| 完全零基础 | The Rust Book | 按章节顺序阅读，完成每章练习 |
| 有其他编程经验 | Rust by Example + Book | 先看 RBE 快速上手，再深入 Book |
| 需要快速查阅语法 | Standard Library 文档 | 使用搜索功能查找具体 API |
| 准备面试/考试 | Brown 交互版 Book | 完成所有测验，查看可视化解释 |
| 喜欢动手练习 | Rustlings | 按提示修复代码，循序渐进 |
| 遇到编译错误 | Compiler Error Index | 搜索错误码，阅读详细解释 |
| 开发 CLI 应用 | Command Line Book | 参考项目结构和最佳实践 |
| 嵌入式开发 | Embedded Rust Book | 学习 no_std 和硬件交互 |

---

## 🌳 资源选择决策树

```
开始选择学习资源
    │
    ├── 你是 Rust 新手？
    │       │
    │       ├── 是 → 有编程基础？
    │       │           │
    │       │           ├── 是 → 想快速上手？
    │       │           │           │
    │       │           │           ├── 是 → Rust by Example
    │       │           │           │
    │       │           │           └── 否 → The Rust Book
    │       │           │
    │       │           └── 否 → The Rust Book（仔细阅读）
    │       │
    │       └── 否 → 需要解决具体问题？
    │                   │
    │                   ├── 是 → 编译错误？
    │                   │           │
    │                   │           ├── 是 → Compiler Error Index
    │                   │           │
    │                   │           └── 否 → Standard Library 文档
    │                   │
    │                   └── 否 → 深入学习？
    │                               │
    │                               ├── 是 → Rust Reference
    │                               │
    │                               └── 否 → releases.rs 了解新特性
    │
    └── 需要练习？
            │
            ├── 是 → 喜欢命令行交互？
            │           │
            │           ├── 是 → Rustlings
            │           │
            │           └── 否 → Brown 交互版 Book
            │
            └── 否 → 查看场景对照表选择
```

---

## 🎯 按目标选择资源

### 目标: 通过 Rust 面试

**推荐路径**:

1. [Brown 交互版 Book](https://rust-book.cs.brown.edu/) - 完成所有测验
2. [Rustlings](https://github.com/rust-lang/rustlings) - 完成 80% 以上练习
3. [Compiler Error Index](https://doc.rust-lang.org/error-index.html) - 熟悉常见错误

### 目标: 开发生产项目

**推荐路径**:

1. [The Rust Book](https://doc.rust-lang.org/book/) - 完整阅读
2. [Rust Reference](https://doc.rust-lang.org/reference/) - 查阅语言规范
3. [Command Line Book](https://rust-cli.github.io/book/) - CLI 项目
4. [Rustonomicon](https://doc.rust-lang.org/nomicon/) - unsafe 代码

### 目标: 贡献 Rust 编译器

**推荐路径**:

1. [rustc-dev-guide](https://rustc-dev-guide.rust-lang.org/) - 编译器开发指南
2. [Rust Reference](https://doc.rust-lang.org/reference/) - 理解语言规范
3. [Ferrocene FLS](https://spec.ferrocene.dev/) - 形式化规范

### 目标: 学术研究（形式化验证）

**推荐路径**:

1. [RustBelt 论文](https://plv.mpi-sws.org/rustbelt/popl18/) - 理论基础
2. [Ferrocene FLS](https://spec.ferrocene.dev/) - 形式化规范
3. 本项目 [formal_methods](../research_notes/formal_methods/) - 中文形式化论证

---

## 🔗 形式化文档链接

### 形式化证明体系（2026-02-14）

| 资源 | 说明 | 形式化链接 |
| :--- | :--- | :--- |
| [FORMAL_PROOF_SYSTEM_GUIDE](../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md) | 批判性分析与推进计划 | [formal_methods/README](../research_notes/formal_methods/README.md) |
| [CORE_THEOREMS_FULL_PROOFS](../research_notes/CORE_THEOREMS_FULL_PROOFS.md) | 核心定理完整证明（L2） | [ownership_model](../research_notes/formal_methods/ownership_model.md)、[borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) |
| [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) | 国际对标 | [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)、[Ferrocene FLS](https://spec.ferrocene.dev/) |

### 官方形式化资源映射

| 官方资源 | 本项目形式化文档 |
| :--- | :--- |
| [Ferrocene FLS - Ownership](https://spec.ferrocene.dev/ownership-and-deconstruction.html) | [ownership_model](../research_notes/formal_methods/ownership_model.md) |
| [Ferrocene FLS - Borrowing](https://spec.ferrocene.dev/ownership-and-deconstruction.html#borrowing) | [borrow_checker_proof](../research_notes/formal_methods/borrow_checker_proof.md) |
| [Ferrocene FLS - Concurrency](https://spec.ferrocene.dev/concurrency.html) | [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md)、[async_state_machine](../research_notes/formal_methods/async_state_machine.md) |
| [Rust Reference - Undefined Behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | [EDGE_CASES_AND_SPECIAL_CASES](./EDGE_CASES_AND_SPECIAL_CASES.md) |

---

## edX 课程资源映射

### 课程与项目内容对齐

| 课程 | 机构 | 链接 | 主要内容 | 本项目对应路径 |
| :--- | :--- | :--- | :--- | :--- |
| Introduction to Rust Programming | Microsoft | <https://www.edx.org/learn/rust/microsoft-introduction-to-rust-programming> | Rust语法基础、所有权、类型系统 | [01_learning/](./) - C01-C04 基础阶段 |
| Rust for Developers | Linux Foundation | <https://www.edx.org/learn/rust/the-linux-foundation-rust-for-developers> | 实战开发、项目构建、最佳实践 | [05_guides/](../05_guides/) - 开发指南 |
| Programming with Rust | W3C | <https://www.edx.org/learn/rust/w3cx-programming-with-rust> | 语法速查、模式匹配、标准库 | [02_reference/quick_reference/](../02_reference/quick_reference/) - 速查卡 |

### 学习路径建议

**初学者路径** (Microsoft课程 → 本项目):

1. 完成 edX Microsoft 入门课程
2. 结合本项目 [LEARNING_PATH_PLANNING.md](./LEARNING_PATH_PLANNING.md) 深化理解
3. 通过 [Rustlings 练习](../../exercises/RUSTLINGS_MAPPING.md) 巩固知识

**开发者进阶路径** (Linux Foundation课程 → 本项目):

1. 完成 edX Linux Foundation 开发者课程
2. 参考本项目 [05_guides/](../05_guides/) 专题指南
3. 阅读 [异步模式速查](../02_reference/quick_reference/async_patterns.md) 等进阶内容

---

## 相关文档

- [文档中心](../README.md)
- [学习路径规划](./LEARNING_PATH_PLANNING.md)
- [Rustlings 映射](../../exercises/RUSTLINGS_MAPPING.md)
- [形式化方法研究](../research_notes/formal_methods/README.md)
