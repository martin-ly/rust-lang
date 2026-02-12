# 本项目概念与官方资源映射表

> **创建日期**: 2026-02-12
> **Rust 版本**: 1.93.0+
> **用途**: 本项目概念/模块 ↔ The Rust Book / Reference / Rust by Example

---

## 官方资源入口

| 资源 | URL | 说明 |
|------|-----|------|
| **The Rust Book** | <https://doc.rust-lang.org/book/> | 官方入门与进阶教程 |
| **Rust Reference** | <https://doc.rust-lang.org/reference/> | 语言规范 |
| **Rust by Example** | <https://doc.rust-lang.org/rust-by-example/> | 示例驱动学习 |
| **Standard Library** | <https://doc.rust-lang.org/std/> | 标准库 API |
| **Rust releases** | <https://releases.rs/> | 版本 changelog |

---

## 模块 → 官方章节映射

| 项目模块 | 本项目路径 | The Rust Book | Rust by Example | Reference |
|----------|------------|---------------|-----------------|-----------|
| **C01 所有权** | crates/c01_ownership_borrow_scope | Ch 4 Understanding Ownership | [Scope](https://doc.rust-lang.org/rust-by-example/scope.html) | [Ownership](https://doc.rust-lang.org/reference/ownership.html) |
| **C02 类型系统** | crates/c02_type_system | Ch 3 Types, Ch 10 Traits | [Custom Types](https://doc.rust-lang.org/rust-by-example/custom_types.html) | [Types](https://doc.rust-lang.org/reference/types.html) |
| **C03 控制流** | crates/c03_control_fn | Ch 3 Control Flow, Ch 6 Enums | [Flow Control](https://doc.rust-lang.org/rust-by-example/flow_control.html) | [Statements](https://doc.rust-lang.org/reference/statements.html) |
| **C04 泛型** | crates/c04_generic | Ch 10 Generic Types, Traits | [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) | [Items](https://doc.rust-lang.org/reference/items/generics.html) |
| **C05 线程** | crates/c05_threads | Ch 16 Fearless Concurrency | [Concurrency](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html) | [Send/Sync](https://doc.rust-lang.org/reference/special-types-and-traits.html) |
| **C06 异步** | crates/c06_async | Ch 16 Async | [Async](https://doc.rust-lang.org/rust-by-example/async.html) | [Coroutines](https://doc.rust-lang.org/reference/items/coroutines.html) |
| **C07 进程** | crates/c07_process | - | [Process](https://doc.rust-lang.org/rust-by-example/std_misc/process.html) | [Process](https://doc.rust-lang.org/std/process/) |
| **C08 算法** | crates/c08_algorithms | - | [Error handling](https://doc.rust-lang.org/rust-by-example/error.html) | [Iterator](https://doc.rust-lang.org/std/iter/) |
| **C09 设计模式** | crates/c09_design_pattern | Ch 17 OOP | [Functional](https://doc.rust-lang.org/rust-by-example/fn.html) | - |
| **C10 网络** | crates/c10_networks | - | [TCP](https://doc.rust-lang.org/rust-by-example/std_misc/net.html) | [net](https://doc.rust-lang.org/std/net/) |
| **C11 宏** | crates/c11_macro_system | Ch 19 Macros | [Macros](https://doc.rust-lang.org/rust-by-example/macros.html) | [Macros](https://doc.rust-lang.org/reference/macros.html) |
| **C12 WASM** | crates/c12_wasm | - | - | [wasm-bindgen](https://rustwasm.github.io/wasm-bindgen/) |

---

## 小节级映射与「本项目补充」

| 官方章节 | 小节 | 本项目补充内容 |
|----------|------|----------------|
| **Book Ch 4** | 4.1-4.3 Ownership, Borrowing, Slices | 思维导图、决策树、证明树（[THINKING_REPRESENTATION_METHODS](./THINKING_REPRESENTATION_METHODS.md)）；边界特例（[EDGE_CASES](./EDGE_CASES_AND_SPECIAL_CASES.md)） |
| **Book Ch 10** | 10.1-10.3 Traits, Lifetimes | 型变理论、生命周期形式化（[research_notes](../research_notes/)）；转换树 |
| **Reference** | Types, Ownership, Special Types | 形式化工程系统（[rust-formal-engineering-system](./rust-formal-engineering-system/)）；variance 专项 |
| **Reference** | Macros by Example, Procedural Macros | 宏系统决策树、反例（[macros_cheatsheet](./quick_reference/macros_cheatsheet.md)） |
| **Book Ch 16** | 16.1-16.3 Async | 空 Future、持锁跨 await 反例（[async_patterns](./quick_reference/async_patterns.md)）；EDGE_CASES |
| **Book Ch 3** | 3.1-3.5 Types, Control Flow | 控制流（[C03](../crates/c03_control_fn/docs/)）；模式匹配决策树 |
| **Book Ch 9** | 9.1-9.3 Error Handling | 错误传播转换树（[THINKING_REPRESENTATION_METHODS](./THINKING_REPRESENTATION_METHODS.md)）；[error_handling_cheatsheet](./quick_reference/error_handling_cheatsheet.md) |
| **Book Ch 11** | 11.1-11.3 Testing | [testing_cheatsheet](./quick_reference/testing_cheatsheet.md)；#[test] 1.93 严格化（[09_compatibility_deep_dive](./toolchain/09_rust_1.93_compatibility_deep_dive.md)） |
| **Reference** | Attributes, Macros | offset_of! 类型检查（1.93）；[macros_cheatsheet](./quick_reference/macros_cheatsheet.md) |
| **Reference** | Type system, Variance | [variance_theory](../research_notes/type_theory/variance_theory.md)；[PROOF_INDEX](./research_notes/PROOF_INDEX.md) |
| **releases.rs** | 1.93 Language/Libraries | [09_rust_1.93_compatibility_deep_dive](./toolchain/09_rust_1.93_compatibility_deep_dive.md)；[07_full_changelog](./toolchain/07_rust_1.93_full_changelog.md) |

> 标注「本项目补充」表示官方资源未覆盖或简略，本项目提供额外深度。

---

## 核心概念映射

| 概念 | 本项目速查卡 | Book 章节 | RBE |
|------|---------------|-----------|-----|
| 所有权 | ownership_cheatsheet | Ch 4.1 | [Move](https://doc.rust-lang.org/rust-by-example/scope/move.html) |
| 借用 | ownership_cheatsheet | Ch 4.2 | [Borrow](https://doc.rust-lang.org/rust-by-example/scope/borrow.html) |
| 生命周期 | type_system | Ch 10.3 | [Lifetime](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html) |
| Trait | type_system | Ch 10 | [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) |
| 错误处理 | error_handling_cheatsheet | Ch 9 | [Error](https://doc.rust-lang.org/rust-by-example/error.html) |
| 泛型 | generics_cheatsheet | Ch 10.1 | [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) |
| 异步 | async_patterns | Ch 16 | [Async](https://doc.rust-lang.org/rust-by-example/async.html) |
| 测试 | testing_cheatsheet | Ch 11 | [Testing](https://doc.rust-lang.org/rust-by-example/testing.html) |

---

## 相关文档

- [文档中心](./README.md)
- [学习路径规划](./LEARNING_PATH_PLANNING.md)
