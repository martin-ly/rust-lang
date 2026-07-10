# Rust By Example 对齐矩阵 {#rust-by-example-对齐矩阵}

> **EN**: Rust By Example Alignment
> **Summary**: Rust By Example 对齐矩阵 Rust By Example Alignment.
> **概念族**: 权威来源对齐 / Rust By Example
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Rust By Example 对齐矩阵 {#rust-by-example-对齐矩阵}](#rust-by-example-对齐矩阵-rust-by-example-对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、基础概念 {#二基础概念}](#二基础概念-二基础概念)
  - [三、所有权（Ownership）与借用（Borrowing） {#三所有权与借用}](#三所有权与借用-三所有权与借用)
  - [四、类型系统（Type System） {#四类型系统}](#四类型系统-四类型系统)
  - [五、并发与异步（Async） {#五并发与异步}](#五并发与异步-五并发与异步)
  - [六、错误处理（Error Handling） {#六错误处理}](#六错误处理-六错误处理)
  - [七、宏（Macro）与元编程 {#七宏与元编程}](#七宏与元编程-七宏与元编程)
  - [八、FFI 与 unsafe {#八ffi-与-unsafe}](#八ffi-与-unsafe-八ffi-与-unsafe)
  - [九、未覆盖缺口 {#九未覆盖缺口}](#九未覆盖缺口-九未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

[Rust By Example](https://doc.rust-lang.org/rust-by-example/) 是 Rust 官方提供的交互式示例集合。本文档将项目中的示例、反例、代码实践与 Rust By Example 的章节建立映射，便于学习者按官方示例路径复习和扩展。

---

## 二、基础概念 {#二基础概念}

| Rust By Example 章节 | 项目文档/示例 | 状态 | 备注 |
|----------------------|---------------|------|------|
| [Hello World](https://doc.rust-lang.org/rust-by-example/hello.html) | [examples/cargo_script_demo.rs](../../examples/cargo_script_demo.rs) | ✅ | 单文件可运行示例 |
| [Primitives](https://doc.rust-lang.org/rust-by-example/primitives.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | ✅ | 标量与复合类型 |
| [Custom Types](https://doc.rust-lang.org/rust-by-example/custom_types.html) | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | ✅ | struct/enum |
| [Variable Bindings](https://doc.rust-lang.org/rust-by-example/variable_bindings.html) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ | 绑定与可变性 |
| [Expressions](https://doc.rust-lang.org/rust-by-example/expression.html) | [crates/c03_control_fn/](../../crates/c03_control_fn/README.md) | ✅ | 表达式与语句 |

---

## 三、所有权与借用 {#三所有权与借用}

| Rust By Example 章节 | 项目文档/示例 | 状态 | 备注 |
|----------------------|---------------|------|------|
| [Ownership](https://doc.rust-lang.org/rust-by-example/scope.html) | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | ✅ | 作用域与所有权 |
| [Borrowing](https://doc.rust-lang.org/rust-by-example/scope/borrow.html) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §2-§3 | ✅ | &T / &mut T |
| [Lifetimes](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html) | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | ✅ | 生命周期标注 |

---

## 四、类型系统 {#四类型系统}

| Rust By Example 章节 | 项目文档/示例 | 状态 | 备注 |
|----------------------|---------------|------|------|
| [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | 泛型 |
| [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | trait 定义与实现 |
| [Trait Objects](https://doc.rust-lang.org/rust-by-example/trait/dyn.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §3 | ✅ | dyn Trait |
| [Associated Items](https://doc.rust-lang.org/rust-by-example/generics/assoc_items.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §6 | ✅ | 关联类型 |

---

## 五、并发与异步 {#五并发与异步}

| Rust By Example 章节 | 项目文档/示例 | 状态 | 备注 |
|----------------------|---------------|------|------|
| [Threads](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html) | [crates/c05_threads/](../../crates/c05_threads/README.md) | ✅ | 线程 |
| [Channels](https://doc.rust-lang.org/rust-by-example/std_misc/channels.html) | [crates/c05_threads/](../../crates/c05_threads/README.md) | ✅ | mpsc |
| [Arc](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §1 | ✅ | Arc<T> |
| [Async](https://doc.rust-lang.org/book/ch17-00-async-await.html) | [crates/c06_async/](../../crates/c06_async/README.md) | ✅ | async/await |

---

## 六、错误处理 {#六错误处理}

| Rust By Example 章节 | 项目文档/示例 | 状态 | 备注 |
|----------------------|---------------|------|------|
| [Error Handling](https://doc.rust-lang.org/rust-by-example/error.html) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | ✅ | Result / Option / ? |
| [panic!](https://doc.rust-lang.org/rust-by-example/error/panic.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §2 | ✅ | RefCell borrow_mut panic |

---

## 七、宏与元编程 {#七宏与元编程}

| Rust By Example 章节 | 项目文档/示例 | 状态 | 备注 |
|----------------------|---------------|------|------|
| [Macros](https://doc.rust-lang.org/rust-by-example/macros.html) | [crates/c11_macro_system_proc/](../../crates/c11_macro_system_proc/README.md) | ✅ | 声明宏（Declarative Macro） |
| [Procedural Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) | [crates/c11_macro_system_proc/](../../crates/c11_macro_system_proc/README.md) | ✅ | 过程宏（Procedural Macro） |

---

## 八、FFI 与 unsafe {#八ffi-与-unsafe}

| Rust By Example 章节 | 项目文档/示例 | 状态 | 备注 |
|----------------------|---------------|------|------|
| [Unsafe Operations](https://doc.rust-lang.org/rust-by-example/unsafe.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | ✅ | unsafe 块 |
| [FFI](https://doc.rust-lang.org/rust-by-example/std_misc/ffi.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | ✅ | 外部函数接口 |

---

## 九、未覆盖缺口 {#九未覆盖缺口}

1. Rust By Example 中「Testing」「Std Library Types」部分可与项目测试文档进一步对齐。
2. 「Crates」章节与 Cargo Book 对齐矩阵可交叉引用（Reference）。
3. 未来可生成自动化的「项目示例 ↔ RBE 章节」反向索引。

> **权威来源**: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [This Week in Rust](https://this-week-in-rust.org/)
- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->
