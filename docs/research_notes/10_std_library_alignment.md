# Standard Library 对齐索引 {#standard-library-对齐索引}

> **EN**: Std Library Alignment
> **Summary**: Standard Library 对齐索引 Std Library Alignment.
> **概念族**: 权威来源对齐 / Standard Library
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Standard Library 对齐索引 {#standard-library-对齐索引}](#standard-library-对齐索引-standard-library-对齐索引)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、核心类型 {#二核心类型}](#二核心类型-二核心类型)
  - [三、所有权（Ownership）与借用（Borrowing）相关 {#三所有权与借用相关}](#三所有权与借用相关-三所有权与借用相关)
  - [四、并发与同步 {#四并发与同步}](#四并发与同步-四并发与同步)
  - [五、集合与迭代器（Iterator） {#五集合与迭代器}](#五集合与迭代器-五集合与迭代器)
  - [六、IO 与异步（Async） {#六io-与异步}](#六io-与异步-六io-与异步)
  - [七、FFI 与 unsafe 辅助 {#七ffi-与-unsafe-辅助}](#七ffi-与-unsafe-辅助-七ffi-与-unsafe-辅助)
  - [八、未覆盖缺口 {#八未覆盖缺口}](#八未覆盖缺口-八未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将 `docs/research_notes/` 中的概念、示例与 [Rust Standard Library](https://doc.rust-lang.org/std/) 的核心类型、trait、模块（Module）建立映射，确保代码实践与官方 API 对齐。

---

## 二、核心类型 {#二核心类型}

| std 模块（Module）/类型 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [std::option::Option](https://doc.rust-lang.org/std/option/enum.Option.html) | [crates/c03_control_fn/](../../crates/c03_control_fn/README.md) | ✅ | Option/Result 处理 |
| [std::result::Result](https://doc.rust-lang.org/std/result/enum.Result.html) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | ✅ | 错误处理（Error Handling） |
| [std::string::String](https://doc.rust-lang.org/std/string/struct.String.html) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §1 | ✅ | 所有权转移示例 |
| [std::vec::Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §2-§3 | ✅ | 借用示例 |
| [std::boxed::Box](https://doc.rust-lang.org/std/boxed/struct.Box.html) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §3 | ✅ | `Box<dyn Trait>` |

---

## 三、所有权与借用相关 {#三所有权与借用相关}

| std 模块/类型 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [std::rc::Rc](https://doc.rust-lang.org/std/rc/struct.Rc.html) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §1 | ✅ | 非线程安全引用（Reference）计数 |
| [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §1 | ✅ | 线程安全引用计数 |
| [std::cell::RefCell](https://doc.rust-lang.org/std/cell/struct.RefCell.html) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §2 | ✅ | 内部可变性 |
| [std::cell::Cell](https://doc.rust-lang.org/std/cell/struct.Cell.html) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §3 | ✅ | 内部可变性 |
| [std::marker::PhantomData](https://doc.rust-lang.org/std/marker/struct.PhantomData.html) | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | ✅ | 型变控制 |

---

## 四、并发与同步 {#四并发与同步}

| std 模块/类型 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §3-§4 | ✅ | 互斥锁 |
| [std::sync::RwLock](https://doc.rust-lang.org/std/sync/struct.RwLock.html) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §7 | ✅ | 读写锁 |
| [std::thread](https://doc.rust-lang.org/std/thread/index.html) | [crates/c05_threads/](../../crates/c05_threads/README.md) | ✅ | 线程 API |
| [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/index.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §3 | ✅ | 原子操作（Atomic Operations） |

---

## 五、集合与迭代器 {#五集合与迭代器}

| std 模块/类型 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [std::iter::Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html) | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | ✅ | trait 系统 |
| [std::collections](https://doc.rust-lang.org/std/collections/index.html) | [crates/c08_algorithms/](../../crates/c08_algorithms/README.md) | 🔄 | 数据结构示例 |

---

## 六、IO 与异步 {#六io-与异步}

| std 模块/类型 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [std::io](https://doc.rust-lang.org/std/io/index.html) | [crates/c10_networks/](../../crates/c10_networks/README.md) | 🔄 | IO 与网络 |
| [std::future::Future](https://doc.rust-lang.org/std/future/trait.Future.html) | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ | Future trait |
| [std::pin::Pin](https://doc.rust-lang.org/std/pin/struct.Pin.html) | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) | ✅ | Pin 保证 |

---

## 七、FFI 与 unsafe 辅助 {#七ffi-与-unsafe-辅助}

| std 模块/类型 | 项目文档 | 状态 | 备注 |
|---------------|----------|------|------|
| [std::ffi::CStr](https://doc.rust-lang.org/std/ffi/struct.CStr.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | ✅ | FFI 字符串 |
| [std::ptr](https://doc.rust-lang.org/std/ptr/index.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §1-§2 | ✅ | 裸指针操作 |
| [std::mem::MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §2 | 🔄 | 未初始化内存 |
| [std::mem::transmute](https://doc.rust-lang.org/std/mem/fn.transmute.html) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 | ✅ | 类型转换 |

---

## 八、未覆盖缺口 {#八未覆盖缺口}

1. `std::fmt`、`std::error::Error` trait 可进一步对齐。
2. `std::process`、`std::env` 等系统交互模块可补充。
3. `std::pin` 投影规则与 `pin-project` 生态可专门展开。

> **权威来源**: [Rust Standard Library](https://doc.rust-lang.org/std/)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [Rustonomicon 对齐](10_rustonomicon_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
