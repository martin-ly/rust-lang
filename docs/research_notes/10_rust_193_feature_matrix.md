# Rust 1.93 特性族多维概念矩阵
>
> **概念族**: 版本特性

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **权威来源**: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html) | [Rust Blog](https://blog.rust-lang.org/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Standard Library](https://doc.rust-lang.org/std/)

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 1.93 特性族多维概念矩阵](#rust-193-特性族多维概念矩阵)
  - [📑 目录](#-目录)
  - [1. 内存与所有权族](#1-内存与所有权族)
  - [2. 类型系统族](#2-类型系统族)
  - [3. Trait 与多态族](#3-trait-与多态族)
  - [4. 控制流与模式匹配族](#4-控制流与模式匹配族)
  - [5. 并发与异步族](#5-并发与异步族)
  - [6. 宏与元编程族](#6-宏与元编程族)
  - [7. 模块与可见性族](#7-模块与可见性族)
  - [8. 常量与编译期族](#8-常量与编译期族)
  - [9. FFI 与不安全族](#9-ffi-与不安全族)
  - [10. Rust 1.93 新增/变更族](#10-rust-193-新增变更族)
  - [11. Rust 1.95/1.96 新增/变更族](#11-rust-195196-新增变更族)
  - [相关文档](#相关文档)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要rust-1960--edition-2024)
    - [本次升级要点](#本次升级要点)
      - [新增 Rust 1.96.0 特性](#新增-rust-1960-特性)
      - [新增 Rust 1.95.0 特性](#新增-rust-1950-特性)
      - [权威来源对齐](#权威来源对齐)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

> **创建日期**: 2026-02-13
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）
> **目标**: 按特性族展开「概念-公理-定理-证明方法-反例」五维矩阵，便于逐特性查找
> **上位文档**: [UNIFIED_SYSTEMATIC_FRAMEWORK](10_unified_systematic_framework.md)、[RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](10_rust_193_language_features_comprehensive_analysis.md)

---

## 1. 内存与所有权族
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 所有权 | 每值恰一所有者 | 规则 1–3, Def 1.1–1.3 | T2 唯一性, T3 内存安全 | 结构归纳、反证 | 使用已移动值 |
| 借用 | 不可变可多、可变独占 | 规则 5–8 | T1 数据竞争自由 | 规则归纳 | 双重可变借用 |
| 生命周期 | 引用有效性约束 | $\ell \subseteq \text{lft}$ | T2 引用有效性 | 三步骤 | 返回局部引用 |
| Pin | 非 Unpin 位置稳定 | Def 1.1–2.2 | T1–T3 | 类型系统 | 非 Unpin 用 Pin::new |
| Box | 堆分配、单一所有权 | BOX1 | BOX-T1 | ownership_model | 使用已移动 Box |
| Rc/Arc | 共享所有权 | RC1/ARC1 | RC-T1 | ownership_model | 跨线程用 Rc |
| Cell/RefCell | 内部可变性 | CELL1/REFCELL1 | REFCELL-T1 | ownership_model | Cell 跨线程共享 |
| MaybeUninit | 延迟初始化 | MAYBEUNINIT1 | MAYBEUNINIT-T1 | ownership_model | 未初始化 assume_init |
| 智能指针 | Deref/Drop 语义 | DROP1/DEREF1 | DROP-T1/DEREF-T1 | ownership_model | 违反 Drop 顺序 |
| 裸指针 | FFI、unsafe 底层 | RAW1 | RAW-T1 | borrow_checker_proof | 解引用空指针 |
| 引用 | 借用、零成本 | &T、&mut T | borrow_checker | - | 悬垂引用 |
| 内存布局 | 与 C 互操作 | REPR1 | REPR-T1 | ownership_model | 错误布局导致 UB |

---

## 2. 类型系统族
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 基本类型 | 机器字、数值、布尔 | - | 进展性 T1、保持性 T2 | type_system_foundations | 溢出（debug panic） |
| 结构体 | 命名字段聚合 | struct | - | - | - |
| 枚举 | tagged union | enum | - | - | - |
| Never (!) | 不可达、发散 | BOT1 | BOT-T1 | type_system_foundations | 1.92 Lint 严格化 |
| Option/Result | 可选值、错误处理 | 构造性 | - | - | unwrap 空值 |
| 型变 | 子类型在泛型中传递 | Def 1.1–3.1 | T1–T4 | variance_theory | &mut 协变 |
| 类型推断 | 减少注解 | 局部推断 | - | - | 歧义时报错 |
| 类型别名 | 简化复杂类型 | type Alias = T | - | - | - |
| 单元类型 () | 无返回值 | 唯一值 () | - | - | - |
| 数组/切片 | 连续内存 | [T; N]、[T] | - | - | 越界 panic |
| str | UTF-8 字符串 | &str、String | - | - | 非 UTF-8 |
| impl Trait | 匿名泛型返回值 | 存在类型 | DYN-T1 | trait_system_formalization | - |
| dyn Trait | 运行时多态 | vtable、对象安全 | - | trait_system_formalization | Clone 非对象安全 |
| Sized | 编译时已知大小 | 默认约束 | - | - | 未 Sized 的 DST |
| Clone/Copy | 显式复制语义 | Copy 位复制 | - | ownership_model | 1.93 Copy 不再 specialization |

---

## 3. Trait 与多态族
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Trait | 行为抽象、多态 | trait、impl for | COH-T1 | trait_system_formalization | - |
| 泛型 | 编译时多态 | 单态化 | - | - | 歧义 impl |
| 关联类型 | Trait 内类型抽象 | type Item | - | - | - |
| GATs | 泛型关联类型 | type Item<'a> | AT-L1 | advanced_types | 约束违反 |
| const 泛型 | 编译时常量参数 | [T; N] | - | advanced_types | 非 const 作参数 |
| Trait 对象 | 运行时多态 | dyn Trait | - | trait_system | 对象安全违规 |
| Send/Sync | 跨线程安全 | Send=可转移、Sync=可共享 | T6.1–T6.3 | async_state_machine | Rc 非 Send |
| Unpin | Pin 的反面 | Def 2.2 | T1–T3 | pin_self_referential | 非 Unpin 栈固定 |
| blanket impl | 泛型实现 | impl<T: Trait> Foo for T | - | - | 冲突 impl |
| Trait 继承 | Trait 组合 | trait B: A | - | - | - |

---

## 4. 控制流与模式匹配族
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| if/else | 条件分支 | 表达式 | - | - | - |
| match | 穷尽模式匹配 | MATCH1 | MATCH-T1 | borrow_checker_proof | 非穷尽 match |
| if let | 单模式匹配 | - | - | - | - |
| loop | 无限循环 | loop、break 返回值 | - | - | - |
| while | 条件循环 | - | - | - | - |
| for | 迭代 | FOR1 | FOR-T1 | borrow_checker_proof | 迭代中修改集合 |
| ? 操作符 | 错误传播 | QUERY1 | QUERY-T1 | borrow_checker_proof | 非 Result 类型 |
| 模式 | 解构、绑定 | ref、mut、@、.. | - | - | 非穷尽 |

---

## 5. 并发与异步族
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 线程 | 多核并行 | SPAWN1 | SPAWN-T1 | async_state_machine | 非 Send 跨线程 |
| Future | 异步 I/O | Def 4.1–5.2 | T6.1–T6.3 | async_state_machine | 未 Pin 自引用 |
| async/await | 异步语法糖 | 生成状态机 | - | async_state_machine | 非 Send 跨 await |
| Pin | Future 位置稳定 | 见内存族 | - | pin_self_referential | - |
| Send/Sync | 见 Trait 族 | - | - | async_state_machine | - |
| 通道 | 消息传递 | CHAN1 | CHAN-T1 | borrow_checker_proof | 发送端 drop 后接收 |
| Mutex/RwLock | 共享可变 | MUTEX1 | MUTEX-T1 | borrow_checker_proof | 死锁 |
| 原子操作 | 无锁并发 | ATOMIC1 | ATOMIC-T1 | ownership_model | 错误内存顺序 |

---

## 6. 宏与元编程族
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 声明宏 | 代码生成、DSL | macro_rules! | - | - | 意外捕获 |
| 过程宏 | 编译器扩展 | derive、attr、function | - | - | 非卫生导致冲突 |
| 属性宏 | 标注语法 | #[attribute] | - | - | 无效位置 |
| derive 宏 | 自动实现 | #[derive(Clone)] | - | - | 自定义 derive 错误 |
| cfg | 条件编译 | #[cfg(...)] | - | - | 1.93 关键词作谓词报错 |

---

## 7. 模块与可见性族
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| mod | 代码组织 | mod、文件即模块 | - | - | 循环依赖 |
| use | 导入简写 | use、pub use | - | - | 私有项导出 |
| pub | 可见性 | pub、pub(crate) | - | - | 越权访问 |
| crate | 包边界 | crate 根 | - | - | - |

---

## 8. 常量与编译期族
>
> **[来源: [crates.io](https://crates.io/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| const | 编译期常量 | const X: T = ... | - | advanced_types | 非常量表达式 |
| const fn | 编译期可求值 | 受限操作 | - | advanced_types | 非 const 操作 |
| const 泛型 | 见 Trait 族 | - | - | - | - |
| const 中 mutable ref | 1.93 允许 | const 含 &mut static | CONST-MUT1 | advanced_types | const_item_interior_mutations |
| const-eval | 编译期求值 | 1.93 指针字节复制 | - | - | - |
| inline | 内联提示 | #[inline] | - | - | - |

---

## 9. FFI 与不安全族
>
> **[来源: [docs.rs](https://docs.rs/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| unsafe | 绕过借用、类型检查 | UNSAFE1 | UNSAFE-T1/T2 | borrow_checker_proof | 违反契约 UB |
| extern | C/FFI 互操作 | EXTERN1 | EXTERN-T1 | borrow_checker_proof | ABI 不匹配 |
| C variadic | 1.93 C 风格可变参数 | CVARIADIC1 | - | borrow_checker_proof | 非 system ABI |
| 裸指针 | 见内存族 | RAW1 | - | - | deref_nullptr 1.93 deny |
| union | C 互操作 | UNION1 | - | ownership_model | 非活动字段读取 |
| transmute | 类型重解释 | TRANSMUTE1 | TRANSMUTE-T1 | ownership_model | 大小/对齐不匹配 |

---

## 10. Rust 1.93 新增/变更族
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| s390x vector | s390x SIMD | is_s390x_feature_detected! | - | toolchain | 非 s390x 架构 |
| C variadic | printf 等 FFI | extern "system" fn(..., ...) | - | toolchain | 非 system ABI |
| cfg 关键词 | 避免误用 | 关键词作 cfg 谓词报错 | - | toolchain | - |
| asm_cfg | 条件汇编 | #[cfg] 在 asm! 行上 | - | toolchain | - |
| LUB coercion | 类型推断正确性 | 修正函数项、安全性 | LUB-T1 | type_system_foundations | - |
| const &mut static | 允许特定 const | 非常 unsafe | CONST-MUT1 | advanced_types | const_item_interior_mutations |
| const_item_interior_mutations | 安全警示 | warn-by-default lint | - | toolchain | - |
| function_casts_as_integer | 可移植性 | warn-by-default | - | toolchain | - |
| deref_nullptr | 安全 | deny-by-default | DEREF-NULL1 | type_system_foundations | 解引用空指针 |
| Copy specialization 移除 | 生命周期安全 | 不再内部 specialization | COP-T1 | type_system_foundations | 可能性能回归 |
| 全局分配器 thread_local | 避免重入 | 允许 thread_local! | - | toolchain | - |

---

## 11. Rust 1.95/1.96 新增/变更族

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**
> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**
> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**

| 特性 | 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `core::range` 新类型 | [`Copy`](https://doc.rust-lang.org/stable/core/marker/trait.Copy.html) + [`IntoIterator`](https://doc.rust-lang.org/stable/core/iter/trait.IntoIterator.html) 范围 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) | RANGE-T1 | type_system_foundations | 混用 legacy `std::ops::Range` |
| `assert_matches!` | 模式断言宏（[core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)） | ASSERT-MATCH1 | - | - | 模式不匹配时 panic |
| `debug_assert_matches!` | 调试模式断言宏（[core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)） | ASSERT-MATCH-D1 | - | - | 仅在 debug 生效 |
| `if let` guards | match 臂 [`if let` 守卫](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards) | GUARD1 | GUARD-T1 | borrow_checker_proof | 绑定作用域错误 |
| `cfg_select!` | 编译期 cfg 选择（[std::cfg_select!](https://doc.rust-lang.org/stable/std/macro.cfg_select.html)、[Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)） | CFG-SEL1 | - | macro_expansion | 无匹配分支 |
| PowerPC inline asm | 内联汇编平台扩展（[Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)） | ASM-PPC1 | - | toolchain | 非 PowerPC 目标 |
| Cargo CVE-2026-5223 | tarball symlink 安全 | [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)、[Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28) | - | toolchain | 第三方 registry 恶意 crate |
| Cargo CVE-2026-5222 | URL 规范化认证 | [CVE-2026-5222](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/)、[Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28) | - | toolchain | 规范化后凭据泄露 |
| WebAssembly 链接行为变更 | 不再默认传递 `--allow-undefined`（[Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/#changes-to-webassembly-targets)、[rustc#149868](https://github.com/rust-lang/rust/pull/149868)） | WASM-LINK1 | - | toolchain | 未定义符号被静默导入 |
| Cargo `target.'cfg(..)'.rustdocflags` | 按 `cfg` 条件设置 rustdocflags | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16846](https://github.com/rust-lang/cargo/pull/16846) | - | toolchain | 配置位置错误 |
| dependency 同时指定 git 与 alternate registry | 本地 git、发布 registry | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16810](https://github.com/rust-lang/cargo/pull/16810) | - | toolchain | registry 不一致 |

---

## 相关文档
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 文档 | 用途 |
| :--- | :--- |
| [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](10_rust_193_language_features_comprehensive_analysis.md) | 92 项特性完整分析 |
| [UNIFIED_SYSTEMATIC_FRAMEWORK](10_unified_systematic_framework.md) | 全局统一框架、五维矩阵总览 |
| [PROOF_INDEX](10_proof_index.md) | 形式化证明索引 |
| [toolchain/07_rust_1.93_full_changelog](../06_toolchain/06_07_rust_1_93_full_changelog.md) | Rust 1.93 完整变更清单 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-06-29
**状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）

---

## ✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs](https://releases.rs/)**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **升级日期**: 2026-06-29

### 本次升级要点

本文档已完成权威国际化来源对齐升级，统一版本基准为 **Rust 1.96.0+ / Edition 2024**，同时保留 1.93/1.94 历史分析章节。

#### 新增 Rust 1.96.0 特性

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `core::range` 新类型 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) | `Range`/`RangeFrom`/`RangeInclusive` 实现 `Copy` + `IntoIterator` |
| `assert_matches!` / `debug_assert_matches!` | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html) | 模式断言宏，失败输出 Debug 信息 |
| Cargo CVE-2026-5223 / CVE-2026-5222 修复 | [Cargo 安全公告](https://github.com/rust-lang/cargo/security/advisories)、[Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 第三方 registry tarball symlink 与 URL 规范化修复 |
| WebAssembly 链接行为变更 | [Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 不再默认传递 `--allow-undefined` |
| Cargo `target.'cfg(..)'.rustdocflags` | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16846](https://github.com/rust-lang/cargo/pull/16846) | 按 `cfg` 条件设置 rustdocflags |
| dependency 同时指定 git 与 alternate registry | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16810](https://github.com/rust-lang/cargo/pull/16810) | 本地 git，发布 registry |

#### 新增 Rust 1.95.0 特性

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `if let` guards on match arms | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | match 臂支持 `if let` 守卫 |
| `cfg_select!` 宏 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)、[releases.rs 1.95.0](https://releases.rs/docs/1.95.0/) | 编译期 cfg 条件选择宏 |
| PowerPC / PowerPC64 内联汇编稳定化 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 稳定 inline assembly for PowerPC |
| `--remap-path-scope` | [Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 控制路径重映射作用域 |
| `cargo init` 禁止在主目录执行 | [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)、[cargo#16566](https://github.com/rust-lang/cargo/pull/16566) | 避免清单发现混乱 |
| `cargo package` 覆盖大 crate 文件损坏修复 | [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)、[cargo#16713](https://github.com/rust-lang/cargo/pull/16713) | 修复 `.crate` 覆盖损坏 |

#### 权威来源对齐

- Rust release notes（releases.rs）
- Rust Blog 对应版本发布公告
- Rust Reference 具体章节（Range Expressions、Match Guards、Inline Assembly、Conditional Compilation）
- Rust Standard Library 具体 API（`core::range`、`core::assert_matches`、`std::ops::ControlFlow`）
- RFC 链接（RFC 3550 等）

---

## 相关概念
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **来源: [Rust Reference - Feature Gates](https://doc.rust-lang.org/reference/)**
> **来源: [Rust Release Notes](https://github.com/rust-lang/rust/blob/master/RELEASES.md)**
> **来源: [RFCs - rust-lang/rfcs](https://github.com/rust-lang/rfcs)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Compiler Team Blog](https://blog.rust-lang.org/inside-rust/)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**
> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**
> **来源: [Rust Reference - Range Expressions](https://doc.rust-lang.org/reference/expressions/range-expr.html)**
> **来源: [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)**
> **来源: [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)**
> **来源: [Rust Standard Library - core::range](https://doc.rust-lang.org/stable/core/range/index.html)**
> **来源: [Rust Standard Library - assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)**
> **来源: [Rust Standard Library - cfg_select!](https://doc.rust-lang.org/stable/std/macro.cfg_select.html)**
> **来源: [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)**
> **来源: [CVE-2026-5222](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/)**
> **来源: [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)**
> **来源: [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)**

---
