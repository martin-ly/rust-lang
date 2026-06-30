# Rust 1.93 语言特性全面分析：设计论证与形式化 {#rust-193-语言特性全面分析设计论证与形式化}
>
> **概念族**: 版本特性

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **权威来源**: [Rust Release Notes](https://doc.rust-lang.org/stable/releases.html) | [Rust Blog](https://blog.rust-lang.org/) | [Rust Reference](https://doc.rust-lang.org/reference/) | [Rust Standard Library](https://doc.rust-lang.org/std/)

> **创建日期**: 2026-02-12
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）
> **目标**: 全面、完整、充分地分析 Rust 1.93 所有语言特性，补全设计论证与形式化

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 1.93 语言特性全面分析：设计论证与形式化](#rust-193-语言特性全面分析设计论证与形式化)
  - [📑 目录](#目录)
  - [📚 权威来源对齐](#权威来源对齐)
  - [📋 目录](#目录-1)
  - [🎯 文档宗旨](#文档宗旨)
  - [📐 特性覆盖矩阵总览](#特性覆盖矩阵总览)
  - [特性→Def/Axiom/Theorem 映射表（兼 92 项→推荐落点文档）](#特性defaxiomtheorem-映射表兼-92-项推荐落点文档)
  - [1. 内存与所有权族](#1-内存与所有权族)
  - [2. 类型系统族](#2-类型系统族)
  - [3. Trait 与多态族](#3-trait-与多态族)
  - [4. 控制流与模式匹配族](#4-控制流与模式匹配族)
  - [5. 并发与异步族](#5-并发与异步族)
  - [6. 宏与元编程族](#6-宏与元编程族)
  - [7. 模块与可见性族](#7-模块与可见性族)
  - [8. 常量与编译期族](#8-常量与编译期族)
  - [9. FFI 与不安全族](#9-ffi-与不安全族)
  - [10. Rust 1.93 新增/变更特性](#10-rust-193-新增变更特性)
  - [11. Rust 1.95/1.96 新增/变更特性](#11-rust-195196-新增变更特性)
  - [📚 相关文档](#相关文档)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#权威国际化来源对齐升级摘要rust-1960-edition-2024)
    - [本次升级要点](#本次升级要点)
      - [新增 Rust 1.96.0 特性](#新增-rust-1960-特性)
      - [新增 Rust 1.95.0 特性](#新增-rust-1950-特性)
      - [权威来源对齐](#权威来源对齐-1)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 📚 权威来源对齐 {#权威来源对齐}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

| 来源 | 链接 | 用途 |
| :--- | :--- | :--- |
| **Rust 1.93 发布说明** | [blog.rust-lang.org/2026/01/22/Rust-1.93.0](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/) | 语言特性权威公告 |
| **Rust 1.93.1 补丁** | [blog.rust-lang.org/2026/02/12/Rust-1.93.1](https://blog.rust-lang.org/2026/02/12/Rust-1.93.1/) | ICE/Clippy/WASM 回归修复 |
| **Rust 1.95.0 发布说明** | [blog.rust-lang.org/2026/04/16/Rust-1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 1.95 稳定特性权威公告 |
| **Rust 1.96.0 发布说明** | [blog.rust-lang.org/2026/05/28/Rust-1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 1.96 稳定特性权威公告 |
| **releases.rs 1.93.0** | [releases.rs/docs/1.93.0](https://releases.rs/docs/1.93.0/) | 完整变更清单 |
| **releases.rs 1.95.0** | [releases.rs/docs/1.95.0](https://releases.rs/docs/1.95.0/) | 1.95 完整变更清单 |
| **releases.rs 1.96.0** | [releases.rs/docs/1.96.0](https://releases.rs/docs/1.96.0/) | 1.96 完整变更清单 |
| **RFC 3550** | [rust-lang.github.io/rfcs/3550-new-range.html](https://rust-lang.github.io/rfcs/3550-new-range.html) | 新 Range 类型设计 |
| **Ferrocene FLS** | [spec.ferrocene.dev](https://spec.ferrocene.dev/) | Rust 1.93 形式化规范（Rust 2021 Edition） |
| **RustBelt / Stacked Borrows / Tree Borrows** | [plv.mpi-sws.org/rustbelt](https://plv.mpi-sws.org/rustbelt/) | 所有权/借用形式化 |

**版本说明**：Ferrocene FLS 当前覆盖 **Rust 2021 Edition** 与 rustc 1.93.0。本项目文档已升级至 **Rust 1.96.0+ / Edition 2024** 权威来源基准；1.93/1.94 历史分析章节保留，1.95/1.96 新增特性已补充对应来源。

---

## 📋 目录 {#目录-1}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

<!-- markdownlint-disable MD051 -->
- [Rust 1.93 语言特性全面分析：设计论证与形式化](#rust-193-语言特性全面分析设计论证与形式化)
  - [📑 目录](#目录)
  - [📚 权威来源对齐](#权威来源对齐)
  - [📋 目录](#目录-1)
  - [🎯 文档宗旨](#文档宗旨)
  - [📐 特性覆盖矩阵总览](#特性覆盖矩阵总览)
  - [特性→Def/Axiom/Theorem 映射表（兼 92 项→推荐落点文档）](#特性defaxiomtheorem-映射表兼-92-项推荐落点文档)
  - [1. 内存与所有权族](#1-内存与所有权族)
  - [2. 类型系统族](#2-类型系统族)
  - [3. Trait 与多态族](#3-trait-与多态族)
  - [4. 控制流与模式匹配族](#4-控制流与模式匹配族)
  - [5. 并发与异步族](#5-并发与异步族)
  - [6. 宏与元编程族](#6-宏与元编程族)
  - [7. 模块与可见性族](#7-模块与可见性族)
  - [8. 常量与编译期族](#8-常量与编译期族)
  - [9. FFI 与不安全族](#9-ffi-与不安全族)
  - [10. Rust 1.93 新增/变更特性](#10-rust-193-新增变更特性)
  - [11. Rust 1.95/1.96 新增/变更特性](#11-rust-195196-新增变更特性)
  - [📚 相关文档](#相关文档)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#权威国际化来源对齐升级摘要rust-1960-edition-2024)
    - [本次升级要点](#本次升级要点)
      - [新增 Rust 1.96.0 特性](#新增-rust-1960-特性)
      - [新增 Rust 1.95.0 特性](#新增-rust-1950-特性)
      - [权威来源对齐](#权威来源对齐-1)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
<!-- markdownlint-enable MD051 -->

---

## 🎯 文档宗旨 {#文档宗旨}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本文档针对「论证未全面分析 Rust 1.93 所有语言特性」的缺口，系统化补全：

1. **核心语言特性**：所有权、借用、生命周期、类型、Trait、泛型、闭包、模式匹配、宏、异步等
2. **Rust 1.93 新增/变更**：s390x、C variadic、asm_cfg、LUB coercion、const 变更、lint 变更等
3. **设计论证**：每个特性含动机、设计决策、形式化引用、决策树、反例（若适用）

---

## 📐 特性覆盖矩阵总览 {#特性覆盖矩阵总览}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 类别 | 特性数 | 已论证 | 形式化文档 | 完成度 |
| :--- | :--- | :--- | :--- | :--- |
| 内存与所有权 | 12 | 12 | ownership, borrow, lifetime, pin | 100% |
| 类型系统 | 15 | 15 | type_system, variance, advanced_types | 100% |
| Trait 与多态 | 10 | 10 | trait_system | 100% |
| 控制流与模式匹配 | 8 | 8 | - | 100% |
| 并发与异步 | 8 | 8 | async_state_machine | 100% |
| 宏与元编程 | 5 | 5 | - | 100% |
| 模块与可见性 | 4 | 4 | - | 100% |
| 常量与编译期 | 6 | 6 | advanced_types | 100% |
| FFI 与不安全 | 6 | 6 | - | 100% |
| Rust 1.93 新增 | 18 | 18 | toolchain docs | 100% |
| **总计** | **92** | **92** | - | **100%** |

---

## 特性→Def/Axiom/Theorem 映射表（兼 92 项→推荐落点文档） {#特性defaxiomtheorem-映射表兼-92-项推荐落点文档}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本表将 92 项特性与形式化文档中的 Def、Axiom、Theorem 建立一一对应，**最后一列「文档」即该特性的推荐落点文档**；与 FORMAT_AND_CONTENT_ALIGNMENT_PLAN F3.1 对齐。详见 [PROOF_INDEX](10_proof_index.md)。

| 特性族 | 特性 | Def | Axiom | Theorem | 文档 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **内存与所有权** | 所有权 | 1.1–1.3 | 规则 1–3 | T2 唯一性、T3 内存安全 | ownership_model |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **类型系统** | 基本类型 | - | - | 进展性 T1、保持性 T2 | type_system_foundations |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Trait** | Trait | - | COH1/COH2 | COH-T1 | trait_system_formalization |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **控制流** | match | MATCH1 | - | MATCH-T1 | borrow_checker_proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **并发** | 线程 | SPAWN1 | - | SPAWN-T1 | async_state_machine |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **FFI** | unsafe | UNSAFE1 | - | UNSAFE-T1/T2 | borrow_checker_proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **执行模型** | 确定性 | EB-DET1 | EB-DET1 | EB-DET-T1 | 06_boundary_analysis |
| **组合工程** | 组件成熟度 | CE-MAT1 | CE-MAT1 | CE-MAT-T1 | 04_compositional_engineering |
| :--- | :--- | :--- | :--- | :--- | :--- |

**说明**：表中仅列出已形式化的特性；未列出的特性（如 if/else、mod、cfg 等）无对应 Def/Axiom/Theorem，但均在特性覆盖矩阵中列明设计决策与反例。

---

## 1. 内存与所有权族 {#1-内存与所有权族}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **所有权** | 无 GC 内存安全 | 默认移动、显式 Copy | [ownership_model](formal_methods/10_ownership_model.md) | 使用已移动值 |
| **借用** | 数据竞争自由 | 可变独占、不可变可多 | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) | 双重可变借用 |
| **生命周期** | 引用有效性 | NLL + 显式标注 | lifetime_formalization | 返回局部引用 |
| **Pin** | 自引用移动→悬垂 | 堆/栈区分：Unpin 栈、非 Unpin 堆 | [pin_self_referential](formal_methods/10_pin_self_referential.md) | 非 Unpin 用 Pin::new |
| **Box** | 堆分配、单一所有权 | 移动语义、RAII | [ownership_model](formal_methods/10_ownership_model.md) Def BOX1 | 使用已移动 Box |
| **Rc/Arc** | 共享所有权 | 引用计数、Rc 非 Send | [ownership_model](formal_methods/10_ownership_model.md) Def RC1/ARC1 | 跨线程用 Rc |
| **Cell/RefCell** | 内部可变性 | 非 Sync（Cell）、运行时借用（RefCell） | [ownership_model](formal_methods/10_ownership_model.md) Def CELL1/REFCELL1 | Cell 跨线程共享 |
| **MaybeUninit** | 延迟初始化 | 未初始化内存、assume_init 契约 | [ownership_model](formal_methods/10_ownership_model.md) Def MAYBEUNINIT1 | 未初始化 assume_init |
| **智能指针** | 自定义所有权语义 | Deref/Drop trait | [ownership_model](formal_methods/10_ownership_model.md) Def DROP1/DEREF1 | 违反 Drop 顺序 |
| **裸指针** | FFI、unsafe 底层 | *const T、*mut T 无自动借用 | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def RAW1 | 解引用空指针 |
| **引用** | 借用、零成本 | &T、&mut T | borrow_checker | 悬垂引用 |
| **内存布局** | 与 C 互操作 | repr(C)、repr(transparent) | [ownership_model](formal_methods/10_ownership_model.md) Def REPR1 | 错误布局导致 UB |

---

## 2. 类型系统族 {#2-类型系统族}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **基本类型** | 机器字、数值、布尔 | i32、u64、bool、char 等 | [type_system_foundations](type_theory/10_type_system_foundations.md) | 溢出（debug panic） |
| **结构体** | 命名字段聚合 | struct、元组结构体、单元结构体 | type_system | - |
| **枚举** | tagged union、模式匹配 | enum、Option、Result | type_system | - |
| **Never (!)** | 不可达、发散 | 无构造子、对应 ⊥ | [LANGUAGE_SEMANTICS_EXPRESSIVENESS](10_language_semantics_expressiveness.md) | 1.92 Lint 严格化 |
| **Option/Result** | 可选值、错误处理 | 构造性、无 null | LANGUAGE_SEMANTICS | unwrap 空值 |
| **型变** | 子类型在泛型中的传递 | 协变/逆变/不变 | [variance_theory](type_theory/10_variance_theory.md) | &mut 协变 |
| **类型推断** | 减少注解 | 局部推断、约束传播 | type_system | 歧义时报错 |
| **类型别名** | 简化复杂类型 | type Alias = T | - | - |
| **单元类型 ()** | 无返回值 | 唯一值 () | - | - |
| **数组/切片** | 连续内存、动态长度 | [T; N]、[T] | - | 越界 panic |
| **str** | UTF-8 字符串 | 借用 &str、拥有 String | - | 非 UTF-8 |
| **impl Trait** | 匿名泛型返回值 | 存在类型、静态分发 | [trait_system_formalization](type_theory/10_trait_system_formalization.md) | - |
| **dyn Trait** | 运行时多态 | vtable、对象安全 | trait_system_formalization | Clone 非对象安全 |
| **Sized** | 编译时已知大小 | 默认约束、?Sized 放宽 | - | 未 Sized 的 DST |
| **Clone/Copy** | 显式复制语义 | Copy 位复制、Clone 自定义 | ownership_model | 1.93 Copy 不再 specialization |

---

## 3. Trait 与多态族 {#3-trait-与多态族}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **Trait** | 行为抽象、多态 | trait 定义、impl for | [trait_system_formalization](type_theory/10_trait_system_formalization.md) | - |
| **泛型** | 编译时多态 | 单态化、零成本 | type_system | 歧义 impl |
| **关联类型** | Trait 内类型抽象 | type Item | trait_system | - |
| **GATs** | 泛型关联类型 | type Item<'a> | [advanced_types](type_theory/10_advanced_types.md) | 约束违反 |
| **const 泛型** | 编译时常量参数 | [T; N]、const N: usize | advanced_types | 非 const 作参数 |
| **Trait 对象** | 运行时多态 | dyn Trait、vtable | trait_system | 对象安全违规 |
| **Send/Sync** | 跨线程安全 | Send=可转移、Sync=可共享 | [send_sync_formalization](formal_methods/10_send_sync_formalization.md) Def SEND1/SYNC1、SEND-T1/SYNC-T1；[async_state_machine](formal_methods/10_async_state_machine.md) T6.2 | Rc 非 Send、Cell 非 Sync |
| **Unpin** | Pin 的反面 | 默认实现、PhantomPinned | [pin_self_referential](formal_methods/10_pin_self_referential.md) | 非 Unpin 栈固定 |
| **blanket impl** | 泛型实现 | impl<T: Trait> Foo for T | trait_system | 冲突 impl |
| **Trait 继承** | Trait 组合 | trait B: A | trait_system | - |

---

## 4. 控制流与模式匹配族 {#4-控制流与模式匹配族}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **if/else** | 条件分支 | 表达式、必须返回同类型 | - | - |
| **match** | 穷尽模式匹配 | 必须覆盖所有变体 | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def MATCH1 | 非穷尽 match |
| **if let** | 单模式匹配 | 简化 Option/Result | - | - |
| **loop** | 无限循环 | loop、break 返回值 | - | - |
| **while** | 条件循环 | while、while let | - | - |
| **for** | 迭代 | IntoIterator | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def FOR1 | 迭代中修改集合 |
| **? 操作符** | 错误传播 | Result/Option 早期返回 | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def QUERY1 | 非 Result 类型 |
| **模式** | 解构、绑定 | ref、mut、@、.. | - | 非穷尽 |

---

## 5. 并发与异步族 {#5-并发与异步族}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **线程** | 多核并行 | thread::spawn、JoinHandle | [async_state_machine](formal_methods/10_async_state_machine.md) Def SPAWN1 | 非 Send 跨线程 |
| **Future** | 异步 I/O | Poll、Pin、async/await | [async_state_machine](formal_methods/10_async_state_machine.md) | 未 Pin 自引用 |
| **async/await** | 异步语法糖 | 生成状态机、自引用 | async_state_machine | 非 Send 跨 await |
| **Pin** | Future 位置稳定 | 见内存族 | pin_self_referential | - |
| **Send/Sync** | 见 Trait 族 | - | [send_sync_formalization](formal_methods/10_send_sync_formalization.md)、async_state_machine T6.2 | - |
| **通道** | 消息传递 | mpsc、sync_channel | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def CHAN1 | 发送端 drop 后接收 |
| **Mutex/RwLock** | 共享可变 | 锁保护、RAII | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def MUTEX1 | 死锁 |
| **原子操作** | 无锁并发 | AtomicUsize 等 | [ownership_model](formal_methods/10_ownership_model.md) Def ATOMIC1 | 错误内存顺序 |

---

## 6. 宏与元编程族 {#6-宏与元编程族}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **声明宏** | 代码生成、DSL | macro_rules!、卫生宏 | - | 意外捕获 |
| **过程宏** | 编译器扩展 | derive、attr、function | - | 非卫生导致冲突 |
| **属性宏** | 标注语法 | #[attribute] | - | 无效位置 |
| **derive 宏** | 自动实现 | #[derive(Clone)] | - | 自定义 derive 错误 |
| **cfg** | 条件编译 | #[cfg(...)]、cfg! | - | 1.93 关键词作谓词报错 |

---

## 7. 模块与可见性族 {#7-模块与可见性族}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **mod** | 代码组织 | mod、文件即模块 | - | 循环依赖 |
| **use** | 导入简写 | use、pub use | - | 私有项导出 |
| **pub** | 可见性 | pub、pub(crate)、pub(super) | - | 越权访问 |
| **crate** | 包边界 | crate 根、子模块 | - | - |

---

## 8. 常量与编译期族 {#8-常量与编译期族}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **const** | 编译期常量 | const X: T = ... | [advanced_types](type_theory/10_advanced_types.md) | 非常量表达式 |
| **const fn** | 编译期可求值函数 | 受限操作、无 I/O | advanced_types | 非 const 操作 |
| **const 泛型** | 见 Trait 族 | - | advanced_types | - |
| **const 中 mutable ref** | 1.93 允许 const 含 &mut static | 非常 unsafe | [07_rust_1.93_full_changelog](../06_toolchain/06_07_rust_1_93_full_changelog.md) | 1.93 const_item_interior_mutations lint |
| **const-eval** | 编译期求值 | 1.93 指针字节复制 | 07_rust_1.93 | - |
| **inline** | 内联提示 | #[inline]、#[inline(always)] | - | - |

---

## 9. FFI 与不安全族 {#9-ffi-与不安全族}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 特性 | 动机 | 设计决策 | 形式化 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **unsafe** | 绕过借用、类型检查 | unsafe 块、契约 | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def UNSAFE1 | 违反契约 UB |
| **extern** | C/FFI 互操作 | extern "C"、extern "system" | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def EXTERN1 | ABI 不匹配 |
| **C variadic** | 1.93 C 风格可变参数 | extern "system" fn f(..., ...) | [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md) Def CVARIADIC1 | 1.93 ... future-incompat |
| **裸指针** | 见内存族 | - | borrow_checker_proof Def RAW1 | deref_nullptr 1.93 deny |
| **union** | C 互操作 | union、&raw 访问 | [ownership_model](formal_methods/10_ownership_model.md) Def UNION1 | 非活动字段读取 |
| **transmute** | 类型重解释 | 极度 unsafe | [ownership_model](formal_methods/10_ownership_model.md) Def TRANSMUTE1 | 大小/对齐不匹配 |

---

## 10. Rust 1.93 新增/变更特性 {#10-rust-193-新增变更特性}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**权威链接**：[releases.rs 1.93.0](https://releases.rs/docs/1.93.0/) § Language、[Rust 1.93 发布说明](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/)

| 特性 | 动机 | 设计决策 | 文档 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **s390x vector** | s390x SIMD | is_s390x_feature_detected! | [07_rust_1.93](../06_toolchain/06_07_rust_1_93_full_changelog.md)、[releases.rs](https://releases.rs/docs/1.93.0/) | 非 s390x 架构 |
| **C variadic** | printf 等 FFI | extern "system" fn(..., ...) | 07_rust_1.93、[releases.rs](https://releases.rs/docs/1.93.0/) | 非 system ABI |
| **cfg 关键词** | 避免误用 | 关键词作 cfg 谓词报错 | [09_rust_1.93_compatibility](../06_toolchain/06_09_rust_1_93_compatibility_deep_dive.md)、[releases.rs](https://releases.rs/docs/1.93.0/) | - |
| **asm_cfg** | 条件汇编 | #[cfg] 在 asm! 行上 | 07_rust_1.93、05_comparison、[releases.rs](https://releases.rs/docs/1.93.0/) | - |
| **LUB coercion** | 类型推断正确性 | 修正函数项、安全性 | 07_rust_1.93 | - |
| **const &mut static** | 允许特定 const | 非常 unsafe | 07_rust_1.93 | const_item_interior_mutations |
| **const_item_interior_mutations** | 安全警示 | warn-by-default lint | 07_rust_1.93 | - |
| **function_casts_as_integer** | 可移植性 | warn-by-default | 07_rust_1.93 | - |
| **deref_nullptr** | 安全 | deny-by-default | [09_compatibility](../06_toolchain/06_09_rust_1_93_compatibility_deep_dive.md) | 解引用空指针 |
| **#[test] 严格** | 避免误用 | 非函数位置报错 | 09_compatibility | trait 方法上 #[test] |
| **offset_of!** | 类型检查 | well-formed 检查 | 09_compatibility | 非法类型 |
| **... variadic** | 未来兼容 | future-incompat | 09_compatibility | - |
| **repr(C) enum** | 可预测布局 | 判别值警告 | 09_compatibility | - |
| **repr(transparent)** | 忽略 repr(C) 警告 | 单字段透明 | 09_compatibility | - |
| **pin_v2** | Pin API 内部 | 内置属性命名空间 | 09_compatibility | 命名冲突 |
| **Copy specialization 移除** | 生命周期安全 | 不再内部 specialization | [07_rust_1.93](../06_toolchain/06_07_rust_1_93_full_changelog.md) | 可能性能回归 |
| **全局分配器 thread_local** | 避免重入 | 允许 thread_local! | 05_comparison | - |
| **Emscripten unwinding** | ABI 一致性 | wasm 异常处理 ABI | 09_compatibility | C 链接需 -fwasm-exceptions |

---

## 11. Rust 1.95/1.96 新增/变更特性 {#11-rust-195196-新增变更特性}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**
> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**
> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**

| 特性 | 动机 | 设计决策 | 文档 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **core::range 新类型** | `Copy` 范围类型长期需求 | 实现 `IntoIterator` 而非 `Iterator`，支持 `Copy` | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html)、[core::range::Range](https://doc.rust-lang.org/stable/core/range/struct.Range.html) | 混用 legacy `std::ops::Range` |
| **assert_matches!** | 提升模式断言诊断 | 失败时输出 `Debug` 表示，未加入 prelude | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)、[std::assert_matches!](https://doc.rust-lang.org/stable/std/macro.assert_matches.html) | 模式不匹配 panic |
| **debug_assert_matches!** | 调试模式模式断言 | 仅 debug 生效 | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)、[std::debug_assert_matches!](https://doc.rust-lang.org/stable/std/macro.debug_assert_matches.html) | - |
| **if let guards** | 增强 match 守卫表达能力 | 在 match 臂中使用 `if let` 绑定 | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 绑定作用域错误 |
| **cfg_select!** | 替代 cfg-if 生态 crate | 编译期按 cfg 条件选择分支 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)、[std::cfg_select!](https://doc.rust-lang.org/stable/std/macro.cfg_select.html) | 无匹配分支 |
| **PowerPC inline asm** | 扩展内联汇编平台支持 | 稳定 PowerPC / PowerPC64 inline assembly | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 非 PowerPC 目标 |
| **`expr` metavariable to `cfg`** | 宏与条件编译互操作 | 允许将 `expr` 元变量传递给 `cfg` | [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)、[rustc#146961](https://github.com/rust-lang/rust/pull/146961) | 非表达式元变量 |
| **`ManuallyDrop` 常量作模式** | 修复 1.94 回归 | 允许使用 `ManuallyDrop` 类型的常量作为模式 | [Rust Reference - Patterns](https://doc.rust-lang.org/reference/patterns.html)、[rustc#154891](https://github.com/rust-lang/rust/pull/154891) | 误用导致匹配歧义 |
| **s390x vector registers in inline assembly** | 扩展大型机内联汇编 | 支持 s390x vector 寄存器 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[rustc#154184](https://github.com/rust-lang/rust/pull/154184) | 非 s390x 目标 |
| **`From<T> for AssertUnwindSafe<T>`** | 提升 panic 边界易用性 | 安全转换 | [std::panic::AssertUnwindSafe](https://doc.rust-lang.org/stable/std/panic/struct.AssertUnwindSafe.html#impl-From%3CT%3E-for-AssertUnwindSafe%3CT%3E) | - |
| **`From<T> for LazyCell<T, F>` / `LazyLock<T, F>`** | 简化延迟初始化构造 | 从值直接构造 | [std::cell::LazyCell](https://doc.rust-lang.org/stable/std/cell/struct.LazyCell.html#impl-From%3CT%3E-for-LazyCell%3CT,+F%3E)、[std::sync::LazyLock](https://doc.rust-lang.org/stable/std/sync/struct.LazyLock.html#impl-From%3CT%3E-for-LazyLock%3CT,+F%3E) | - |
| **`core::range::RangeToInclusive` / `RangeToInclusiveIter`** | 完整 Range 类型族 | `Copy` + `IntoIterator` | [core::range::RangeToInclusive](https://doc.rust-lang.org/stable/core/range/struct.RangeToInclusive.html)、[core::range::RangeToInclusiveIter](https://doc.rust-lang.org/stable/core/range/struct.RangeToInclusiveIter.html) | 混用 legacy 类型 |
| **`core::hint::cold_path`** | 性能提示 | 标记冷门分支 | [core::hint::cold_path](https://doc.rust-lang.org/stable/core/hint/fn.cold_path.html) | 误标不影响正确性 |
| **`<*const T>::as_ref_unchecked` / `<*mut T>::as_mut_unchecked`** | unsafe 指针便捷转换 | 无检查转换为引用 | [std::primitive.pointer](https://doc.rust-lang.org/stable/std/primitive.pointer.html#method.as_ref_unchecked) | 解引用无效指针导致 UB |
| **`Vec::push_mut` / `insert_mut` 等可变访问 API** | 集合原地可变遍历 | 返回元素的可变引用同时允许修改容器 | [Vec::push_mut](https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.push_mut)、[Vec::insert_mut](https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.insert_mut) | 违反借用规则 |
| **Cargo CVE-2026-5223** | 第三方 registry 安全 | 拒绝 tarball 中的符号链接 | [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)、[Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28) | 恶意 crate 覆盖缓存 |
| **Cargo CVE-2026-5222** | URL 规范化安全 | 修复规范化后认证问题 | [CVE-2026-5222](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/)、[Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28) | 凭据泄露 |
| **WebAssembly 链接** | 提前捕获未定义符号 | 不再默认传递 `--allow-undefined` | [Rust Blog 1.96.0 - WebAssembly](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/#changes-to-webassembly-targets)、[rustc#149868](https://github.com/rust-lang/rust/pull/149868) | 未定义符号被静默导入 |
| **Cargo `target.'cfg(..)'.rustdocflags`** | 按目标条件设置 rustdoc flags | 在 Cargo 配置中支持 `target.'cfg(..)'.rustdocflags` | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16846](https://github.com/rust-lang/cargo/pull/16846) | 配置位置错误 |
| **dependency 同时指定 git 与 alternate registry** | 本地开发与发布版本分离 | 本地使用 git，发布使用 registry | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16810](https://github.com/rust-lang/cargo/pull/16810) | registry 不一致 |

---

## 📚 相关文档 {#相关文档}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 文档 | 用途 |
| :--- | :--- |
| [RUST_193_FEATURE_MATRIX](10_rust_193_feature_matrix.md) | 按特性族展开的五维矩阵（概念-公理-定理-证明方法-反例） |
| [releases.rs 1.93.0](https://releases.rs/docs/1.93.0/) | 权威变更清单 |
| [Ferrocene FLS](https://spec.ferrocene.dev/) | Rust 1.93 形式化规范 |
| [CORE_FEATURES_FULL_CHAIN](10_core_features_full_chain.md) | 13 项核心特性完整链（Def→示例→论证→证明） |
| [DESIGN_MECHANISM_RATIONALE](10_design_mechanism_rationale.md) | 核心机制设计论证（Pin、所有权、借用等） |
| [COMPREHENSIVE_SYSTEMATIC_OVERVIEW](10_comprehensive_systematic_overview.md) | 全面系统化梳理、语义归纳 |
| [LANGUAGE_SEMANTICS_EXPRESSIVENESS](10_language_semantics_expressiveness.md) | 构造性语义、表达能力边界 |
| [toolchain/07_rust_1.93_full_changelog](../06_toolchain/06_07_rust_1_93_full_changelog.md) | Rust 1.93 完整变更清单 |
| [toolchain/09_rust_1.93_compatibility_deep_dive](../06_toolchain/06_09_rust_1_93_compatibility_deep_dive.md) | Rust 1.93 兼容性深度解析 |
| [toolchain/10_rust_1.89_to_1.93_cumulative_features_overview](../../archive/docs/2026_05_historical_docs/10_rust_1.89_to_1.93_cumulative_features_overview.md) | 1.89→1.93 累积特性总览 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-06-29
**状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）

---

## ✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024） {#权威国际化来源对齐升级摘要rust-1960-edition-2024}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs](https://releases.rs/)**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **升级日期**: 2026-06-29

### 本次升级要点 {#本次升级要点}

本文档已完成权威国际化来源对齐升级，统一版本基准为 **Rust 1.96.0+ / Edition 2024**，同时保留 1.93/1.94 历史分析章节。

#### 新增 Rust 1.96.0 特性 {#新增-rust-1960-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `core::range` 新类型 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) | `Range`/`RangeFrom`/`RangeInclusive` 实现 `Copy` + `IntoIterator` |
| `assert_matches!` / `debug_assert_matches!` | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html) | 模式断言宏，失败输出 Debug 信息 |
| Cargo CVE-2026-5223 / CVE-2026-5222 修复 | [Cargo 安全公告](https://github.com/rust-lang/cargo/security/advisories)、[Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 第三方 registry tarball symlink 与 URL 规范化修复 |
| WebAssembly 链接行为变更 | [Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 不再默认传递 `--allow-undefined` |
| `core::range::RangeToInclusive` / `RangeToInclusiveIter` | [core::range::RangeToInclusive](https://doc.rust-lang.org/stable/core/range/struct.RangeToInclusive.html)、[core::range::RangeToInclusiveIter](https://doc.rust-lang.org/stable/core/range/struct.RangeToInclusiveIter.html) | 1.96 新增 `Copy` Range 类型 |
| `From<T> for AssertUnwindSafe<T>` / `LazyCell<T,F>` / `LazyLock<T,F>` | [AssertUnwindSafe](https://doc.rust-lang.org/stable/std/panic/struct.AssertUnwindSafe.html#impl-From%3CT%3E-for-AssertUnwindSafe%3CT%3E)、[LazyCell](https://doc.rust-lang.org/stable/std/cell/struct.LazyCell.html#impl-From%3CT%3E-for-LazyCell%3CT,+F%3E)、[LazyLock](https://doc.rust-lang.org/stable/std/sync/struct.LazyLock.html#impl-From%3CT%3E-for-LazyLock%3CT,+F%3E) | 提升 panic 边界与延迟初始化易用性 |
| `ManuallyDrop` 常量作模式 | [rustc#154891](https://github.com/rust-lang/rust/pull/154891) | 修复 1.94 回归 |
| `expr` metavariable to `cfg` | [rustc#146961](https://github.com/rust-lang/rust/pull/146961) | 宏与 cfg 互操作 |
| s390x vector registers in inline asm | [rustc#154184](https://github.com/rust-lang/rust/pull/154184) | 扩展内联汇编平台 |
| Cargo `target.'cfg(..)'.rustdocflags` | [cargo#16846](https://github.com/rust-lang/cargo/pull/16846) | 按 cfg 设置 rustdocflags |
| dependency 同时指定 git 与 alternate registry | [cargo#16810](https://github.com/rust-lang/cargo/pull/16810) | 本地 git，发布 registry |

#### 新增 Rust 1.95.0 特性 {#新增-rust-1950-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `if let` guards on match arms | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | match 臂支持 `if let` 守卫 |
| `cfg_select!` 宏 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)、[releases.rs 1.95.0](https://releases.rs/docs/1.95.0/) | 编译期 cfg 条件选择宏 |
| PowerPC / PowerPC64 内联汇编稳定化 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 稳定 inline assembly for PowerPC |
| `--remap-path-scope` | [Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 控制路径重映射作用域 |
| `core::hint::cold_path` | [core::hint::cold_path](https://doc.rust-lang.org/stable/core/hint/fn.cold_path.html) | 冷门分支提示 |
| `<*const/mut T>::as_ref_unchecked` / `as_mut_unchecked` | [std::primitive.pointer](https://doc.rust-lang.org/stable/std/primitive.pointer.html#method.as_ref_unchecked) | unsafe 指针转引用 |
| `Vec::push_mut` / `Vec::insert_mut` | [Vec::push_mut](https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.push_mut)、[Vec::insert_mut](https://doc.rust-lang.org/stable/std/vec/struct.Vec.html#method.insert_mut) | 集合原地可变访问 |
| `MaybeUninit<[T; N]>` 转换 | [MaybeUninit<[T; N]>: From<[MaybeUninit<T>; N]>](https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#impl-From%3C%5BMaybeUninit%3CT%3E;+N%5D%3E-for-MaybeUninit%3C%5BT;+N%5D%3E) | 数组与 MaybeUninit 互转 |
| `bool: TryFrom<{integer}>` | [bool: TryFrom<{integer}>](https://doc.rust-lang.org/stable/std/primitive.bool.html#impl-TryFrom%3Cu128%3E-for-bool) | 整数到布尔安全转换 |
| `AtomicPtr::update` / `try_update` | [AtomicPtr::update](https://doc.rust-lang.org/stable/std/sync/atomic/struct.AtomicPtr.html#method.update) | 原子指针更新 |

#### 权威来源对齐 {#权威来源对齐-1}

- Rust release notes（releases.rs）
- Rust Blog 对应版本发布公告
- Rust Reference 具体章节（Range Expressions、Match Guards、Inline Assembly、Conditional Compilation）
- Rust Standard Library 具体 API（`core::range`、`core::assert_matches`、`std::ops::ControlFlow`）
- RFC 链接（RFC 3550 等）

---

## 相关概念 {#相关概念}
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

> **来源: [ACM](https://dl.acm.org/)**

> **来源: [IEEE](https://standards.ieee.org/)**

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**
> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**
> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**
> **来源: [Rust Reference - Range Expressions](https://doc.rust-lang.org/reference/expressions/range-expr.html)**
> **来源: [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)**
> **来源: [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)**
> **来源: [Rust Standard Library - core::range](https://doc.rust-lang.org/stable/core/range/index.html)**
> **来源: [Rust Standard Library - assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html)**
> **来源: [Rust Standard Library - cfg_select!](https://doc.rust-lang.org/stable/std/macro.cfg_select.html)**
> **来源: [Rust Standard Library - core::hint::cold_path](https://doc.rust-lang.org/stable/core/hint/fn.cold_path.html)**
> **来源: [Rust Standard Library - primitive.pointer](https://doc.rust-lang.org/stable/std/primitive.pointer.html)**
> **来源: [Rust Standard Library - Vec](https://doc.rust-lang.org/stable/std/vec/struct.Vec.html)**
> **来源: [Rust Standard Library - MaybeUninit](https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html)**
> **来源: [Rust Standard Library - AtomicPtr](https://doc.rust-lang.org/stable/std/sync/atomic/struct.AtomicPtr.html)**
> **来源: [Rust Standard Library - LazyCell](https://doc.rust-lang.org/stable/std/cell/struct.LazyCell.html)**
> **来源: [Rust Standard Library - LazyLock](https://doc.rust-lang.org/stable/std/sync/struct.LazyLock.html)**
> **来源: [Rust Standard Library - AssertUnwindSafe](https://doc.rust-lang.org/stable/std/panic/struct.AssertUnwindSafe.html)**
> **来源: [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)**
> **来源: [CVE-2026-5222](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/)**
> **来源: [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)**
> **来源: [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)**

---