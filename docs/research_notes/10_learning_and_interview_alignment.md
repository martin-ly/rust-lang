# 学习路径与面试题权威来源对齐矩阵 {#学习路径与面试题权威来源对齐矩阵}

> **EN**: Learning And Interview Alignment
> **Summary**: 学习路径与面试题权威来源对齐矩阵 Learning And Interview Alignment.
> **概念族**: 权威来源对齐 / 学习路径 / 面试评估
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [学习路径与面试题权威来源对齐矩阵 {#学习路径与面试题权威来源对齐矩阵}](#学习路径与面试题权威来源对齐矩阵-学习路径与面试题权威来源对齐矩阵)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、官方学习资源对齐 {#二官方学习资源对齐}](#二官方学习资源对齐-二官方学习资源对齐)
    - [The Rust Programming Language (TRPL) {#the-rust-programming-language-trpl}](#the-rust-programming-language-trpl-the-rust-programming-language-trpl)
    - [Rust By Example {#rust-by-example}](#rust-by-example-rust-by-example)
    - [Rustlings {#rustlings}](#rustlings-rustlings)
    - [Standard Library 文档 {#standard-library-文档}](#standard-library-文档-standard-library-文档)
  - [三、社区学习资源对齐 {#三社区学习资源对齐}](#三社区学习资源对齐-三社区学习资源对齐)
    - [Rust 语言圣经 (course.rs) {#rust-语言圣经-coursers}](#rust-语言圣经-coursers-rust-语言圣经-coursers)
    - [Rust 中文社区 {#rust-中文社区}](#rust-中文社区-rust-中文社区)
    - [Rust Japan {#rust-japan}](#rust-japan-rust-japan)
    - [Exercism Rust track {#exercism-rust-track}](#exercism-rust-track-exercism-rust-track)
  - [四、面试评估与权威来源映射 {#四面试评估与权威来源映射}](#四面试评估与权威来源映射-四面试评估与权威来源映射)
    - [所有权（Ownership） {#所有权}](#所有权-所有权)
    - [借用（Borrowing）与生命周期（Lifetimes） {#借用与生命周期}](#借用与生命周期-借用与生命周期)
    - [类型系统（Type System） {#类型系统}](#类型系统-类型系统)
    - [并发与异步（Async） {#并发与异步}](#并发与异步-并发与异步)
    - [Unsafe 与 FFI {#unsafe-与-ffi}](#unsafe-与-ffi-unsafe-与-ffi)
    - [设计模式与工程实践 {#设计模式与工程实践}](#设计模式与工程实践-设计模式与工程实践)
  - [五、Bloom 层级对应矩阵 {#五bloom-层级对应矩阵}](#五bloom-层级对应矩阵-五bloom-层级对应矩阵)
  - [六、与项目文档映射 {#六与项目文档映射}](#六与项目文档映射-六与项目文档映射)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

---

## 一、对齐说明 {#一对齐说明}

本文档将 Rust 学习路径、面试评估题目与国际化权威来源建立系统映射，覆盖官方教程、交互式示例、练习项目、标准库文档、中文/日文社区资源以及 Exercism 等实践平台。对齐目标：

- 为初学者到专家提供可追溯的权威学习路径。
- 将常见面试题锚定到官方规范、教程或学术来源，避免口耳相传的偏差。
- 建立学习主题与 Bloom 认知层级（L1-L6）的对应关系，便于教学设计。

> **权威来源范围**: P0 官方文档、P1 学术论文/工具、P2 社区资源。

---

## 二、官方学习资源对齐 {#二官方学习资源对齐}

### The Rust Programming Language (TRPL) {#the-rust-programming-language-trpl}

| TRPL 章节 | 学习主题 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|-----------|----------|-----------------|----------|--------------|
| Ch 1-3: 开始 / 基础概念 | 安装、变量、类型、函数、控制流 | L1-L2 | [10_rust_book_alignment.md](10_rust_book_alignment.md) §Ch 1-3 | [TRPL Ch 1-3](https://doc.rust-lang.org/book/ch00-00-introduction.html) |
| Ch 4: 所有权（Ownership） | 所有权三规则、Move/Copy、借用（Borrowing）、切片（Slice） | L2-L4 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | [TRPL Ch 4](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) |
| Ch 10: 泛型（Generics）、Trait、生命周期 | 泛型、Trait bound、生命周期标注 | L3-L5 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [TRPL Ch 10](https://doc.rust-lang.org/book/ch10-00-generics.html) |
| Ch 15: 智能指针（Smart Pointer） | Box/Rc/Arc/RefCell/Weak、内部可变性 | L3-L4 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) §Def 4.1-4.5 | [TRPL Ch 15](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) |
| Ch 16: 无畏并发 | 线程、mpsc、Mutex、Send/Sync | L3-L5 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [TRPL Ch 16](https://doc.rust-lang.org/book/ch16-00-concurrency.html) |
| Ch 17: 异步编程基础 | async/await、Future、Pin | L3-L5 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | [TRPL Ch 17](https://doc.rust-lang.org/book/ch17-00-async-await.html) |
| Ch 20: 高级特性 | Unsafe Rust、宏（Macro）、高级 Trait/类型 | L4-L6 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) | [TRPL Ch 20](https://doc.rust-lang.org/book/ch20-00-advanced-features.html) |

### Rust By Example {#rust-by-example}

| RBE 章节 | 学习主题 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|----------|----------|-----------------|----------|--------------|
| Hello / Primitives / Custom Types | 基础语法、类型 | L1-L2 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) §二 | [RBE 基础](https://doc.rust-lang.org/rust-by-example/hello.html) |
| Scope / Borrowing / Lifetimes | 作用域、借用、生命周期 | L2-L4 | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §2-§3 | [RBE Scope](https://doc.rust-lang.org/rust-by-example/scope.html) |
| Generics / Traits | 泛型与 Trait | L3-L4 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [RBE Generics](https://doc.rust-lang.org/rust-by-example/generics.html) |
| Threads / Channels / Async | 并发与异步示例 | L3-L5 | [crates/c05_threads/README.md](../../crates/c05_threads/README.md)、[crates/c06_async/README.md](../../crates/c06_async/README.md) | [RBE Std misc](https://doc.rust-lang.org/rust-by-example/std_misc.html) |
| Unsafe / FFI / Macros | unsafe、FFI、宏 | L4-L6 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md)、[crates/c11_macro_system_proc/README.md](../../crates/c11_macro_system_proc/README.md) | [RBE Unsafe](https://doc.rust-lang.org/rust-by-example/unsafe.html) |

### Rustlings {#rustlings}

| Rustlings 模块（Module） | 学习主题 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|----------------|----------|-----------------|----------|--------------|
| intro / variables / functions | 基础语法 | L1-L2 | [exercises/README.md](../../exercises/README.md) | [rustlings](https://github.com/rust-lang/rustlings) |
| ownership / borrow / lifetimes | 所有权与借用 | L2-L4 | [crates/c01_ownership_borrow_scope/README.md](../../crates/c01_ownership_borrow_scope/README.md) | [rustlings exercises](https://github.com/rust-lang/rustlings) |
| structs / enums / modules | 类型与模块（Module） | L2-L3 | [crates/c02_type_system/README.md](../../crates/c02_type_system/README.md)、[formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | [rustlings exercises](https://github.com/rust-lang/rustlings) |
| errors / generics / traits | 错误处理（Error Handling）、泛型、Trait | L3-L4 | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md)、[type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [rustlings exercises](https://github.com/rust-lang/rustlings) |
| tests / iterators / threads | 测试、迭代器（Iterator）、线程 | L3-L4 | [crates/c05_threads/README.md](../../crates/c05_threads/README.md)、[crates/c08_algorithms/README.md](../../crates/c08_algorithms/README.md) | [rustlings exercises](https://github.com/rust-lang/rustlings) |
| smart_pointers / conversions / clippy | 智能指针（Smart Pointer）、类型转换、Clippy | L3-L5 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) §Def 4.1-4.5 | [rustlings exercises](https://github.com/rust-lang/rustlings) |

### Standard Library 文档 {#standard-library-文档}

| std 模块 | 学习主题 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|----------|----------|-----------------|----------|--------------|
| `std::vec` / `std::collections` | 集合与迭代器 | L2-L3 | [docs/02_reference/quick_reference/02_collections_iterators_cheatsheet.md](../02_reference/quick_reference/02_collections_iterators_cheatsheet.md) | [std collections](https://doc.rust-lang.org/std/collections/index.html) |
| `std::option` / `std::result` | 错误处理（Error Handling） | L2-L4 | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) | [std result](https://doc.rust-lang.org/std/result/index.html) |
| `std::sync` | 并发原语 | L3-L5 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [std sync](https://doc.rust-lang.org/std/sync/index.html) |
| `std::pin` / `std::future` | Pin 与 Future | L4-L6 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) | [std pin](https://doc.rust-lang.org/std/pin/index.html) |
| `std::marker` (Send/Sync/PhantomData) | 标记 Trait | L4-L5 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [std marker](https://doc.rust-lang.org/std/marker/index.html) |

---

## 三、社区学习资源对齐 {#三社区学习资源对齐}

### Rust 语言圣经 (course.rs) {#rust-语言圣经-coursers}

| course.rs 章节 | 学习主题 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|----------------|----------|-----------------|----------|--------------|
| 基础入门 | 变量、类型、控制流 | L1-L2 | [10_learning_path_comprehensive.md](10_learning_path_comprehensive.md) §路径一 | [course.rs 基础](https://course.rs/basic/) |
| 所有权与借用 | 所有权、借用、生命周期 | L2-L4 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md)、[formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | [course.rs 所有权](https://course.rs/basic/ownership.html) |
| 泛型（Generics）与特征 | 泛型、Trait、生命周期 | L3-L5 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [course.rs 泛型](https://course.rs/basic/trait.html) |
| 深入类型 | 智能指针、并发、异步（Async） | L4-L6 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md)、[formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | [course.rs 深入类型](https://course.rs/advance/) |

### Rust 中文社区 {#rust-中文社区}

| 来源 | 用途 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|------|------|-----------------|----------|--------------|
| [Rust 中文社区论坛 [已失效]]<!-- 原链接: https://rustcc.cn/ --> | 问答、博客、招聘、活动 | L1-L6 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | [rustcc.cn [已失效]]<!-- 原链接: https://rustcc.cn/ --> |
| [Rust 语言中文翻译](https://kaisery.github.io/trpl-zh-cn/) | TRPL 中文版 | L1-L5 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | [TRPL 中文](https://kaisery.github.io/trpl-zh-cn/) |
| [Rust Reference 中文](https://rustwiki.org/zh-CN/reference/) | Reference 社区翻译 | L3-L6 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | [Reference 中文](https://rustwiki.org/zh-CN/reference/) |

### Rust Japan {#rust-japan}

| 来源 | 用途 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|------|------|-----------------|----------|--------------|
| [Rust Japan Community](https://rust-jp.rs/) | 活动、资源、日文教程索引 | L1-L6 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | [rust-jp.rs](https://rust-jp.rs/) |
| [The Rust Programming Language 日本語版](https://doc.rust-jp.rs/book-ja/) | TRPL 日文版 | L1-L5 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | [TRPL 日文](https://doc.rust-jp.rs/book-ja/) |
| [Rust by Example 日本語版](https://doc.rust-jp.rs/rust-by-example-ja/) | RBE 日文版 | L1-L5 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | [RBE 日文](https://doc.rust-jp.rs/rust-by-example-ja/) |

### Exercism Rust track {#exercism-rust-track}

| Exercism 主题 | 学习主题 | 对应 Bloom 层级 | 项目文档 | 权威来源链接 |
|---------------|----------|-----------------|----------|--------------|
| 基础练习 (Hello World, Reverse String) | 字符串、基础语法 | L1-L2 | [exercises/rustlings_style](../../exercises/rustlings_style) | [Exercism Rust](https://exercism.org/tracks/rust) |
| 中级练习 (Clock, Gigasecond) | 类型设计、时间处理 | L2-L3 | [crates/c02_type_system/README.md](../../crates/c02_type_system/README.md) | [Exercism Rust](https://exercism.org/tracks/rust) |
| 高级练习 (Parallel Letter Frequency) | 并发、并行 | L3-L5 | [crates/c05_threads/README.md](../../crates/c05_threads/README.md) | [Exercism Rust](https://exercism.org/tracks/rust) |
| 概念练习 (Arc, Mutex, Lifetimes) | 所有权、并发、生命周期 | L3-L5 | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md)、[formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) | [Exercism Rust Concepts](https://exercism.org/tracks/rust/concepts) |

---

## 四、面试评估与权威来源映射 {#四面试评估与权威来源映射}

### 所有权 {#所有权}

| 常见面试题 | 核心考察点 | Bloom 层级 | 项目文档 | 权威来源 |
|------------|------------|------------|----------|----------|
| 什么是所有权？三规则是什么？ | 所有权基本语义 | L1-L2 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q1 | [TRPL Ch 4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) |
| Move 和 Copy 有什么区别？ | 值语义与资源管理 | L2-L3 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q2 | [TRPL Ch 4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)、[Reference Copy](https://doc.rust-lang.org/reference/special-types-and-traits.html#copy) |
| 为什么 `Rc` 不是 `Send`？ | 引用（Reference）计数与线程安全 | L4-L5 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q5 | [TRPL Ch 16.4](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html)、[Rustonomicon Send/Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) |
| 所有权系统能否防止内存泄漏？ | 安全保证边界 | L5-L6 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q13 | [Rustonomicon Leakpocalypse](https://doc.rust-lang.org/nomicon/leaking.html) |

### 借用与生命周期 {#借用与生命周期}

| 常见面试题 | 核心考察点 | Bloom 层级 | 项目文档 | 权威来源 |
|------------|------------|------------|----------|----------|
| 借用规则是什么？ | 借用基本规则 | L1-L2 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q3 | [TRPL Ch 4.2](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) |
| 为什么不可变借用（Mutable Borrow）和可变借用不能共存？ | 别名可变性 | L3-L4 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q8 | [Rust Reference Aliasing](https://doc.rust-lang.org/reference/behavior-considered-undefined.html#ruling-out-aliasing) |
| 什么是 NLL？ | 非词法生命周期 | L4-L5 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q9 | [RFC 2094 NLL](https://rust-lang.github.io/rfcs/2094-nll.html) |
| 生命周期省略的三条规则是什么？ | 生命周期省略 | L3-L4 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q20 | [Rust Reference Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html) |
| `for<'a>` 高阶 Trait bound 如何理解？ | HRTB | L5-L6 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q21 | [Rust Reference HRTB](https://doc.rust-lang.org/reference/trait-bounds.html#higher-ranked-trait-bounds) |

### 类型系统 {#类型系统}

| 常见面试题 | 核心考察点 | Bloom 层级 | 项目文档 | 权威来源 |
|------------|------------|------------|----------|----------|
| `impl Trait` 和 `dyn Trait` 的区别？ | 静态/动态分发 | L3-L4 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q17 | [TRPL Ch 18.2](https://doc.rust-lang.org/book/ch18-02-trait-objects.html)、[Reference Trait Objects](https://doc.rust-lang.org/reference/types/trait-object.html) |
| 什么是型变（Variance）？ | 子类型与型变 | L4-L5 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q19 | [Rustonomicon Subtyping](https://doc.rust-lang.org/nomicon/subtyping.html) |
| 什么是 GAT？ | 泛型关联类型 | L5-L6 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q22 | [RFC 1590 GAT [已失效]]<!-- 原链接: https://rust-lang.github.io/rfcs/1590-generic-associated-types.html --> |
| 空指针优化（NPO）是什么？ | 布局优化 | L4-L5 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q24 | [Rust Reference Niche](https://doc.rust-lang.org/reference/type-layout.html#reprc-enums)、[Rustonomicon NPO](https://doc.rust-lang.org/nomicon/exotic-sizes.html#niche-values) |

### 并发与异步 {#并发与异步}

| 常见面试题 | 核心考察点 | Bloom 层级 | 项目文档 | 权威来源 |
|------------|------------|------------|----------|----------|
| `Send` 和 `Sync` 的区别？ | 并发安全（Concurrency Safety）标记 | L2-L3 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q26 | [TRPL Ch 16.4](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html)、[Rustonomicon Send/Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) |
| `Mutex` 和 `RwLock` 怎么选？ | 锁选型 | L3-L4 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q27 | [std sync](https://doc.rust-lang.org/std/sync/index.html) |
| 为什么 `Cell` 不是 `Sync`？ | 内部可变性与线程安全 | L4-L5 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q31 | [Rustonomicon Send/Sync](https://doc.rust-lang.org/nomicon/send-and-sync.html) |
| 什么是 `Pin`？为什么 async/await 需要它？ | 自引用与状态机 | L4-L6 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q11、Q32 | [Rustonomicon Pin](https://doc.rust-lang.org/nomicon/what-unsafe-does.html)、[Async Book Pin [已失效]]<!-- 原链接: https://rust-lang.github.io/async-book/04_pinning/01_chapter.html --> |
| 跨 await 持锁有什么风险？ | 异步并发安全 | L5-L6 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q33 | [Async Book Shared State](https://rust-lang.github.io/async-book/03_async_await/01_chapter.html) |

### Unsafe 与 FFI {#unsafe-与-ffi}

| 常见面试题 | 核心考察点 | Bloom 层级 | 项目文档 | 权威来源 |
|------------|------------|------------|----------|----------|
| `unsafe` 块与安全抽象的关系？ | unsafe 边界 | L4-L5 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) | [Rustonomicon Safe Abstraction](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html) |
| `Box::leak` 有什么用途？ | 泄漏与 `'static` | L4-L5 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q14 | [std Box::leak](https://doc.rust-lang.org/std/boxed/struct.Box.html#method.leak) |
| `transmute` 的风险是什么？ | 类型布局与 UB | L5-L6 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 | [Rustonomicon Transmute](https://doc.rust-lang.org/nomicon/transmutes.html) |
| FFI 调用时需要注意哪些内存协议？ | FFI 安全 | L5-L6 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 | [Rustonomicon FFI](https://doc.rust-lang.org/nomicon/ffi.html)、[Unsafe Code Guidelines FFI](https://rust-lang.github.io/unsafe-code-guidelines/glossary.html) |

### 设计模式与工程实践 {#设计模式与工程实践}

| 常见面试题 | 核心考察点 | Bloom 层级 | 项目文档 | 权威来源 |
|------------|------------|------------|----------|----------|
| 什么是内部可变性模式？ | 设计模式应用 | L3-L4 | [10_interview_questions_collection.md](10_interview_questions_collection.md) Q7 | [TRPL Ch 15.5](https://doc.rust-lang.org/book/ch15-05-interior-mutability.html)、[Rust Design Patterns Interior Mutability](https://rust-unofficial.github.io/patterns/patterns/behavioural/interior-mutability.html) |
| 如何用 Trait 对象实现多态？ | 面向 trait 的设计 | L3-L4 | [10_rust_book_alignment.md](10_rust_book_alignment.md) §Ch 18 | [TRPL Ch 18](https://doc.rust-lang.org/book/ch18-00-oop.html) |
| Builder / 类型状态模式如何实现？ | 惯用法 | L4-L5 | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §4 | [Rust Design Patterns Builder](https://rust-unofficial.github.io/patterns/patterns/creational/builder.html) |
| 如何保证 API 的未来兼容性？ | API 设计 | L5-L6 | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) §3 | [Rust API Guidelines Future-proofing](https://rust-lang.github.io/api-guidelines/future-proofing.html) |

---

## 五、Bloom 层级对应矩阵 {#五bloom-层级对应矩阵}

| 学习主题 | L1 记忆 | L2 理解 | L3 应用 | L4 分析 | L5 评价 | L6 创造 |
|----------|---------|---------|---------|---------|---------|---------|
| 所有权 | 三规则 | Move/Copy 语义 | 修复所有权错误 | 分析 Rc/Arc 边界 | 评价所有权安全保证 | 设计自定义智能指针 |
| 借用 | 借用规则 | 引用有效性 | 重构借用代码 | NLL 行为分析 | 评价别名可变性设计 | 设计安全封装 |
| 生命周期 | 标注语法 | 省略规则 | 添加生命周期标注 | 型变与生命周期 | 评价复杂 lifetime 设计 | 设计自引用类型 API |
| 类型系统（Type System） | Trait/泛型语法 | 关联类型/GAT | 实现泛型 API | 型变分析 | 评价类型安全设计 | 设计类型状态机 |
| 并发 | Send/Sync 定义 | 线程/锁模型 | 使用 Mutex/Arc | 死锁/饥饿分析 | 评价并发架构 | 设计无锁/异步运行时（Runtime） |
| Unsafe | unsafe 语法 | UB 分类 | 封装 unsafe 抽象 | 内存布局分析 | 评价 unsafe 边界 | 设计安全 FFI 封装 |
| 设计模式 | 模式名称 | Rust 惯用法 | 实现 Builder/状态机 | 模式与所有权交互 | 评价模式适用性 | 设计领域特定抽象 |

**权威来源链接映射**:

- **L1-L2**: [TRPL](https://doc.rust-lang.org/book/)、[RBE](https://doc.rust-lang.org/rust-by-example/)、[course.rs](https://course.rs/)
- **L3-L4**: [Rustlings](https://github.com/rust-lang/rustlings)、[Exercism Rust](https://exercism.org/tracks/rust)、[std 文档](https://doc.rust-lang.org/std/)
- **L5-L6**: [Rustonomicon](https://doc.rust-lang.org/nomicon/)、[Rust Reference](https://doc.rust-lang.org/reference/)、[Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)、[RFCs](https://rust-lang.github.io/rfcs/)、[RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)

---

## 六、与项目文档映射 {#六与项目文档映射}

| 本矩阵主题 | 对应项目文档 | 说明 |
|------------|--------------|------|
| 综合学习路径 | [10_learning_path_comprehensive.md](10_learning_path_comprehensive.md) | 初学者/进阶者/专家路径 |
| 面试题集锦 | [10_interview_questions_collection.md](10_interview_questions_collection.md) | 按难度分级的面试题库 |
| TRPL 逐章对齐 | [10_rust_book_alignment.md](10_rust_book_alignment.md) | TRPL 21 章细粒度映射 |
| RBE 示例对齐 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) | 官方交互式示例映射 |
| 多语言来源 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | 中文/日文/多语言权威来源 |
| 权威来源总网络 | [10_authoritative_source_alignment_network.md](10_authoritative_source_alignment_network.md) | P0/P1/P2 权威来源总入口 |
| 知识图谱 | [10_knowledge_graph_index.md](10_knowledge_graph_index.md) | 六层两网一库概念节点与边 |
| 社区最佳实践 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | API Guidelines、Design Patterns、Performance Book |
| 标准库对齐 | [10_std_library_alignment.md](10_std_library_alignment.md) | std API 与项目示例映射 |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. **Rustlings 与项目 exercises 的自动化反向索引尚未建立**：目前为人工映射，可补充脚本生成「题目 → 项目文件」反向索引。
2. **Exercism Rust track 概念练习与项目反例的逐题映射可细化**：特别是高级并发、unsafe、宏相关练习。
3. **面试题的 Bloom 层级评分尚未完全标准化**：部分题目可能因面试官追问深度而在 L4-L6 之间浮动，建议建立评分 rubric。
4. **社区视频/课程资源（如 Rustconf、YouTube 教程）未纳入**：当前仅覆盖文本型权威来源。
5. **多语言面试题表述差异未系统整理**：可结合 [data/i18n_terminology.yaml](../../data/i18n_terminology.yaml) 扩展术语对照。

> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | [Rustlings](https://github.com/rust-lang/rustlings) | [Rust Standard Library](https://doc.rust-lang.org/std/) | [course.rs](https://course.rs/) | [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ --> | [Rust Japan](https://rust-jp.rs/) | [Exercism Rust](https://exercism.org/tracks/rust)

---

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [综合学习路径](10_learning_path_comprehensive.md)
- [面试题集锦](10_interview_questions_collection.md)
- [Rust Book 对齐](10_rust_book_alignment.md)
- [Rust By Example 对齐](10_rust_by_example_alignment.md)
- [国际化多语言来源对齐](10_i18n_source_alignment.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 权威来源索引 {#权威来源索引}

> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
> **来源**: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)
> **来源**: [Rust Standard Library](https://doc.rust-lang.org/std/)
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **来源**: [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **来源**: [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/)
> **来源**: [Rust RFCs](https://rust-lang.github.io/rfcs/)
> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
> **来源**: [course.rs](https://course.rs/)
> **来源**: [Rust 中文社区 [已失效]]<!-- 原链接: https://rustcc.cn/ -->
> **来源**: [Rust Japan](https://rust-jp.rs/)
> **来源**: [Exercism Rust track](https://exercism.org/tracks/rust)
> **来源**: [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-06-29 (Rust 1.97.0+ / Edition 2024 权威来源对齐)
**状态**: ✅ 已完成
