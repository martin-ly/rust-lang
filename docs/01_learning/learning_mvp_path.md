# TRPL 3rd Ed 章节映射表

<!-- canonical-normalized 2026-07-11 -->
> **权威来源（Canonical）**: 本文件为 `docs/` 侧 **TRPL 3rd Ed → `concept/` 逐章映射权威页**（[`concept/00_meta/trpl_3rd_ed_mapping.md`](../../concept/00_meta/trpl_3rd_ed_mapping.md) 为重定向 stub 指向本文件）。表中各 Rust 概念的深度解释以其对应的 `concept/` 权威页为准；按能力阶段的学习路径总览见 [`concept/00_meta/04_navigation/learning_mvp_path.md`](../../concept/00_meta/04_navigation/learning_mvp_path.md)。
>
> 根据 AGENTS.md §2 Canonical 规则：本文仅保留 TRPL 章节到 concept 页的映射关系、覆盖缺口（gap）标注与使用建议等独特内容，不重复各 concept 页中的概念定义、规则与定理推导。

> **EN**: TRPL 3rd Edition Chapter Mapping Table
> **Summary**: Maps each chapter of *The Rust Programming Language* 3rd Edition to the corresponding `concept/` authority page(s) in this knowledge base, with notes on coverage gaps.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **最后更新**: 2026-07-09
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

本表将官方教材 [*The Rust Programming Language* 3rd Edition](https://doc.rust-lang.org/book/title-page.html)（简称 TRPL）的 22 章逐章映射到本知识库 `concept/` 目录下的权威概念页。学习者可按教材顺序，通过本表快速定位到本项目中最深入、最权威的讲解来源。

> **关联路径**: 如需按能力阶段学习，请参阅 [concept/00_meta/04_navigation/learning_mvp_path.md](../../concept/00_meta/04_navigation/learning_mvp_path.md)（MVP 学习路径）。

---

## 映射表

| TRPL Chapter | Topic | Corresponding `concept/` Page | Notes / Gap |
|:---|:---|:---|:---|
| **Ch 1** · [Getting Started](https://doc.rust-lang.org/book/ch01-00-getting-started.html) | 安装 Rust、Hello World、Hello Cargo | [Rust 起步指南](../../concept/01_foundation/00_start/00_start.md) · [工具链](../../concept/06_ecosystem/00_toolchain/01_toolchain.md) · [Cargo 入门](../../concept/06_ecosystem/01_cargo/80_cargo_getting_started.md) | 覆盖完整 |
| **Ch 2** · [Programming a Guessing Game](https://doc.rust-lang.org/book/ch02-00-guessing-game-tutorial.html) | 通过猜数字游戏综合练习变量、输入、循环、错误处理（Error Handling） | [Rust 起步指南](../../concept/01_foundation/00_start/00_start.md) · [变量模型](../../concept/01_foundation/03_values_and_references/20_variable_model.md) · [控制流](../../concept/01_foundation/04_control_flow/07_control_flow.md) · [错误处理基础](../../concept/01_foundation/08_error_handling/32_error_handling_basics.md) | 项目式教程，无独立“猜数字游戏”概念页；相关概念已覆盖 |
| **Ch 3** · [Common Programming Concepts](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html) | 变量与可变性、数据类型、函数、注释、控制流 | [变量模型](../../concept/01_foundation/03_values_and_references/20_variable_model.md) · [类型系统（Type System）](../../concept/01_foundation/02_type_system/04_type_system.md) · [数值类型](../../concept/01_foundation/02_type_system/10_numerics.md) · [函数](../../concept/01_foundation/07_modules_and_items/12_functions.md) · [控制流](../../concept/01_foundation/04_control_flow/07_control_flow.md) | §3.4 Comments 无独立概念页，归入[词法结构](../../concept/04_formal/05_rustc_internals/45_lexical_structure.md) / [表达式参考](../../concept/04_formal/05_rustc_internals/48_statements_and_expressions_reference.md) |
| **Ch 4** · [Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) | 所有权、引用（Reference）与借用、切片 | [所有权](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [借用（Borrowing）](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) · [移动语义](../../concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md) · [模式匹配（Pattern Matching）与切片](../../concept/01_foundation/04_control_flow/40_patterns.md) | §4.3 Slice Type 无独立权威页，相关内容分散在[类型系统（Type System）](../../concept/01_foundation/02_type_system/04_type_system.md)与[模式](../../concept/01_foundation/04_control_flow/40_patterns.md) |
| **Ch 5** · [Using Structs to Structure Related Data](https://doc.rust-lang.org/book/ch05-00-structs.html) | 结构体定义与实例化、方法语法 | [结构体（Struct）](../../concept/01_foundation/07_modules_and_items/14_structs.md) · [实现与方法](../../concept/01_foundation/07_modules_and_items/16_implementations.md) · [类型系统](../../concept/01_foundation/02_type_system/04_type_system.md) | 覆盖完整 |
| **Ch 6** · [Enums and Pattern Matching](https://doc.rust-lang.org/book/ch06-00-enums.html) | 枚举定义、`match`、`if let`、`let...else` | [枚举（Enum）](../../concept/01_foundation/07_modules_and_items/15_enumerations.md) · [控制流](../../concept/01_foundation/04_control_flow/07_control_flow.md) · [模式](../../concept/01_foundation/04_control_flow/40_patterns.md) | 覆盖完整 |
| **Ch 7** · [Packages, Crates, and Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | 包与 crate、模块（Module）树、路径、`use`、多文件模块 | [模块与路径](../../concept/01_foundation/07_modules_and_items/11_modules_and_paths.md) · [`use` 声明](../../concept/01_foundation/07_modules_and_items/13_use_declarations.md) · [crate 与源文件](../../concept/01_foundation/07_modules_and_items/38_crates_and_source_files.md) · [模块系统（进阶）](../../concept/02_intermediate/05_modules_and_visibility/10_module_system.md) · [API 命名约定](../../concept/02_intermediate/05_modules_and_visibility/22_api_naming_conventions.md) | 覆盖完整 |
| **Ch 8** · [Common Collections](https://doc.rust-lang.org/book/ch08-00-common-collections.html) | `Vec`、`String`、`HashMap` | [集合基础](../../concept/01_foundation/05_collections/08_collections.md) · [高级集合](../../concept/01_foundation/05_collections/17_collections_advanced.md) · [字符串与编码](../../concept/01_foundation/06_strings_and_text/09_strings_and_text.md) · [字符串与编码进阶](../../concept/01_foundation/06_strings_and_text/18_strings_and_encoding.md) | 覆盖完整 |
| **Ch 9** · [Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html) | `panic!`、`Result`、`?`、错误处理哲学 | [panic 与 abort](../../concept/01_foundation/08_error_handling/13_panic_and_abort.md) · [错误处理基础](../../concept/01_foundation/08_error_handling/32_error_handling_basics.md) · [错误处理控制流](../../concept/01_foundation/08_error_handling/33_error_handling_control_flow.md) · [错误处理（进阶）](../../concept/02_intermediate/03_error_handling/04_error_handling.md) | 覆盖完整 |
| **Ch 10** · [Generic Types, Traits, and Lifetimes](https://doc.rust-lang.org/book/title-page.html) | 泛型（Generics）、trait、生命周期 | [泛型](../../concept/02_intermediate/01_generics/02_generics.md) · [Trait](../../concept/02_intermediate/00_traits/01_traits.md) · [派生 Trait](../../concept/02_intermediate/00_traits/31_derive_traits.md) · [生命周期基础](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) · [高级生命周期](../../concept/01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md) | 覆盖完整 |
| **Ch 11** · [Writing Automated Tests](https://doc.rust-lang.org/book/ch11-00-testing.html) | 编写测试、控制测试运行、测试组织 | [测试基础](../../concept/01_foundation/10_testing_basics/16_testing_basics.md) · [测试策略](../../concept/06_ecosystem/09_testing_and_quality/12_testing_strategies.md) · [测试（进阶）](../../concept/06_ecosystem/09_testing_and_quality/16_testing.md) | 覆盖完整 |
| **Ch 12** · [An I/O Project: Building a Command Line Program](https://doc.rust-lang.org/book/ch12-00-an-io-project.html) | 命令行参数、文件读取、重构、TDD、环境变量、错误重定向 | [CLI 开发](../../concept/06_ecosystem/05_systems_and_embedded/25_cli_development.md) · [Cargo 工作流](../../concept/06_ecosystem/01_cargo/81_cargo_workflow.md) · [错误处理（Error Handling）基础](../../concept/01_foundation/08_error_handling/32_error_handling_basics.md) | 项目式教程，无独立“grep 项目”概念页；工程实践概念已覆盖 |
| **Ch 13** · [Iterators and Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html) | 闭包、迭代器（Iterator）、性能对比 | [闭包基础](../../concept/01_foundation/00_start/15_closure_basics.md) · [闭包类型](../../concept/02_intermediate/04_types_and_conversions/07_closure_types.md) · [迭代器模式](../../concept/02_intermediate/07_iterators_and_closures/15_iterator_patterns.md) | 覆盖完整 |
| **Ch 14** · [More about Cargo and Crates.io](https://doc.rust-lang.org/book/ch14-00-more-about-cargo.html) | Release Profile、发布 crate、Workspace、`cargo install`、自定义命令 | [Cargo 工作区](../../concept/06_ecosystem/01_cargo/78_cargo_workspaces.md) · [注册表与发布](../../concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md) · [Cargo 子命令与插件](../../concept/06_ecosystem/01_cargo/66_cargo_subcommands_and_plugins.md) · [Profile 与 Lint](../../concept/06_ecosystem/01_cargo/65_cargo_profiles_and_lints.md) · [Cargo 清单参考](../../concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md) | 覆盖完整 |
| **Ch 15** · [Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) | `Box<T>`、`Deref`、`Drop`、`Rc<T>`、`RefCell<T>`、循环引用 | [智能指针（Smart Pointer）](../../concept/02_intermediate/02_memory_management/12_smart_pointers.md) · [内部可变性](../../concept/02_intermediate/02_memory_management/08_interior_mutability.md) · [Cow 与借用（Borrowing）](../../concept/02_intermediate/02_memory_management/11_cow_and_borrowed.md) | 覆盖完整 |
| **Ch 16** · [Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | 线程、`mpsc` 通道、`Mutex`、`Arc`、`Send`/`Sync` | [并发基础](../../concept/03_advanced/00_concurrency/01_concurrency.md) · [并发模式](../../concept/03_advanced/00_concurrency/10_concurrency_patterns.md) · [原子与内存序](../../concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md) | 覆盖完整 |
| **Ch 17** · [Async and Await](https://doc.rust-lang.org/book/ch17-00-async-await.html) | `Future`、`async`/`await`、并发、Stream、任务与线程 | [异步编程基础](../../concept/03_advanced/01_async/02_async.md) · [Future 与执行器机制](../../concept/03_advanced/01_async/39_future_and_executor_mechanisms.md) · [Pin/Unpin](../../concept/03_advanced/01_async/06_pin_unpin.md) · [异步高级](../../concept/03_advanced/01_async/25_async_advanced.md) | 覆盖完整；对应 TRPL 3rd Ed 新增章 |
| **Ch 18** · [Object Oriented Programming Features](https://doc.rust-lang.org/book/ch18-00-oop.html) | OOP 特征、trait object、状态模式 | [Trait](../../concept/02_intermediate/00_traits/01_traits.md) · [分发机制](../../concept/02_intermediate/00_traits/39_dispatch_mechanisms.md) · [高级 Trait](../../concept/02_intermediate/00_traits/19_advanced_traits.md) · [设计模式](../../concept/06_ecosystem/03_design_patterns/02_patterns.md) | Rust 无传统 OOP，相关概念通过 trait 与设计模式覆盖 |
| **Ch 19** · [Patterns and Matching](https://doc.rust-lang.org/book/ch19-00-patterns.html) | 模式使用场景、可反驳性、模式语法 | [模式](../../concept/01_foundation/04_control_flow/40_patterns.md) · [模式参考](../../concept/04_formal/05_rustc_internals/49_patterns_reference.md) | 覆盖完整 |
| **Ch 20** · [Advanced Features](https://doc.rust-lang.org/book/ch20-00-advanced-features.html) | Unsafe Rust、高级 Trait、高级类型、高级函数与闭包（Closures）、宏 | [Unsafe Rust](../../concept/03_advanced/02_unsafe/03_unsafe.md) · [Unsafe 模式](../../concept/03_advanced/02_unsafe/12_unsafe_rust_patterns.md) · [高级 Trait](../../concept/02_intermediate/00_traits/19_advanced_traits.md) · [高级类型系统](../../concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md) · [闭包类型](../../concept/02_intermediate/04_types_and_conversions/07_closure_types.md) · [宏](../../concept/03_advanced/03_proc_macros/04_macros.md) · [过程宏（Procedural Macro）](../../concept/03_advanced/03_proc_macros/07_proc_macro.md) | 覆盖完整 |
| **Ch 21** · [Final Project: Building a Multithreaded Web Server](https://doc.rust-lang.org/book/title-page.html) <!-- link: known-broken --> | 单线程/多线程 Web 服务器、优雅关闭 | [Web 框架与网络服务](../../concept/06_ecosystem/04_web_and_networking/27_web_frameworks.md) · [高性能网络服务架构](../../concept/06_ecosystem/04_web_and_networking/39_high_performance_network_service_architecture.md) · [并发基础](../../concept/03_advanced/00_concurrency/01_concurrency.md) | 项目式教程，无独立“Web 服务器项目”概念页；相关并发/网络概念已覆盖 |
| **Ch 22** · [Appendix](https://doc.rust-lang.org/book/appendix-00.html) | 关键字、运算符与符号、可派生 Trait、开发工具、Edition、翻译、Rust 开发与 Nightly | [关键字](../../concept/01_foundation/00_start/36_keywords.md) · [运算符与符号](../../concept/01_foundation/00_start/37_operators_and_symbols.md) · [派生 Trait](../../concept/02_intermediate/00_traits/31_derive_traits.md) · [开发工具](../../concept/01_foundation/10_testing_basics/42_useful_development_tools.md) · [工具链生态](../../concept/06_ecosystem/00_toolchain/79_development_tools.md) · [Edition](../../concept/02_intermediate/00_traits/32_editions.md) · [Nightly Rust](../../concept/07_future/00_version_tracking/50_nightly_rust.md) · [Rust 发布流程](../../concept/02_intermediate/00_traits/33_rust_release_process.md) | 覆盖完整；附录 G 见[版本跟踪](../../concept/07_future/00_version_tracking/05_rust_version_tracking.md) |

---

## 覆盖统计

| 类别 | 数量 | 说明 |
|:---:|:---:|:---|
| 已映射章节 | 22 / 22 | Ch 1–Ch 22 均有对应 `concept/` 页面 |
| 项目式教程 | 3 | Ch 2、Ch 12、Ch 21 为综合项目，无独立项目概念页，但拆解后的知识点均已映射 |
| 已知缺口 | 2 | §3.4 Comments、§4.3 Slice Type 缺乏独立权威页；相关内容可在[词法结构](../../concept/04_formal/05_rustc_internals/45_lexical_structure.md)、[类型系统](../../concept/01_foundation/02_type_system/04_type_system.md)与[模式](../../concept/01_foundation/04_control_flow/40_patterns.md)中找到 |

---

## 使用建议

1. **按教材顺序学习**：打开 TRPL 对应章节，读完后再点击本表中的 `concept/` 链接进行深化。
2. **查漏补缺**：若某章在 `concept/` 中映射了多个页面，建议优先阅读与 TRPL 小节标题最贴近的页面。
3. **Gap 处理**：标注为“gap”的主题表示本项目尚未建立独立权威页；如需补充，请遵循 [Canonical 规则](../../AGENTS.md) 在 `concept/` 中新建，并更新本表。

---

> **文档版本**: 1.0
> **对应 Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 22 章全映射 · 已知 2 个小节缺口
