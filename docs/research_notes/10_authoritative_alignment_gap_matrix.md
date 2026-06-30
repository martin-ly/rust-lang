# docs/research_notes 权威国际化对齐缺口矩阵 {#docsresearch_notes-权威国际化对齐缺口矩阵}
>
> **概念族**: 权威来源对齐

> **内容分级**: [核心级]
>
> **分级**: [A]
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: 🔄 持续更新中
> **用途**: 系统识别 docs/research_notes 与 P0/P1/P2 权威来源之间的内容缺口，并给出优先级化补全建议
>
> **权威来源**:
>
> [Rust Reference](https://doc.rust-lang.org/reference/) |
> [The Rust Programming Language](https://doc.rust-lang.org/book/) |
> [Rustonomicon](https://doc.rust-lang.org/nomicon/) |
> [RustBelt](https://plv.mpi-sws.org/rustbelt/) |
> [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) |
> [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3) |
> [Aeneas](https://github.com/AeneasVerif/aeneas) |
> [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)

---

## 📑 目录 {#目录}

- [docs/research\_notes 权威国际化对齐缺口矩阵](#docsresearch_notes-权威国际化对齐缺口矩阵)
  - [📑 目录](#目录)
  - [📊 矩阵说明](#矩阵说明)
  - [🔬 experiments/ 实验主题](#experiments-实验主题)
  - [🧮 formal\_methods/ 形式化方法](#formal_methods-形式化方法)
  - [📐 type\_theory/ 类型理论](#type_theory-类型理论)
  - [📦 formal\_modules/ 形式化模块](#formal_modules-形式化模块)
  - [🏗️ software\_design\_theory/ 软件设计理论](#software_design_theory-软件设计理论)
  - [🔧 形式化工具](#形式化工具)
  - [🗺️ 后续执行路线图](#后续执行路线图)
    - [P0：立即执行（官方来源与核心安全）](#p0立即执行官方来源与核心安全)
    - [P1：短期完善（学术来源与工程实践）](#p1短期完善学术来源与工程实践)
    - [P2：中期增强（社区来源与扩展主题）](#p2中期增强社区来源与扩展主题)
  - [📚 权威来源索引](#权威来源索引)

---

## 📊 矩阵说明 {#矩阵说明}

本矩阵按 **主题 → 当前文件 → P0 官方来源 → P1 学术/形式化来源 → P2 社区来源 → 已对齐内容 → 待补缺口 → 优先级 → 建议升级动作** 的维度展开，覆盖 `docs/research_notes/` 下实验、形式化方法、类型理论、形式化模块、软件设计理论与主流形式化工具共 6 大领域。每行至少标注一条权威来源链接，用于快速复核。

> **来源:** [Rust Official Docs](https://doc.rust-lang.org/)

---

## 🔬 experiments/ 实验主题 {#experiments-实验主题}

| 主题 | 当前文件 | P0 官方来源 | P1 学术/形式化来源 | P2 社区来源 | 已对齐内容 | 待补缺口 | 优先级 | 建议升级动作 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| experiments/performance_benchmarks | `docs/research_notes/experiments/10_performance_benchmarks.md` | [Criterion.rs Book](https://bheisler.github.io/criterion.rs/book/)、[rustc Book](https://doc.rust-lang.org/rustc/) | — | [Rust Performance Book](https://nnethercote.github.io/perf-book/) | 元信息、来源索引、基本 benchmark 示例 | 统计显著性章节、PGO 示例、回归检测、噪声控制 | P0 | 补充 Criterion 统计方法、Rust 1.96 `profile` 示例与 CI 回归检测脚本 |
| experiments/memory_analysis | `docs/research_notes/experiments/10_memory_analysis.md` | [The Rust Book – Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)、[Rustonomicon](https://doc.rust-lang.org/nomicon/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Rust Performance Book – Heap Allocation](https://nnethercote.github.io/perf-book/heap-alloc.html) | 所有权与借用基础、堆栈示意 | `alloc`/`Layout`/对齐细节、Miri 检测用例、cache line 分析 | P0 | 增加 `std::alloc` 示例、Miri UB 检测流程、1.96 allocator API 更新 |
| experiments/concurrency_performance | `docs/research_notes/experiments/10_concurrency_performance.md` | [Rust Reference – Concurrency](https://doc.rust-lang.org/reference/)、[The Rust Book – Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) | [RustBelt](https://plv.mpi-sws.org/rustbelt/)、[Oxide](https://arxiv.org/abs/1903.00982) | [Rust Performance Book – Parallelism](https://nnethercote.github.io/perf-book/parallelism.html) | `Send`/`Sync` 模型、mutex/lock-free 对比 | 调度器模型、criterion-iter 多线程基准、contention 量化 | P0 | 补充 `rayon`/`crossbeam` benchmark、tokio runtime profile 示例 |
| experiments/compiler_optimizations | `docs/research_notes/experiments/10_compiler_optimizations.md` | [rustc Book – Codegen](https://doc.rust-lang.org/rustc/codegen-options.html)、[Cargo Book – Profiles](https://doc.rust-lang.org/cargo/reference/profiles.html) | [LLVM Language Reference](https://llvm.org/docs/LangRef.html) | [Rust Performance Book – Compile Times](https://nnethercote.github.io/perf-book/compile-times.html) | `opt-level`、`lto`、`codegen-units` 说明 | MIR opt 可视化、`rustc -Z` 调优、1.96 新优化 passes | P1 | 增加 `rustc -Z print-mono-items` 示例、优化前后 MIR 对比 |
| experiments/macro_expansion_performance | `docs/research_notes/experiments/10_macro_expansion_performance.md` | [Rust Reference – Macros](https://doc.rust-lang.org/reference/macros.html)、[The Rust Book – Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) | [Macros in Rust: Little Book](https://danielkeep.github.io/tlborm/book/) | [Rust Performance Book – Macros](https://nnethercote.github.io/perf-book/procedural-macros.html) | 声明宏与过程宏对比、展开示意 | `cargo expand` 定量分析、compile-time 内存占用、proc-macro2 开销 | P1 | 补充 proc-macro 编译时间基准、`tt-call`/`tt-muncher` 性能对比 |

> **来源:** [Criterion.rs Book](https://bheisler.github.io/criterion.rs/book/)
>
> **来源:** [Rust Performance Book](https://nnethercote.github.io/perf-book/)

---

## 🧮 formal_methods/ 形式化方法 {#formal_methods-形式化方法}

| 主题 | 当前文件 | P0 官方来源 | P1 学术/形式化来源 | P2 社区来源 | 已对齐内容 | 待补缺口 | 优先级 | 建议升级动作 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| formal_methods/ownership | `docs/research_notes/formal_methods/10_ownership_model.md` | [The Rust Book – Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)、[Rust Reference – Ownership](https://doc.rust-lang.org/reference/ownership.html) | [RustBelt](https://plv.mpi-sws.org/rustbelt/)、[Oxide](https://arxiv.org/abs/1903.00982) | [Rust Design Patterns – RAII](https://rust-unofficial.github.io/patterns/idioms/raii.html) | 所有权三规则、move/copy/clone 语义 | 形式化所有权逻辑（ separation logic ）、资源代数公理、dropck 证明 | P0 | 引入 Iris 资源代数片段、与 RustBelt protocol 对齐 |
| formal_methods/borrow | `docs/research_notes/formal_methods/10_borrow_checker_proof.md` | [Rust Reference – Borrowing](https://doc.rust-lang.org/reference/expressions.html?highlight=borrow#borrowing)、[Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)、[Stacked Borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md) | [Rust Design Patterns – Borrowing](https://rust-unofficial.github.io/patterns/) | 不可变/可变借用规则、NLL 说明 | Tree Borrows 迁移影响、two-phase borrow 形式化、aliasing model 对比 | P0 | 更新为 Tree Borrows 默认模型，补充 aliasing 边界反例 |
| formal_methods/lifetime | *(分散于 `10_ownership_model.md`、`10_borrow_checker_proof.md`)* | [Rust Reference – Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html)、[The Rust Book – Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) | [Oxide](https://arxiv.org/abs/1903.00982)、[Aeneas LLBC](https://arxiv.org/abs/2207.09467) | [Rust Reference – Lifetime Annotations](https://doc.rust-lang.org/reference/lifetime-elision.html) | 生命周期省略、'static、高阶 trait bound | 完整 lifetime calculus、region inference 算法、outlives 关系证明 | P0 | 创建独立 `10_lifetime_formalization.md`，与 type_theory 交叉引用 |
| formal_methods/variance | `docs/research_notes/formal_methods/10_variance_concept_mindmap.md` | [Rust Reference – Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html) | [Oxide](https://arxiv.org/abs/1903.00982)、[TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) | [Rustonomicon – Variance](https://doc.rust-lang.org/nomicon/subtyping.html) | 协变/逆变/不变定义、常见类型方差表 | 方差推导规则、形式化 soundness 证明、self-referential 类型边界 | P1 | 补充形式化 variance lattice 图、与 HRTB 交互示例 |

> **来源:** [RustBelt](https://plv.mpi-sws.org/rustbelt/)
>
> **来源:** [Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)

---

## 📐 type_theory/ 类型理论 {#type_theory-类型理论}

| 主题 | 当前文件 | P0 官方来源 | P1 学术/形式化来源 | P2 社区来源 | 已对齐内容 | 待补缺口 | 优先级 | 建议升级动作 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| type_theory/lifetime | `docs/research_notes/type_theory/10_lifetime_formalization.md` | [Rust Reference – Lifetimes](https://doc.rust-lang.org/reference/lifetime-elision.html)、[The Rust Book – Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) | [Oxide](https://arxiv.org/abs/1903.00982)、[Aeneas LLBC](https://arxiv.org/abs/2207.09467) | [Rust Reference – Lifetime Annotations](https://doc.rust-lang.org/reference/lifetime-elision.html) | 生命周期语法、省略规则、区域约束 | 区域推导算法（Revar / Polonius）、lifetime parametricity、高阶生命周期语义 | P0 | 与 formal_methods/lifetime 合并定义，补充 Polonius 事实示例 |
| type_theory/variance | `docs/research_notes/type_theory/10_variance_theory.md` | [Rust Reference – Subtyping and Variance](https://doc.rust-lang.org/reference/subtyping.html) | [Oxide](https://arxiv.org/abs/1903.00982)、[TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) | [Rustonomicon – Variance](https://doc.rust-lang.org/nomicon/subtyping.html) | 方差基础概念、类型构造器分类 | 方差组合规则、递归类型方差、与 trait object 子类型交互 | P1 | 补充 `PhantomData` 形式化角色、 variance-based API 设计模式 |

> **来源:** [Oxide](https://arxiv.org/abs/1903.00982)
>
> **来源:** [Aeneas LLBC Paper](https://arxiv.org/abs/2207.09467)

---

## 📦 formal_modules/ 形式化模块 {#formal_modules-形式化模块}

| 主题 | 当前文件 | P0 官方来源 | P1 学术/形式化来源 | P2 社区来源 | 已对齐内容 | 待补缺口 | 优先级 | 建议升级动作 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| formal_modules/module_system | `docs/research_notes/formal_modules/10_module_system_specification.md` | [Rust Reference – Modules](https://doc.rust-lang.org/reference/items/modules.html)、[Cargo Book – Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | [Oxide](https://arxiv.org/abs/1903.00982) | [Rust Design Patterns – Module Organization](https://rust-unofficial.github.io/patterns/) | `mod`/`use`/`pub` 规则、模块树 | 可见性形式化、crate 边界语义、re-export 与 name resolution 证明 | P1 | 引入命名解析小步语义、与 linkage 章节交叉引用 |
| formal_modules/linkage | `docs/research_notes/formal_modules/20_linkage_and_symbols.md` | [Rust Reference – Linkage](https://doc.rust-lang.org/reference/linkage.html)、[rustc Book – Linker](https://doc.rust-lang.org/rustc/linker-plugin-lto.html) | [ELF/PE 规范](https://refspecs.linuxfoundation.org/elf/elf.pdf) | [Rust Performance Book – Linking](https://nnethercote.github.io/perf-book/build-configuration.html) | `extern`、`#[no_mangle]`、crate type 说明 | symbol visibility 形式化、LTO/PGO 与模块边界、dylib 安全契约 | P1 | 补充 `nm`/`readelf` 示例、link-time 优化前后符号表对比 |
| formal_modules/HIR_MIR | `docs/research_notes/formal_modules/30_module_hir_mir_mapping.md` | [rustc-dev-guide – HIR](https://rustc-dev-guide.rust-lang.org/hir.html)、[rustc-dev-guide – MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html) | [Rustc MIR 论文](https://www.cs.indiana.edu/~sabahi/MIR.pdf) | [Rust Compiler Development Guide](https://rustc-dev-guide.rust-lang.org/) | HIR/MIR 定义、borrowck 位置 | MIR 语义小步规则、drop elaboration、const eval 与 MIR 交互 | P1 | 增加 `rustc +nightly -Z unpretty=mir` 输出解读 |
| formal_modules/safety_abstraction | `docs/research_notes/formal_modules/40_module_safety_abstraction.md` | [Rustonomicon](https://doc.rust-lang.org/nomicon/)、[Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/)、[Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) | [Rust Design Patterns – Unsafe Guidelines](https://rust-unofficial.github.io/patterns/) | unsafe boundary、invariant、 abstraction 概念 | 模块级 safety invariant 证明、公开 API 契约、ghost state 封装 | P0 | 引入 RustBelt protocol 示例、补充标准库抽象案例分析 |
| formal_modules/tools_mapping | `docs/research_notes/formal_modules/10_formalization_ecology_mindmap.md` | [Rust Official Docs](https://doc.rust-lang.org/)、[Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [Aeneas](https://github.com/AeneasVerif/aeneas)、[coq-of-rust](https://github.com/formal-land/coq-of-rust)、[RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Awesome Rust – Verification](https://github.com/rust-unofficial/awesome-rust#verification) | 工具列表与能力对比 | 工具版本兼容性矩阵、模块/可见性支持度、CI 集成示例 | P1 | 更新各工具 Rust 1.96 支持状态，补充 `formal_modules/50_formal_tools_module_mapping.md` 引用 |

> **来源:** [Rust Reference – Modules](https://doc.rust-lang.org/reference/items/modules.html)
>
> **来源:** [rustc-dev-guide – MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html)

---

## 🏗️ software_design_theory/ 软件设计理论 {#software_design_theory-软件设计理论}

| 主题 | 当前文件 | P0 官方来源 | P1 学术/形式化来源 | P2 社区来源 | 已对齐内容 | 待补缺口 | 优先级 | 建议升级动作 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| software_design_theory/01_design_patterns_formal（创建型） | `docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/README.md` | [The Rust Book – OOP](https://doc.rust-lang.org/book/ch17-00-oop.html)、[API Guidelines](https://rust-lang.github.io/api-guidelines/) | [Design Patterns (GoF)](https://en.wikipedia.org/wiki/Design_Patterns) | [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) | 单例、工厂、建造者等 Rust 实现 | 形式化 invariant、所有权友好的 builder 证明、零成本抽象度量 | P1 | 为每个模式补充前置/后置条件与反例 |
| software_design_theory/01_design_patterns_formal（结构型） | `docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/README.md` | [The Rust Book – Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)、[Rust Reference – Traits](https://doc.rust-lang.org/reference/items/traits.html) | [RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Rust Design Patterns – Structural](https://rust-unofficial.github.io/patterns/) | Adapter、Decorator、Proxy 等实现 | 组合安全性、trait object 与泛型选择的形式化依据、生命周期兼容矩阵 | P1 | 补充 `Deref`/`AsRef` 形式化对比、self-referential 结构处理 |
| software_design_theory/01_design_patterns_formal（行为型） | `docs/research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/README.md` | [The Rust Book – Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html)、[Rust Reference – Closures](https://doc.rust-lang.org/reference/types/closure.html) | [Category Theory for Programmers](https://bartoszmilewski.com/2014/10/28/category-theory-for-programmers-the-preface/) | [Rust Design Patterns – Behavioral](https://rust-unofficial.github.io/patterns/) | 迭代器、策略、观察者等模式 | Fn/FnMut/FnOnce 与行为模式的类型安全、状态机形式化 | P1 | 补充 `Iterator` 代数定律、状态转移不变量证明 |
| software_design_theory/02_workflow | `docs/research_notes/software_design_theory/02_workflow/README.md` | [Cargo Book](https://doc.rust-lang.org/cargo/)、[Rust By Example](https://doc.rust-lang.org/rust-by-example/) | — | [Rust Design Patterns – Workflow](https://rust-unofficial.github.io/patterns/) | 开发、测试、发布流程 | 可复现构建、workspace 工作流、1.96 edition 迁移 checklist | P1 | 增加 `cargo-husky`/`cargo-make` 集成、workspace 依赖对齐示例 |
| software_design_theory/02_workflow_safe_complete_models | `docs/research_notes/software_design_theory/02_workflow_safe_complete_models/README.md` | [The Rust Book – Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)、[Rust Reference – Errors](https://doc.rust-lang.org/reference/errors.html) | [Type Systems for Error Handling](https://arxiv.org/abs/1805.08637) | [Rust Design Patterns – Error Handling](https://rust-unofficial.github.io/patterns/idioms/privatize-errors.html) | Result/Option、错误处理策略 | 完整错误分类法、`?` 与 `try` 形式化、错误恢复策略证明 | P1 | 补充 `thiserror`/`anyhow` 对比与 1.96 `try` block 状态 |
| software_design_theory/03_execution_models | `docs/research_notes/software_design_theory/03_execution_models/README.md` | [The Rust Book – Concurrency/Async](https://doc.rust-lang.org/book/ch16-00-concurrency.html)、[Async Book](https://rust-lang.github.io/async-book/) | [Oxide](https://arxiv.org/abs/1903.00982)、[RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Rust Design Patterns – Concurrency](https://rust-unofficial.github.io/patterns/) | 同步/异步/并发/并行/分布式模型 | async/await 状态机语义、Pin 形式化、executor 调度模型 | P0 | 与 1.96 async trait 稳定性对齐，补充 `pin-project` 形式化说明 |
| software_design_theory/04_compositional_engineering | `docs/research_notes/software_design_theory/04_compositional_engineering/README.md` | [API Guidelines](https://rust-lang.github.io/api-guidelines/)、[Cargo Book – SemVer](https://doc.rust-lang.org/cargo/reference/semver.html) | [Modular Software Verification](https://software.imdea.org/~cflanagan/papers/rse.pdf) | [Rust Design Patterns – API Design](https://rust-unofficial.github.io/patterns/) | 组合原则、trait 组合、版本兼容 | 形式化组合语义、semver 与类型系统兼容性、crate 边界不变量 | P1 | 增加向后兼容性检查表、`semverver`/`cargo-public-api` 示例 |
| software_design_theory/05_boundary_system | `docs/research_notes/software_design_theory/05_boundary_system/README.md` | [Rustonomicon](https://doc.rust-lang.org/nomicon/)、[Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/)、[Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) | [Rust Design Patterns – FFI](https://rust-unofficial.github.io/patterns/idioms/ffi.html) | safe/unsafe boundary、expressive/inexpressive matrix | FFI 边界契约、C ABI 形式化、unsafe 抽象证明义务 | P0 | 补充 `cbindgen`/`cxx` 与 Miri 检测组合示例 |
| software_design_theory/05_distributed | `docs/research_notes/software_design_theory/05_distributed/README.md` | [Cargo Book](https://doc.rust-lang.org/cargo/)、[Rust By Example – Networking](https://doc.rust-lang.org/rust-by-example/std/net.html) | [DISTAL / 分布式系统形式化](https://decomposition.al/) | [Rust Design Patterns – Distributed](https://rust-unofficial.github.io/patterns/) | Saga、CQRS、Circuit Breaker 等模式 | 一致性模型、容错形式化、actor 模型与 tokio 集成 | P1 | 补充 `tarpc`/`tonic` 示例、一致性级别与错误恢复策略矩阵 |
| software_design_theory/06_rust_idioms | `docs/research_notes/software_design_theory/06_rust_idioms.md` | [The Rust Book](https://doc.rust-lang.org/book/)、[API Guidelines](https://rust-lang.github.io/api-guidelines/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/) | [Rust Design Patterns – Idioms](https://rust-unofficial.github.io/patterns/idioms/) | 惯用代码风格、类型封装 | 惯用法与形式化安全性的映射、零成本抽象证明、clippy lint 与最佳实践 | P1 | 为每条 idioms 补充官方来源与反例 |
| software_design_theory/07_anti_patterns | `docs/research_notes/software_design_theory/07_anti_patterns.md` | [Rust Reference](https://doc.rust-lang.org/reference/)、[Clippy Lints](https://rust-lang.github.io/rust-clippy/master/index.html) | [Common Rust Anti-patterns](https://rust-unofficial.github.io/patterns/anti_patterns/) | [Rust Design Patterns – Anti-patterns](https://rust-unofficial.github.io/patterns/anti_patterns/) | 常见反模式列表 | 反模式与编译器错误/UB 的关联、重构形式化收益 | P2 | 补充 clippy 自动检测映射、重构前后 Miri 验证示例 |
| software_design_theory/07_crate_architectures | `docs/research_notes/software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md` | [Cargo Book](https://doc.rust-lang.org/cargo/)、[API Guidelines](https://rust-lang.github.io/api-guidelines/) | [Software Architecture in Practice](https://www.pearson.com/en-us/subject-catalog/p/software-architecture-in-practice/P200000005792) | [Rust Design Patterns – Architecture](https://rust-unofficial.github.io/patterns/) | 主流 crate 架构概览 | crate 分层形式化、public API 稳定性证明、模块依赖循环检测 | P1 | 为每个 crate 补充官方文档来源与依赖图、版本兼容性矩阵 |

> **来源:** [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
>
> **来源:** [API Guidelines](https://rust-lang.github.io/api-guidelines/)

---

## 🔧 形式化工具 {#形式化工具}

| 主题 | 当前文件 | P0 官方来源 | P1 学术/形式化来源 | P2 社区来源 | 已对齐内容 | 待补缺口 | 优先级 | 建议升级动作 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| Aeneas | `docs/research_notes/10_aeneas_integration_plan.md`、`formal_modules/50_formal_tools_module_mapping.md` | [Aeneas – GitHub](https://github.com/AeneasVerif/aeneas) | [Aeneas LLBC Paper](https://arxiv.org/abs/2207.09467) | [Aeneas Tutorials](https://aeneas-verif.org/) | 工具定位、LLBC 概念 | 1.96 语法支持度、trait 与泛型证明、模块边界处理 | P1 | 更新安装与 `aeneas` 命令示例，补充 trait 证明案例 |
| coq-of-rust | `docs/research_notes/10_coq_of_rust_integration_plan.md`、`formal_modules/50_formal_tools_module_mapping.md` | [coq-of-rust – GitHub](https://github.com/formal-land/coq-of-rust) | [coq-of-rust 论文/文档](https://formal-land.github.io/coq-of-rust/) | [Coq 社区](https://coq.inria.fr/) | 翻译流程、Coq 输出结构 | 1.96 新特性翻译、unsafe 子集覆盖、证明自动化策略 | P1 | 增加 `coq-of-rust` 对 2024 edition 的适配状态 |
| RustBelt | `docs/research_notes/10_rustbelt_alignment.md` | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [RustBelt Paper (POPL 2018)](https://plv.mpi-sws.org/rustbelt/popl18/)、[RustBelt Project](https://plv.mpi-sws.org/rustbelt/) | [RustBelt Blog Series](https://plv.mpi-sws.org/rustbelt/) | 协议、资源、逻辑关系 | Iris 最新进展、1.96 标准库新抽象证明、Tree Borrows 兼容 | P0 | 补充 `Rc`/`Arc`/`Cell` 证明纲要、与 Tree Borrows 协调 |
| Tree Borrows | `docs/research_notes/10_rustsem_semantics.md` | [Unsafe Code Guidelines](https://rust-lang.github.io/unsafe-code-guidelines/) | [Tree Borrows Blog](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)、[Tree Borrows Paper](https://arxiv.org/abs/2410.12379) | [Miri 文档](https://github.com/rust-lang/miri) | 别名模型动机、与 Stacked Borrows 对比 | 默认启用状态、与 `UnsafeCell`/raw pointer 交互、形式化操作语义 | P0 | 更新为默认别名模型，补充 UB 判定流程图 |
| RustSEM | `docs/research_notes/10_rustsem_semantics.md` | [Rust Reference](https://doc.rust-lang.org/reference/)、[Rust Official Docs](https://doc.rust-lang.org/) | [RustSEM Project](https://rustsem.github.io/)、[Oxide](https://arxiv.org/abs/1903.00982) | [Rust Formal Methods WG](https://rust-formal-methods.github.io/) | 操作语义框架、小步/大步语义 | 并发语义、async 语义、与 rustc 最新 MIR 对齐 | P1 | 补充 1.96 语言子集覆盖表、与 Miri 对比 |
| Oxide | *(引用多处，无独立文件)* | [Rust Reference](https://doc.rust-lang.org/reference/) | [Oxide Paper](https://arxiv.org/abs/1903.00982) | [Rust Formal Methods WG](https://rust-formal-methods.github.io/) | 生命周期/所有权类型系统 | 独立章节缺失、与 Polonius 对接、1.96 新类型特性 | P1 | 创建 `type_theory/10_oxide_formalization.md` 独立文档 |
| Verus | `docs/research_notes/10_verification_tools_matrix.md` | [Verus – GitHub](https://github.com/verus-lang/verus) | [Verus Paper](https://verus-lang.github.io/verus/) | [Verus Zulip](https://verus-lang.zulipchat.com/) | 命令式验证、所有权证明 | 1.96 兼容性、并发证明、trait 规范支持 | P1 | 更新 Verus 对 2024 edition 支持状态，补充并发案例 |
| Kani | `docs/research_notes/10_verification_tools_matrix.md` | [Kani – GitHub](https://github.com/model-checking/kani) | [Kani Documentation](https://model-checking.github.io/kani/) | [Kani 示例](https://github.com/model-checking/kani/tree/main/tests) | `#[kani::proof]`、属性证明 | 1.96 标准库 harness、并发模型检查、与 cargo 集成最佳实践 | P0 | 补充 `kani` 对 2024 edition 的验证示例、CI 模板 |
| Prusti | `docs/research_notes/10_verification_tools_matrix.md` | [Prusti – ETH Zurich](https://www.pm.inf.ethz.ch/research/prusti.html) | [Prusti Paper](https://www.pm.inf.ethz.ch/publications/RusBos21.html) | [Prusti Zulip](https://prusti.zulipchat.com/) | 契约式验证、`#[requires]`/`#[ensures]` | Rust 1.96 支持状态、泛型/高阶函数证明、维护状态 | P2 | 标注工具维护状态，补充替代方案（Verus/Creusot）对比 |
| Creusot | `docs/research_notes/10_verification_tools_matrix.md` | [Creusot – GitHub](https://github.com/creusot-rs/creusot) | [Creusot Paper](https://hal.science/hal-03737979/) | [Creusot 文档](https://creusot-rs.github.io/) | Why3 后端、谓词规范 | 1.96 语法支持、闭包/迭代器规范、教程完整性 | P1 | 更新 Creusot 安装指南、补充 iterator 规范示例 |
| Miri | `docs/research_notes/10_verification_tools_matrix.md` | [Miri – GitHub](https://github.com/rust-lang/miri) | [Stacked Borrows](https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md)、[Tree Borrows](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html) | [Miri 文档](https://github.com/rust-lang/miri) | `cargo miri`、UB 检测 | 1.96 新 UB 类别、extern function 支持、与 Tree Borrows 默认集成 | P0 | 更新 `MIRIFLAGS=-Zmiri-tree-borrows` 默认配置、补充 async Miri 示例 |

> **来源:** [Rust Formal Methods WG](https://rust-formal-methods.github.io/)
>
> **来源:** [Miri – GitHub](https://github.com/rust-lang/miri)

---

## 🗺️ 后续执行路线图 {#后续执行路线图}

### P0：立即执行（官方来源与核心安全） {#p0立即执行官方来源与核心安全}

1. **experiments/performance_benchmarks**：补充 Criterion 统计方法、Rust 1.96 `profile` 示例、CI 回归检测脚本。
2. **experiments/memory_analysis**：增加 `std::alloc`/`Layout` 示例、Miri UB 检测流程、cache line 分析。
3. **experiments/concurrency_performance**：补充 `rayon`/`crossbeam` benchmark、tokio runtime profile 示例。
4. **formal_methods/ownership**：引入 Iris 资源代数片段，与 RustBelt protocol 对齐。
5. **formal_methods/borrow**：更新为 Tree Borrows 默认别名模型，补充 aliasing 边界反例。
6. **formal_methods/lifetime + type_theory/lifetime**：合并定义，创建/更新独立生命周期形式化文档，补充 Polonius 事实示例。
7. **software_design_theory/03_execution_models**：与 1.96 async trait 稳定性对齐，补充 `pin-project` 形式化说明。
8. **software_design_theory/05_boundary_system**：补充 `cbindgen`/`cxx` 与 Miri 检测组合示例。
9. **形式化工具 RustBelt/Tree Borrows/Kani/Miri**：更新默认模型与 1.96 兼容性，补充标准库抽象证明纲要和 CI 模板。

### P1：短期完善（学术来源与工程实践） {#p1短期完善学术来源与工程实践}

1. **experiments/compiler_optimizations**：增加 `rustc -Z print-mono-items` 示例、优化前后 MIR 对比。
2. **experiments/macro_expansion_performance**：补充 proc-macro 编译时间基准、`tt-call`/`tt-muncher` 性能对比。
3. **formal_methods/variance + type_theory/variance**：补充 `PhantomData` 形式化角色、variance lattice 图。
4. **formal_modules/**：补充命名解析/链接/MIR 小步语义、unsafe 抽象证明义务。
5. **software_design_theory/01_design_patterns_formal**：为创建/结构/行为型模式补充不变量与反例。
6. **software_design_theory/02_workflow_safe_complete_models**：补充 `thiserror`/`anyhow` 对比与 1.96 `try` block 状态。
7. **software_design_theory/04_compositional_engineering + 07_crate_architectures**：增加 semver 兼容性检查与 crate 依赖图。
8. **形式化工具 Aeneas/coqo-of-rust/RustSEM/Oxide/Verus/Creusot**：更新 1.96 支持状态、补充 trait/并发/iterator 证明案例。

### P2：中期增强（社区来源与扩展主题） {#p2中期增强社区来源与扩展主题}

1. **software_design_theory/07_anti_patterns**：补充 clippy 自动检测映射、重构前后 Miri 验证示例。
2. **形式化工具 Prusti**：标注维护状态，补充替代方案（Verus/Creusot）对比。
3. **跨文档索引**：建立从本矩阵到 `docs/research_notes/INDEX.md` 与 `10_cross_reference_index.md` 的反向链接，确保每处缺口都有追踪 issue。
4. **国际化**：为 P0 行补充英文摘要，便于与国际 Rust 形式化社区对齐。

---

## 📚 权威来源索引 {#权威来源索引}

| 级别 | 来源名称 | URL |
| :--- | :--- | :--- |
| P0 | The Rust Book | <https://doc.rust-lang.org/book/> |
| P0 | Rust Reference | <https://doc.rust-lang.org/reference/> |
| P0 | rustc Book | <https://doc.rust-lang.org/rustc/> |
| P0 | Cargo Book | <https://doc.rust-lang.org/cargo/> |
| P0 | Rustonomicon | <https://doc.rust-lang.org/nomicon/> |
| P0 | Rust By Example | <https://doc.rust-lang.org/rust-by-example/> |
| P0 | Unsafe Code Guidelines | <https://rust-lang.github.io/unsafe-code-guidelines/> |
| P0 | API Guidelines | <https://rust-lang.github.io/api-guidelines/> |
| P0 | Async Book | <https://rust-lang.github.io/async-book/> |
| P0 | Clippy Lints | <https://rust-lang.github.io/rust-clippy/master/index.html> |
| P0 | rustc-dev-guide | <https://rustc-dev-guide.rust-lang.org/> |
| P1 | RustBelt | <https://plv.mpi-sws.org/rustbelt/> |
| P1 | RustBelt POPL 2018 | <https://plv.mpi-sws.org/rustbelt/popl18/> |
| P1 | Tree Borrows | <https://www.ralfj.de/blog/2023/06/02/tree-borrows.html> |
| P1 | Tree Borrows Paper | <https://arxiv.org/abs/2410.12379> |
| P1 | Stacked Borrows | <https://github.com/rust-lang/unsafe-code-guidelines/blob/master/wip/stacked-borrows.md> |
| P1 | Oxide | <https://arxiv.org/abs/1903.00982> |
| P1 | Aeneas LLBC Paper | <https://arxiv.org/abs/2207.09467> |
| P1 | RustSEM | <https://rustsem.github.io/> |
| P1 | Verus | <https://verus-lang.github.io/verus/> |
| P1 | Kani | <https://model-checking.github.io/kani/> |
| P1 | Prusti | <https://www.pm.inf.ethz.ch/research/prusti.html> |
| P1 | Creusot | <https://creusot-rs.github.io/> |
| P2 | Rust Design Patterns | <https://rust-unofficial.github.io/patterns/> |
| P2 | Rust Performance Book | <https://nnethercote.github.io/perf-book/> |
| P2 | Criterion.rs Book | <https://bheisler.github.io/criterion.rs/book/> |
| P2 | Miri | <https://github.com/rust-lang/miri> |
| P2 | Aeneas | <https://github.com/AeneasVerif/aeneas> |
| P2 | coq-of-rust | <https://github.com/formal-land/coq-of-rust> |
| P2 | Rust Formal Methods WG | <https://rust-formal-methods.github.io/> |

---

> **来源:** [Rust Official Docs](https://doc.rust-lang.org/)
>
> **说明**: 本矩阵将持续追踪权威来源更新，每次 Rust 小版本发布后复盘一次，确保缺口定义与升级动作保持时效性。