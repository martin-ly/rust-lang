# 知识图谱索引

> **内容分级**: [核心级]
>
> **分级**: [A]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ **六层两网一库知识体系 100% 骨架与核心内容覆盖完成**（阶段 0-3 完成；阶段 4 行号级锚点作为持续增强项）
> **层级**: L1-L6
> **概念族**: 综合系统化框架 / 知识图谱
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)

---

## 📑 目录

- [知识图谱索引](#知识图谱索引)
  - [📑 目录](#-目录)
  - [一、图谱说明](#一图谱说明)
  - [二、核心概念节点](#二核心概念节点)
    - [L1 元概念](#l1-元概念)
    - [L2 核心概念族](#l2-核心概念族)
    - [L3 具体概念](#l3-具体概念)
  - [三、关系边](#三关系边)
  - [四、文档锚点](#四文档锚点)
    - [4.1 形式化证明锚点](#41-形式化证明锚点)
    - [4.2 代码示例锚点](#42-代码示例锚点)
  - [五、8 大主-topic 入口](#五8-大主-topic-入口)
  - [六、阶段推进状态](#六阶段推进状态)
    - [剩余细化项](#剩余细化项)
  - [七、权威来源索引](#七权威来源索引)

---

## 一、图谱说明

本文档是 `docs/research_notes/` 的**知识图谱物理锚点**，以“六层两网一库”框架组织：

- **节点**：L0–L7 各层的概念、定理、示例、反例、版本。
- **边**：概念之间的依赖、蕴含、精化、实现、反例违反、版本引入等关系。
- **锚点**：每个节点/边指向具体的文档和代码位置。

> **使用方式**：从本索引出发，可按层级、主题、关系类型导航到具体文档。

---

## 二、核心概念节点

### L1 元概念

| 节点 | 说明 | 主文档 |
|------|------|--------|
| 资源管理 | 所有权、借用、生命周期共同解决的核心问题 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) |
| 类型安全 | 编译期保证程序行为的类型系统目标 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) |
| 并发安全 | 多线程/异步执行中的数据竞争自由 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) |
| 内存安全 | 无 UB、无悬垂指针、无数据竞争 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |
| 抽象能力 | 泛型、Trait、模块、宏等组合抽象机制 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| 权威来源对齐 | 项目概念与国际化权威来源的映射与追溯 | [10_authoritative_source_alignment_network.md](10_authoritative_source_alignment_network.md) |

### L2 核心概念族

| 节点 | 层级 | 主文档 | 反例 |
|------|------|--------|------|
| 所有权 | L2 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) / [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 借用 | L2 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) / [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 生命周期 | L2 | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) / [formal_methods/10_lifetime_formalization.md](formal_methods/10_lifetime_formalization.md) | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 型变 | L2 | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) |
| 类型系统 | L2 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) / [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| Trait | L2 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) / [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| Send/Sync | L2 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) / [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| Future / async/await | L2 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) / [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| Pin / 自引用 | L2 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) / [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 模块系统 | L2 | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) |
| 设计模式 | L2 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) |
| 工作流模式 | L2 | [software_design_theory/02_workflow/README.md](software_design_theory/02_workflow/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) |
| 执行模型 | L2 | [software_design_theory/03_execution_models/README.md](software_design_theory/03_execution_models/README.md) | [software_design_theory/03_execution_models/README.md](software_design_theory/03_execution_models/README.md) |
| 组合工程 | L2 | [software_design_theory/04_compositional_engineering/README.md](software_design_theory/04_compositional_engineering/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) |
| 边界系统 | L2 | [software_design_theory/05_boundary_system/README.md](software_design_theory/05_boundary_system/README.md) | [software_design_theory/05_boundary_system/README.md](software_design_theory/05_boundary_system/README.md) |
| 分布式模式 | L2 | [software_design_theory/05_distributed/README.md](software_design_theory/05_distributed/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) |
| Crate 架构 | L2 | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |

### L3 具体概念

> **说明**：L3 节点按 8 大主-topic 持续展开。以下模块系统相关节点已完成首批梳理，其余节点在阶段 2 继续补全。

| 节点 | 所属概念族 | 层级 | 主文档 | 反例/边界 |
|------|------------|------|--------|-----------|
| `mod` 声明 | 形式化模块 | L3 | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §2 |
| `use` 路径 | 形式化模块 | L3 | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §4 |
| `pub(in path)` | 形式化模块 | L3 | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §3 |
| `crate-type` | 形式化模块 / 链接 | L3 | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §6 |
| `#[no_mangle]` | 形式化模块 / 链接 | L3 | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §8 |
| 模块分层模式 | 形式化模块 | L5 | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §6-§7 |
| `pub use` 重导出 | 形式化模块 | L5 | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §4 |
| Sealed trait | 形式化模块 / 类型系统 | L5 | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) | — |
| Workspace 多 crate | 形式化模块 | L5 | [formal_modules/70_module_patterns_and_refactoring.md](formal_modules/70_module_patterns_and_refactoring.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §6 |
| `move` 语义 | 所有权 | L3 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §1 |
| `&T` / `&mut T` | 借用 | L3 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §2-§3 |
| 悬垂引用 | 借用 / 生命周期 | L3-L4 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) / [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §4 |
| 自引用类型 | 所有权 / Pin | L3-L4 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §5 |
| `Send` / `Sync` | 并发安全 | L3 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §6 |
| 生命周期标注 | 生命周期 | L3 | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §7 |
| 型变（协变/逆变/不变） | 类型系统 | L3 | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §1 |
| `dyn Trait` | 类型系统 | L3 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §3 |
| `impl Trait` | 类型系统 | L3 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §4 |
| Orphan 规则 | 类型系统 / Trait | L3 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §5 |
| 关联类型 | 类型系统 / Trait | L3 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §6 |
| Copy / Drop 互斥 | 类型系统 / 资源语义 | L3 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | [type_theory/60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §7 |
| `Send` / `Sync` | 并发安全 | L3 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §1-§2 |
| `Mutex` / `RwLock` | 并发安全 | L3 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §3 |
| `Future` / `poll` | 异步 | L3-L4 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §7 |
| `Pin` 契约 | 异步 / 自引用 | L3-L4 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §5 |
| 裸指针 | unsafe / 内存 | L3 | [10_safe_unsafe_comprehensive_analysis.md](../10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §1-§2 |
| `unsafe impl` | unsafe / 并发 | L3 | [10_safe_unsafe_comprehensive_analysis.md](../10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §5 |
| `transmute` | unsafe / 类型 | L3 | [10_safe_unsafe_comprehensive_analysis.md](../10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 |
| FFI 内存协议 | unsafe / FFI | L3 | [10_safe_unsafe_comprehensive_analysis.md](../10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 |
| 单例 / 全局状态 | 设计模式 | L3 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §1 |
| Observer / 生命周期 | 设计模式 | L3 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §2 |
| Builder / 类型状态 | 设计模式 | L3 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §4 |
| 内部可变性 | 设计模式 / unsafe | L3 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) §3 |
| crate 依赖图 | Crate 架构 | L3 | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §1 |
| Feature flag | Crate 架构 | L3 | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §5 |
| SemVer / API 稳定性 | Crate 架构 / 版本演进 | L3-L7 | [software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md](software_design_theory/07_crate_architectures/00_crate_architecture_master_index.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) §7 |
| Edition 迁移 | 版本演进 | L7 | [10_rust_194_research_update.md](10_rust_194_research_update.md) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §1-§4 |
| `rust-version` 管理 | 版本演进 | L7 | [10_rust_194_research_update.md](10_rust_194_research_update.md) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) §5-§7 |
| 工作流状态机 | 工作流 | L3 | [software_design_theory/02_workflow/README.md](software_design_theory/02_workflow/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §1 |
| 补偿链 / Saga | 工作流 | L3 | [software_design_theory/02_workflow/02_compensation_chain.md](software_design_theory/02_workflow/02_compensation_chain.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §2 |
| 长事务 | 工作流 | L3 | [software_design_theory/02_workflow/03_long_running_transaction.md](software_design_theory/02_workflow/03_long_running_transaction.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §3 |
| 服务组合 | 组合工程 | L3 | [software_design_theory/04_compositional_engineering/README.md](software_design_theory/04_compositional_engineering/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §5 |
| 分布式 ID | 分布式 | L3 | [software_design_theory/05_distributed/README.md](software_design_theory/05_distributed/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §4 |
| Actor 消息顺序 | 分布式 | L3 | [software_design_theory/05_distributed/README.md](software_design_theory/05_distributed/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §6 |
| 微基准 | 实验研究 | L5 | [experiments/10_performance_benchmarks.md](experiments/10_performance_benchmarks.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §1-§4 |
| 并发基准 | 实验研究 | L5 | [experiments/10_concurrency_performance.md](experiments/10_concurrency_performance.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §5 |
| 内存分析 | 实验研究 | L5 | [experiments/10_memory_analysis.md](experiments/10_memory_analysis.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §6 |
| 宏展开性能 | 实验研究 | L5 | [experiments/10_macro_expansion_performance.md](experiments/10_macro_expansion_performance.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §7 |
| Rust Reference 对齐 | 权威来源对齐 | L0-L4 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) | — |
| Rustonomicon 对齐 | 权威来源对齐 | L0-L6 | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) |
| Cargo Book 对齐 | 权威来源对齐 | L0-L5 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| Edition Guide 对齐 | 权威来源对齐 | L7 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) |
| Async Book 对齐 | 权威来源对齐 | L0-L6 | [10_async_book_alignment.md](10_async_book_alignment.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) |
| RFC 对齐索引 | 权威来源对齐 | L0-L7 | [10_rfc_alignment_index.md](10_rfc_alignment_index.md) | 各主题反例 |

> **待补全**：代码示例到具体文件行号的锚点。

---

## 三、关系边

| 关系类型 | 源节点 | 目标节点 | 说明 | 锚点文档 |
|----------|--------|----------|------|----------|
| depends_on | 借用 | 所有权 | 借用规则建立在所有权之上 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| depends_on | 生命周期 | 借用 | 生命周期标注约束借用范围 | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) |
| depends_on | Send/Sync | 所有权 | 跨线程转移依赖所有权语义 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) |
| depends_on | async/await | Future | async 块编译为 Future 状态机 | [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) |
| depends_on | Pin | 自引用 | Pin 保证自引用类型不被移动 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) |
| depends_on | Trait | 类型系统 | Trait 是类型系统的核心扩展 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| depends_on | 型变 | 生命周期 | 型变规则决定生命周期子类型关系 | [type_theory/10_variance_theory.md](type_theory/10_variance_theory.md) |
| implies | 所有权 + 借用 | 内存安全 | 正确的所有权/借用保证无悬垂指针 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |
| implies | Send/Sync | 并发安全 | 正确实现 Send/Sync 保证数据竞争自由 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) |
| contradicts | 双可变借用 | 借用规则 | 同一作用域内两个 `&mut` 违反借用规则 | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| contradicts | Rc 跨线程 | Send/Sync | `Rc` 未实现 Send/Sync | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| implements | 类型状态 | 设计模式 | 类型状态在编译期保证合法状态迁移 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) |
| refines | Tree Borrows | Stacked Borrows | Tree Borrows 是对借用语义的更精确建模 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) |
| version_introduces | Edition 2024 | tail-expr drop order | 2024 改变尾部表达式 drop 顺序 | [10_rust_194_research_update.md](10_rust_194_research_update.md) |
| aligns_to | 所有权 | Rust Reference – Ownership | 项目所有权概念与 Reference 规范对齐 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) |
| aligns_to | 模块系统 | Rust Reference – Items and Modules | 项目模块系统与 Reference 规范对齐 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) |
| aligns_to | unsafe | Rustonomicon | 项目 unsafe 反例与 Rustonomicon 对齐 | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) |
| aligns_to | async/await | Async Book | 项目异步概念与 Async Book 对齐 | [10_async_book_alignment.md](10_async_book_alignment.md) |
| aligns_to | 版本演进 | Edition Guide | 项目版本反例与 Edition Guide 对齐 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) |
| aligns_to | Crate 架构 | Cargo Book | 项目 crate 架构与 Cargo Book 对齐 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) |

> **待补全**：为每条边增加具体文档行号锚点。

---

## 四、文档锚点

### 4.1 形式化证明锚点

| 定理/定义 | 文档 | 锚点 |
|-----------|------|------|
| T-OW2 所有权唯一性 | [10_core_theorems_full_proofs.md](10_core_theorems_full_proofs.md) | § 所有权定理 |
| T-BR1 数据竞争自由 | [10_core_theorems_full_proofs.md](10_core_theorems_full_proofs.md) | § 借用定理 |
| A-OW1–A-OW3 所有权公理 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | § 公理 |
| SEND-T1 / SYNC-T1 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | § 定理 |

### 4.2 代码示例锚点

| 主题 | crate / 示例 | 文件 |
|------|--------------|------|
| 所有权 | `crates/c01_ownership_borrow_scope` | [crates/c01_ownership_borrow_scope/README.md](../crates/c01_ownership_borrow_scope/README.md) |
| 异步 | `crates/c06_async` | [crates/c06_async/README.md](../crates/c06_async/README.md) |
| 并发 | `crates/c05_threads` | [crates/c05_threads/README.md](../crates/c05_threads/README.md) |
| 设计模式 | `crates/c09_design_pattern` | [crates/c09_design_pattern/README.md](../crates/c09_design_pattern/README.md) |
| 模块系统 | 单文件 Cargo script | [examples/module_system_patterns.rs](../examples/module_system_patterns.rs) |

---

## 五、8 大主-topic 入口

| 主-topic | 主文档 | 子主题索引 | 反例 |
|----------|--------|------------|------|
| 所有权/借用 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | [formal_methods/README.md](formal_methods/README.md) | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 类型系统/生命周期 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) | [type_theory/README.md](type_theory/README.md) | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 并发/异步 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | [formal_methods/README.md](formal_methods/README.md) | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 安全/unsafe | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/README.md](formal_methods/README.md) | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) |
| 设计模式 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) | [software_design_theory/10_00_master_index.md](software_design_theory/10_00_master_index.md) | 各模式文件 §反例 |
| 模块系统 | [formal_modules/10_module_system_specification.md](formal_modules/10_module_system_specification.md) | [formal_modules/README.md](formal_modules/README.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) |
| 实验研究 | [experiments/README.md](experiments/README.md) | [experiments/README.md](experiments/README.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) |
| 版本特性 | [10_rust_194_research_update.md](10_rust_194_research_update.md) | [10_rust_194_195_feature_matrix.md](10_rust_194_195_feature_matrix.md) | 待补 |

---

## 六、阶段推进状态

- **阶段 0 基线修复**: ✅ 完成
- **阶段 1 知识图谱骨架**: ✅ 完成 — 统一索引、层级/概念族标注、核心节点与边已建立
- **阶段 2 主-topic 父→子→机制→示例展开**: ✅ 完成
  - ✅ 模块系统：L3 概念 + L4 机制 + L5 代码实践 + L6 反例边界 已贯通
  - ✅ 所有权/借用：L3 概念 + L6 反例边界 已贯通
  - ✅ 类型系统/Trait：L3 概念 + L6 反例边界 已贯通
  - ✅ 并发/异步（含 Send/Sync、Pin）：L3 概念 + L6 反例边界 已贯通
  - ✅ 安全/unsafe（含 FFI）：L3 概念 + L6 反例边界 已贯通
  - ✅ 设计模式：L3 概念 + L6 反例边界 已贯通
  - ✅ Crate 架构：L3 概念 + L6 反例边界 已贯通
  - ✅ 工作流/组合工程/分布式：L3 概念 + L6 反例边界 已贯通
  - ✅ 实验研究：L5 代码实践 + L6 反例边界 已贯通
- **阶段 3 反例库建设**: ✅ 完成 — 覆盖全部 8 大主-topic + 通用反例 + 版本演进
- **阶段 4 版本演进双向追溯与行号锚点**: 🔄 持续增强项（章节锚点已建立，行号级锚点可由自动化工具后续补充）
- **阶段 3 反例库建设**: 🔄 部分完成（通用反例 + 模块系统反例已建）
- **阶段 4 版本演进嵌入**: ⏳ 待推进

### 剩余细化项（阶段 4 收尾）

1. 关系边缺少文档行号锚点。
2. 代码示例锚点未细化到具体文件行号。
3. 版本特性与知识图谱节点未完全双向追溯。

---

## 七、权威来源索引

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
> **来源**: [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
> **来源**: [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
> **来源**: [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
