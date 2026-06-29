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
  - [三、关系类型与符号对照](#三关系类型与符号对照)
  - [四、关系边](#四关系边)
  - [五、文档锚点](#五文档锚点)
    - [4.1 形式化证明锚点](#41-形式化证明锚点)
    - [4.2 代码示例锚点](#42-代码示例锚点)
  - [六、8 大主-topic 入口](#六8-大主-topic-入口)
  - [七、阶段推进状态](#七阶段推进状态)
    - [剩余细化项（阶段 4 收尾）](#剩余细化项阶段-4-收尾)
  - [八、权威来源索引](#八权威来源索引)
  - [社区权威参考](#社区权威参考)

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
| Redis / redis-rs | Crate 架构 / 缓存 / 消息 / 分布式协调 | L3-L5 | [software_design_theory/07_crate_architectures/22_redis_architecture.md](software_design_theory/07_crate_architectures/22_redis_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| MongoDB / mongodb-rust-driver | Crate 架构 / 文档数据库 / NoSQL / 异步数据访问 | L3-L5 | [software_design_theory/07_crate_architectures/23_mongodb_architecture.md](software_design_theory/07_crate_architectures/23_mongodb_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| regex / regex crate | Crate 架构 / 文本处理 / 模式匹配 / 验证 | L3-L5 | [software_design_theory/07_crate_architectures/24_regex_architecture.md](software_design_theory/07_crate_architectures/24_regex_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| chrono | Crate 架构 / 日期时间 / 时区 / Duration | L3-L5 | [software_design_theory/07_crate_architectures/25_chrono_architecture.md](software_design_theory/07_crate_architectures/25_chrono_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| 微基准 | 实验研究 | L5 | [experiments/10_performance_benchmarks.md](experiments/10_performance_benchmarks.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §1-§4 |
| 并发基准 | 实验研究 | L5 | [experiments/10_concurrency_performance.md](experiments/10_concurrency_performance.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §5 |
| 内存分析 | 实验研究 | L5 | [experiments/10_memory_analysis.md](experiments/10_memory_analysis.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §6 |
| 宏展开性能 | 实验研究 | L5 | [experiments/10_macro_expansion_performance.md](experiments/10_macro_expansion_performance.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) §7 |
| Rust Reference 对齐 | 权威来源对齐 | L0-L4 | [10_rust_reference_alignment.md](10_rust_reference_alignment.md) / [10_rust_reference_chapters_alignment.md](10_rust_reference_chapters_alignment.md) | — |
| Rustonomicon 对齐 | 权威来源对齐 | L0-L6 | [10_rustonomicon_alignment.md](10_rustonomicon_alignment.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) |
| Cargo Book 对齐 | 权威来源对齐 | L0-L5 | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| Edition Guide 对齐 | 权威来源对齐 | L7 | [10_edition_guide_alignment.md](10_edition_guide_alignment.md) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) |
| Async Book 对齐 | 权威来源对齐 | L0-L6 | [10_async_book_alignment.md](10_async_book_alignment.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) |
| RFC 对齐索引 | 权威来源对齐 | L0-L7 | [10_rfc_alignment_index.md](10_rfc_alignment_index.md) | 各主题反例 |
| Ferrocene FLS 对齐 | 权威来源对齐 | L0-L4 | [10_ferrocene_fls_alignment.md](10_ferrocene_fls_alignment.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) |
| rustc-dev-guide 对齐 | 权威来源对齐 | L0-L4 | [10_rustc_dev_guide_alignment.md](10_rustc_dev_guide_alignment.md) | [formal_modules/60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) |
| Standard Library 对齐 | 权威来源对齐 | L0-L5 | [10_std_library_alignment.md](10_std_library_alignment.md) | 各主题反例 |
| 社区最佳实践对齐 | 权威来源对齐 | L0-L5 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) / [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) |
| Rust By Example 对齐 | 权威来源对齐 | L0-L5 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) | 各主题反例 |
| Unsafe Code Guidelines 对齐 | 权威来源对齐 | L0-L6 | [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) |
| Rustc 错误码对齐 | 权威来源对齐 | L6 | [10_rustc_errors_alignment.md](10_rustc_errors_alignment.md) | 各主题反例 |
| 学术论文与工具对齐 | 权威来源对齐 | L0-L4 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) |
| 验证工具实战对齐 | 权威来源对齐 | L3-L4 | [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) | [10_verification_tools_matrix.md](10_verification_tools_matrix.md) |
| RFC 深度论证链 | 权威来源对齐 / 论证 | L0-L3 | [10_rfc_argumentation_chain.md](10_rfc_argumentation_chain.md) | [10_rfc_alignment_index.md](10_rfc_alignment_index.md) |
| 国际化多语言来源 | 权威来源对齐 / i18n | L0-L1 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) | — |
| 权威来源版本跟踪 | 权威来源对齐 / 运维 | L0-L7 | [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) | — |
| RFC 实现状态追踪 | 权威来源对齐 / 版本演进 | L0-L7 | [10_rfc_tracking_status.md](10_rfc_tracking_status.md) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) |
| 设计模式权威来源对齐 | 权威来源对齐 / 设计模式 | L0-L5 | [10_design_patterns_authoritative_alignment.md](10_design_patterns_authoritative_alignment.md) | [software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md](software_design_theory/01_design_patterns_formal/60_design_patterns_counterexamples.md) |
| 异步生态权威来源对齐 | 权威来源对齐 / 异步生态 | L0-L5 | [10_async_ecosystem_alignment.md](10_async_ecosystem_alignment.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) |
| 版本演进权威来源对齐 | 权威来源对齐 / 版本演进 | L0-L7 | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) |
| 安全/unsafe 权威来源对齐 | 权威来源对齐 / 安全 / unsafe | L0-L6 | [10_safety_and_unsafe_authoritative_alignment.md](10_safety_and_unsafe_authoritative_alignment.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) |
| 工具链生态权威来源对齐 | 权威来源对齐 / 工具链 | L0-L4 | [10_toolchain_ecosystem_alignment.md](10_toolchain_ecosystem_alignment.md) | [10_cargo_book_alignment.md](10_cargo_book_alignment.md) |
| 翻译版本差异检测 | 权威来源对齐 / i18n / 运维 | L0-L1 | [10_i18n_translation_gap_analysis.md](10_i18n_translation_gap_analysis.md) | [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) |
| 行号级锚点索引 | 权威来源对齐 / 锚点 | L0-L7 | [10_authoritative_source_line_anchors.md](10_authoritative_source_line_anchors.md) | 各对齐文档 |
| RFC 到反例映射 | 权威来源对齐 / RFC / 反例 | L0-L5 | [10_rfc_to_counterexample_mapping.md](10_rfc_to_counterexample_mapping.md) | 各 `60_*_counterexamples.md` |
| 性能与测试权威来源对齐 | 权威来源对齐 / 性能 / 测试 | L0-L5 | [10_performance_and_testing_alignment.md](10_performance_and_testing_alignment.md) | [experiments/60_experiments_counterexamples.md](experiments/60_experiments_counterexamples.md) |
| 宏/FFI/嵌入式生态权威来源对齐 | 权威来源对齐 / 宏 / FFI / 嵌入式 | L0-L5 | [10_macros_ffi_embedded_alignment.md](10_macros_ffi_embedded_alignment.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) / [crates/c13_embedded/README.md](../crates/c13_embedded/README.md) |
| 学术资源对齐索引 | 权威来源对齐 / 学术资源 | L0-L6 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) |
| 错误处理与网络/Web 生态权威来源对齐 | 权威来源对齐 / 错误处理 / 网络 / Web | L0-L5 | [10_error_handling_network_web_alignment.md](10_error_handling_network_web_alignment.md) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) / [crates/c10_networks/README.md](../crates/c10_networks/README.md) |
| 数据库、存储与云原生生态权威来源对齐 | 权威来源对齐 / 数据库 / 存储 / 云原生 | L0-L5 | [10_database_storage_cloud_alignment.md](10_database_storage_cloud_alignment.md) | [crates/c10_networks/README.md](../crates/c10_networks/README.md) |
| CI/CD 与供应链安全权威来源对齐 | 权威来源对齐 / CI/CD / 供应链安全 | L0-L4 | [10_cicd_supply_chain_alignment.md](10_cicd_supply_chain_alignment.md) | [.github/workflows/ci.yml](../.github/workflows/ci.yml) |
| 权威来源缺口与反向追溯索引 | 权威来源对齐 / 缺口分析 / 反向追溯 | L0-L7 | [10_authoritative_source_gap_and_backref_index.md](10_authoritative_source_gap_and_backref_index.md) | [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md) / [10_authoritative_alignment_gap_analysis.md](10_authoritative_alignment_gap_analysis.md) |
| Crate 架构权威来源对齐 | 权威来源对齐 / Crate 架构 | L0-L5 | [10_crate_architecture_authoritative_alignment.md](10_crate_architecture_authoritative_alignment.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| 学习路径与面试题权威来源对齐 | 权威来源对齐 / 学习路径 / 面试评估 | L0-L5 | [10_learning_and_interview_alignment.md](10_learning_and_interview_alignment.md) | [10_interview_questions_collection.md](10_interview_questions_collection.md) |
| 权威来源自动补全计划 | 权威来源对齐 / 补全计划 | L0-L7 | [10_authoritative_source_completion_plan.md](10_authoritative_source_completion_plan.md) | [10_authoritative_alignment_gap_analysis.md](10_authoritative_alignment_gap_analysis.md) / [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md) |
| 权威来源对齐 / 100% 完成路线图 | 权威来源对齐 / 100% 路线图 | L0-L7 | [10_authoritative_source_100_percent_roadmap.md](10_authoritative_source_100_percent_roadmap.md) | [10_authoritative_source_completion_plan.md](10_authoritative_source_completion_plan.md) / [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md) |

> **已补充**：关键概念已建立到权威来源的行号级锚点索引，见 [10_authoritative_source_line_anchors.md](10_authoritative_source_line_anchors.md)。

---

## 三、关系类型与符号对照

> **来源**:
> [Rust Reference](https://doc.rust-lang.org/reference/) |
> [The Rust Programming Language](https://doc.rust-lang.org/book/) |
> [Rustonomicon](https://doc.rust-lang.org/nomicon/) |
> [Rust Design Patterns](https://rust-unofficial.github.io/patterns/) |
> [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
>

`10_concept_relationship_network.md` 使用符号关系（≡/⇒/⊥/∘/⊂）表达概念间语义；本知识图谱索引使用英文动词关系类型。
下表给出两套术语的统一映射，使概念网络与 KG 边可以互相转换。

| 符号 | 符号名称 | KG 关系类型 | 语义说明 | 典型场景 |
|------|----------|-------------|----------|----------|
| ≡ | 等价 | `equivalent_to` / `aligns_to` | 两概念语义可互换，或项目概念与权威来源对齐 | `Future` ≡ `async/await` |
| ⇒ | 蕴含 | `implies` | A 成立必然导致 B 成立 | 所有权 ⇒ 移动语义 |
| ⊥ | 互斥 | `contradicts` | 同一上下文中不能同时成立 | 共享借用 ⊥ 可变借用 |
| ∘ | 组合 | `composes_with` / `depends_on` | A 与 B 组合形成新概念，或 A 的实现依赖 B | `Mutex ∘ Arc` ⇒ 线程安全共享可变 |
| ⊂ | 层次/精化 | `refines` / `hierarchical` | A 是 B 的子集、特例或更精化的模型 | 移动语义 ⊂ 所有权 |

> **映射规则**：符号网络的 ∘ 在本 KG 中根据语境拆分为 `composes_with`（强调语义组合）或 `depends_on`（强调实现依赖）；⊂ 拆分为 `refines`（强调更精确建模）或 `hierarchical`（强调层次包含）。

## 四、关系边

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
| aligns_to | 安全/unsafe | Ferrocene FLS | 项目 unsafe 边界与 FLS 对齐 | [10_ferrocene_fls_alignment.md](10_ferrocene_fls_alignment.md) |
| aligns_to | 借用检查 | rustc-dev-guide | 项目借用检查与编译器实现对齐 | [10_rustc_dev_guide_alignment.md](10_rustc_dev_guide_alignment.md) |
| aligns_to | 核心类型 | Standard Library | 项目示例与 std API 对齐 | [10_std_library_alignment.md](10_std_library_alignment.md) |
| aligns_to | 设计模式 | API Guidelines | 项目模式与社区最佳实践对齐 | [10_community_best_practices_alignment.md](10_community_best_practices_alignment.md) |
| aligns_to | 核心概念 | Rust By Example | 项目示例与官方交互式示例对齐 | [10_rust_by_example_alignment.md](10_rust_by_example_alignment.md) |
| aligns_to | unsafe | Unsafe Code Guidelines | 项目 unsafe 边界与 UCG 对齐 | [10_unsafe_code_guidelines_alignment.md](10_unsafe_code_guidelines_alignment.md) |
| aligns_to | 反例边界 | Rust Error Codes | 项目反例与 rustc 错误码对齐 | [10_rustc_errors_alignment.md](10_rustc_errors_alignment.md) |
| aligns_to | 形式化证明 | Academic Papers | 项目形式化内容与学术论文对齐 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) |
| aligns_to | 核心定理 | Verification Tools | 项目定理与可验证工具能力对齐 | [10_verification_tools_practical_alignment.md](10_verification_tools_practical_alignment.md) |
| aligns_to | 语言设计决策 | RFC Argumentation | 项目概念与 RFC 论证链对齐 | [10_rfc_argumentation_chain.md](10_rfc_argumentation_chain.md) |
| aligns_to | 项目概念 | i18n Sources | 项目术语与中/日/多语言来源对齐 | [10_i18n_source_alignment.md](10_i18n_source_alignment.md) |
| tracks | 权威来源 | Version | 权威来源版本与检查日期跟踪 | [10_authoritative_source_version_tracking.md](10_authoritative_source_version_tracking.md) |
| tracks | RFC | Implementation Status | RFC 实现状态与项目响应跟踪 | [10_rfc_tracking_status.md](10_rfc_tracking_status.md) |
| aligns_to | 设计模式 | Design Patterns | GoF/Rust 惯用法与企业级模式对齐 | [10_design_patterns_authoritative_alignment.md](10_design_patterns_authoritative_alignment.md) |
| aligns_to | 异步生态 | Async Ecosystem | tokio/async-std/smol/axum/tonic 生态对齐 | [10_async_ecosystem_alignment.md](10_async_ecosystem_alignment.md) |
| tracks | 版本演进 | Release Blog | 官方版本发布说明与关键特性映射 | [10_version_evolution_alignment.md](10_version_evolution_alignment.md) |
| aligns_to | 安全/unsafe | UCG / Rustonomicon / RustBelt | 项目安全边界与多层级权威来源对齐 | [10_safety_and_unsafe_authoritative_alignment.md](10_safety_and_unsafe_authoritative_alignment.md) |
| aligns_to | 工具链 | Rust Toolchain | rustc、rustup、Cargo、clippy、rust-analyzer 等生态对齐 | [10_toolchain_ecosystem_alignment.md](10_toolchain_ecosystem_alignment.md) |
| aligns_to | 性能/测试 | Performance/Testing Book | 项目性能优化与测试策略与 Rust Performance Book / Cargo / Miri / Sanitizer 对齐 | [10_performance_and_testing_alignment.md](10_performance_and_testing_alignment.md) |
| aligns_to | 宏/FFI/嵌入式生态 | Macros / FFI / Embedded Ecosystem | 项目宏系统、FFI、WebAssembly、嵌入式内容与多层级权威来源对齐 | [10_macros_ffi_embedded_alignment.md](10_macros_ffi_embedded_alignment.md) |
| tracks | 翻译版本 | i18n Sources | 多语言翻译与英文原版版本差异跟踪 | [10_i18n_translation_gap_analysis.md](10_i18n_translation_gap_analysis.md) |
| anchors_to | 核心概念 | Authoritative Source | 关键概念到权威来源 GitHub 行号级锚点 | [10_authoritative_source_line_anchors.md](10_authoritative_source_line_anchors.md) |
| maps_to | RFC | Counterexample | RFC 关键约束到项目反例文档映射 | [10_rfc_to_counterexample_mapping.md](10_rfc_to_counterexample_mapping.md) |
| aligns_to | 项目概念 | 学术论文 | 项目核心概念与 IEEE/ACM/arXiv/Springer 学术资源对齐 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) |
| aligns_to | 错误处理与网络/Web 生态 | Rust Book / std::result / thiserror / anyhow / eyre / tokio::net / hyper / tonic / axum / tower / HTTP/3 / WebSocket / OpenAPI | 错误处理、网络与 Web 权威来源对齐 | [10_error_handling_network_web_alignment.md](10_error_handling_network_web_alignment.md) |
| aligns_to | 数据库与存储生态 | Database / Storage / Cloud Ecosystem | 项目数据库/存储/云原生内容与官方文档、crate 生态对齐 | [10_database_storage_cloud_alignment.md](10_database_storage_cloud_alignment.md) |
| aligns_to | CI/CD 与供应链安全 | GitHub Actions / Cargo Book / Security Tools | 项目 CI/CD 与供应链安全实践与官方文档对齐 | [10_cicd_supply_chain_alignment.md](10_cicd_supply_chain_alignment.md) |
| tracks | 权威来源缺口 | P0/P1/P2 补全优先级 | 按 P0/P1/P2 跟踪权威来源缺口与项目文档映射 | [10_authoritative_source_gap_and_backref_index.md](10_authoritative_source_gap_and_backref_index.md) |
| aligns_to | Crate 架构 | Cargo Book / Reference / API Guidelines / Rust Design Patterns / crates.io | 项目 crate 架构与多层级 Crate 架构权威来源对齐 | [10_crate_architecture_authoritative_alignment.md](10_crate_architecture_authoritative_alignment.md) |
| aligns_to | 学习路径 | 官方学习资源 | 项目学习路径与 TRPL/RBE/Rustlings/std 对齐 | [10_learning_and_interview_alignment.md](10_learning_and_interview_alignment.md) |
| aligns_to | 学习路径 | 社区学习资源 | 项目学习路径与 course.rs/中文社区/Rust Japan/Exercism 对齐 | [10_learning_and_interview_alignment.md](10_learning_and_interview_alignment.md) |
| maps_to | 面试题 | 权威来源 | 面试题目到官方规范、RFC、论文的映射 | [10_learning_and_interview_alignment.md](10_learning_and_interview_alignment.md) |
| depends_on | Redis | 异步/await | Redis 异步客户端基于 Future 与 async/await 构建 | [software_design_theory/07_crate_architectures/22_redis_architecture.md](software_design_theory/07_crate_architectures/22_redis_architecture.md) |
| depends_on | Redis | 并发安全 | MultiplexedConnection 的 Clone + Send 依赖 Send/Sync 保证 | [software_design_theory/07_crate_architectures/22_redis_architecture.md](software_design_theory/07_crate_architectures/22_redis_architecture.md) |
| implements | Redis | 缓存 | Redis 提供键值缓存、TTL、LRU 近似淘汰 | [software_design_theory/07_crate_architectures/22_redis_architecture.md](software_design_theory/07_crate_architectures/22_redis_architecture.md) |
| implements | Redis | 分布式 | Redis 提供 Pub/Sub、Streams、分布式锁、Cluster 协调 | [software_design_theory/07_crate_architectures/22_redis_architecture.md](software_design_theory/07_crate_architectures/22_redis_architecture.md) |
| aligns_to | Redis | redis-rs docs | 项目 Redis 概念与 redis-rs 官方文档对齐 | [software_design_theory/07_crate_architectures/22_redis_architecture.md](software_design_theory/07_crate_architectures/22_redis_architecture.md) |
| refines | MongoDB | NoSQL | MongoDB 是文档型 NoSQL 数据库的典型实现 | [software_design_theory/07_crate_architectures/23_mongodb_architecture.md](software_design_theory/07_crate_architectures/23_mongodb_architecture.md) |
| refines | MongoDB | 文档数据库 | MongoDB 以 BSON 文档为数据模型 | [software_design_theory/07_crate_architectures/23_mongodb_architecture.md](software_design_theory/07_crate_architectures/23_mongodb_architecture.md) |
| depends_on | MongoDB | 异步/await | mongodb-rust-driver 基于 Tokio 与 async/await 构建 | [software_design_theory/07_crate_architectures/23_mongodb_architecture.md](software_design_theory/07_crate_architectures/23_mongodb_architecture.md) |
| implements | MongoDB | 分布式 | MongoDB 副本集/分片集群提供分布式文档存储 | [software_design_theory/07_crate_architectures/23_mongodb_architecture.md](software_design_theory/07_crate_architectures/23_mongodb_architecture.md) |
| aligns_to | MongoDB | mongodb-rust-driver docs | 项目 MongoDB 概念与 mongodb-rust-driver 官方文档对齐 | [software_design_theory/07_crate_architectures/23_mongodb_architecture.md](software_design_theory/07_crate_architectures/23_mongodb_architecture.md) |
| refines | regex | 字符串处理 | 正则表达式是字符串模式匹配与提取的精化模型 | [software_design_theory/07_crate_architectures/24_regex_architecture.md](software_design_theory/07_crate_architectures/24_regex_architecture.md) |
| refines | regex | 解析 | 正则表达式可用于结构化文本的轻量级解析 | [software_design_theory/07_crate_architectures/24_regex_architecture.md](software_design_theory/07_crate_architectures/24_regex_architecture.md) |
| refines | regex | 验证 | 正则表达式是输入格式验证的常用工具 | [software_design_theory/07_crate_architectures/24_regex_architecture.md](software_design_theory/07_crate_architectures/24_regex_architecture.md) |
| depends_on | regex | 性能 | 正则引擎的 DFA/NFA/Hybrid 选择直接影响匹配性能 | [software_design_theory/07_crate_architectures/24_regex_architecture.md](software_design_theory/07_crate_architectures/24_regex_architecture.md) |
| aligns_to | regex | regex crate docs | 项目 regex 概念与 regex crate 官方文档对齐 | [software_design_theory/07_crate_architectures/24_regex_architecture.md](software_design_theory/07_crate_architectures/24_regex_architecture.md) |
| refines | chrono | 日期时间 | chrono 是 Rust 生态日期时间处理的典型实现 | [software_design_theory/07_crate_architectures/25_chrono_architecture.md](software_design_theory/07_crate_architectures/25_chrono_architecture.md) |
| refines | chrono | 时区 | chrono 通过 TimeZone trait 类型化时区抽象 | [software_design_theory/07_crate_architectures/25_chrono_architecture.md](software_design_theory/07_crate_architectures/25_chrono_architecture.md) |
| depends_on | chrono | 时间 / Duration | chrono Duration 与 DateTime 运算依赖时间语义 | [software_design_theory/07_crate_architectures/25_chrono_architecture.md](software_design_theory/07_crate_architectures/25_chrono_architecture.md) |
| depends_on | chrono | 异步调度 | 异步超时、定时任务常依赖 chrono 计算时间点 | [software_design_theory/07_crate_architectures/25_chrono_architecture.md](software_design_theory/07_crate_architectures/25_chrono_architecture.md) |
| aligns_to | chrono | chrono docs | 项目 chrono 概念与 chrono 官方文档对齐 | [software_design_theory/07_crate_architectures/25_chrono_architecture.md](software_design_theory/07_crate_architectures/25_chrono_architecture.md) |
| depends_on | 权威来源自动补全计划 | 权威来源缺口分析 | 补全计划基于缺口分析结果制定优先级 | [10_authoritative_source_completion_plan.md](10_authoritative_source_completion_plan.md) |
| refines | 权威来源自动补全计划 | 覆盖率提升路径 | 为 P0/P1/P2 缺口提供推荐权威来源与优先级 | [10_authoritative_source_completion_plan.md](10_authoritative_source_completion_plan.md) |
| implements | 权威来源对齐 / 100% 完成路线图 | 覆盖率提升路径 | 将补全计划落实为 P0/P1/P2 100% 覆盖的冲刺阶段与质量门禁 | [10_authoritative_source_100_percent_roadmap.md](10_authoritative_source_100_percent_roadmap.md) |
| tracks | 权威来源对齐 / 100% 完成路线图 | 权威来源对齐网络 | 跟踪 P0/P1/P2 覆盖率与 12 项自动化检查状态 | [10_authoritative_source_100_percent_roadmap.md](10_authoritative_source_100_percent_roadmap.md) |

| depends_on | 生命周期 | 所有权 | 生命周期语义建立在所有权规则之上；引用的有效性取决于被引用值的所有权 | [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) / P0: [Rust Reference – Lifetime elision](https://doc.rust-lang.org/reference/lifetime-elision.html) |
| depends_on | Pin | Future | `Future::poll` 要求 `Pin<&mut Self>`，Pin 是 Future 安全自引用的实现依赖 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) / P0: [Async Book – Pinning](https://rust-lang.github.io/async-book/04_pinning/01_chapter.html) |
| depends_on | unsafe | 借用/所有权 | `unsafe` 块绕过借用检查器，其正确性依赖对所有权/借用规则的手工维护 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) / P0: [Rustonomicon – Meet Safe and Unsafe](https://doc.rust-lang.org/nomicon/meet-safe-and-unsafe.html) |
| depends_on | FFI | unsafe | FFI 调用必须位于 `unsafe` 块/函数中，正确性依赖 unsafe 语义 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) / P0: [Rustonomicon – FFI](https://doc.rust-lang.org/nomicon/ffi.html) |
| depends_on | 模块系统 | crate-type | `crate-type` 决定模块系统编译产物形态（bin/lib/cdylib 等） | [formal_modules/20_linkage_and_symbols.md](formal_modules/20_linkage_and_symbols.md) / P0: [Cargo Book – crate-type](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#the-crate-type-field) |
| implies | 所有权 | 移动语义 | 所有权规则默认通过移动转移资源 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) / P0: [TRPL – Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) |
| implies | 借用 | 生命周期 | 借用产生引用，引用必须携带生命周期约束 | [formal_methods/10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md) / P0: [Rust Reference – Lifetime elision](https://doc.rust-lang.org/reference/lifetime-elision.html) |
| implies | RAII | 资源管理 | RAII 将资源获取与对象生命周期绑定，是资源管理的核心惯用法 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) / P0: [TRPL – Drop](https://doc.rust-lang.org/book/ch15-03-drop.html) |
| implies | Send+Sync | 并发安全 | 类型同时满足 Send 与 Sync 时可在多线程间安全共享 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) / P0: [Rust Reference – Send/Sync](https://doc.rust-lang.org/reference/special-types-and-traits.html) |
| contradicts | Copy | Drop | 编译器禁止同时实现 Copy 与 Drop | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) / P0: [Rust Reference – Copy](https://doc.rust-lang.org/reference/special-types-and-traits.html#copy) |
| contradicts | 同一数据共享+可变借用 | 借用规则 | 同一数据的共享借用与可变借用不能共存 | [10_counter_examples_compendium.md](10_counter_examples_compendium.md) / P0: [TRPL – References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) |
| contradicts | Pin 契约违反 | 自引用安全 | 破坏 Pin 的不移动契约将导致自引用指针失效 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) / P0: [Async Book – Pin contract](https://rust-lang.github.io/async-book/04_pinning/01_chapter.html) |
| implements | Mutex | 内部可变性 | `Mutex<T>` 在共享所有权下提供内部可变性 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) / P0: [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html) |
| implements | Arc | 共享所有权 | `Arc<T>` 通过原子引用计数实现线程安全的共享所有权 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) / P0: [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html) |
| implements | Channel | 消息传递模式 | `std::sync::mpsc` 实现线程间消息传递模式 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) / P0: [TRPL – Message Passing](https://doc.rust-lang.org/book/ch16-02-message-passing.html) |
| refines | Pin | 所有权 | Pin 是对所有权模型的精化，保证特定值不被移动 | [formal_methods/10_pin_self_referential.md](formal_methods/10_pin_self_referential.md) / P1: [RustBelt – Pin reasoning](https://plv.mpi-sws.org/rustbelt/popl18/) |
| refines | core::range | 范围/迭代器 | `core::range` 模块精化了 Rust 的范围与迭代器抽象 | [10_rust_194_research_update.md](10_rust_194_research_update.md) / P0: [Rust 1.96 Release Notes – core::range](https://releases.rs/1.96.0/) |
| version_introduces | Edition 2024 | tail-expr drop order | 2024 Edition 改变尾部表达式临时值作用域/drop 顺序 | [10_rust_194_research_update.md](10_rust_194_research_update.md) / P0: [Edition Guide – Tail expression temporary scope](https://doc.rust-lang.org/edition-guide/rust-2024/temporary-tail-expr-scope.html) |
| version_introduces | 1.95 | if-let guards | Rust 1.95 稳定化 `if let` guards | [10_rust_194_research_update.md](10_rust_194_research_update.md) / P0: [Rust 1.95 Release Notes](https://releases.rs/1.95.0/) |
| version_introduces | 1.96 | core::range / assert_matches! | Rust 1.96 引入 `core::range` 模块并稳定化 `assert_matches!` | [10_rust_194_195_feature_matrix.md](10_rust_194_195_feature_matrix.md) / P0: [Rust 1.96 Release Notes](https://releases.rs/1.96.0/) |

> **待补全**：为每条边增加具体文档行号锚点。

---

## 五、文档锚点

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
| 所有权 | `crates/c01_ownership_borrow_scope` | [crates/c01_ownership_borrow_scope/README.md](../../crates/c01_ownership_borrow_scope/README.md) |
| 异步 | `crates/c06_async` | [crates/c06_async/README.md](../../crates/c06_async/README.md) |
| 并发 | `crates/c05_threads` | [crates/c05_threads/README.md](../../crates/c05_threads/README.md) |
| 设计模式 | `crates/c09_design_pattern` | [crates/c09_design_pattern/README.md](../../crates/c09_design_pattern/README.md) |
| 模块系统 | 单文件 Cargo script | [examples/module_system_patterns.rs](../../examples/module_system_patterns.rs) |
| 宏系统 | `crates/c11_macro_system` | [crates/c11_macro_system/examples/](../../crates/c11_macro_system/examples/) |
| FFI / Embedded / WASM | `crates/c12_wasm` / `crates/c13_embedded` | [crates/c12_wasm/examples/](../../crates/c12_wasm/examples/) / [crates/c13_embedded/examples/](../../crates/c13_embedded/examples/) |
| 异步/并发示例 | `crates/c06_async` / `crates/c05_threads` | [crates/c06_async/examples/](../../crates/c06_async/examples/) / [crates/c05_threads/examples/](../../crates/c05_threads/examples/) |
| Redis 示例 | `crates/c06_async` | [crates/c06_async/examples/redis_basic_kv.rs](../../crates/c06_async/examples/redis_basic_kv.rs) / [redis_pub_sub.rs](../../crates/c06_async/examples/redis_pub_sub.rs) / [redis_distributed_lock.rs](../../crates/c06_async/examples/redis_distributed_lock.rs) |
| regex 示例 | `crates/c07_process` | [crates/c07_process/examples/regex_basic_matching.rs](../../crates/c07_process/examples/regex_basic_matching.rs) / [regex_common_validation.rs](../../crates/c07_process/examples/regex_common_validation.rs) |
| chrono 示例 | `crates/c07_process` | [crates/c07_process/examples/chrono_parse_format.rs](../../crates/c07_process/examples/chrono_parse_format.rs) / [chrono_timezone_duration.rs](../../crates/c07_process/examples/chrono_timezone_duration.rs) |
| 验证工具示例 | `crates/c15_verification_tools` | [crates/c15_verification_tools/examples/](../../crates/c15_verification_tools/examples/) |
| 顶层 examples 目录 | `examples/` | [examples/](../../examples/) |
| 形式化验证工具 | `crates/c15_verification_tools` | [crates/c15_verification_tools/README.md](../../crates/c15_verification_tools/README.md) |

---

## 六、8 大主-topic 入口

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

## 七、阶段推进状态

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
2. 已建立示例文件级锚点，行号级锚点持续补充。
3. 版本特性与知识图谱节点未完全双向追溯。

---

## 八、权威来源索引

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
> **来源**: [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
> **来源**: [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
> **来源**: [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
>
## 社区权威参考

- [Rust 中文社区](https://rustcc.cn/)
- [This Week in Rust](https://this-week-in-rust.org/)
