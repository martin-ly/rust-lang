# 知识图谱索引 {#知识图谱索引}

> **EN**: Knowledge Graph Index
> **Summary**: 知识图谱索引 Knowledge Graph Index.
> **内容分级**: [核心级]
>
> **分级**: [A]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: ✅ **六层两网一库知识体系 100% 骨架与核心内容覆盖完成**（阶段 0-3 完成；阶段 4 行号级锚点作为持续增强项）
> **层级**: L1-L6
> **概念族**: 综合系统化框架 / 知识图谱
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)

---

## 📑 目录 {#目录}

- [知识图谱索引 {#知识图谱索引}](#知识图谱索引-知识图谱索引)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、图谱说明 {#一图谱说明}](#一图谱说明-一图谱说明)
  - [二、核心概念节点 {#二核心概念节点}](#二核心概念节点-二核心概念节点)
    - [L1 元概念 {#l1-元概念}](#l1-元概念-l1-元概念)
    - [L2 核心概念族 {#l2-核心概念族}](#l2-核心概念族-l2-核心概念族)
    - [L3 具体概念 {#l3-具体概念}](#l3-具体概念-l3-具体概念)
  - [三、关系类型与符号对照 {#三关系类型与符号对照}](#三关系类型与符号对照-三关系类型与符号对照)
  - [四、关系边 {#四关系边}](#四关系边-四关系边)
  - [五、文档锚点 {#五文档锚点}](#五文档锚点-五文档锚点)
    - [4.1 形式化证明锚点 {#41-形式化证明锚点}](#41-形式化证明锚点-41-形式化证明锚点)
    - [4.2 代码示例锚点 {#42-代码示例锚点}](#42-代码示例锚点-42-代码示例锚点)
  - [六、8 大主-topic 入口 {#六8-大主-topic-入口}](#六8-大主-topic-入口-六8-大主-topic-入口)
  - [七、阶段推进状态 {#七阶段推进状态}](#七阶段推进状态-七阶段推进状态)
    - [剩余细化项（阶段 4 收尾） {#剩余细化项阶段-4-收尾}](#剩余细化项阶段-4-收尾-剩余细化项阶段-4-收尾)
  - [八、权威来源索引 {#八权威来源索引}](#八权威来源索引-八权威来源索引)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、图谱说明 {#一图谱说明}

本文档是 `docs/research_notes/` 的**知识图谱物理锚点**，以“六层两网一库”框架组织：

- **节点**：L0–L7 各层的概念、定理、示例、反例、版本。
- **边**：概念之间的依赖、蕴含、精化、实现、反例违反、版本引入等关系。
- **锚点**：每个节点/边指向具体的文档和代码位置。

> **使用方式**：从本索引出发，可按层级、主题、关系类型导航到具体文档。

---

## 二、核心概念节点 {#二核心概念节点}

### L1 元概念 {#l1-元概念}

| 节点 | 说明 | 主文档 |
|------|------|--------|
| 资源管理 | 所有权、借用、生命周期共同解决的核心问题 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) |
| 类型安全 | 编译期保证程序行为的类型系统目标 | [type_theory/10_type_system_foundations.md](type_theory/10_type_system_foundations.md) |
| 并发安全 | 多线程/异步执行中的数据竞争自由 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) |
| 内存安全 | 无 UB、无悬垂指针、无数据竞争 | [10_safe_unsafe_comprehensive_analysis.md](10_safe_unsafe_comprehensive_analysis.md) |
| 抽象能力 | 泛型、Trait、模块、宏等组合抽象机制 | [type_theory/10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md) |
| 权威来源对齐 | 项目概念与国际化权威来源的映射与追溯 | [10_authoritative_source_alignment_network.md](10_authoritative_source_alignment_network.md) |

### L2 核心概念族 {#l2-核心概念族}

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
| 算法练习 | L2-L4 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) | [exercises/src/algorithms/](../../exercises/src/algorithms/) |

### L3 具体概念 {#l3-具体概念}

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
| 裸指针 | unsafe / 内存 | L3 | [10_safe_unsafe_comprehensive_analysis.md](./10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §1-§2 |
| `unsafe impl` | unsafe / 并发 | L3 | [10_safe_unsafe_comprehensive_analysis.md](./10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §5 |
| `transmute` | unsafe / 类型 | L3 | [10_safe_unsafe_comprehensive_analysis.md](./10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §7 |
| FFI 内存协议 | unsafe / FFI | L3 | [10_safe_unsafe_comprehensive_analysis.md](./10_safe_unsafe_comprehensive_analysis.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §6 |
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
| 配置管理 | 组合工程 | L3-L5 | [software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md](software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md) | [software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md](software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md) §反例边界 |
| 分布式 ID | 分布式 | L3 | [software_design_theory/05_distributed/README.md](software_design_theory/05_distributed/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §4 |
| Actor 消息顺序 | 分布式 | L3 | [software_design_theory/05_distributed/README.md](software_design_theory/05_distributed/README.md) | [software_design_theory/60_workflow_compositional_distributed_counterexamples.md](software_design_theory/60_workflow_compositional_distributed_counterexamples.md) §6 |
| Fallback / Degrade | 分布式 | L4-L6 | [software_design_theory/05_distributed/08_fallback_pattern.md](software_design_theory/05_distributed/08_fallback_pattern.md) | [software_design_theory/05_distributed/08_fallback_pattern.md](software_design_theory/05_distributed/08_fallback_pattern.md) §四反例边界 |
| 限流（Rate Limiting） | 分布式 | L4-L6 | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) §5 反例边界 |
| 幂等（Idempotency） | 分布式 | L4-L6 | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) §5 反例边界 |
| Token Bucket | 限流算法 | L4 | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) §4 Rust 实现示例 |
| Sliding Window | 限流算法 | L4 | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) | [software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md](software_design_theory/05_distributed/09_rate_limiting_idempotency_pattern.md) §4 Rust 实现示例 |
| Redis / redis-rs | Crate 架构 / 缓存 / 消息 / 分布式协调 | L3-L5 | [software_design_theory/07_crate_architectures/22_redis_architecture.md](software_design_theory/07_crate_architectures/22_redis_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| MongoDB / mongodb-rust-driver | Crate 架构 / 文档数据库 / NoSQL / 异步数据访问 | L3-L5 | [software_design_theory/07_crate_architectures/23_mongodb_architecture.md](software_design_theory/07_crate_architectures/23_mongodb_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| regex / regex crate | Crate 架构 / 文本处理 / 模式匹配 / 验证 | L3-L5 | [software_design_theory/07_crate_architectures/24_regex_architecture.md](software_design_theory/07_crate_architectures/24_regex_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| chrono | Crate 架构 / 日期时间 / 时区 / Duration | L3-L5 | [software_design_theory/07_crate_architectures/25_chrono_architecture.md](software_design_theory/07_crate_architectures/25_chrono_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| Kafka / rdkafka | Crate 架构 / 消息队列 / 流处理 / 分布式 / 异步 | L3-L5 | [software_design_theory/07_crate_architectures/26_kafka_architecture.md](software_design_theory/07_crate_architectures/26_kafka_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| kube-rs / Kubernetes | Crate 架构 / 云原生 / Kubernetes / 分布式 / 异步 / 控制器模式 | L3-L5 | [software_design_theory/07_crate_architectures/27_kube_rs_architecture.md](software_design_theory/07_crate_architectures/27_kube_rs_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| lapin / RabbitMQ | Crate 架构 / 消息队列 / AMQP / 异步 / 分布式 | L3-L5 | [software_design_theory/07_crate_architectures/28_lapin_architecture.md](software_design_theory/07_crate_architectures/28_lapin_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| Meilisearch / meilisearch-sdk | Crate 架构 / 全文搜索 / 搜索引擎 / 异步 | L3-L5 | [software_design_theory/07_crate_architectures/30_meilisearch_architecture.md](software_design_theory/07_crate_architectures/30_meilisearch_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| SurrealDB / surrealdb | Crate 架构 / 文档-图数据库 / 异步数据访问 | L3-L5 | [software_design_theory/07_crate_architectures/31_surrealdb_architecture.md](software_design_theory/07_crate_architectures/31_surrealdb_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| vector / vector crate | Crate 架构 / 向量搜索 / ANN | L3-L5 | [software_design_theory/07_crate_architectures/32_vector_architecture.md](software_design_theory/07_crate_architectures/32_vector_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| sentry / sentry-rust | Crate 架构 / 错误追踪 / 可观测性 | L3-L5 | [software_design_theory/07_crate_architectures/33_sentry_architecture.md](software_design_theory/07_crate_architectures/33_sentry_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| metrics / metrics-rs | Crate 架构 / 指标 / Prometheus / 可观测性 | L3-L5 | [software_design_theory/07_crate_architectures/34_metrics_architecture.md](software_design_theory/07_crate_architectures/34_metrics_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| ort / onnxruntime-rs | Crate 架构 / AI 推理 / ONNX Runtime / FFI 绑定 | L3-L5 | [software_design_theory/07_crate_architectures/35_ort_architecture.md](software_design_theory/07_crate_architectures/35_ort_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| tract / tract-onnx | Crate 架构 / AI 推理 / 纯 Rust ONNX 引擎 | L3-L5 | [software_design_theory/07_crate_architectures/36_tract_architecture.md](software_design_theory/07_crate_architectures/36_tract_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| aws-sdk-rust | Crate 架构 / 云计算 / AWS SDK / 异步 HTTP | L3-L5 | [software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md](software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| azure-sdk-rust | Crate 架构 / 云计算 / Azure SDK / TokenCredential | L3-L5 | [software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md](software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| Salvo | Crate 架构 / Web 框架 / 异步 / HTTP | L3-L5 | [software_design_theory/07_crate_architectures/39_salvo_architecture.md](software_design_theory/07_crate_architectures/39_salvo_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| ntex | Crate 架构 / Web 框架 / 可组合网络服务 / 异步 | L3-L5 | [software_design_theory/07_crate_architectures/40_ntex_architecture.md](software_design_theory/07_crate_architectures/40_ntex_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| Askama | Crate 架构 / 模板引擎 / HTML 渲染 / 编译期生成 | L3-L5 | [software_design_theory/07_crate_architectures/41_askama_architecture.md](software_design_theory/07_crate_architectures/41_askama_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| Maud | Crate 架构 / 模板引擎 / HTML DSL / 过程宏 | L3-L5 | [software_design_theory/07_crate_architectures/42_maud_architecture.md](software_design_theory/07_crate_architectures/42_maud_architecture.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| GUI / 跨平台 UI | Crate 架构 / GUI / 跨平台 UI / 桌面 / Web / 原生 | L3-L5 | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) §4 |
| LRU/LFU/ARC/CLOCK/W-TinyLFU | 算法 / 缓存策略 | L3-L5 | [10_cache_eviction_policies_guide.md](10_cache_eviction_policies_guide.md) | [10_cache_eviction_policies_guide.md](10_cache_eviction_policies_guide.md) §反例边界 |
| Treiber Stack | 并发安全 / 无锁数据结构 | L4-L5 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) §七反例边界 |
| Michael-Scott Queue | 并发安全 / 无锁数据结构 | L4-L5 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) §七反例边界 |
| Hazard Pointer / EBR | 并发安全 / 内存回收 | L4-L6 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) §七反例边界 |
| ABA 问题 | 并发安全 / 无锁数据结构 | L5-L6 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) §七反例边界 |
| 内存序 (Acquire/Release/AcqRel) | 并发安全 / 无锁数据结构 | L4-L5 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) |
| 排序算法 | 算法练习 | L2-L3 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) | [exercises/src/algorithms/sorting.rs](../../exercises/src/algorithms/sorting.rs) |
| 搜索算法 | 算法练习 | L2-L3 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) | [exercises/src/algorithms/searching.rs](../../exercises/src/algorithms/searching.rs) |
| 图论算法 | 算法练习 | L3-L4 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) | [exercises/src/algorithms/graph.rs](../../exercises/src/algorithms/graph.rs) |
| 动态规划 | 算法练习 | L3-L4 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) | [exercises/src/algorithms/dynamic_programming.rs](../../exercises/src/algorithms/dynamic_programming.rs) |
| 经典数据结构 | 算法练习 | L2-L4 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) | [exercises/src/algorithms/data_structures.rs](../../exercises/src/algorithms/data_structures.rs) |
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
| 宏/FFI/嵌入式生态权威来源对齐 | 权威来源对齐 / 宏 / FFI / 嵌入式 | L0-L5 | [10_macros_ffi_embedded_alignment.md](10_macros_ffi_embedded_alignment.md) | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) / [crates/c13_embedded/README.md](../../crates/c13_embedded/README.md) |
| 学术资源对齐索引 | 权威来源对齐 / 学术资源 | L0-L6 | [10_academic_papers_alignment.md](10_academic_papers_alignment.md) | [10_international_formal_verification_index.md](10_international_formal_verification_index.md) |
| 错误处理与网络/Web 生态权威来源对齐 | 权威来源对齐 / 错误处理 / 网络 / Web | L0-L5 | [10_error_handling_network_web_alignment.md](10_error_handling_network_web_alignment.md) | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) / [crates/c10_networks/README.md](../../crates/c10_networks/README.md) |
| 数据库、存储与云原生生态权威来源对齐 | 权威来源对齐 / 数据库 / 存储 / 云原生 | L0-L5 | [10_database_storage_cloud_alignment.md](10_database_storage_cloud_alignment.md) | [crates/c10_networks/README.md](../../crates/c10_networks/README.md) |
| CI/CD 与供应链安全权威来源对齐 | 权威来源对齐 / CI/CD / 供应链安全 | L0-L4 | [10_cicd_supply_chain_alignment.md](10_cicd_supply_chain_alignment.md) | [.github/workflows/ci.yml](../../.github/workflows/ci.yml) |
| 权威来源缺口与反向追溯索引 | 权威来源对齐 / 缺口分析 / 反向追溯 | L0-L7 | [10_authoritative_source_gap_and_backref_index.md](10_authoritative_source_gap_and_backref_index.md) | [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md) / [10_authoritative_alignment_gap_analysis.md](10_authoritative_alignment_gap_analysis.md) |
| Crate 架构权威来源对齐 | 权威来源对齐 / Crate 架构 | L0-L5 | [10_crate_architecture_authoritative_alignment.md](10_crate_architecture_authoritative_alignment.md) | [software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md](software_design_theory/07_crate_architectures/60_crate_architecture_counterexamples.md) |
| 学习路径与面试题权威来源对齐 | 权威来源对齐 / 学习路径 / 面试评估 | L0-L5 | [10_learning_and_interview_alignment.md](10_learning_and_interview_alignment.md) | [10_interview_questions_collection.md](10_interview_questions_collection.md) |
| 权威来源自动补全计划 | 权威来源对齐 / 补全计划 | L0-L7 | [10_authoritative_source_completion_plan.md](10_authoritative_source_completion_plan.md) | [10_authoritative_alignment_gap_analysis.md](10_authoritative_alignment_gap_analysis.md) / [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md) |
| 权威来源对齐 / 100% 完成路线图 | 权威来源对齐 / 100% 路线图 | L0-L7 | [10_authoritative_source_100_percent_roadmap.md](10_authoritative_source_100_percent_roadmap.md) | [10_authoritative_source_completion_plan.md](10_authoritative_source_completion_plan.md) / [10_authoritative_alignment_gap_matrix.md](10_authoritative_alignment_gap_matrix.md) |

> **已补充**：关键概念已建立到权威来源的行号级锚点索引，见 [10_authoritative_source_line_anchors.md](10_authoritative_source_line_anchors.md)。

---

## 三、关系类型与符号对照 {#三关系类型与符号对照}

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

## 四、关系边 {#四关系边}

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
| refines | Kafka | 消息队列 | Kafka 是基于发布-订阅模型的分布式消息队列实现 | [software_design_theory/07_crate_architectures/26_kafka_architecture.md](software_design_theory/07_crate_architectures/26_kafka_architecture.md) |
| refines | Kafka | 流处理 | Kafka Consumer Group / Partition 语义支撑流式处理 | [software_design_theory/07_crate_architectures/26_kafka_architecture.md](software_design_theory/07_crate_architectures/26_kafka_architecture.md) |
| depends_on | Kafka | 异步/await | rdkafka FutureProducer / StreamConsumer 基于 async/await 构建 | [software_design_theory/07_crate_architectures/26_kafka_architecture.md](software_design_theory/07_crate_architectures/26_kafka_architecture.md) |
| implements | Kafka | 分布式 | Kafka 通过 Partition / Replica / Consumer Group 提供分布式日志与协调 | [software_design_theory/07_crate_architectures/26_kafka_architecture.md](software_design_theory/07_crate_architectures/26_kafka_architecture.md) |
| aligns_to | Kafka | rdkafka docs | 项目 Kafka 概念与 rdkafka 官方文档对齐 | [software_design_theory/07_crate_architectures/26_kafka_architecture.md](software_design_theory/07_crate_architectures/26_kafka_architecture.md) |
| refines | kube-rs | 云原生 | kube-rs 是 Rust 生态 Kubernetes 云原生编程模型的典型实现 | [software_design_theory/07_crate_architectures/27_kube_rs_architecture.md](software_design_theory/07_crate_architectures/27_kube_rs_architecture.md) |
| refines | kube-rs | Kubernetes | kube-rs 封装 Kubernetes API 与控制器模式 | [software_design_theory/07_crate_architectures/27_kube_rs_architecture.md](software_design_theory/07_crate_architectures/27_kube_rs_architecture.md) |
| depends_on | kube-rs | 异步/await | kube-rs Client / watcher / Controller 基于 Tokio 与 async/await 构建 | [software_design_theory/07_crate_architectures/27_kube_rs_architecture.md](software_design_theory/07_crate_architectures/27_kube_rs_architecture.md) |
| implements | kube-rs | 控制器模式 | kube-rs `Controller::new` + `reconcile` 实现 Kubernetes 控制器模式 | [software_design_theory/07_crate_architectures/27_kube_rs_architecture.md](software_design_theory/07_crate_architectures/27_kube_rs_architecture.md) |
| implements | kube-rs | 分布式 | kube-rs 通过 watcher 与 Controller 支撑分布式集群状态调谐 | [software_design_theory/07_crate_architectures/27_kube_rs_architecture.md](software_design_theory/07_crate_architectures/27_kube_rs_architecture.md) |
| aligns_to | kube-rs | kube-rs docs | 项目 kube-rs 概念与 kube-rs 官方文档对齐 | [software_design_theory/07_crate_architectures/27_kube_rs_architecture.md](software_design_theory/07_crate_architectures/27_kube_rs_architecture.md) |
| refines | lapin | 消息队列 | lapin 是 AMQP/RabbitMQ 消息队列的 Rust 实现 | [software_design_theory/07_crate_architectures/28_lapin_architecture.md](software_design_theory/07_crate_architectures/28_lapin_architecture.md) |
| refines | lapin | AMQP | lapin 基于 AMQP 0-9-1 协议与 RabbitMQ 交互 | [software_design_theory/07_crate_architectures/28_lapin_architecture.md](software_design_theory/07_crate_architectures/28_lapin_architecture.md) |
| depends_on | lapin | 异步/await | lapin Connection/Channel/Consumer 基于 async/await 构建 | [software_design_theory/07_crate_architectures/28_lapin_architecture.md](software_design_theory/07_crate_architectures/28_lapin_architecture.md) |
| implements | lapin | 分布式 | RabbitMQ 通过 exchange/queue/binding 支撑分布式消息路由 | [software_design_theory/07_crate_architectures/28_lapin_architecture.md](software_design_theory/07_crate_architectures/28_lapin_architecture.md) |
| aligns_to | lapin | lapin docs | 项目 lapin 概念与 lapin 官方文档对齐 | [software_design_theory/07_crate_architectures/28_lapin_architecture.md](software_design_theory/07_crate_architectures/28_lapin_architecture.md) |
| refines | Meilisearch | 全文搜索 | Meilisearch 是 typo-tolerant 即时搜索引擎的典型实现 | [software_design_theory/07_crate_architectures/30_meilisearch_architecture.md](software_design_theory/07_crate_architectures/30_meilisearch_architecture.md) |
| depends_on | Meilisearch | 异步/await | meilisearch-sdk 的 Client/Index/search 基于 async/await 构建 | [software_design_theory/07_crate_architectures/30_meilisearch_architecture.md](software_design_theory/07_crate_architectures/30_meilisearch_architecture.md) |
| aligns_to | Meilisearch | meilisearch-sdk docs | 项目 Meilisearch 概念与 meilisearch-sdk 官方文档对齐 | [software_design_theory/07_crate_architectures/30_meilisearch_architecture.md](software_design_theory/07_crate_architectures/30_meilisearch_architecture.md) |
| refines | SurrealDB | 文档数据库 | SurrealDB 支持文档模型与 SurrealQL 查询 | [software_design_theory/07_crate_architectures/31_surrealdb_architecture.md](software_design_theory/07_crate_architectures/31_surrealdb_architecture.md) |
| refines | SurrealDB | 图数据库 | SurrealDB 支持图遍历与关系记录 ID | [software_design_theory/07_crate_architectures/31_surrealdb_architecture.md](software_design_theory/07_crate_architectures/31_surrealdb_architecture.md) |
| depends_on | SurrealDB | 异步/await | surrealdb 远程 WebSocket/HTTP 引擎基于 async/await 构建 | [software_design_theory/07_crate_architectures/31_surrealdb_architecture.md](software_design_theory/07_crate_architectures/31_surrealdb_architecture.md) |
| aligns_to | SurrealDB | surrealdb docs | 项目 SurrealDB 概念与 surrealdb 官方文档对齐 | [software_design_theory/07_crate_architectures/31_surrealdb_architecture.md](software_design_theory/07_crate_architectures/31_surrealdb_architecture.md) |
| refines | vector | 向量搜索 | vector crate 是内存 HNSW 近似最近邻搜索的实现 | [software_design_theory/07_crate_architectures/32_vector_architecture.md](software_design_theory/07_crate_architectures/32_vector_architecture.md) |
| depends_on | vector | 数值计算 | 向量索引与距离计算依赖线性代数/数值计算基础 | [software_design_theory/07_crate_architectures/32_vector_architecture.md](software_design_theory/07_crate_architectures/32_vector_architecture.md) |
| aligns_to | vector | vector docs | 项目 vector 概念与 vector crate 官方文档对齐 | [software_design_theory/07_crate_architectures/32_vector_architecture.md](software_design_theory/07_crate_architectures/32_vector_architecture.md) |
| refines | sentry | 可观测性 | sentry 是错误追踪、崩溃报告与性能监控的可观测性实现 | [software_design_theory/07_crate_architectures/33_sentry_architecture.md](software_design_theory/07_crate_architectures/33_sentry_architecture.md) |
| depends_on | sentry | 异步/await | sentry 的 Hub/Scope/Transaction 与异步任务上下文绑定 | [software_design_theory/07_crate_architectures/33_sentry_architecture.md](software_design_theory/07_crate_architectures/33_sentry_architecture.md) |
| implements | sentry | 错误追踪 | sentry 捕获 panic、error、message 并上报 Sentry 服务 | [software_design_theory/07_crate_architectures/33_sentry_architecture.md](software_design_theory/07_crate_architectures/33_sentry_architecture.md) |
| aligns_to | sentry | sentry docs | 项目 sentry 概念与 sentry-rust 官方文档对齐 | [software_design_theory/07_crate_architectures/33_sentry_architecture.md](software_design_theory/07_crate_architectures/33_sentry_architecture.md) |
| refines | metrics | 可观测性 | metrics crate 是 Rust 指标 facade 与 Prometheus 导出的实现 | [software_design_theory/07_crate_architectures/34_metrics_architecture.md](software_design_theory/07_crate_architectures/34_metrics_architecture.md) |
| implements | metrics | 指标收集 | metrics 提供 counter/gauge/histogram 三类指标记录 | [software_design_theory/07_crate_architectures/34_metrics_architecture.md](software_design_theory/07_crate_architectures/34_metrics_architecture.md) |
| depends_on | metrics | 异步/调度 | Prometheus exporter 的 HTTP listener 与 upkeep 任务依赖 Tokio | [software_design_theory/07_crate_architectures/34_metrics_architecture.md](software_design_theory/07_crate_architectures/34_metrics_architecture.md) |
| aligns_to | metrics | metrics docs | 项目 metrics 概念与 metrics-rs 官方文档对齐 | [software_design_theory/07_crate_architectures/34_metrics_architecture.md](software_design_theory/07_crate_architectures/34_metrics_architecture.md) |
| refines | ort | AI 推理 | ort 是 ONNX Runtime C++ 运行时的安全 Rust 绑定 | [software_design_theory/07_crate_architectures/35_ort_architecture.md](software_design_theory/07_crate_architectures/35_ort_architecture.md) |
| depends_on | ort | 类型系统 | Tensor<T> 元素类型与形状在编译期受 Rust 类型系统约束 | [software_design_theory/07_crate_architectures/35_ort_architecture.md](software_design_theory/07_crate_architectures/35_ort_architecture.md) |
| depends_on | ort | FFI | ort 通过 FFI 调用 ONNX Runtime 动态库 | [software_design_theory/07_crate_architectures/35_ort_architecture.md](software_design_theory/07_crate_architectures/35_ort_architecture.md) |
| aligns_to | ort | ort docs | 项目 ort 概念与 pykeio/ort 官方文档对齐 | [software_design_theory/07_crate_architectures/35_ort_architecture.md](software_design_theory/07_crate_architectures/35_ort_architecture.md) |
| refines | tract | AI 推理 | tract 是纯 Rust ONNX/TensorFlow 推理引擎 | [software_design_theory/07_crate_architectures/36_tract_architecture.md](software_design_theory/07_crate_architectures/36_tract_architecture.md) |
| depends_on | tract | 类型系统 | TypedModel 利用类型化事实进行维度推导 | [software_design_theory/07_crate_architectures/36_tract_architecture.md](software_design_theory/07_crate_architectures/36_tract_architecture.md) |
| depends_on | tract | 数值计算 | tract 张量运算依赖底层数值计算内核 | [software_design_theory/07_crate_architectures/36_tract_architecture.md](software_design_theory/07_crate_architectures/36_tract_architecture.md) |
| aligns_to | tract | tract docs | 项目 tract 概念与 snipsco/tract 官方文档对齐 | [software_design_theory/07_crate_architectures/36_tract_architecture.md](software_design_theory/07_crate_architectures/36_tract_architecture.md) |
| refines | aws-sdk-rust | 云计算 | aws-sdk-rust 是 AWS 云服务的类型化 Rust 客户端 | [software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md](software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md) |
| depends_on | aws-sdk-rust | 异步/await | AWS SDK 客户端基于 Tokio 与 async/await 构建 | [software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md](software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md) |
| implements | aws-sdk-rust | 服务层 | Smithy 生成代码实现按服务分 crate 的服务层模式 | [software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md](software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md) |
| aligns_to | aws-sdk-rust | AWS docs | 项目 AWS SDK 概念与 awslabs/aws-sdk-rust 官方文档对齐 | [software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md](software_design_theory/07_crate_architectures/37_aws_sdk_architecture.md) |
| refines | azure-sdk-rust | 云计算 | azure-sdk-rust 是 Azure 云服务的类型化 Rust 客户端 | [software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md](software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md) |
| depends_on | azure-sdk-rust | 异步/await | Azure SDK 客户端基于 Tokio 与 async/await 构建 | [software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md](software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md) |
| depends_on | azure-sdk-rust | TokenCredential | BlobServiceClient 通过 TokenCredential 抽象统一认证 | [software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md](software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md) |
| aligns_to | azure-sdk-rust | Azure docs | 项目 Azure SDK 概念与 Azure/azure-sdk-for-rust 官方文档对齐 | [software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md](software_design_theory/07_crate_architectures/38_azure_sdk_architecture.md) |
| refines | Salvo | Web 框架 | Salvo 是基于 Hyper/Tokio 的二线 Web 框架实现 | [software_design_theory/07_crate_architectures/39_salvo_architecture.md](software_design_theory/07_crate_architectures/39_salvo_architecture.md) |
| depends_on | Salvo | 异步/await | Salvo Handler 与 Server 基于 Tokio 与 async/await 构建 | [software_design_theory/07_crate_architectures/39_salvo_architecture.md](software_design_theory/07_crate_architectures/39_salvo_architecture.md) |
| depends_on | Salvo | Hyper | Salvo 复用 Hyper 进行 HTTP 协议解析 | [software_design_theory/07_crate_architectures/39_salvo_architecture.md](software_design_theory/07_crate_architectures/39_salvo_architecture.md) |
| refines | ntex | Web 框架 | ntex 是自研 HTTP 协议栈的二线 Web 框架实现 | [software_design_theory/07_crate_architectures/40_ntex_architecture.md](software_design_theory/07_crate_architectures/40_ntex_architecture.md) |
| depends_on | ntex | 异步/await | ntex App / HttpServer 基于 async/await 与 Service trait 构建 | [software_design_theory/07_crate_architectures/40_ntex_architecture.md](software_design_theory/07_crate_architectures/40_ntex_architecture.md) |
| refines | Askama | 模板引擎 | Askama 是编译期 Jinja-like 模板引擎 | [software_design_theory/07_crate_architectures/41_askama_architecture.md](software_design_theory/07_crate_architectures/41_askama_architecture.md) |
| implements | Askama | HTML 渲染 | Askama 通过编译期代码生成渲染 HTML | [software_design_theory/07_crate_architectures/41_askama_architecture.md](software_design_theory/07_crate_architectures/41_askama_architecture.md) |
| refines | Maud | 模板引擎 | Maud 是编译期 HTML DSL 宏模板引擎 | [software_design_theory/07_crate_architectures/42_maud_architecture.md](software_design_theory/07_crate_architectures/42_maud_architecture.md) |
| implements | Maud | HTML 渲染 | Maud 通过 `html!` 宏在编译期生成 HTML | [software_design_theory/07_crate_architectures/42_maud_architecture.md](software_design_theory/07_crate_architectures/42_maud_architecture.md) |
| refines | GUI / 跨平台 UI | 桌面应用 | Tauri / egui / iced 覆盖原生桌面 GUI 场景 | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) |
| refines | GUI / 跨平台 UI | Web 应用 | Dioxus / Leptos 覆盖 Web 与 SSR 场景 | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) |
| depends_on | GUI / 跨平台 UI | 异步/await | Tauri / Dioxus / Leptos 的命令处理与渲染循环依赖 async/await | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) |
| depends_on | GUI / 跨平台 UI | wgpu | egui / iced 的跨平台渲染依赖 wgpu | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) |
| implements | GUI / 跨平台 UI | 响应式编程 | Dioxus / Leptos 通过信号实现细粒度响应式 | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) |
| aligns_to | GUI / 跨平台 UI | Tauri / Dioxus / Leptos / egui / iced docs | 项目 GUI 概念与各框架官方文档对齐 | [software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md](software_design_theory/07_crate_architectures/29_gui_cross_platform_ui_architecture.md) |
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
| refines | 缓存淘汰策略 | 算法 / 缓存策略 | 缓存淘汰是算法在容量受限场景下的精化模型 | [10_cache_eviction_policies_guide.md](10_cache_eviction_policies_guide.md) |
| implements | CLOCK | 近似 LRU | CLOCK 用引用位近似 LRU 的最近使用顺序 | [10_cache_eviction_policies_guide.md](10_cache_eviction_policies_guide.md) |
| refines | ARC | LRU/LFU | ARC 通过 T1/T2/B1/B2 自平衡适应最近/频繁访问 | [10_cache_eviction_policies_guide.md](10_cache_eviction_policies_guide.md) |
| depends_on | W-TinyLFU | 频率 Sketch | W-TinyLFU 依赖 Count-Min Sketch / 门限过滤器做准入判断 | [10_cache_eviction_policies_guide.md](10_cache_eviction_policies_guide.md) |
| contradicts | LRU 固定容量 | LFU 长周期热点 | LRU 在扫描型负载下表现差；LFU 对新热点响应慢 | [10_cache_eviction_policies_guide.md](10_cache_eviction_policies_guide.md) |
| refines | 算法练习 | 学习资源 | 算法练习是对项目学习资源体系的精化补充 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) |
| composes_with | Fallback | 超时模式 | 超时是触发 fallback 的典型条件 | [software_design_theory/05_distributed/08_fallback_pattern.md](software_design_theory/05_distributed/08_fallback_pattern.md) / P0: [Tokio Tutorial](https://tokio.rs/tokio/tutorial) |
| composes_with | Fallback | 熔断模式 | 熔断器 Open 状态直接走 fallback 路径 | [software_design_theory/05_distributed/08_fallback_pattern.md](software_design_theory/05_distributed/08_fallback_pattern.md) |
| refines | Degrade | 分布式模式 | 降级是分布式韧性模式的精化形式 | [software_design_theory/05_distributed/08_fallback_pattern.md](software_design_theory/05_distributed/08_fallback_pattern.md) |
| depends_on | Fallback | 独立回退源 | 回退结果不能依赖主路径的失败域 | [software_design_theory/05_distributed/08_fallback_pattern.md](software_design_theory/05_distributed/08_fallback_pattern.md) |
| contradicts | Fallback 共享失败域 | 失败隔离 | fallback 仍访问主依赖会导致级联失败 | [software_design_theory/05_distributed/08_fallback_pattern.md](software_design_theory/05_distributed/08_fallback_pattern.md) §反例 1 |
| depends_on | 排序算法 | 切片 / 索引 / 递归 | 排序实现依赖 Rust 切片、索引与递归控制 | [exercises/src/algorithms/sorting.rs](../../exercises/src/algorithms/sorting.rs) / P0: [TRPL – Slices](https://doc.rust-lang.org/book/ch04-03-slices.html) |
| depends_on | 搜索算法 | 切片 / 队列 / DFS/BFS | 搜索实现依赖切片、标准库队列与图遍历模板 | [exercises/src/algorithms/searching.rs](../../exercises/src/algorithms/searching.rs) / P0: [std::collections::VecDeque](https://doc.rust-lang.org/std/collections/struct.VecDeque.html) |
| depends_on | 图论算法 | 优先队列 / 并查集 | Dijkstra 依赖 BinaryHeap；Kruskal/环检测依赖并查集 | [exercises/src/algorithms/graph.rs](../../exercises/src/algorithms/graph.rs) / P0: [std::collections::BinaryHeap](https://doc.rust-lang.org/std/collections/struct.BinaryHeap.html) |
| depends_on | 动态规划 | 迭代 / 滚动数组 | DP 实现依赖 Rust 迭代器与滚动数组空间优化 | [exercises/src/algorithms/dynamic_programming.rs](../../exercises/src/algorithms/dynamic_programming.rs) / P0: [TRPL – Iterators](https://doc.rust-lang.org/book/ch13-02-iterators.html) |
| depends_on | 经典数据结构 | 泛型 / Trait / HashMap | 数据结构实现依赖泛型、Trait 与标准库 HashMap | [exercises/src/algorithms/data_structures.rs](../../exercises/src/algorithms/data_structures.rs) / P0: [TRPL – Generic Types](https://doc.rust-lang.org/book/ch10-00-generics.html) |
| implements | LRU 缓存 | 经典数据结构 | `LruCache` 是 LRU 淘汰策略的直接实现 | [exercises/src/algorithms/data_structures.rs](../../exercises/src/algorithms/data_structures.rs) |
| implements | 前缀树 | 经典数据结构 | `Trie` 实现字符串前缀高效存储与检索 | [exercises/src/algorithms/data_structures.rs](../../exercises/src/algorithms/data_structures.rs) |
| aligns_to | 算法练习 | Rust By Example | 算法练习与官方交互式示例风格对齐 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) / P0: [Rust By Example](https://doc.rust-lang.org/rust-by-example/) |
| aligns_to | 算法练习 | CLRS / LeetCode | 算法题目与经典教材及在线判题来源对齐 | [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md) / P1: [CLRS](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/) / P2: [LeetCode](https://leetcode.com/) |
| refines | Treiber Stack | 无锁数据结构 | Treiber Stack 是无锁 LIFO 栈的经典实现 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) / P0: [Rust Atomics and Locks](https://marabos.nl/atomics/) |
| refines | Michael-Scott Queue | 无锁数据结构 | Michael-Scott Queue 是无锁 FIFO 队列的经典实现 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) / P0: [Rust Atomics and Locks](https://marabos.nl/atomics/) |
| depends_on | 无锁数据结构 | Hazard Pointer / EBR | 无锁结构的安全内存回收依赖 Hazard Pointer 或 EBR | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) / P2: [crossbeam-epoch docs](https://docs.rs/crossbeam-epoch) |
| depends_on | 无锁数据结构 | 内存序 (Acquire/Release/AcqRel) | CAS 与共享指针的可见性由内存序保证 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) / P1: [Rust Reference – Memory Model](https://doc.rust-lang.org/reference/memory-model.html) |
| depends_on | 无锁数据结构 | Send/Sync | 无锁结构跨线程共享要求类型满足 Send/Sync | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) / P0: [Rust Reference – Send/Sync](https://doc.rust-lang.org/reference/special-types-and-traits.html) |
| contradicts | 无锁数据结构 | 立即释放节点 | 弹出后立即释放节点会导致 use-after-free | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) §七反例边界 |
| contradicts | 无锁数据结构 | Relaxed 读共享指针 | Relaxed 无法保证看到完整发布的节点 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) §七反例边界 |
| implements | Hazard Pointer / EBR | 并发安全 | EBR 通过 epoch 延迟释放保证并发访问安全 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) / P2: [crossbeam-epoch docs](https://docs.rs/crossbeam-epoch) |
| aligns_to | 无锁数据结构 | Rust Atomics and Locks | 项目无锁结构与 Rust Atomics and Locks 对齐 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) / P0: [Rust Atomics and Locks](https://marabos.nl/atomics/) |
| aligns_to | Hazard Pointer / EBR | crossbeam-epoch | 项目 EBR 桥接与 crossbeam-epoch 官方文档对齐 | [10_lock_free_data_structures_guide.md](10_lock_free_data_structures_guide.md) / P2: [crossbeam-epoch docs](https://docs.rs/crossbeam-epoch) |
| refines | 配置管理 | 组合工程 | 配置管理是组合工程在运行期参数维度的精化 | [software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md](software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md) |
| depends_on | 配置管理 | Builder / 类型状态 | 类型安全配置常借助 Builder 组合来源与验证 | [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md) |
| depends_on | 配置管理 | 错误处理 | 配置解析错误需要显式处理与边界隔离 | [10_error_handling_cheatsheet.md](10_error_handling_cheatsheet.md) |
| implements | 配置管理 | 12-factor 配置原则 | 环境变量覆盖文件/默认配置符合 12-factor | [software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md](software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md) |
| aligns_to | 配置管理 | config / clap / envy / figment docs | 项目配置模式与各 crate 官方文档对齐 | [software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md](software_design_theory/04_compositional_engineering/03_configuration_management_pattern.md) |

> **待补全**：为每条边增加具体文档行号锚点。

---

## 五、文档锚点 {#五文档锚点}

### 4.1 形式化证明锚点 {#41-形式化证明锚点}

| 定理/定义 | 文档 | 锚点 |
|-----------|------|------|
| T-OW2 所有权唯一性 | [10_core_theorems_full_proofs.md](10_core_theorems_full_proofs.md) | § 所有权定理 |
| T-BR1 数据竞争自由 | [10_core_theorems_full_proofs.md](10_core_theorems_full_proofs.md) | § 借用定理 |
| A-OW1–A-OW3 所有权公理 | [formal_methods/10_ownership_model.md](formal_methods/10_ownership_model.md) | § 公理 |
| SEND-T1 / SYNC-T1 | [formal_methods/10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md) | § 定理 |

### 4.2 代码示例锚点 {#42-代码示例锚点}

| 主题 | crate / 示例 | 文件 |
|------|--------------|------|
| 所有权 | `crates/c01_ownership_borrow_scope` | [crates/c01_ownership_borrow_scope/README.md](../../crates/c01_ownership_borrow_scope/README.md) |
| 异步 | `crates/c06_async` | [crates/c06_async/README.md](../../crates/c06_async/README.md) |
| 并发 | `crates/c05_threads` | [crates/c05_threads/README.md](../../crates/c05_threads/README.md) |
| 设计模式 | `crates/c09_design_pattern` | [crates/c09_design_pattern/README.md](../../crates/c09_design_pattern/README.md) |
| 模块系统 | 单文件 Cargo script | [examples/module_system_patterns.rs](../../examples/module_system_patterns.rs) |
| 宏系统 | `crates/c11_macro_system_proc` | [crates/c11_macro_system_proc/examples/](../../crates/c11_macro_system_proc/examples/) |
| FFI / Embedded / WASM | `crates/c12_wasm` / `crates/c13_embedded` | [crates/c12_wasm/examples/](../../crates/c12_wasm/examples/) / [crates/c13_embedded/examples/](../../crates/c13_embedded/examples/) |
| 异步/并发示例 | `crates/c06_async` / `crates/c05_threads` | [crates/c06_async/examples/](../../crates/c06_async/examples/) / [crates/c05_threads/examples/](../../crates/c05_threads/examples/) |
| Fallback / Degrade 示例 | `crates/c06_async` | [crates/c06_async/examples/fallback_degrade_pattern.rs](../../crates/c06_async/examples/fallback_degrade_pattern.rs) |
| Redis 示例 | `crates/c06_async` | [crates/c06_async/examples/redis_basic_kv.rs](../../crates/c06_async/examples/redis_basic_kv.rs) / [redis_pub_sub.rs](../../crates/c06_async/examples/redis_pub_sub.rs) / [redis_distributed_lock.rs](../../crates/c06_async/examples/redis_distributed_lock.rs) |
| Kafka 示例 | `crates/c10_networks` | [crates/c10_networks/examples/kafka_async_producer.rs](../../crates/c10_networks/examples/kafka_async_producer.rs) / [kafka_consumer_group.rs](../../crates/c10_networks/examples/kafka_consumer_group.rs) |
| lapin 示例 | `crates/c10_networks` | [crates/c10_networks/examples/lapin_publisher.rs](../../crates/c10_networks/examples/lapin_publisher.rs) / [lapin_consumer.rs](../../crates/c10_networks/examples/lapin_consumer.rs) |
| Meilisearch 示例 | `crates/c10_networks` | [crates/c10_networks/examples/meilisearch_basic_search.rs](../../crates/c10_networks/examples/meilisearch_basic_search.rs) |
| SurrealDB 示例 | `crates/c10_networks` | [crates/c10_networks/examples/surrealdb_basic_crud.rs](../../crates/c10_networks/examples/surrealdb_basic_crud.rs) |
| vector 示例 | `crates/c10_networks` | [crates/c10_networks/examples/vector_hnsw_search.rs](../../crates/c10_networks/examples/vector_hnsw_search.rs) |
| sentry 示例 | `crates/c06_async` | [crates/c06_async/examples/sentry_error_capture.rs](../../crates/c06_async/examples/sentry_error_capture.rs) |
| metrics 示例 | `crates/c06_async` | [crates/c06_async/examples/metrics_basic_prometheus.rs](../../crates/c06_async/examples/metrics_basic_prometheus.rs) |
| ort 示例 | `crates/c08_algorithms` | [crates/c08_algorithms/examples/ort_basic_inference.rs](../../crates/c08_algorithms/examples/ort_basic_inference.rs) |
| tract 示例 | `crates/c08_algorithms` | [crates/c08_algorithms/examples/tract_basic_inference.rs](../../crates/c08_algorithms/examples/tract_basic_inference.rs) |
| AWS SDK 示例 | `crates/c10_networks` | [crates/c10_networks/examples/aws_sdk_list_buckets.rs](../../crates/c10_networks/examples/aws_sdk_list_buckets.rs) |
| Azure SDK 示例 | `crates/c10_networks` | [crates/c10_networks/examples/azure_blob_list_containers.rs](../../crates/c10_networks/examples/azure_blob_list_containers.rs) |
| Salvo 示例 | `crates/c06_async` | [crates/c06_async/examples/salvo_web_routing.rs](../../crates/c06_async/examples/salvo_web_routing.rs) |
| ntex 示例 | `crates/c06_async` | [crates/c06_async/examples/ntex_web_routing.rs](../../crates/c06_async/examples/ntex_web_routing.rs) |
| Askama 示例 | `crates/c06_async` | [crates/c06_async/examples/askama_template_rendering.rs](../../crates/c06_async/examples/askama_template_rendering.rs) |
| Maud 示例 | `crates/c06_async` | [crates/c06_async/examples/maud_template_rendering.rs](../../crates/c06_async/examples/maud_template_rendering.rs) |
| kube-rs 示例 | `crates/c10_networks` | [crates/c10_networks/examples/kube_list_pods.rs](../../crates/c10_networks/examples/kube_list_pods.rs) / [kube_watch_pods.rs](../../crates/c10_networks/examples/kube_watch_pods.rs) |
| regex 示例 | `crates/c07_process` | [crates/c07_process/examples/regex_basic_matching.rs](../../crates/c07_process/examples/regex_basic_matching.rs) / [regex_common_validation.rs](../../crates/c07_process/examples/regex_common_validation.rs) |
| chrono 示例 | `crates/c07_process` | [crates/c07_process/examples/chrono_parse_format.rs](../../crates/c07_process/examples/chrono_parse_format.rs) / [chrono_timezone_duration.rs](../../crates/c07_process/examples/chrono_timezone_duration.rs) |
| 验证工具示例 | `crates/c15_verification_tools` | [crates/c15_verification_tools/examples/](../../crates/c15_verification_tools/examples/) |
| GUI / 跨平台 UI 示例 | `crates/c16_gui` | [crates/c16_gui/examples/](../../crates/c16_gui/examples/) |
| 顶层 examples 目录 | `examples/` | [examples/](../../examples/) |
| 缓存淘汰策略 | `c08_algorithms` | [crates/c08_algorithms/examples/cache_eviction_policies_demo.rs](../../crates/c08_algorithms/examples/cache_eviction_policies_demo.rs) |
| 算法专项练习 | `exercises` | [exercises/src/algorithms/](../../exercises/src/algorithms/) |
| 形式化验证工具 | `crates/c15_verification_tools` | [crates/c15_verification_tools/README.md](../../crates/c15_verification_tools/README.md) |

---

## 六、8 大主-topic 入口 {#六8-大主-topic-入口}

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

## 七、阶段推进状态 {#七阶段推进状态}

- **阶段 0 基线修复**: ✅ 完成
- **阶段 1 知识图谱骨架**: ✅ 完成 — 统一索引、层级/概念族标注、核心节点与边已建立
- **阶段 2 主-topic 父→子→机制→示例展开**: ✅ 完成
  - ✅ 算法练习：L2-L4 排序/搜索/图论/DP/数据结构专项练习与单元测试已落地 [10_algorithm_exercises_guide.md](10_algorithm_exercises_guide.md)
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

### 剩余细化项（阶段 4 收尾） {#剩余细化项阶段-4-收尾}

1. 关系边缺少文档行号锚点。
2. 已建立示例文件级锚点，行号级锚点持续补充。
3. 版本特性与知识图谱节点未完全双向追溯。

---

## 八、权威来源索引 {#八权威来源索引}

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
> **来源**: [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
> **来源**: [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
> **来源**: [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
>
## 社区权威参考 {#社区权威参考}

- [Rust 中文社区](https://rustcc.cn/)
- [This Week in Rust](https://this-week-in-rust.org/)
