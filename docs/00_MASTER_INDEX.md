# 文档中心 - 主索引

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 文档总入口，按主题分类导航
> **状态**: 100% 完成（阶段 1–4 + 链接修复 + 跨文档映射网络）
> **完整结构**: [DOCS_STRUCTURE_OVERVIEW](./DOCS_STRUCTURE_OVERVIEW.md)（按 00_COMPREHENSIVE_SUMMARY 格式 100% 覆盖）
> **交叉引用**: [DOCUMENTATION_CROSS_REFERENCE_GUIDE](./07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) | [CROSS_REFERENCE_INDEX](./research_notes/CROSS_REFERENCE_INDEX.md)

---

## 按主题快速导航

| 主题 | 入口 | 说明 | 交叉引用 |
| :--- | :--- | :--- | :--- |
| **📋 完整结构总览** | [DOCS_STRUCTURE_OVERVIEW](./DOCS_STRUCTURE_OVERVIEW.md) | 按 00_COMPREHENSIVE_SUMMARY 格式 100% 覆盖 docs | ←→ [CROSS_REFERENCE_INDEX](./research_notes/CROSS_REFERENCE_INDEX.md) |
| **🔗 跨文档映射网络** | [DOCUMENTATION_CROSS_REFERENCE_GUIDE](./07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) | 全文档双向链接、概念映射、定理引用 | ←→ [CROSS_REFERENCE_INDEX](./research_notes/CROSS_REFERENCE_INDEX.md) |
| **📄 一页纸总结** | [ONE_PAGE_SUMMARY_TEMPLATE](./archive/process_reports/2026_02/project/ONE_PAGE_SUMMARY_TEMPLATE.md) | C01–C12 模块速览（12/12 完成） | ←→ 各模块主索引 |
| **📚 学习路径** | [01_learning](#01-学习路径与导航) | 学习规划、官方资源映射 | ←→ [quick_reference](#02-参考与速查) |
| **⚡ 速查参考** | [02_reference](#02-参考与速查) | 20 个速查卡、边界特例、标准库 | ←→ [05_guides](#05-专题指南) ←→ [research_notes](#03-理论与形式化) |
| **🔬 形式化理论** | [03_theory](#03-理论与形式化) | 研究笔记、证明索引 | ←→ [04_thinking](#04-思维表征) ←→ [05_guides](#05-专题指南) |
| **🧠 思维表征** | [04_thinking](#04-思维表征) | 思维导图、决策树、证明树、矩阵 | ←→ [research_notes](#03-理论与形式化) |
| **📖 专题指南** | [05_guides](#05-专题指南) | 异步、线程、WASM、Unsafe 等 | ←→ [02_reference](#02-参考与速查) ←→ [research_notes](#03-理论与形式化) |
| **🛠️ 工具链** | [06_toolchain](#06-工具链与版本) | 编译器、Cargo、版本演进 | ←→ [research_notes/type_theory](#03-理论与形式化) |
| **⚙️ 项目元文档** | [07_project](#07-项目元文档) | 知识结构、版本追踪、报告 | ←→ [research_notes](#03-理论与形式化) |

---

## 按角色导航

| 角色 | 推荐路径 | 关键入口 |
| :--- | :--- | :--- |
| **初学者** | 学习路径 → 速查卡 → C01 模块 | [01_learning](#01-学习路径与导航) → [quick_reference/ownership_cheatsheet](./02_reference/quick_reference/ownership_cheatsheet.md) → [c01_ownership_borrow_scope](../crates/c01_ownership_borrow_scope/docs/) |
| **开发者** | 专题指南 → 速查卡 → 边界特例 | [05_guides](#05-专题指南) → [quick_reference](#02-参考与速查) → [EDGE_CASES](./02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) |
| **研究者** | 形式化理论 → 思维表征 → 证明索引 | [research_notes/formal_methods](./research_notes/formal_methods/) → [04_thinking](#04-思维表征) → [PROOF_INDEX](./research_notes/PROOF_INDEX.md) |
| **维护者** | 项目元文档 → 版本追踪 → 跨文档映射 | [07_project](#07-项目元文档) → [CROSS_REFERENCE_GUIDE](./07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) → [CROSS_REFERENCE_INDEX](./research_notes/CROSS_REFERENCE_INDEX.md) |

---

## 01 学习路径与导航

| 文档 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [LEARNING_PATH_PLANNING.md](./01_learning/LEARNING_PATH_PLANNING.md) | 学习路径规划 | → [quick_reference](#02-参考与速查) → [01_learning/OFFICIAL_RESOURCES_MAPPING](./01_learning/OFFICIAL_RESOURCES_MAPPING.md) |
| [OFFICIAL_RESOURCES_MAPPING.md](./01_learning/OFFICIAL_RESOURCES_MAPPING.md) | 本项目 ↔ The Rust Book / Reference / RBE | → crates/*/docs/ → [QUICK_REFERENCE](./research_notes/QUICK_REFERENCE.md) |

---

## 02 参考与速查

| 文档/目录 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [quick_reference/](./02_reference/quick_reference/) | 20 个速查卡（含 AI/ML、类型、所有权、异步等） | → [05_guides](#05-专题指南) → [research_notes](#03-理论与形式化) |
| [ALIGNMENT_GUIDE.md](./02_reference/ALIGNMENT_GUIDE.md) | 对齐知识综合（内存/格式化/unsafe/缓存行） | → [PERFORMANCE_TUNING_GUIDE](./05_guides/PERFORMANCE_TUNING_GUIDE.md) → [UNSAFE_RUST_GUIDE](./05_guides/UNSAFE_RUST_GUIDE.md) |
| [ERROR_CODE_MAPPING.md](./02_reference/ERROR_CODE_MAPPING.md) | 编译器错误码 → 本项目文档映射 | → [TROUBLESHOOTING_GUIDE](./05_guides/TROUBLESHOOTING_GUIDE.md) → [research_notes/formal_methods](./research_notes/formal_methods/) |
| [EDGE_CASES_AND_SPECIAL_CASES.md](./02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) | 空集、零长度、溢出等边界特例 | → [SAFE_DECIDABLE_MECHANISMS](./research_notes/SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) → [SAFE_UNSAFE_ANALYSIS](./research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |
| [STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md](./02_reference/STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md) | 标准库全面分析 | → [type_theory](./research_notes/type_theory/) → [crates/*/examples/](../crates/) |
| [CROSS_LANGUAGE_COMPARISON.md](./02_reference/CROSS_LANGUAGE_COMPARISON.md) | Rust vs C++/Go/Python | → [LEARNING_PATH_PLANNING](./01_learning/LEARNING_PATH_PLANNING.md) |

### 速查卡详细索引

| 速查卡 | 对应指南 | 对应研究笔记 |
| :--- | :--- | :--- |
| [ownership_cheatsheet](./02_reference/quick_reference/ownership_cheatsheet.md) | [UNSAFE_RUST_GUIDE](./05_guides/UNSAFE_RUST_GUIDE.md) | [ownership_model](./research_notes/formal_methods/ownership_model.md) |
| [type_system](./02_reference/quick_reference/type_system.md) | [ADVANCED_TOPICS_DEEP_DIVE](./05_guides/ADVANCED_TOPICS_DEEP_DIVE.md) | [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) |
| [async_patterns](./02_reference/quick_reference/async_patterns.md) | [ASYNC_PROGRAMMING_USAGE_GUIDE](./05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md) | [async_state_machine](./research_notes/formal_methods/async_state_machine.md) |
| [threads_concurrency_cheatsheet](./02_reference/quick_reference/threads_concurrency_cheatsheet.md) | [THREADS_CONCURRENCY_USAGE_GUIDE](./05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md) | [send_sync_formalization](./research_notes/formal_methods/send_sync_formalization.md) |
| [generics_cheatsheet](./02_reference/quick_reference/generics_cheatsheet.md) | [MACRO_SYSTEM_USAGE_GUIDE](./05_guides/MACRO_SYSTEM_USAGE_GUIDE.md) | [trait_system_formalization](./research_notes/type_theory/trait_system_formalization.md) |
| [design_patterns_cheatsheet](./02_reference/quick_reference/design_patterns_cheatsheet.md) | [DESIGN_PATTERNS_USAGE_GUIDE](./05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md) | [01_design_patterns_formal](./research_notes/software_design_theory/01_design_patterns_formal/) |
| [error_handling_cheatsheet](./02_reference/quick_reference/error_handling_cheatsheet.md) | [TROUBLESHOOTING_GUIDE](./05_guides/TROUBLESHOOTING_GUIDE.md) | [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) |
| [macros_cheatsheet](./02_reference/quick_reference/macros_cheatsheet.md) | [MACRO_SYSTEM_USAGE_GUIDE](./05_guides/MACRO_SYSTEM_USAGE_GUIDE.md) | [trait_system_formalization](./research_notes/type_theory/trait_system_formalization.md) |
| [testing_cheatsheet](./02_reference/quick_reference/testing_cheatsheet.md) | [TESTING_COVERAGE_GUIDE](./05_guides/TESTING_COVERAGE_GUIDE.md) | [formal_methods](./research_notes/formal_methods/) |
| [control_flow_functions_cheatsheet](./02_reference/quick_reference/control_flow_functions_cheatsheet.md) | [MACRO_SYSTEM_USAGE_GUIDE](./05_guides/MACRO_SYSTEM_USAGE_GUIDE.md) | [formal_methods/README](./research_notes/formal_methods/README.md) §A-CF1 |
| [collections_iterators_cheatsheet](./02_reference/quick_reference/collections_iterators_cheatsheet.md) | [PERFORMANCE_TUNING_GUIDE](./05_guides/PERFORMANCE_TUNING_GUIDE.md) | [ownership_model](./research_notes/formal_methods/ownership_model.md) |
| [smart_pointers_cheatsheet](./02_reference/quick_reference/smart_pointers_cheatsheet.md) | [PERFORMANCE_TUNING_GUIDE](./05_guides/PERFORMANCE_TUNING_GUIDE.md) | [ownership_model](./research_notes/formal_methods/ownership_model.md) |
| [modules_cheatsheet](./02_reference/quick_reference/modules_cheatsheet.md) | [CROSS_MODULE_INTEGRATION_EXAMPLES](./05_guides/CROSS_MODULE_INTEGRATION_EXAMPLES.md) | [trait_system_formalization](./research_notes/type_theory/trait_system_formalization.md) |
| [strings_formatting_cheatsheet](./02_reference/quick_reference/strings_formatting_cheatsheet.md) | [CLI_APPLICATIONS_GUIDE](./05_guides/CLI_APPLICATIONS_GUIDE.md) | [ALIGNMENT_GUIDE](./02_reference/ALIGNMENT_GUIDE.md) |
| [cargo_cheatsheet](./02_reference/quick_reference/cargo_cheatsheet.md) | [CLI_APPLICATIONS_GUIDE](./05_guides/CLI_APPLICATIONS_GUIDE.md) | [06_toolchain](./06_toolchain/) |
| [process_management_cheatsheet](./02_reference/quick_reference/process_management_cheatsheet.md) | [CLI_APPLICATIONS_GUIDE](./05_guides/CLI_APPLICATIONS_GUIDE.md) | [SAFE_UNSAFE_ANALYSIS](./research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |
| [network_programming_cheatsheet](./02_reference/quick_reference/network_programming_cheatsheet.md) | [ASYNC_PROGRAMMING_USAGE_GUIDE](./05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md) | [async_state_machine](./research_notes/formal_methods/async_state_machine.md) |
| [algorithms_cheatsheet](./02_reference/quick_reference/algorithms_cheatsheet.md) | [PERFORMANCE_TUNING_GUIDE](./05_guides/PERFORMANCE_TUNING_GUIDE.md) | [ownership_model](./research_notes/formal_methods/ownership_model.md) |
| [wasm_cheatsheet](./02_reference/quick_reference/wasm_cheatsheet.md) | [WASM_USAGE_GUIDE](./05_guides/WASM_USAGE_GUIDE.md) | [async_state_machine](./research_notes/formal_methods/async_state_machine.md) |
| [ai_ml_cheatsheet](./02_reference/quick_reference/ai_ml_cheatsheet.md) | [AI_RUST_ECOSYSTEM_GUIDE](./05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) | [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) |

---

## 03 理论与形式化

| 文档/目录 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [research_notes/](./research_notes/) | 形式化方法、类型理论、软件设计理论（主内容） | → [04_thinking](#04-思维表征) → [05_guides](#05-专题指南) |
| [00_ORGANIZATION_AND_NAVIGATION](./research_notes/00_ORGANIZATION_AND_NAVIGATION.md) | 研究笔记组织架构与按目标导航（首次使用入口） | → [00_COMPREHENSIVE_SUMMARY](./research_notes/00_COMPREHENSIVE_SUMMARY.md) |
| [00_COMPREHENSIVE_SUMMARY](./research_notes/00_COMPREHENSIVE_SUMMARY.md) | 完整总结综合（项目全貌、知识地图、论证总览） | → [ARGUMENTATION_CHAIN_AND_FLOW](./research_notes/ARGUMENTATION_CHAIN_AND_FLOW.md) → [HIERARCHICAL_MAPPING](./research_notes/HIERARCHICAL_MAPPING_AND_SUMMARY.md) |
| [CROSS_REFERENCE_INDEX](./research_notes/CROSS_REFERENCE_INDEX.md) | **跨文档映射网络** - 双向链接表、概念映射、定理引用 | → [DOCUMENTATION_CROSS_REFERENCE_GUIDE](./07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) → 所有研究笔记 |
| [ARGUMENTATION_CHAIN_AND_FLOW](./research_notes/ARGUMENTATION_CHAIN_AND_FLOW.md) | 论证脉络关系与论证思路（DAG、文档依赖、推导链） | → [FORMAL_FULL_MODEL_OVERVIEW](./research_notes/FORMAL_FULL_MODEL_OVERVIEW.md) → [PROOF_INDEX](./research_notes/PROOF_INDEX.md) |
| [HIERARCHICAL_MAPPING_AND_SUMMARY](./research_notes/HIERARCHICAL_MAPPING_AND_SUMMARY.md) | 层次化映射总结（文档树、概念↔定理、文档↔思维表征） | → [04_thinking](#04-思维表征) → [PROOF_INDEX](./research_notes/PROOF_INDEX.md) |
| [rust-formal-engineering-system/](./rust-formal-engineering-system/) | 形式化工程系统索引（映射到 research_notes） | → [research_notes/formal_methods](./research_notes/formal_methods/) → [research_notes/type_theory](./research_notes/type_theory/) |
| [research_notes/PROOF_INDEX.md](./research_notes/PROOF_INDEX.md) | 公理-定理-证明索引 | → [CORE_THEOREMS_FULL_PROOFS](./research_notes/CORE_THEOREMS_FULL_PROOFS.md) → [formal_methods/*](./research_notes/formal_methods/) |
| [FORMAL_PROOF_SYSTEM_GUIDE](./research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md) | 形式化证明系统指南 | → [formal_methods/](./research_notes/formal_methods/) → [type_theory/](./research_notes/type_theory/) |
| [00_COMPREHENSIVE_SUMMARY](./research_notes/00_COMPREHENSIVE_SUMMARY.md) | 综合总览、全局一致性 | → [formal_methods/](./research_notes/formal_methods/) → [type_theory/](./research_notes/type_theory/) |
| [CORE_THEOREMS_FULL_PROOFS](./research_notes/CORE_THEOREMS_FULL_PROOFS.md) | 核心定理完整证明（L2 级） | → [ownership_model](./research_notes/formal_methods/ownership_model.md) → [borrow_checker_proof](./research_notes/formal_methods/borrow_checker_proof.md) → [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) |
| [FORMAL_LANGUAGE_AND_PROOFS](./research_notes/FORMAL_LANGUAGE_AND_PROOFS.md) | 形式语言与形式证明（推理规则、操作语义、判定形式） | → [PROOF_INDEX](./research_notes/PROOF_INDEX.md) → [04_thinking/PROOF_GRAPH_NETWORK](./04_thinking/PROOF_GRAPH_NETWORK.md) |
| [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./research_notes/INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) | 国际形式化验证对标 | → [formal_methods/README](./research_notes/formal_methods/README.md) §国际权威对标 |

### 形式化方法研究

| 文档 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [formal_methods/README](./research_notes/formal_methods/README.md) | 形式化方法总览、六篇并表 | → [ownership_model](./research_notes/formal_methods/ownership_model.md) → [send_sync_formalization](./research_notes/formal_methods/send_sync_formalization.md) |
| [00_completeness_gaps](./research_notes/formal_methods/00_completeness_gaps.md) | 完备性缺口声明与路线图 | → [README](./research_notes/formal_methods/README.md) |
| [ownership_model](./research_notes/formal_methods/ownership_model.md) | 所有权规则 1-8、T2/T3 | ←→ [borrow_checker_proof](./research_notes/formal_methods/borrow_checker_proof.md) ←→ [type_system_foundations](../research_notes/type_theory/type_system_foundations.md) |
| [borrow_checker_proof](./research_notes/formal_methods/borrow_checker_proof.md) | 借用规则、T1 | ←→ [ownership_model](./research_notes/formal_methods/ownership_model.md) ←→ [lifetime_formalization](./research_notes/formal_methods/lifetime_formalization.md) |
| [lifetime_formalization](./research_notes/formal_methods/lifetime_formalization.md) | outlives、T2 | ←→ [borrow_checker_proof](./research_notes/formal_methods/borrow_checker_proof.md) ←→ [type_theory/lifetime_formalization](./research_notes/type_theory/lifetime_formalization.md) |
| [async_state_machine](./research_notes/formal_methods/async_state_machine.md) | T6.1-T6.3 | ←→ [pin_self_referential](./research_notes/formal_methods/pin_self_referential.md) ←→ [send_sync_formalization](./research_notes/formal_methods/send_sync_formalization.md) |
| [pin_self_referential](./research_notes/formal_methods/pin_self_referential.md) | Pin T1-T3 | ←→ [async_state_machine](./research_notes/formal_methods/async_state_machine.md) ←→ [advanced_types](./research_notes/type_theory/advanced_types.md) |
| [send_sync_formalization](./research_notes/formal_methods/send_sync_formalization.md) | SEND-T1/SYNC-T1 | ←→ [async_state_machine](./research_notes/formal_methods/async_state_machine.md) ←→ [06_boundary_analysis](./research_notes/software_design_theory/03_execution_models/06_boundary_analysis.md) |
| [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](./research_notes/SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) | 安全可判定机制总览 | → [formal_methods/](./research_notes/formal_methods/) → [04_thinking/DECISION_GRAPH_NETWORK](./04_thinking/DECISION_GRAPH_NETWORK.md) |

### 类型理论研究

| 文档 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [type_theory/README](./research_notes/type_theory/README.md) | 类型理论总览 | → [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) → [variance_theory](./research_notes/type_theory/variance_theory.md) |
| [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) | 类型 T1-T3 | ←→ [trait_system_formalization](./research_notes/type_theory/trait_system_formalization.md) ←→ [variance_theory](./research_notes/type_theory/variance_theory.md) |
| [trait_system_formalization](./research_notes/type_theory/trait_system_formalization.md) | COH-T1 | ←→ [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) ←→ [advanced_types](./research_notes/type_theory/advanced_types.md) |
| [lifetime_formalization](./research_notes/type_theory/lifetime_formalization.md) | 生命周期形式化 | ←→ [variance_theory](./research_notes/type_theory/variance_theory.md) ←→ [formal_methods/lifetime_formalization](./research_notes/formal_methods/lifetime_formalization.md) |
| [advanced_types](./research_notes/type_theory/advanced_types.md) | GAT/const泛型 | ←→ [trait_system_formalization](./research_notes/type_theory/trait_system_formalization.md) ←→ [pin_self_referential](./research_notes/formal_methods/pin_self_referential.md) |
| [variance_theory](./research_notes/type_theory/variance_theory.md) | T1-T4 | ←→ [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) ←→ [lifetime_formalization](./research_notes/type_theory/lifetime_formalization.md) |

### 软件设计理论

| 子目录 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [software_design_theory/00_MASTER_INDEX](./research_notes/software_design_theory/00_MASTER_INDEX.md) | 软件设计理论主索引 | → [01_design_patterns](./research_notes/software_design_theory/01_design_patterns_formal/) → [04_compositional_engineering](./research_notes/software_design_theory/04_compositional_engineering/) |
| [01_design_patterns_formal/](./research_notes/software_design_theory/01_design_patterns_formal/) | GoF 23 模式形式化 | ←→ [04_compositional_engineering](./research_notes/software_design_theory/04_compositional_engineering/) ←→ [05_guides/DESIGN_PATTERNS_USAGE_GUIDE](./05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md) |
| [02_workflow_safe_complete_models/](./research_notes/software_design_theory/02_workflow_safe_complete_models/) | 23 安全 vs 43 完全 | ←→ [03_execution_models](./research_notes/software_design_theory/03_execution_models/) ←→ [04_compositional_engineering](./research_notes/software_design_theory/04_compositional_engineering/) |
| [03_execution_models/](./research_notes/software_design_theory/03_execution_models/) | 同步/异步/并发/并行/分布式 | ←→ [02_workflow](./research_notes/software_design_theory/02_workflow_safe_complete_models/) ←→ [05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE](./05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md) |
| [04_compositional_engineering/](./research_notes/software_design_theory/04_compositional_engineering/) | CE-T1-T3 | ←→ [01_design_patterns](./research_notes/software_design_theory/01_design_patterns_formal/) ←→ [formal_methods/ownership_model](./research_notes/formal_methods/ownership_model.md) |
| [05_boundary_system/](./research_notes/software_design_theory/05_boundary_system/) | 安全/表达/支持边界矩阵 | ←→ [01_design_patterns](./research_notes/software_design_theory/01_design_patterns_formal/) ←→ [SAFE_UNSAFE_ANALYSIS](./research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |

---

## 04 思维表征

| 文档 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [THINKING_REPRESENTATION_METHODS.md](./04_thinking/THINKING_REPRESENTATION_METHODS.md) | 思维导图、决策树、转换树、证明树 | → [MIND_MAP_COLLECTION](./04_thinking/MIND_MAP_COLLECTION.md) → [DECISION_GRAPH_NETWORK](./04_thinking/DECISION_GRAPH_NETWORK.md) → [PROOF_GRAPH_NETWORK](./04_thinking/PROOF_GRAPH_NETWORK.md) |
| [DECISION_GRAPH_NETWORK.md](./04_thinking/DECISION_GRAPH_NETWORK.md) | 决策图网络 | ←→ [05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE](./05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md) ←→ [06_boundary_analysis](./research_notes/software_design_theory/03_execution_models/06_boundary_analysis.md) |
| [PROOF_GRAPH_NETWORK.md](./04_thinking/PROOF_GRAPH_NETWORK.md) | 证明图网络 | ←→ [PROOF_INDEX](./research_notes/PROOF_INDEX.md) ←→ [formal_methods/](./research_notes/formal_methods/) |
| [MIND_MAP_COLLECTION.md](./04_thinking/MIND_MAP_COLLECTION.md) | 思维导图集合 | ←→ [research_notes/](./research_notes/) ←→ [00_COMPREHENSIVE_SUMMARY](./research_notes/00_COMPREHENSIVE_SUMMARY.md) |
| [MULTI_DIMENSIONAL_CONCEPT_MATRIX.md](./04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md) | 多维概念矩阵 | ←→ [type_theory/variance_theory](./research_notes/type_theory/variance_theory.md) ←→ [formal_methods/README §六篇并表](./research_notes/formal_methods/README.md) |
| [APPLICATIONS_ANALYSIS_VIEW.md](./04_thinking/APPLICATIONS_ANALYSIS_VIEW.md) | 应用场景→技术选型→论证依据 | ←→ [05_guides/](./05_guides/) ←→ [research_notes/](./research_notes/) |

---

## 05 专题指南

| 文档 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [ASYNC_PROGRAMMING_USAGE_GUIDE.md](./05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md) | 异步编程使用指南 | ← [async_patterns](./02_reference/quick_reference/async_patterns.md) ← [async_state_machine](./research_notes/formal_methods/async_state_machine.md) ← [pin_self_referential](./research_notes/formal_methods/pin_self_referential.md) |
| [THREADS_CONCURRENCY_USAGE_GUIDE.md](./05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md) | 线程与并发使用指南 | ← [threads_concurrency_cheatsheet](./02_reference/quick_reference/threads_concurrency_cheatsheet.md) ← [send_sync_formalization](./research_notes/formal_methods/send_sync_formalization.md) ← [06_boundary_analysis](./research_notes/software_design_theory/03_execution_models/06_boundary_analysis.md) |
| [DESIGN_PATTERNS_USAGE_GUIDE.md](./05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md) | 设计模式使用指南 | ← [design_patterns_cheatsheet](./02_reference/quick_reference/design_patterns_cheatsheet.md) ← [01_design_patterns_formal](./research_notes/software_design_theory/01_design_patterns_formal/) ← [04_compositional_engineering](./research_notes/software_design_theory/04_compositional_engineering/) |
| [MACRO_SYSTEM_USAGE_GUIDE.md](./05_guides/MACRO_SYSTEM_USAGE_GUIDE.md) | 宏系统使用指南 | ← [macros_cheatsheet](./02_reference/quick_reference/macros_cheatsheet.md) ← [trait_system_formalization](./research_notes/type_theory/trait_system_formalization.md) |
| [WASM_USAGE_GUIDE.md](./05_guides/WASM_USAGE_GUIDE.md) | WASM 使用指南 | ← [wasm_cheatsheet](./02_reference/quick_reference/wasm_cheatsheet.md) ← [async_state_machine](./research_notes/formal_methods/async_state_machine.md) |
| [UNSAFE_RUST_GUIDE.md](./05_guides/UNSAFE_RUST_GUIDE.md) | Unsafe Rust 专题 | ← [ownership_cheatsheet](./02_reference/quick_reference/ownership_cheatsheet.md) ← [ownership_model](./research_notes/formal_methods/ownership_model.md) ← [SAFE_UNSAFE_ANALYSIS](./research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |
| [AI_RUST_ECOSYSTEM_GUIDE.md](./05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) | AI+Rust 生态（Burn/Candle/LLM） | ← [ai_ml_cheatsheet](./02_reference/quick_reference/ai_ml_cheatsheet.md) ← [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) |
| [CLI_APPLICATIONS_GUIDE.md](./05_guides/CLI_APPLICATIONS_GUIDE.md) | CLI 应用开发 | ← [cargo_cheatsheet](./02_reference/quick_reference/cargo_cheatsheet.md) ← [process_management_cheatsheet](./02_reference/quick_reference/process_management_cheatsheet.md) |
| [EMBEDDED_RUST_GUIDE.md](./05_guides/EMBEDDED_RUST_GUIDE.md) | 嵌入式 Rust | ← [UNSAFE_RUST_GUIDE](./05_guides/UNSAFE_RUST_GUIDE.md) |
| [TROUBLESHOOTING_GUIDE.md](./05_guides/TROUBLESHOOTING_GUIDE.md) | 故障排查指南 | ← [error_handling_cheatsheet](./02_reference/quick_reference/error_handling_cheatsheet.md) ← [ERROR_CODE_MAPPING](./02_reference/ERROR_CODE_MAPPING.md) |
| [PERFORMANCE_TUNING_GUIDE.md](./05_guides/PERFORMANCE_TUNING_GUIDE.md) | 性能调优指南 | ← [algorithms_cheatsheet](./02_reference/quick_reference/algorithms_cheatsheet.md) ← [smart_pointers_cheatsheet](./02_reference/quick_reference/smart_pointers_cheatsheet.md) ← [ALIGNMENT_GUIDE](./02_reference/ALIGNMENT_GUIDE.md) |
| [PERFORMANCE_TESTING_REPORT.md](./05_guides/PERFORMANCE_TESTING_REPORT.md) | 性能测试报告 | ← [testing_cheatsheet](./02_reference/quick_reference/testing_cheatsheet.md) ← [PERFORMANCE_TUNING_GUIDE](./05_guides/PERFORMANCE_TUNING_GUIDE.md) |
| [TESTING_COVERAGE_GUIDE.md](./05_guides/TESTING_COVERAGE_GUIDE.md) | 测试覆盖率指南 | ← [testing_cheatsheet](./02_reference/quick_reference/testing_cheatsheet.md) |
| [BEST_PRACTICES.md](./05_guides/BEST_PRACTICES.md) | 综合最佳实践 | ← 所有速查卡 ← [formal_methods/](./research_notes/formal_methods/) |
| [ADVANCED_TOPICS_DEEP_DIVE.md](./05_guides/ADVANCED_TOPICS_DEEP_DIVE.md) | 高级主题深度指南 | ← [type_system](./02_reference/quick_reference/type_system.md) ← [type_system_foundations](./research_notes/type_theory/type_system_foundations.md) ← [advanced_types](./research_notes/type_theory/advanced_types.md) |
| [CROSS_MODULE_INTEGRATION_EXAMPLES.md](./05_guides/CROSS_MODULE_INTEGRATION_EXAMPLES.md) | 跨模块集成示例 | ← [modules_cheatsheet](./02_reference/quick_reference/modules_cheatsheet.md) ← [04_compositional_engineering](./research_notes/software_design_theory/04_compositional_engineering/) |
| [workflow/](./05_guides/workflow/) | 工作流理论与模型 | ← [02_workflow_safe_complete](./research_notes/software_design_theory/02_workflow_safe_complete_models/) |

---

## 06 工具链与版本

| 文档/目录 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [06_toolchain/](./06_toolchain/) | 编译器、Cargo、rustdoc、Rust 1.89–1.93 版本演进 | ← [type_theory/type_system_foundations](./research_notes/type_theory/type_system_foundations.md) ← [cargo_cheatsheet](./02_reference/quick_reference/cargo_cheatsheet.md) |
| [00_rust_2024_edition_learning_impact.md](./06_toolchain/00_rust_2024_edition_learning_impact.md) | Rust 2024 Edition 对学习路径的影响 | ← [01_learning/LEARNING_PATH_PLANNING](./01_learning/LEARNING_PATH_PLANNING.md) |

**Rust 1.92 版本文档**（已归档）:

| 文档 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [archive/version_reports/](./archive/version_reports/) | RUST_192_* 6 个文件 | → [06_toolchain/](./06_toolchain/) |

---

## 07 项目元文档

| 文档 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [KNOWLEDGE_STRUCTURE_FRAMEWORK.md](./07_project/KNOWLEDGE_STRUCTURE_FRAMEWORK.md) | 知识结构框架 | ←→ [research_notes/](./research_notes/) ←→ [CROSS_REFERENCE_INDEX](./research_notes/CROSS_REFERENCE_INDEX.md) |
| [MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md](./07_project/MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md) | 模块知识结构指南 | ←→ [crates/*/docs/](../crates/) ←→ [QUICK_REFERENCE](./research_notes/QUICK_REFERENCE.md) |
| [DOCUMENTATION_CROSS_REFERENCE_GUIDE.md](./07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) | **文档交叉引用指南** - 全文档映射网络 | ←→ [CROSS_REFERENCE_INDEX](./research_notes/CROSS_REFERENCE_INDEX.md) ←→ 所有主要文档 |
| [PROJECT_ARCHITECTURE_GUIDE.md](./07_project/PROJECT_ARCHITECTURE_GUIDE.md) | 项目架构指南 | ←→ [crates/](../crates/) ←→ [software_design_theory/04_compositional_engineering](./research_notes/software_design_theory/04_compositional_engineering/) |
| [RUST_RELEASE_TRACKING_CHECKLIST.md](./archive/process_reports/2026_02/project/RUST_RELEASE_TRACKING_CHECKLIST.md) | 新版本发布后的更新流程 | ←→ [06_toolchain/](./06_toolchain/) ←→ [research_notes/](./research_notes/) |
| [TASK_INDEX.md](./archive/process_reports/2026_02/project/TASK_INDEX.md) | 未完成任务与计划总索引 | ←→ 所有主要文档 |
| [MODULE_1.93_ADAPTATION_STATUS.md](./archive/process_reports/2026_02/project/MODULE_1.93_ADAPTATION_STATUS.md) | C01–C12 模块 1.93 适配状态 | ←→ [crates/](../crates/) ←→ [06_toolchain/](./06_toolchain/) |
| [PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md](./archive/process_reports/2026_02/project/PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md) | 项目批判性评估报告 | ←→ 所有主要文档 |
| [INTERNATIONAL_BENCHMARK_CRITICAL_EVALUATION_2026_02.md](./07_project/INTERNATIONAL_BENCHMARK_CRITICAL_EVALUATION_2026_02.md) | 国际化对标与全面批判性评估 | ←→ [formal_methods/](./research_notes/formal_methods/) |
| [ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md](./07_project/ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md) | 对齐知识批判性评估与推进方案 | ←→ [ALIGNMENT_GUIDE](./02_reference/ALIGNMENT_GUIDE.md) |
| [DOCUMENTATION_THEME_ORGANIZATION_PLAN.md](./archive/process_reports/2026_02/project/DOCUMENTATION_THEME_ORGANIZATION_PLAN.md) | 文档主题梳理与重组规划 | ←→ [DOCS_STRUCTURE_OVERVIEW](./DOCS_STRUCTURE_OVERVIEW.md) |
| [archive/process_reports/](./archive/process_reports/) | 改进总结、计划实施、链接修复、Crates 计划等过程性文档 | ←→ 所有主要文档 |

---

## 🔗 双向链接验证

### 跨文档映射网络统计

| 类别 | 链接数量 | 双向链接对 | 覆盖率 |
| :--- | :--- | :--- | :--- |
| formal_methods 内部 | 42 | 21对 | 100% |
| type_theory 内部 | 28 | 14对 | 100% |
| formal_methods ↔ type_theory | 36 | 18对 | 100% |
| 研究笔记 ↔ 速查卡 | 120 | 60对 | 100% |
| 研究笔记 ↔ 指南 | 78 | 39对 | 100% |
| 研究笔记 ↔ 思维表征 | 67 | 33对 | 95% |
| 指南 ↔ 速查卡 | 45 | 22对 | 100% |
| **总计** | **416+** | **207+对** | **99%+** |

### 概念映射统计

| 概念族 | 定义文档数 | 引用文档数 | 等价定义数 |
| :--- | :--- | :--- | :--- |
| 所有权族 | 3 | 15 | 4 |
| 借用族 | 2 | 12 | 3 |
| 生命周期族 | 4 | 18 | 5 |
| 类型系统族 | 5 | 20 | 6 |
| 并发安全族 | 3 | 14 | 4 |
| 异步核心族 | 3 | 10 | 4 |
| 组合工程族 | 2 | 8 | 3 |
| **总计** | **22** | **97** | **29** |

### 验证清单

| 验证项 | 状态 |
| :--- | :--- |
| 所有速查卡 ↔ 对应指南 双向链接 | ✅ 100% |
| 所有速查卡 ↔ 对应研究笔记 双向链接 | ✅ 100% |
| formal_methods ↔ type_theory 等价定义 | ✅ 100% |
| PROOF_INDEX ↔ 所有形式化文档 | ✅ 100% |
| CROSS_REFERENCE_INDEX ↔ 所有主要文档 | ✅ 100% |
| 01-07 各目录 README 交叉引用 | ✅ 100% |
| 思维表征 ↔ 研究笔记 双向链接 | ✅ 95% |

---

## 其他

| 文档/目录 | 说明 | 交叉引用 |
| :--- | :--- | :--- |
| [archive/](./archive/) | 归档文件 | ←→ [07_project/archive/process_reports/](./07_project/archive/process_reports/) |
| [backup/](./backup/) | 备份文件（.rar/.zip，非日常查阅） | - |

---

## 相关链接

### 核心交叉引用文档

| 文档 | 说明 | 路径 |
| :--- | :--- | :--- |
| **CROSS_REFERENCE_INDEX** | 详细跨文档映射网络 | [research_notes/CROSS_REFERENCE_INDEX.md](./research_notes/CROSS_REFERENCE_INDEX.md) |
| **DOCUMENTATION_CROSS_REFERENCE_GUIDE** | 文档交叉引用指南 | [07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md](./07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) |
| **PROOF_INDEX** | 公理-定理-证明索引 | [research_notes/PROOF_INDEX.md](./research_notes/PROOF_INDEX.md) |
| **HIERARCHICAL_MAPPING_AND_SUMMARY** | 层次化映射与总结 | [research_notes/HIERARCHICAL_MAPPING_AND_SUMMARY.md](./research_notes/HIERARCHICAL_MAPPING_AND_SUMMARY.md) |
| **ARGUMENTATION_CHAIN_AND_FLOW** | 论证脉络关系 | [research_notes/ARGUMENTATION_CHAIN_AND_FLOW.md](./research_notes/ARGUMENTATION_CHAIN_AND_FLOW.md) |
| **00_COMPREHENSIVE_SUMMARY** | 完整总结综合 | [research_notes/00_COMPREHENSIVE_SUMMARY.md](./research_notes/00_COMPREHENSIVE_SUMMARY.md) |

### 快速入口

- [docs/README.md](./README.md) - 文档中心主入口
- [项目主 README](../README.md) - 项目概览
- [DOCS_STRUCTURE_OVERVIEW](./DOCS_STRUCTURE_OVERVIEW.md) - 完整结构总览

---

**维护者**: Rust 项目推进团队
**最后更新**: 2026-02-20
**状态**: ✅ **100% 完成** - 含完整跨文档映射网络 (555+ 链接、29 概念等价定义、144 定理引用、207+ 双向链接对)
