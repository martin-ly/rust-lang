# 层间映射图谱（Inter-Layer Mapping Atlas）

> **EN**: Inter-Layer Mapping Atlas
> **Summary**: L0–L7 各层之间的依赖、蕴含、反馈关系，基于前置/后置概念元数据与「相关概念」章节引用的全层统计。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、层间引用矩阵（行 = 源层，列 = 目标层）

> 统计口径：前置概念元数据 + 后置概念元数据 + 「相关概念/延伸阅读」章节内链接，同一（源，目标）对按 后置 > 前置 > 相关概念节 优先级去重计 1 次。

| 源层 \ 目标层 | L0 元信息层 | L1 基础概念层 | L2 进阶概念层 | L3 高级概念层 | L4 形式化理论层 | L5 对比分析层 | L6 生态工程层 | L7 前沿趋势层 |
|---|---|---|---|---|---|---|---|---|
| L0 元信息层 | 70 | 15 | 2 | 7 | 9 | 6 | 10 | 2 |
| L1 基础概念层 | 39 | 167 | 62 | 36 | 8 | 4 | 18 | 3 |
| L2 进阶概念层 | 13 | 63 | 73 | 39 | 13 | 4 | 12 | 5 |
| L3 高级概念层 | 17 | 38 | 65 | 221 | 17 | 3 | 39 | 10 |
| L4 形式化理论层 | 27 | 43 | 20 | 74 | 176 | 9 | 17 | 19 |
| L5 对比分析层 | 12 | 24 | 14 | 15 | 9 | 25 | 19 | 3 |
| L6 生态工程层 | 26 | 60 | 58 | 114 | 29 | 63 | 389 | 30 |
| L7 前沿趋势层 | 8 | 35 | 40 | 45 | 21 | 3 | 33 | 128 |

## 二、跨层关键桥接概念

跨层边合计 **1429** 条（前置概念 667 · 后置概念 347 · 相关概念节 415），下表按层序展示前 160 条。

| 源层 | 概念 | 指向层 | 目标概念 | 依据 |
|:---|:---|:---|:---|:---|
| L0 元信息层 | [Rust 安全边界扩展推理树](../../00_meta/00_framework/boundary_extension_tree.md) | L3 高级概念层 | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 相关概念节 |
| L0 元信息层 | [Rust 安全边界扩展推理树](../../00_meta/00_framework/boundary_extension_tree.md) | L4 形式化理论层 | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 相关概念节 |
| L0 元信息层 | [Rust 安全边界扩展推理树](../../00_meta/00_framework/boundary_extension_tree.md) | L6 生态工程层 | [WASI & WebAssembly Component Model](../../06_ecosystem/05_systems_and_embedded/01_wasi.md) | 相关概念节 |
| L0 元信息层 | [Comprehensive Rust 课程映射](../../00_meta/00_framework/comprehensive_rust_mapping.md) | L6 生态工程层 | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念 |
| L0 元信息层 | [C/C++ → Rust 工程层对比路线图](../../00_meta/00_framework/cpp_rust_engineering_roadmap.md) | L1 基础概念层 | [变量模型：从通用 PL 视角看 Rust 的所有权](../../01_foundation/03_values_and_references/03_variable_model.md) | 前置概念 |
| L0 元信息层 | [C/C++ → Rust 工程层对比路线图](../../00_meta/00_framework/cpp_rust_engineering_roadmap.md) | L5 对比分析层 | [Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) | 前置概念 |
| L0 元信息层 | [C/C++ → Rust 工程层对比路线图](../../00_meta/00_framework/cpp_rust_engineering_roadmap.md) | L5 对比分析层 | [Rust vs C++：ABI、对象模型与内存布局](../../05_comparative/01_systems_languages/02_cpp_abi_object_model.md) | 后置概念 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L1 基础概念层 | [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L3 高级概念层 | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L4 形式化理论层 | [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L4 形式化理论层 | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L5 对比分析层 | [Rust vs Go：线性所有权 vs CSP 过程逻辑](../../05_comparative/01_systems_languages/03_rust_vs_go.md) | 相关概念节 |
| L0 元信息层 | [Rust 编译期可判定性谱系全景](../../00_meta/00_framework/decidability_spectrum.md) | L7 前沿趋势层 | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L4 形式化理论层 | [Type Theory](../../04_formal/00_type_theory/01_type_theory.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L4 形式化理论层 | [Linear Logic & Affine Logic](../../04_formal/01_ownership_logic/01_linear_logic.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L5 对比分析层 | [Paradigm Matrix: Multi-Language Formal Comparison](../../05_comparative/00_paradigms/01_paradigm_matrix.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L5 对比分析层 | [Rust vs Go：线性所有权 vs CSP 过程逻辑](../../05_comparative/01_systems_languages/03_rust_vs_go.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L6 生态工程层 | [Design Patterns](../../06_ecosystem/03_design_patterns/01_patterns.md) | 相关概念节 |
| L0 元信息层 | [Rust 语义表达力多视角深化](../../00_meta/00_framework/expressiveness_multiview.md) | L7 前沿趋势层 | [Effects System: Concept Pre-study](../../07_future/03_preview_features/01_effects_system.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系全局思维导图](../../00_meta/00_framework/knowledge_mindmap.md) | L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系全局思维导图](../../00_meta/00_framework/knowledge_mindmap.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 相关概念节 |
| L0 元信息层 | [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/00_framework/pattern_semantic_space_index.md) | L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | 前置概念 |
| L0 元信息层 | [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/00_framework/pattern_semantic_space_index.md) | L6 生态工程层 | [Design Patterns](../../06_ecosystem/03_design_patterns/01_patterns.md) | 前置概念 |
| L0 元信息层 | [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/00_framework/pattern_semantic_space_index.md) | L6 生态工程层 | [模式组合代数：设计模式的结构化关联与冲突分析](../../06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md) | 后置概念 |
| L0 元信息层 | [通用 PL 基座路线图：Rust 在编程语言坐标系中的位置](../../00_meta/00_framework/pl_foundations_roadmap.md) | L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 前置概念 |
| L0 元信息层 | [通用 PL 基座路线图：Rust 在编程语言坐标系中的位置](../../00_meta/00_framework/pl_foundations_roadmap.md) | L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | 前置概念 |
| L0 元信息层 | [语义桥：算法、设计模式与工作流模式的统一谱系](../../00_meta/00_framework/semantic_bridge_algorithms_patterns.md) | L3 高级概念层 | [并行与分布式模式谱系：从线程池到共识算法](../../03_advanced/00_concurrency/07_parallel_distributed_pattern_spectrum.md) | 后置概念 |
| L0 元信息层 | [语义桥：算法、设计模式与工作流模式的统一谱系](../../00_meta/00_framework/semantic_bridge_algorithms_patterns.md) | L6 生态工程层 | [Design Patterns](../../06_ecosystem/03_design_patterns/01_patterns.md) | 前置概念 |
| L0 元信息层 | [语义桥：算法、设计模式与工作流模式的统一谱系](../../00_meta/00_framework/semantic_bridge_algorithms_patterns.md) | L6 生态工程层 | [模式组合代数：设计模式的结构化关联与冲突分析](../../06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md) | 后置概念 |
| L0 元信息层 | [语义桥：算法、设计模式与工作流模式的统一谱系](../../00_meta/00_framework/semantic_bridge_algorithms_patterns.md) | L6 生态工程层 | [算法与竞赛编程 (Algorithms & Competitive Programming)](../../06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md) | 前置概念 |
| L0 元信息层 | [Rust Semantic Expressiveness: A Panoramic Survey](../../00_meta/00_framework/semantic_expressiveness.md) | L4 形式化理论层 | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 相关概念节 |
| L0 元信息层 | [Rust Semantic Expressiveness: A Panoramic Survey](../../00_meta/00_framework/semantic_expressiveness.md) | L5 对比分析层 | [Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系定理推理森林](../../00_meta/00_framework/theorem_inference_forest.md) | L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系定理推理森林](../../00_meta/00_framework/theorem_inference_forest.md) | L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系定理推理森林](../../00_meta/00_framework/theorem_inference_forest.md) | L3 高级概念层 | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | 相关概念节 |
| L0 元信息层 | [Rust 职业市场全景：2026 年数据与分析](../../00_meta/04_navigation/02_career_landscape.md) | L6 生态工程层 | [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) | 相关概念节 |
| L0 元信息层 | [Rust 职业市场全景：2026 年数据与分析](../../00_meta/04_navigation/02_career_landscape.md) | L6 生态工程层 | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念 |
| L0 元信息层 | [跨层知识图谱](../../00_meta/04_navigation/04_inter_layer_map.md) | L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 相关概念节 |
| L0 元信息层 | [跨层知识图谱](../../00_meta/04_navigation/04_inter_layer_map.md) | L4 形式化理论层 | [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系层次内模型间映射图](../../00_meta/04_navigation/06_intra_layer_model_map.md) | L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系层次内模型间映射图](../../00_meta/04_navigation/06_intra_layer_model_map.md) | L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系层次内模型间映射图](../../00_meta/04_navigation/06_intra_layer_model_map.md) | L4 形式化理论层 | [Linear Logic & Affine Logic](../../04_formal/01_ownership_logic/01_linear_logic.md) | 相关概念节 |
| L0 元信息层 | [Rust 知识体系层次内模型间映射图](../../00_meta/04_navigation/06_intra_layer_model_map.md) | L4 形式化理论层 | [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | 相关概念节 |
| L1 基础概念层 | [Rust 起步指南](../../01_foundation/00_start/00_start.md) | L6 生态工程层 | [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | 相关概念节 |
| L1 基础概念层 | [编程语言理论基础](../../01_foundation/00_start/01_pl_prerequisites.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 后置概念 |
| L1 基础概念层 | [编程语言理论基础](../../01_foundation/00_start/01_pl_prerequisites.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/02_zero_cost_abstractions.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 前置概念 |
| L1 基础概念层 | [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/02_zero_cost_abstractions.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 前置概念 |
| L1 基础概念层 | [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/02_zero_cost_abstractions.md) | L5 对比分析层 | [Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) | 后置概念 |
| L1 基础概念层 | [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/02_zero_cost_abstractions.md) | L6 生态工程层 | [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) | 后置概念 |
| L1 基础概念层 | [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/02_zero_cost_abstractions.md) | L7 前沿趋势层 | [Cranelift 后端预研：Rust 编译器的快速调试编译](../../07_future/03_preview_features/16_cranelift_backend_preview.md) | 相关概念节 |
| L1 基础概念层 | [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 前置概念 |
| L1 基础概念层 | [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | L2 进阶概念层 | [闭包类型系统：Fn、FnMut、FnOnce 的捕获语义](../../02_intermediate/04_types_and_conversions/02_closure_types.md) | 后置概念 |
| L1 基础概念层 | [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | L2 进阶概念层 | [Rust 迭代器模式](../../02_intermediate/07_iterators_and_closures/01_iterator_patterns.md) | 后置概念 |
| L1 基础概念层 | [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 后置概念 |
| L1 基础概念层 | [副作用与纯度：从引用透明到 Rust 的所有权效果](../../01_foundation/00_start/04_effects_and_purity.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 后置概念 |
| L1 基础概念层 | [副作用与纯度：从引用透明到 Rust 的所有权效果](../../01_foundation/00_start/04_effects_and_purity.md) | L4 形式化理论层 | [求值策略：Call-by-Value, Call-by-Name, Call-by-Need](../../04_formal/03_operational_semantics/04_evaluation_strategies.md) | 前置概念 |
| L1 基础概念层 | [副作用与纯度：从引用透明到 Rust 的所有权效果](../../01_foundation/00_start/04_effects_and_purity.md) | L7 前沿趋势层 | [Effects System: Concept Pre-study](../../07_future/03_preview_features/01_effects_system.md) | 后置概念 |
| L1 基础概念层 | [标准 I/O 与进程](../../01_foundation/00_start/05_std_io_and_process.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 相关概念节 |
| L1 基础概念层 | [标准 I/O 与进程](../../01_foundation/00_start/05_std_io_and_process.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 后置概念 |
| L1 基础概念层 | [标准 I/O 与进程](../../01_foundation/00_start/05_std_io_and_process.md) | L6 生态工程层 | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念 |
| L1 基础概念层 | [Rust 关键字](../../01_foundation/00_start/06_keywords.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 前置概念 |
| L1 基础概念层 | [Rust 运算符与符号](../../01_foundation/00_start/07_operators_and_symbols.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 前置概念 |
| L1 基础概念层 | [Rust 运算符与符号](../../01_foundation/00_start/07_operators_and_symbols.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [Rust 运算符与符号](../../01_foundation/00_start/07_operators_and_symbols.md) | L3 高级概念层 | [Macros](../../03_advanced/03_proc_macros/01_macros.md) | 后置概念 |
| L1 基础概念层 | [Rust 所有权-借用-生命周期知识图谱](../../01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md) | L2 进阶概念层 | [智能指针：堆内存管理与共享语义](../../02_intermediate/02_memory_management/04_smart_pointers.md) | 后置概念 |
| L1 基础概念层 | [Rust 所有权-借用-生命周期知识图谱](../../01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md) | L3 高级概念层 | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | 后置概念 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L0 元信息层 | [方法论：思维表征与知识结构规范](../../00_meta/00_framework/methodology.md) | 相关概念节 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 相关概念节 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L2 进阶概念层 | [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) | 相关概念节 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L3 高级概念层 | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | 相关概念节 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 相关概念节 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L3 高级概念层 | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 相关概念节 |
| L1 基础概念层 | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | L5 对比分析层 | [Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) | 相关概念节 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 后置概念 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L2 进阶概念层 | [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) | 相关概念节 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L3 高级概念层 | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | 后置概念 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 相关概念节 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L3 高级概念层 | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 相关概念节 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L4 形式化理论层 | [Linear Logic & Affine Logic](../../04_formal/01_ownership_logic/01_linear_logic.md) | 后置概念 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L5 对比分析层 | [Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) | 相关概念节 |
| L1 基础概念层 | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | L7 前沿趋势层 | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 相关概念节 |
| L1 基础概念层 | [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 后置概念 |
| L1 基础概念层 | [Lifetimes 高级主题](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | L0 元信息层 | [跨层知识图谱](../../00_meta/04_navigation/04_inter_layer_map.md) | 相关概念节 |
| L1 基础概念层 | [Lifetimes 高级主题](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 相关概念节 |
| L1 基础概念层 | [Lifetimes 高级主题](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 相关概念节 |
| L1 基础概念层 | [Lifetimes 高级主题](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 相关概念节 |
| L1 基础概念层 | [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | L0 元信息层 | [Rust 知识体系学习指南](../../00_meta/04_navigation/07_learning_guide.md) | 前置概念 |
| L1 基础概念层 | [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | L2 进阶概念层 | [构造与初始化：C++ 的构造函数 vs Rust 的结构体字面量](../../02_intermediate/00_traits/05_construction_and_initialization.md) | 后置概念 |
| L1 基础概念层 | [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | L2 进阶概念层 | [测验：C/C++ → Rust 基础知识对比](../../02_intermediate/09_quizzes/30_quiz_cpp_rust_foundations.md) | 相关概念节 |
| L1 基础概念层 | [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | L5 对比分析层 | [Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) | 后置概念 |
| L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | L0 元信息层 | [方法论：思维表征与知识结构规范](../../00_meta/00_framework/methodology.md) | 相关概念节 |
| L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | L0 元信息层 | [跨层知识图谱](../../00_meta/04_navigation/04_inter_layer_map.md) | 相关概念节 |
| L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 后置概念 |
| L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | L3 高级概念层 | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 相关概念节 |
| L1 基础概念层 | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | L4 形式化理论层 | [Type Theory](../../04_formal/00_type_theory/01_type_theory.md) | 相关概念节 |
| L1 基础概念层 | [Never Type (`!`)：底类型与穷尽性](../../01_foundation/02_type_system/02_never_type.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [Never Type (`!`)：底类型与穷尽性](../../01_foundation/02_type_system/02_never_type.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 后置概念 |
| L1 基础概念层 | [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/02_type_system/03_numerics.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/02_type_system/03_numerics.md) | L2 进阶概念层 | [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) | 相关概念节 |
| L1 基础概念层 | [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/02_type_system/03_numerics.md) | L6 生态工程层 | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 相关概念节 |
| L1 基础概念层 | [类型强制与转换：显式与隐式的边界](../../01_foundation/02_type_system/04_coercion_and_casting.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [类型强制与转换：显式与隐式的边界](../../01_foundation/02_type_system/04_coercion_and_casting.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 前置概念 |
| L1 基础概念层 | [类型强制与转换：显式与隐式的边界](../../01_foundation/02_type_system/04_coercion_and_casting.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [类型强制与转换：显式与隐式的边界](../../01_foundation/02_type_system/04_coercion_and_casting.md) | L3 高级概念层 | [Rust FFI：与外部代码的安全边界](../../03_advanced/04_ffi/01_rust_ffi.md) | 后置概念 |
| L1 基础概念层 | [数据抽象谱系：从 C struct 到 Rust enum + trait](../../01_foundation/02_type_system/05_data_abstraction_spectrum.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 后置概念 |
| L1 基础概念层 | [数据抽象谱系：从 C struct 到 Rust enum + trait](../../01_foundation/02_type_system/05_data_abstraction_spectrum.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [数据抽象谱系：从 C struct 到 Rust enum + trait](../../01_foundation/02_type_system/05_data_abstraction_spectrum.md) | L3 高级概念层 | [类型擦除与动态分发](../../03_advanced/06_low_level_patterns/03_type_erasure.md) | 后置概念 |
| L1 基础概念层 | [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/03_values_and_references/01_reference_semantics.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/03_values_and_references/01_reference_semantics.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/03_values_and_references/01_reference_semantics.md) | L2 进阶概念层 | [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) | 后置概念 |
| L1 基础概念层 | [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/03_values_and_references/01_reference_semantics.md) | L3 高级概念层 | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 相关概念节 |
| L1 基础概念层 | [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/03_values_and_references/01_reference_semantics.md) | L4 形式化理论层 | [Linear Logic & Affine Logic](../../04_formal/01_ownership_logic/01_linear_logic.md) | 相关概念节 |
| L1 基础概念层 | [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/03_values_and_references/02_value_vs_reference_semantics.md) | L0 元信息层 | [Rust 知识体系学习指南](../../00_meta/04_navigation/07_learning_guide.md) | 前置概念 |
| L1 基础概念层 | [变量模型：从通用 PL 视角看 Rust 的所有权](../../01_foundation/03_values_and_references/03_variable_model.md) | L2 进阶概念层 | [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) | 后置概念 |
| L1 基础概念层 | [变量模型：从通用 PL 视角看 Rust 的所有权](../../01_foundation/03_values_and_references/03_variable_model.md) | L4 形式化理论层 | [求值策略：Call-by-Value, Call-by-Name, Call-by-Need](../../04_formal/03_operational_semantics/04_evaluation_strategies.md) | 后置概念 |
| L1 基础概念层 | [控制流：表达式导向的流程控制](../../01_foundation/04_control_flow/01_control_flow.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [控制流：表达式导向的流程控制](../../01_foundation/04_control_flow/01_control_flow.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [控制流：表达式导向的流程控制](../../01_foundation/04_control_flow/01_control_flow.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 后置概念 |
| L1 基础概念层 | [模式匹配](../../01_foundation/04_control_flow/02_patterns.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 相关概念节 |
| L1 基础概念层 | [模式匹配](../../01_foundation/04_control_flow/02_patterns.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念 |
| L1 基础概念层 | [模式匹配](../../01_foundation/04_control_flow/02_patterns.md) | L2 进阶概念层 | [高级类型系统：从关联类型到类型级编程](../../02_intermediate/04_types_and_conversions/04_type_system_advanced.md) | 后置概念 |
| L1 基础概念层 | [语句与表达式](../../01_foundation/04_control_flow/03_statements_and_expressions.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 相关概念节 |
| L1 基础概念层 | [语句与表达式](../../01_foundation/04_control_flow/03_statements_and_expressions.md) | L2 进阶概念层 | [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) | 后置概念 |
| L1 基础概念层 | [语句与表达式](../../01_foundation/04_control_flow/03_statements_and_expressions.md) | L3 高级概念层 | [Async/Await](../../03_advanced/01_async/01_async.md) | 后置概念 |
| L1 基础概念层 | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/01_collections.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/01_collections.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 前置概念 |
| L1 基础概念层 | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/01_collections.md) | L2 进阶概念层 | [智能指针：堆内存管理与共享语义](../../02_intermediate/02_memory_management/04_smart_pointers.md) | 后置概念 |
| L1 基础概念层 | [高级集合类型：BTreeMap、VecDeque、BinaryHeap 与自定义 Hasher 深度分析](../../01_foundation/05_collections/02_collections_advanced.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [高级集合类型：BTreeMap、VecDeque、BinaryHeap 与自定义 Hasher 深度分析](../../01_foundation/05_collections/02_collections_advanced.md) | L2 进阶概念层 | [Generics](../../02_intermediate/01_generics/01_generics.md) | 相关概念节 |
| L1 基础概念层 | [高级集合类型：BTreeMap、VecDeque、BinaryHeap 与自定义 Hasher 深度分析](../../01_foundation/05_collections/02_collections_advanced.md) | L2 进阶概念层 | [智能指针：堆内存管理与共享语义](../../02_intermediate/02_memory_management/04_smart_pointers.md) | 后置概念 |
| L1 基础概念层 | [高级集合类型：BTreeMap、VecDeque、BinaryHeap 与自定义 Hasher 深度分析](../../01_foundation/05_collections/02_collections_advanced.md) | L6 生态工程层 | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念 |
| L1 基础概念层 | [字符串与文本：Rust 的 Unicode 处理与格式化系统](../../01_foundation/06_strings_and_text/01_strings_and_text.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [字符串与文本：Rust 的 Unicode 处理与格式化系统](../../01_foundation/06_strings_and_text/01_strings_and_text.md) | L3 高级概念层 | [Rust FFI：与外部代码的安全边界](../../03_advanced/04_ffi/01_rust_ffi.md) | 后置概念 |
| L1 基础概念层 | [字符串与编码：Rust 的文本处理类型系统](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [字符串与编码：Rust 的文本处理类型系统](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) | L3 高级概念层 | [Rust FFI：与外部代码的安全边界](../../03_advanced/04_ffi/01_rust_ffi.md) | 后置概念 |
| L1 基础概念层 | [格式化与显示](../../01_foundation/06_strings_and_text/03_formatting_and_display.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 相关概念节 |
| L1 基础概念层 | [格式化与显示](../../01_foundation/06_strings_and_text/03_formatting_and_display.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 前置概念 |
| L1 基础概念层 | [格式化与显示](../../01_foundation/06_strings_and_text/03_formatting_and_display.md) | L2 进阶概念层 | [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) | 后置概念 |
| L1 基础概念层 | [格式化与显示](../../01_foundation/06_strings_and_text/03_formatting_and_display.md) | L6 生态工程层 | [Rust 常用开发工具](../../06_ecosystem/00_toolchain/14_development_tools.md) | 后置概念 |
| L1 基础概念层 | [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | L0 元信息层 | [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | 相关概念节 |
| L1 基础概念层 | [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | L6 生态工程层 | [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) | 后置概念 |
| L1 基础概念层 | [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | L6 生态工程层 | [Core Crates](../../06_ecosystem/02_core_crates/01_core_crates.md) | 后置概念 |
| L1 基础概念层 | [Functions](../../01_foundation/07_modules_and_items/02_functions.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 前置概念 |
| L1 基础概念层 | [Functions](../../01_foundation/07_modules_and_items/02_functions.md) | L2 进阶概念层 | [Traits](../../02_intermediate/00_traits/01_traits.md) | 后置概念 |
| L1 基础概念层 | [Use Declarations](../../01_foundation/07_modules_and_items/03_use_declarations.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 前置概念 |
| L1 基础概念层 | [Use Declarations](../../01_foundation/07_modules_and_items/03_use_declarations.md) | L2 进阶概念层 | [Rust API 命名约定](../../02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md) | 后置概念 |
| L1 基础概念层 | [Structs](../../01_foundation/07_modules_and_items/04_structs.md) | L0 元信息层 | [Rust 核心术语英中对照表](../../00_meta/01_terminology/01_terminology_glossary.md) | 前置概念 |

## 三、与现有元文件的关系

- 更详细的层间依赖图见 [../04_navigation/04_inter_layer_map.md](../04_navigation/04_inter_layer_map.md)
- 层内模型映射见 [../04_navigation/06_intra_layer_model_map.md](../04_navigation/06_intra_layer_model_map.md)
- 形式化本体规范见 [kg_ontology_v2.md](kg_ontology_v2.md)

---

> 本文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 生成；请勿手工编辑，更新后重新运行生成脚本。
