# 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)
> 生成时间：2026-07-28 04:47
> 工具：`scripts/topic_authority_aligner.py` | 数据来源：Rust 官方文档、形式化/验证生态、工业生态、项目路线图

## 1. 当前项目概念层级（L0-L7）

### L00（71 篇）

- `concept/00_meta/00_framework/bloom_taxonomy.md` — Bloom Taxonomy（Bloom 分类法）
- `concept/00_meta/00_framework/boundary_extension_tree.md` — Rust 安全边界扩展推理树
- `concept/00_meta/00_framework/cognitive_dimension_matrix.md` — Rust 知识体系双维认知矩阵（Krathwohl × Bloom）
- `concept/00_meta/00_framework/competency_graph.md` — Rust 知识体系能力图谱（Competency Graph）
- `concept/00_meta/00_framework/comprehensive_rust_mapping.md` — Comprehensive Rust 课程映射
- `concept/00_meta/00_framework/concept_definition_decision_forest.md` — Rust 知识体系概念定义判定森林（Concept Definition Decision Forest）
- `concept/00_meta/00_framework/cpp_rust_engineering_roadmap.md` — C/C++ → Rust 工程层对比路线图
- `concept/00_meta/00_framework/decidability_spectrum.md` — Rust 编译期可判定性谱系全景（Decidability Spectrum）
- `concept/00_meta/00_framework/expressiveness_multiview.md` — Rust 语义表达力多视角深化（Multiview Expressiveness Analysis）
- `concept/00_meta/00_framework/fault_tree_analysis_collection.md` — Rust 知识体系失效分析树集（Fault Tree Analysis Collection）
- `concept/00_meta/00_framework/knowledge_mindmap.md` — Rust 知识体系全局思维导图（Knowledge Mindmap）
- `concept/00_meta/00_framework/methodology.md` — 方法论：思维表征与知识结构规范
- `concept/00_meta/00_framework/paradigm_transition_matrix.md` — Rust 范式转换模式矩阵（Paradigm Transition Matrix）
- `concept/00_meta/00_framework/pattern_semantic_space_index.md` — 模式语义空间索引：设计模式在概念体系中的坐标
- `concept/00_meta/00_framework/pl_foundations_roadmap.md` — 通用 PL 基座路线图：Rust 在编程语言坐标系中的位置
- `concept/00_meta/00_framework/semantic_bridge_algorithms_patterns.md` — 语义桥：算法、设计模式与工作流模式的统一谱系
- `concept/00_meta/00_framework/semantic_expressiveness.md` — Rust Semantic Expressiveness: A Panoramic Survey（Rust 语义表达力全景梳理）
- `concept/00_meta/00_framework/semantic_space.md` — Rust 表征空间（Semantic / Representational Space）
- `concept/00_meta/00_framework/theorem_inference_forest.md` — Rust 知识体系定理推理森林
- `concept/00_meta/00_framework/theorem_registry.md` — 定理链全局注册表（Theorem Registry）
- `concept/00_meta/00_framework/todos.md` — 全局待办清单（Global TODO Tracker）
- `concept/00_meta/01_terminology/01_terminology_glossary.md` — Rust 核心术语英中对照表
- `concept/00_meta/01_terminology/02_bilingual_template_v2.md` — Concept 文件双语模板 v2（Bilingual Template v2）
- `concept/00_meta/01_terminology/03_bilingual_template.md` — Concept 文件双语模板（Bilingual Template）
- `concept/00_meta/02_sources/01_authority_source_map.md` — 权威来源映射表（Authority Source Map）
- `concept/00_meta/02_sources/02_rustbelt_predicate_map.md` — RustBelt 谓词映射图
- `concept/00_meta/02_sources/03_sources.md` — 权威来源清单与知识来源关系分析
- `concept/00_meta/02_sources/04_topic_authority_alignment_map.md` — 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)
- `concept/00_meta/02_sources/05_international_authority_index.md` — International Authority Index（国际化权威来源索引）
- `concept/00_meta/02_sources/06_external_authority_topic_index.md` — 外部权威来源主题索引（External Authority Topic Index）
- … 共 71 篇

### L01（57 篇）

- `concept/01_foundation/00_start/00_start.md` — Rust 起步指南
- `concept/01_foundation/00_start/01_pl_prerequisites.md` — 编程语言理论基础（PL Prerequisites）
- `concept/01_foundation/00_start/02_zero_cost_abstractions.md` — 零成本抽象：Rust 的性能哲学
- `concept/01_foundation/00_start/03_closure_basics.md` — 闭包基础：捕获环境与匿名函数
- `concept/01_foundation/00_start/04_effects_and_purity.md` — 副作用与纯度：从引用透明到 Rust 的所有权效果
- `concept/01_foundation/00_start/05_std_io_and_process.md` — 标准 I/O 与进程（std I/O and Process）
- `concept/01_foundation/00_start/06_keywords.md` — Rust 关键字（Keywords）
- `concept/01_foundation/00_start/07_operators_and_symbols.md` — Rust 运算符与符号（Operators and Symbols）
- `concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md` — Rust 所有权-借用-生命周期知识图谱
- `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` — 所有权
- `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` — 借用
- `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` — Lifetimes（生命周期）
- `concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md` — Lifetimes 高级主题
- `concept/01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md` — Move 语义：C++ 与 Rust 的资源转移模型
- `concept/01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md` — 所有权清单自测：Brown University Ownership Inventory
- `concept/01_foundation/02_type_system/01_type_system.md` — 类型系统基础
- `concept/01_foundation/02_type_system/02_never_type.md` — Never Type (`!`)：底类型与穷尽性
- `concept/01_foundation/02_type_system/03_numerics.md` — 数值类型与运算：从整数到浮点的完整图景
- `concept/01_foundation/02_type_system/04_coercion_and_casting.md` — 类型强制与转换：显式与隐式的边界
- `concept/01_foundation/02_type_system/05_data_abstraction_spectrum.md` — 数据抽象谱系：从 C struct 到 Rust enum + trait
- `concept/01_foundation/03_values_and_references/01_reference_semantics.md` — 引用语义：自动解引用、Deref 强制与类型转换
- `concept/01_foundation/03_values_and_references/02_value_vs_reference_semantics.md` — 值语义 vs 引用语义：从 C++、Java、Python 到 Rust
- `concept/01_foundation/03_values_and_references/03_variable_model.md` — 变量模型：从通用 PL 视角看 Rust 的所有权
- `concept/01_foundation/04_control_flow/01_control_flow.md` — 控制流：表达式导向的流程控制
- `concept/01_foundation/04_control_flow/02_patterns.md` — 模式匹配（Patterns）
- `concept/01_foundation/04_control_flow/03_let_chains.md` — 链式 let 与 let 守卫（Let Chains & If-Let Guards）
- `concept/01_foundation/04_control_flow/04_statements_and_expressions.md` — 语句与表达式（Statements and Expressions）
- `concept/01_foundation/04_control_flow/05_let_else.md` — let-else：失败分支提前返回
- `concept/01_foundation/05_collections/01_collections.md` — 集合类型：Rust 标准库的数据结构谱系
- `concept/01_foundation/05_collections/02_collections_advanced.md` — 高级集合类型：BTreeMap、VecDeque、BinaryHeap 与自定义 Hasher 深度分析
- … 共 57 篇

### L02（41 篇）

- `concept/02_intermediate/00_traits/01_traits.md` — Trait 系统
- `concept/02_intermediate/00_traits/02_dispatch_mechanisms.md` — 分发机制 (Dispatch Mechanisms)
- `concept/02_intermediate/00_traits/03_serde_patterns.md` — Serde 序列化模式：Rust 的类型驱动数据转换
- `concept/02_intermediate/00_traits/04_advanced_traits.md` — 高级 Trait 主题：从关联类型到特化
- `concept/02_intermediate/00_traits/05_construction_and_initialization.md` — 构造与初始化：C++ 的构造函数 vs Rust 的结构体字面量
- `concept/02_intermediate/00_traits/06_derive_traits.md` — 可派生 Trait（Derive Traits）
- `concept/02_intermediate/00_traits/07_generic_associated_types.md` — 泛型关联类型（Generic Associated Types, GATs）
- `concept/02_intermediate/00_traits/08_negative_impls.md` — 负实现（Negative Impls）
- `concept/02_intermediate/00_traits/09_associated_type_defaults.md` — 关联类型默认值（Associated Type Defaults）
- `concept/02_intermediate/01_generics/01_generics.md` — 泛型系统
- `concept/02_intermediate/01_generics/02_const_generics.md` — Const Generics（常量泛型）：值作为类型参数
- `concept/02_intermediate/01_generics/03_type_level_programming.md` — 类型级编程 (Type-Level Programming)
- `concept/02_intermediate/01_generics/04_quiz_traits_and_generics.md` — 测验：Trait 与泛型（试点扩展）
- `concept/02_intermediate/01_generics/05_const_generics_and_trait_objects.md` — 常量泛型与 Trait 对象：静态分发与动态分发的交叉边界
- `concept/02_intermediate/02_memory_management/01_memory_management.md` — 内存管理
- `concept/02_intermediate/02_memory_management/02_interior_mutability.md` — 内部可变性：编译期规则的运行时逃逸
- `concept/02_intermediate/02_memory_management/03_cow_and_borrowed.md` — Cow：写时克隆与零拷贝抽象
- `concept/02_intermediate/02_memory_management/04_smart_pointers.md` — 智能指针：堆内存管理与共享语义
- `concept/02_intermediate/02_memory_management/05_quiz_memory_management.md` — 测验：内存管理（L2 试点扩展）
- `concept/02_intermediate/03_error_handling/01_error_handling.md` — 错误处理进阶
- `concept/02_intermediate/03_error_handling/02_error_handling_deep_dive.md` — 错误处理深入：从 Result 到自定义错误生态
- `concept/02_intermediate/03_error_handling/03_panic.md` — Panic 机制
- `concept/02_intermediate/03_error_handling/04_exception_safety_rust_cpp.md` — 异常安全：C++ 与 Rust 的错误处理哲学
- `concept/02_intermediate/04_types_and_conversions/01_range_types.md` — Rust 范围类型语义：`std::ops::Range` → `core::range`
- `concept/02_intermediate/04_types_and_conversions/02_closure_types.md` — 闭包类型系统：Fn、FnMut、FnOnce 的捕获语义
- `concept/02_intermediate/04_types_and_conversions/03_newtype_and_wrapper.md` — Newtype 与包装器模式：类型安全的零成本抽象
- `concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md` — 高级类型系统：从关联类型到类型级编程
- `concept/02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md` — RTTI 与动态类型识别：从 C++ 到 Rust
- `concept/02_intermediate/04_types_and_conversions/06_unions.md` — 联合体（Unions）
- `concept/02_intermediate/04_types_and_conversions/07_type_conversions.md` — 类型转换（Type Conversions）
- … 共 41 篇

### L03（74 篇）

- `concept/03_advanced/00_concurrency/01_concurrency.md` — 并发模型
- `concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md` — Send 与 Sync：Auto Trait 的并发安全契约
- `concept/03_advanced/00_concurrency/03_concurrency_patterns.md` — 并发模式：从消息传递到锁自由的数据结构
- `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` — Send/Sync 边界判定
- `concept/03_advanced/00_concurrency/05_cross_platform_concurrency.md` — Cross-Platform Concurrency（跨平台并发）
- `concept/03_advanced/00_concurrency/06_atomics_and_memory_ordering.md` — 原子操作与内存序：无锁并发的精确控制
- `concept/03_advanced/00_concurrency/07_lock_free.md` — 无锁编程与内存模型
- `concept/03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md` — 并行与分布式模式谱系：从线程池到共识算法
- `concept/03_advanced/00_concurrency/09_quiz_concurrency_async.md` — 测验：并发与异步（L3 试点扩展）
- `concept/03_advanced/00_concurrency/10_quiz_semantic_models.md` — 测验：语义模型与跨语言对比（L3）
- `concept/03_advanced/01_async/01_async.md` — Async/Await（异步编程）
- `concept/03_advanced/01_async/02_async_advanced.md` — Async/Await 高级主题
- `concept/03_advanced/01_async/03_async_patterns.md` — 异步模式：从 Future 到生产级并发
- `concept/03_advanced/01_async/04_future_and_executor_mechanisms.md` — Future 与 Executor 机制 (Future and Executor Mechanisms)
- `concept/03_advanced/01_async/05_async_cancellation_safety.md` — Async 取消安全（Cancellation Safety）
- `concept/03_advanced/01_async/06_async_boundary_panorama.md` — Async 边界全景（Async Boundary Panorama）
- `concept/03_advanced/01_async/07_async_closures.md` — Async Closures（异步闭包）
- `concept/03_advanced/01_async/08_pin_unpin.md` — Pin 与 Unpin：自引用类型的不动性保证
- `concept/03_advanced/01_async/09_stream_algebra_and_backpressure.md` — Stream 代数与背压：拉取式序列的形式刻画
- `concept/03_advanced/01_async/10_executor_fairness_and_scheduling.md` — Executor 公平性与调度：Tokio 调度器 internals
- `concept/03_advanced/01_async/11_pin_projection_counterexamples.md` — Pin 投射反例集：unsafe 结构投射的 UB 目录与正确模式库
- `concept/03_advanced/01_async/12_waker_contract_deep_dive.md` — Waker 契约深度解析：RawWakerVTable 实现与契约违反反例集
- `concept/03_advanced/01_async/13_async_trait_object_safety.md` — Async Trait 对象安全：dyn 兼容解决方案谱系与选型矩阵
- `concept/03_advanced/01_async/14_gat_async_boundary.md` — GAT 与 Async 交叉边界语义
- `concept/03_advanced/01_async/15_state_machine_semantics.md` — 状态机语义与工作流模型
- `concept/03_advanced/01_async/16_structured_concurrency.md` — 结构化并发（Structured Concurrency）
- `concept/03_advanced/02_unsafe/00_before_formal.md` — 是否需要进入 L4 形式化层？
- `concept/03_advanced/02_unsafe/01_unsafe.md` — Unsafe Rust 安全编程
- `concept/03_advanced/02_unsafe/02_unsafe_boundary_panorama.md` — Unsafe 边界全景（Unsafe Boundary Panorama）
- `concept/03_advanced/02_unsafe/03_nll_and_polonius.md` — NLL 与 Polonius：借用检查器的演进
- … 共 74 篇

### L04（64 篇）

- `concept/04_formal/00_type_theory/01_type_theory.md` — Type Theory（类型论基础）
- `concept/04_formal/00_type_theory/02_subtype_variance.md` — 子类型与变型：Rust 类型系统中的协变、逆变与不变
- `concept/04_formal/00_type_theory/03_type_inference.md` — 类型推断：Hindley-Milner 算法与 Rust 的工业实现
- `concept/04_formal/00_type_theory/04_category_theory.md` — 范畴论与 Rust：从函子到单子
- `concept/04_formal/00_type_theory/05_lambda_calculus.md` — Lambda 演算与 Rust 计算模型
- `concept/04_formal/00_type_theory/06_type_semantics.md` — Type Semantics（类型语义）
- `concept/04_formal/00_type_theory/07_type_checking_and_inference.md` — rustc 类型检查与类型推断
- `concept/04_formal/00_type_theory/08_type_inference_complexity.md` — Type Inference Complexity（类型推断复杂度）
- `concept/04_formal/00_type_theory/09_type_system_reference.md` — 类型系统参考（Type System Reference）
- `concept/04_formal/00_type_theory/10_dependent_refinement_types.md` — 依赖类型与细化类型（Dependent Types and Refinement Types）
- `concept/04_formal/00_type_theory/11_formal_design_pattern_theory.md` — 形式化设计模式理论 (Formal Design Pattern Theory)
- `concept/04_formal/00_type_theory/12_pattern_composition_algebra.md` — 模式组合代数：设计模式的结构化关联与冲突分析
- `concept/04_formal/00_type_theory/13_formal_algorithm_theory.md` — 形式化算法理论
- `concept/04_formal/01_ownership_logic/01_linear_logic.md` — 线性逻辑与仿射逻辑
- `concept/04_formal/01_ownership_logic/02_ownership_formal.md` — 所有权形式化
- `concept/04_formal/01_ownership_logic/03_linear_logic_applications.md` — 线性逻辑在 Rust 中的工程应用
- `concept/04_formal/01_ownership_logic/04_borrow_checking_decidability.md` — Borrow Checking Decidability（借用检查可判定性）
- `concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md` — Tree Borrows 深度解析
- `concept/04_formal/01_ownership_logic/06_behavior_considered_undefined.md` — 未定义行为清单（Behavior Considered Undefined）
- `concept/04_formal/02_separation_logic/01_rustbelt.md` — RustBelt 与验证工具链
- `concept/04_formal/02_separation_logic/02_separation_logic.md` — 分离逻辑：Rust 所有权的形式化根基
- `concept/04_formal/02_separation_logic/03_safety_tags_in_formal.md` — Safety Tags（安全标签）
- `concept/04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md` — BorrowSanitizer 运行时别名模型检测
- `concept/04_formal/03_operational_semantics/01_denotational_semantics.md` — 指称语义与领域理论
- `concept/04_formal/03_operational_semantics/02_hoare_logic.md` — Hoare 逻辑：程序验证的形式化基础与 Rust 契约
- `concept/04_formal/03_operational_semantics/03_operational_semantics.md` — 操作语义：程序行为的形式化定义
- `concept/04_formal/03_operational_semantics/04_evaluation_strategies.md` — 求值策略：Call-by-Value, Call-by-Name, Call-by-Need
- `concept/04_formal/03_operational_semantics/05_axiomatic_semantics.md` — Axiomatic Semantics（公理语义）
- `concept/04_formal/03_operational_semantics/06_aeneas_symbolic_semantics.md` — Aeneas Symbolic Semantics（Aeneas 符号化语义）
- `concept/04_formal/03_operational_semantics/07_constant_evaluation.md` — 常量求值（Constant Evaluation）
- … 共 64 篇

### L05（27 篇）

- `concept/05_comparative/00_paradigms/01_paradigm_matrix.md` — Paradigm Matrix: Multi-Language Formal Comparison（多语言范式对比矩阵）
- `concept/05_comparative/00_paradigms/02_execution_model_isomorphism.md` — Rust 执行模型同构性矩阵：同步 · 异步 · 并发 · 并行
- `concept/05_comparative/00_paradigms/03_cpp_rust_surface_features.md` — C++ vs Rust：构造、运算符、RTTI、友元
- `concept/05_comparative/00_paradigms/04_five_models_definition_matrix.md` — 五模型定义矩阵：同步 · 并发 · 并行 · 异步 · 分布式
- `concept/05_comparative/00_paradigms/05_language_semantic_model_matrix.md` — 统一语言 × 语义模型表达力矩阵
- `concept/05_comparative/01_systems_languages/01_rust_vs_cpp.md` — Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>
- `concept/05_comparative/01_systems_languages/02_cpp_abi_object_model.md` — Rust vs C++：ABI、对象模型与内存布局
- `concept/05_comparative/01_systems_languages/03_rust_vs_go.md` — Rust vs Go：线性所有权 vs CSP 过程逻辑
- `concept/05_comparative/01_systems_languages/04_rust_vs_ruby.md` — Rust vs Ruby：性能与表达力的两极
- `concept/05_comparative/01_systems_languages/05_rust_vs_swift.md` — Rust vs Swift：现代系统语言的两种路径
- `concept/05_comparative/01_systems_languages/06_rust_vs_zig.md` — Rust vs Zig：现代系统语言的两种哲学
- `concept/05_comparative/01_systems_languages/07_rust_vs_ada_spark.md` — Rust vs Ada/SPARK：现代所有权类型系统与安全关键形式化子集的工程对比
- `concept/05_comparative/01_systems_languages/08_rust_vs_d.md` — Rust vs D：所有权类型系统与可选 GC 系统语言的工程对比
- `concept/05_comparative/01_systems_languages/09_rust_vs_nim.md` — Rust vs Nim：所有权类型系统与 Python 式系统语言的工程对比
- `concept/05_comparative/02_managed_languages/01_rust_vs_java.md` — Rust vs Java：系统编程与托管运行时的范式对比
- `concept/05_comparative/02_managed_languages/02_rust_vs_python.md` — Rust vs Python：系统编程与动态脚本的对照分析
- `concept/05_comparative/02_managed_languages/03_rust_vs_javascript.md` — Rust vs JavaScript：系统编程与脚本执行的范式差异
- `concept/05_comparative/02_managed_languages/04_rust_vs_kotlin.md` — Rust vs Kotlin：静态安全的两种路径
- `concept/05_comparative/02_managed_languages/05_rust_vs_scala.md` — Rust vs Scala：类型系统的两种哲学
- `concept/05_comparative/02_managed_languages/06_rust_vs_csharp.md` — Rust vs C#：托管与原生之路
- `concept/05_comparative/02_managed_languages/07_rust_vs_elixir.md` — Rust vs Elixir 对比分析
- `concept/05_comparative/02_managed_languages/08_rust_vs_typescript.md` — Rust vs TypeScript：静态类型系统的两种哲学 —— 编译期证明与渐进式工程
- `concept/05_comparative/02_managed_languages/09_rust_vs_haskell.md` — Rust vs Haskell：所有权/RAII 与惰性纯函数式语言的系统对比
- `concept/05_comparative/02_managed_languages/10_rust_vs_ocaml.md` — Rust vs OCaml：系统安全与函数式表达力的对比
- `concept/05_comparative/02_managed_languages/11_rust_vs_fsharp.md` — Rust vs F#：系统所有权与函数式数据生态的对比
- `concept/05_comparative/03_domain_comparisons/01_safety_boundaries.md` — Rust 安全保证的边界条件全景
- `concept/05_comparative/03_domain_comparisons/02_quiz_rust_vs_systems.md` — 测验：Rust vs 系统编程语言（L5 试点扩展）

### L06（131 篇）

- `concept/06_ecosystem/00_toolchain/01_toolchain.md` — 工具链与 Cargo
- `concept/06_ecosystem/00_toolchain/02_logging_observability.md` — 日志与可观测性：Rust 服务端监控生态
- `concept/06_ecosystem/00_toolchain/03_devops_and_ci_cd.md` — DevOps 与 CI/CD：Rust 的持续交付工程实践
- `concept/06_ecosystem/00_toolchain/04_compiler_internals.md` — Rust 编译器内部原理
- `concept/06_ecosystem/00_toolchain/05_compiler_infrastructure.md` — Rust 编译器基础设施深度解析
- `concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md` — 测验：Rust 工具链（L6 试点扩展）
- `concept/06_ecosystem/00_toolchain/07_rustdoc_196_changes.md` — Rustdoc 1.96–1.97 变更
- `concept/06_ecosystem/00_toolchain/08_platform_rust_integration.md` — 将 Rust 集成到现有平台
- `concept/06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md` — Rust 编译器的 LLVM 后端与代码生成
- `concept/06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md` — rustc Driver、Interface 与 Stable MIR
- `concept/06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md` — rustc 编译器诊断与 UI Tests
- `concept/06_ecosystem/00_toolchain/12_rustc_bootstrap.md` — rustc 自举（Bootstrap）
- `concept/06_ecosystem/00_toolchain/13_compiler_testing.md` — rustc 编译器测试体系
- `concept/06_ecosystem/00_toolchain/14_development_tools.md` — Rust 常用开发工具
- `concept/06_ecosystem/00_toolchain/15_z_flags_reference.md` — rustc / Cargo `-Z` 不稳定选项参考清单
- `concept/06_ecosystem/00_toolchain/16_rustdoc_internals.md` — Rustdoc 内部实现
- `concept/06_ecosystem/01_cargo/01_cargo_script.md` — Cargo Script 脚本化 Rust
- `concept/06_ecosystem/01_cargo/02_public_private_deps.md` — Cargo `public = true` 与 Resolver v3
- `concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md` — Resolver v3 与 `public = true` 的 feature unification 演示
- `concept/06_ecosystem/01_cargo/04_cargo_196_features.md` — Cargo 1.96 新特性与工具链变更
- `concept/06_ecosystem/01_cargo/05_cargo_build_scripts.md` — Cargo Build Scripts（`build.rs`）
- `concept/06_ecosystem/01_cargo/06_cargo_dependency_resolution.md` — Cargo 依赖解析
- `concept/06_ecosystem/01_cargo/07_cargo_source_replacement.md` — Cargo Source Replacement 与 Vendoring
- `concept/06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md` — Cargo Registry 与包发布
- `concept/06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md` — Cargo 认证与构建缓存
- `concept/06_ecosystem/01_cargo/10_cargo_manifest_reference.md` — Cargo Manifest 参考速查
- `concept/06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md` — Cargo Profiles 与 Lints
- `concept/06_ecosystem/01_cargo/12_cargo_subcommands_and_plugins.md` — Cargo 子命令与插件生态
- `concept/06_ecosystem/01_cargo/13_cargo_security_cves.md` — Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223
- `concept/06_ecosystem/01_cargo/14_cargo_workspaces.md` — Cargo Workspaces（工作区）
- … 共 131 篇

### L07（71 篇）

- `concept/07_future/00_version_tracking/01_rust_version_tracking.md` — Rust 形式模型演进跟踪（1.79–1.97+）
- `concept/07_future/00_version_tracking/02_editions.md` — Rust Editions（语言版本）
- `concept/07_future/00_version_tracking/03_rust_release_process.md` — Rust 发布流程（Rust Release Process）
- `concept/07_future/00_version_tracking/04_nightly_rust.md` — Rust 的发布流程与 Nightly Rust
- `concept/07_future/00_version_tracking/feature_domain_matrix_197.md` — Rust 1.97.0 特性 × 领域反查矩阵
- `concept/07_future/00_version_tracking/migration_197_decision_tree.md` — Rust 1.97 兼容性迁移判定树
- `concept/07_future/00_version_tracking/rust_1_100_preview.md` — Rust 1.100+ 前沿特性预览
- `concept/07_future/00_version_tracking/rust_1_90_stabilized.md` — Rust 1.90 网络特性参考
- `concept/07_future/00_version_tracking/rust_1_91_stabilized.md` — Rust 1.91 稳定特性
- `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` — Rust 1.92 稳定特性
- `concept/07_future/00_version_tracking/rust_1_93_stabilized.md` — Rust 1.93 稳定特性
- `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` — c10_networks - Rust 1.94 更新概览
- `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` — Rust 1.95.0 稳定特性
- `concept/07_future/00_version_tracking/rust_1_96_stabilized.md` — Rust 1.96 稳定特性（当前 patch 1.96.1）
- `concept/07_future/00_version_tracking/rust_1_97_1.md` — Rust 1.97.1 稳定补丁
- `concept/07_future/00_version_tracking/rust_1_97_preview.md` — Rust 1.97.0 前沿特性预览（已归档）
- `concept/07_future/00_version_tracking/rust_1_97_stabilized.md` — Rust 1.97.0 稳定特性
- `concept/07_future/00_version_tracking/rust_1_98_preview.md` — Rust 1.98+ 前沿特性预览
- `concept/07_future/00_version_tracking/rust_1_98_stabilized.md` — Rust 1.98.0 稳定特性
- `concept/07_future/00_version_tracking/rust_1_99_preview.md` — Rust 1.99+ 前沿特性预览
- `concept/07_future/01_edition_roadmap/01_rust_edition_preview.md` — Rust 2024 Edition (1.85.0+ stable)
- `concept/07_future/01_edition_roadmap/02_edition_guide.md` — Edition 2024 完全指南：新特性与迁移策略
- `concept/07_future/01_edition_roadmap/03_rust_edition_guide.md` — Rust Edition 机制与迁移指南
- `concept/07_future/01_edition_roadmap/04_roadmap.md` — Rust 2027 Edition 及未来路线图
- `concept/07_future/02_preview_features/01_effects_system.md` — Effects System: Concept Pre-study（效果系统：概念预研）
- `concept/07_future/02_preview_features/02_mcdc_coverage_preview.md` — MC/DC Coverage 概念预研：安全关键 Rust 的覆盖率验证
- `concept/07_future/02_preview_features/03_safety_tags_preview.md` — Safety Tags 概念预研：Unsafe 契约的机器可读标注
- `concept/07_future/02_preview_features/04_parallel_frontend_preview.md` — 并行前端编译预研：Rust 编译器的多核扩展
- `concept/07_future/02_preview_features/05_derive_coerce_pointee_preview.md` — 派生 CoercePointee 预研：智能指针的自动类型强制
- `concept/07_future/02_preview_features/06_const_trait_impl_preview.md` — Const Trait Impl 预研：常量上下文中的 Trait 泛化
- … 共 71 篇

### L0_meta（3 篇）

- `concept/sources/INDEX.md` — 权威来源索引库
- `concept/sources/rfc_index.md` — RFC 索引：关键设计提案跟踪
- `concept/sources/theorem_tier_spec.md` — 定理分级规范（Theorem Tier Specification）

## 2. 权威来源覆盖统计

| 来源类别 | 权威主题数 | 已对齐 | 缺口 | 覆盖率 |
|----------|-----------|--------|------|--------|
| formal_verification | 12 | 12 | 0 | 100.0% |
| industrial_ecosystem | 25 | 25 | 0 | 100.0% |
| roadmap | 16 | 16 | 0 | 100.0% |

## 3. 未覆盖空间（按优先级分组）

> 注：以下缺口基于标题/路径关键词匹配，部分可能已被项目文件间接覆盖但标题未体现，需人工复核。

### P0 官方核心（0 项）


### P1 形式化/验证（0 项）


### P2 工业生态（0 项）


### P3 前沿探索（0 项）


## 4. 项目独有主题（权威来源未直接强调）

> 共 488 个 concept 文件未被权威来源主题直接命中。这些多为项目特色的中文学习路径、对比分析、决策树或生态 deep-dive。

- `concept/00_meta/06_trpl_3rd_ed_mapping.md` — TRPL 3rd Ed 章节映射
- `concept/00_meta/07_trpl_3rd_edition_alignment.md` — TRPL 第 3 版对照审计（TRPL 3rd Edition Alignment Audit）
- `concept/00_meta/08_usability_testing_framework.md` — Rust 知识体系可用性测试框架（Usability Testing Framework）
- `concept/00_meta/00_framework/bloom_taxonomy.md` — Bloom Taxonomy（Bloom 分类法）
- `concept/00_meta/00_framework/boundary_extension_tree.md` — Rust 安全边界扩展推理树
- `concept/00_meta/00_framework/cognitive_dimension_matrix.md` — Rust 知识体系双维认知矩阵（Krathwohl × Bloom）
- `concept/00_meta/00_framework/competency_graph.md` — Rust 知识体系能力图谱（Competency Graph）
- `concept/00_meta/00_framework/comprehensive_rust_mapping.md` — Comprehensive Rust 课程映射
- `concept/00_meta/00_framework/concept_definition_decision_forest.md` — Rust 知识体系概念定义判定森林（Concept Definition Decision Forest）
- `concept/00_meta/00_framework/cpp_rust_engineering_roadmap.md` — C/C++ → Rust 工程层对比路线图
- `concept/00_meta/00_framework/decidability_spectrum.md` — Rust 编译期可判定性谱系全景（Decidability Spectrum）
- `concept/00_meta/00_framework/expressiveness_multiview.md` — Rust 语义表达力多视角深化（Multiview Expressiveness Analysis）
- `concept/00_meta/00_framework/fault_tree_analysis_collection.md` — Rust 知识体系失效分析树集（Fault Tree Analysis Collection）
- `concept/00_meta/00_framework/knowledge_mindmap.md` — Rust 知识体系全局思维导图（Knowledge Mindmap）
- `concept/00_meta/00_framework/methodology.md` — 方法论：思维表征与知识结构规范
- `concept/00_meta/00_framework/paradigm_transition_matrix.md` — Rust 范式转换模式矩阵（Paradigm Transition Matrix）
- `concept/00_meta/00_framework/pattern_semantic_space_index.md` — 模式语义空间索引：设计模式在概念体系中的坐标
- `concept/00_meta/00_framework/pl_foundations_roadmap.md` — 通用 PL 基座路线图：Rust 在编程语言坐标系中的位置
- `concept/00_meta/00_framework/semantic_expressiveness.md` — Rust Semantic Expressiveness: A Panoramic Survey（Rust 语义表达力全景梳理）
- `concept/00_meta/00_framework/semantic_space.md` — Rust 表征空间（Semantic / Representational Space）
- `concept/00_meta/00_framework/theorem_inference_forest.md` — Rust 知识体系定理推理森林
- `concept/00_meta/00_framework/theorem_registry.md` — 定理链全局注册表（Theorem Registry）
- `concept/00_meta/00_framework/todos.md` — 全局待办清单（Global TODO Tracker）
- `concept/00_meta/01_terminology/01_terminology_glossary.md` — Rust 核心术语英中对照表
- `concept/00_meta/01_terminology/02_bilingual_template_v2.md` — Concept 文件双语模板 v2（Bilingual Template v2）
- `concept/00_meta/01_terminology/03_bilingual_template.md` — Concept 文件双语模板（Bilingual Template）
- `concept/00_meta/02_sources/01_authority_source_map.md` — 权威来源映射表（Authority Source Map）
- `concept/00_meta/02_sources/02_rustbelt_predicate_map.md` — RustBelt 谓词映射图
- `concept/00_meta/02_sources/03_sources.md` — 权威来源清单与知识来源关系分析
- `concept/00_meta/02_sources/04_topic_authority_alignment_map.md` — 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)
- `concept/00_meta/02_sources/06_external_authority_topic_index.md` — 外部权威来源主题索引（External Authority Topic Index）
- `concept/00_meta/03_audit/01_concept_audit_guide.md` — Concept Audit Guide（概念审计指南）
- `concept/00_meta/03_audit/02_asp_marking_guide.md` — Rust 知识体系 A/S/P 三维认知标记规范
- `concept/00_meta/03_audit/03_audit_checklist.md` — 概念一致性检查清单（Concept Consistency Audit Checklist）
- `concept/00_meta/03_audit/04_concept_consistency_audit_checklist.md` — 概念一致性（Coherence）检查清单
- `concept/00_meta/03_audit/05_template_deduplication_guide.md` — 模板去同质化指南
- `concept/00_meta/03_audit/06_grading_system.md` — 内容分级与受众标签体系
- `concept/00_meta/03_audit/07_quality_dashboard_v2.md` — Rust 知识体系思维表征覆盖率仪表板（Quality Dashboard v2）
- `concept/00_meta/03_audit/08_feature_inventory_methodology.md` — Rust 语言特性盘点方法论
- `concept/00_meta/04_navigation/01_cross_reference_matrix.md` — Cross Reference Matrix（交叉引用矩阵）
- … 共 488 项

## 5. 重复/需合并主题提示

> 检测到 3 对标题高度相似的主题，建议人工复核是否重复。

- `concept/04_formal/00_type_theory/11_formal_design_pattern_theory.md` vs `concept/06_ecosystem/03_design_patterns/11_formal_design_pattern_theory.md` — 形式化设计模式理论 (Formal Design Pattern Theory)
- `concept/04_formal/00_type_theory/12_pattern_composition_algebra.md` vs `concept/06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md` — 模式组合代数：设计模式的结构化关联与冲突分析
- `concept/04_formal/00_type_theory/13_formal_algorithm_theory.md` vs `concept/06_ecosystem/11_domain_applications/12_formal_algorithm_theory.md` — 形式化算法理论
## 6. 维护机制

1. 每季度运行 `python scripts/topic_authority_aligner.py --phase all` 更新本文件。
2. 新缺口优先进入 `reports/TOPIC_ALIGNMENT_AND_GAP_PLAN_*.md` 任务池。
3. 已确认覆盖的缺口从本文件移除或标记为 `verified-covered`。

