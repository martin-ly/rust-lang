# 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)

> **EN**: Topic-Authority Alignment Map
> **Summary**: 维护 Rust 知识库中各概念主题与其权威来源（官方文档、学术论文、工业生态、路线图）之间的对齐关系，确保每个概念有单一可信解释来源。
>
> 生成时间：2026-07-05 05:12
> 工具：`scripts/topic_authority_aligner.py` | 数据来源：Rust 官方文档、形式化/验证生态、工业生态、项目路线图

## 1. 当前项目概念层级（L0-L7）

### L00（62 篇）

- `concept/00_meta/00_framework/03_bloom_taxonomy.md` — Bloom Taxonomy（Bloom 分类法）
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
- `concept/00_meta/00_framework/todos.md` — 全局待办清单（Global TODO Tracker）
- `concept/00_meta/01_terminology/bilingual_template.md` — Concept 文件双语模板（Bilingual Template）
- `concept/00_meta/01_terminology/bilingual_template_v2.md` — Concept 文件双语模板 v2（Bilingual Template v2）
- `concept/00_meta/01_terminology/terminology_glossary.md` — Rust 核心术语英中对照表
- `concept/00_meta/02_sources/authority_source_map.md` — 权威来源映射表（Authority Source Map）
- `concept/00_meta/02_sources/international_authority_index.md` — International Authority Index（国际化权威来源索引）
- `concept/00_meta/02_sources/rustbelt_predicate_map.md` — RustBelt 谓词映射图（RustBelt Predicate Map）
- `concept/00_meta/02_sources/sources.md` — 权威来源清单与知识来源关系分析
- `concept/00_meta/02_sources/topic_authority_alignment_map.md` — 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)
- `concept/00_meta/03_audit/08_concept_audit_guide.md` — Concept Audit Guide（概念审计指南）
- `concept/00_meta/03_audit/asp_marking_guide.md` — Rust 知识体系 A/S/P 三维认知标记规范
- … 共 62 篇

### L01（53 篇）

- `concept/01_foundation/00_start/00_start.md` — Rust 起步指南
- `concept/01_foundation/00_start/06_zero_cost_abstractions.md` — 零成本抽象：Rust 的性能哲学
- `concept/01_foundation/00_start/15_closure_basics.md` — 闭包基础：捕获环境与匿名函数
- `concept/01_foundation/00_start/21_effects_and_purity.md` — 副作用与纯度：从引用透明到 Rust 的所有权效果
- `concept/01_foundation/00_start/34_pl_prerequisites.md` — 编程语言理论基础（PL Prerequisites）
- `concept/01_foundation/00_start/36_keywords.md` — Rust 关键字（Keywords）
- `concept/01_foundation/00_start/37_operators_and_symbols.md` — Rust 运算符与符号（Operators and Symbols）
- `concept/01_foundation/00_start/47_std_io_and_process.md` — 标准 I/O 与进程（std I/O and Process）
- `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` — Ownership（所有权）
- `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` — Borrowing（借用）
- `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` — Lifetimes（生命周期）
- `concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md` — Move 语义：C++ 与 Rust 的资源转移模型
- `concept/01_foundation/01_ownership_borrow_lifetime/28_ownership_inventories_brown_book.md` — 所有权清单自测：Brown University Ownership Inventory
- `concept/01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md` — Lifetimes 高级主题
- `concept/01_foundation/02_type_system/04_type_system.md` — Type System Basics（类型系统基础）
- `concept/01_foundation/02_type_system/10_numerics.md` — 数值类型与运算：从整数到浮点的完整图景
- `concept/01_foundation/02_type_system/14_coercion_and_casting.md` — 类型强制与转换：显式与隐式的边界
- `concept/01_foundation/02_type_system/22_data_abstraction_spectrum.md` — 数据抽象谱系：从 C struct 到 Rust enum + trait
- `concept/01_foundation/02_type_system/31_never_type.md` — Never Type (`!`)：底类型与穷尽性
- `concept/01_foundation/03_values_and_references/05_reference_semantics.md` — 引用语义：自动解引用、Deref 强制与类型转换
- `concept/01_foundation/03_values_and_references/19_value_vs_reference_semantics.md` — 值语义 vs 引用语义：从 C++、Java、Python 到 Rust
- `concept/01_foundation/03_values_and_references/20_variable_model.md` — 变量模型：从通用 PL 视角看 Rust 的所有权
- `concept/01_foundation/04_control_flow/07_control_flow.md` — 控制流：表达式导向的流程控制
- `concept/01_foundation/04_control_flow/40_patterns.md` — 模式匹配（Patterns）
- `concept/01_foundation/04_control_flow/41_statements_and_expressions.md` — 语句与表达式（Statements and Expressions）
- `concept/01_foundation/05_collections/08_collections.md` — 集合类型：Rust 标准库的数据结构谱系
- `concept/01_foundation/05_collections/17_collections_advanced.md` — 高级集合类型：BTreeMap、VecDeque、BinaryHeap 与自定义 Hasher 深度分析
- `concept/01_foundation/06_strings_and_text/09_strings_and_text.md` — 字符串与文本：Rust 的 Unicode 处理与格式化系统
- `concept/01_foundation/06_strings_and_text/18_strings_and_encoding.md` — 字符串与编码：Rust 的文本处理类型系统
- `concept/01_foundation/06_strings_and_text/46_formatting_and_display.md` — 格式化与显示（Display and Debug Formatting）
- … 共 53 篇

### L02（36 篇）

- `concept/02_intermediate/00_traits/01_traits.md` — Traits（Trait 系统）
- `concept/02_intermediate/00_traits/09_serde_patterns.md` — Serde 序列化模式：Rust 的类型驱动数据转换
- `concept/02_intermediate/00_traits/18_lifetimes_advanced.md` — 生命周期高级主题：从 HRTB 到自引用类型
- `concept/02_intermediate/00_traits/19_advanced_traits.md` — 高级 Trait 主题：从关联类型到特化
- `concept/02_intermediate/00_traits/28_construction_and_initialization.md` — 构造与初始化：C++ 的构造函数 vs Rust 的结构体字面量
- `concept/02_intermediate/00_traits/31_derive_traits.md` — 可派生 Trait（Derive Traits）
- `concept/02_intermediate/00_traits/32_editions.md` — Rust Editions（语言版本）
- `concept/02_intermediate/00_traits/33_rust_release_process.md` — Rust 发布流程（Rust Release Process）
- `concept/02_intermediate/01_generics/02_generics.md` — Generics（泛型系统）
- `concept/02_intermediate/01_generics/23_quiz_traits_and_generics.md` — 测验：Trait 与泛型（试点扩展）
- `concept/02_intermediate/02_memory_management/03_memory_management.md` — Memory Management（内存管理）
- `concept/02_intermediate/02_memory_management/08_interior_mutability.md` — 内部可变性：编译期规则的运行时逃逸
- `concept/02_intermediate/02_memory_management/11_cow_and_borrowed.md` — Cow：写时克隆与零拷贝抽象
- `concept/02_intermediate/02_memory_management/12_smart_pointers.md` — 智能指针：堆内存管理与共享语义
- `concept/02_intermediate/02_memory_management/24_quiz_memory_management.md` — 测验：内存管理（L2 试点扩展）
- `concept/02_intermediate/03_error_handling/04_error_handling.md` — Error Handling（错误处理）
- `concept/02_intermediate/03_error_handling/16_error_handling_deep_dive.md` — 错误处理深入：从 Result 到自定义错误生态
- `concept/02_intermediate/03_error_handling/27_exception_safety_rust_cpp.md` — 异常安全：C++ 与 Rust 的错误处理哲学
- `concept/02_intermediate/04_types_and_conversions/06_range_types.md` — Rust 范围类型语义：`std::ops::Range` → `core::range`
- `concept/02_intermediate/04_types_and_conversions/07_closure_types.md` — 闭包类型系统：Fn、FnMut、FnOnce 的捕获语义
- `concept/02_intermediate/04_types_and_conversions/14_newtype_and_wrapper.md` — Newtype 与包装器模式：类型安全的零成本抽象
- `concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md` — 高级类型系统：从关联类型到类型级编程
- `concept/02_intermediate/04_types_and_conversions/25_rtti_and_dynamic_typing.md` — RTTI 与动态类型识别：从 C++ 到 Rust
- `concept/02_intermediate/04_types_and_conversions/35_unions.md` — 联合体（Unions）
- `concept/02_intermediate/04_types_and_conversions/37_type_conversions.md` — 类型转换（Type Conversions）
- `concept/02_intermediate/05_modules_and_visibility/10_module_system.md` — 模块系统：Rust 的代码组织与可见性规则
- `concept/02_intermediate/05_modules_and_visibility/22_api_naming_conventions.md` — Rust API 命名约定
- `concept/02_intermediate/05_modules_and_visibility/29_friend_vs_module_privacy.md` — 友元 vs 模块可见性：C++ 的 `friend` 与 Rust 的隐私边界
- `concept/02_intermediate/06_macros_and_metaprogramming/05_assert_matches.md` — `assert_matches!`：模式匹配断言的形式化语义
- `concept/02_intermediate/06_macros_and_metaprogramming/13_dsl_and_embedding.md` — DSL 与嵌入 式设计：Rust 中的领域特定语言
- … 共 36 篇

### L03（37 篇）

- `concept/03_advanced/00_concurrency/01_concurrency.md` — Concurrency（并发模型）
- `concept/03_advanced/00_concurrency/10_concurrency_patterns.md` — 并发 模式：从消息 传递到锁自由的数据结构
- `concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md` — 原子操作与内存序：无锁并发的精确控制
- `concept/03_advanced/00_concurrency/16_lock_free.md` — 无锁编程与内存模型
- `concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md` — 并行与分布式模式谱系：从线程池到共识算法
- `concept/03_advanced/00_concurrency/21_quiz_concurrency_async.md` — 测验：并发与异步（L3 试点扩展）
- `concept/03_advanced/01_async/02_async.md` — Async/Await（异步编程）
- `concept/03_advanced/01_async/06_pin_unpin.md` — Pin 与 Unpin：自引用类型的不动性保证
- `concept/03_advanced/01_async/24_async_closures.md` — Async Closures（异步闭包）
- `concept/03_advanced/01_async/25_async_advanced.md` — Async/Await 高级主题
- `concept/03_advanced/01_async/26_async_patterns.md` — 异步模式：从 Future 到生产级并发
- `concept/03_advanced/02_unsafe/00_before_formal.md` — 是否需要进入 L4 形式化层？
- `concept/03_advanced/02_unsafe/03_unsafe.md` — Unsafe Rust 安全编程
- `concept/03_advanced/02_unsafe/08_nll_and_polonius.md` — NLL 与 Polonius：借用检查器的演进
- `concept/03_advanced/02_unsafe/12_unsafe_rust_patterns.md` — Unsafe Rust 模式：安全抽象的核心技术
- `concept/03_advanced/02_unsafe/22_quiz_unsafe.md` — 测验：Unsafe Rust（L3 试点扩展）
- `concept/03_advanced/02_unsafe/29_memory_model.md` — Rust 内存模型（Memory Model）
- `concept/03_advanced/02_unsafe/30_rust_runtime.md` — Rust 运行时（The Rust Runtime）
- `concept/03_advanced/02_unsafe/31_panic.md` — Panic 机制
- `concept/03_advanced/02_unsafe/35_unsafe_reference.md` — Unsafe 参考（Unsafe Reference）
- `concept/03_advanced/03_proc_macros/04_macros.md` — Macros（宏系统）
- `concept/03_advanced/03_proc_macros/07_proc_macro.md` — 过程宏：编译期代码生成的元编程工具
- `concept/03_advanced/03_proc_macros/23_quiz_macros.md` — 测验：宏系统（L3 试点扩展）
- `concept/03_advanced/03_proc_macros/28_conditional_compilation.md` — 条件编译（Conditional Compilation）
- `concept/03_advanced/04_ffi/05_rust_ffi.md` — Rust FFI：与外部代码的安全边界
- `concept/03_advanced/04_ffi/09_ffi_advanced.md` — FFI 高级主题：跨语言边界的安全与性能
- `concept/03_advanced/04_ffi/27_linkage.md` — Linkage（链接）
- `concept/03_advanced/05_inline_assembly/13_inline_assembly.md` — 内联汇编 (Inline Assembly)
- `concept/03_advanced/06_low_level_patterns/14_custom_allocators.md` — 自定义分配器与内存布局优化
- `concept/03_advanced/06_low_level_patterns/15_zero_copy_parsing.md` — 零拷贝解析与序列化优化
- … 共 37 篇

### L04（51 篇）

- `concept/04_formal/00_type_theory/02_type_theory.md` — Type Theory（类型论基础）
- `concept/04_formal/00_type_theory/06_subtype_variance.md` — 子类型与变型：Rust 类型系统中的协变、逆变与不变
- `concept/04_formal/00_type_theory/08_type_inference.md` — 类型推断：Hindley-Milner 算法与 Rust 的工业实现
- `concept/04_formal/00_type_theory/10_category_theory.md` — 范畴论与 Rust：从函子到单子
- `concept/04_formal/00_type_theory/14_lambda_calculus.md` — Lambda 演算与 Rust 计算模型
- `concept/04_formal/00_type_theory/21_type_semantics.md` — Type Semantics（类型语义）
- `concept/04_formal/00_type_theory/27_type_checking_and_inference.md` — rustc 类型检查与类型推断
- `concept/04_formal/00_type_theory/29_type_inference_complexity.md` — Type Inference Complexity（类型推断复杂度）
- `concept/04_formal/00_type_theory/50_type_system_reference.md` — 类型系统参考（Type System Reference）
- `concept/04_formal/01_ownership_logic/01_linear_logic.md` — Linear Logic & Affine Logic（线性逻辑与仿射逻辑）
- `concept/04_formal/01_ownership_logic/03_ownership_formal.md` — Ownership Formalization（所有权形式化）
- `concept/04_formal/01_ownership_logic/09_linear_logic_applications.md` — 线性逻辑在 Rust 中的工程应用
- `concept/04_formal/01_ownership_logic/28_borrow_checking_decidability.md` — Borrow Checking Decidability（借用检查可判定性）
- `concept/04_formal/01_ownership_logic/36_tree_borrows_deep_dive.md` — Tree Borrows 深度解析
- `concept/04_formal/01_ownership_logic/37_behavior_considered_undefined.md` — 未定义行为清单（Behavior Considered Undefined）
- `concept/04_formal/02_separation_logic/04_rustbelt.md` — RustBelt & Verification Toolchain（RustBelt 与验证工具链）
- `concept/04_formal/02_separation_logic/11_separation_logic.md` — 分离逻辑：Rust 所有权的形式化根基
- `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` — Safety Tags（安全标签）
- `concept/04_formal/02_separation_logic/34_borrow_sanitizer_in_formal.md` — BorrowSanitizer 运行时别名模型检测
- `concept/04_formal/03_operational_semantics/12_denotational_semantics.md` — 指称语义与领域理论
- `concept/04_formal/03_operational_semantics/15_hoare_logic.md` — Hoare 逻辑：程序验证的形式化基础与 Rust 契约
- `concept/04_formal/03_operational_semantics/17_operational_semantics.md` — 操作语义：程序行为的形式化定义
- `concept/04_formal/03_operational_semantics/18_evaluation_strategies.md` — 求值策略：Call-by-Value, Call-by-Name, Call-by-Need
- `concept/04_formal/03_operational_semantics/20_axiomatic_semantics.md` — Axiomatic Semantics（公理语义）
- `concept/04_formal/03_operational_semantics/30_aeneas_symbolic_semantics.md` — Aeneas Symbolic Semantics（Aeneas 符号化语义）
- `concept/04_formal/03_operational_semantics/39_constant_evaluation.md` — 常量求值（Constant Evaluation）
- `concept/04_formal/04_model_checking/05_verification_toolchain.md` — Verification Toolchain Selection Guide（验证工具链选择指南）
- `concept/04_formal/04_model_checking/13_formal_methods.md` — 形式化方法在 Rust 中的应用
- `concept/04_formal/04_model_checking/16_aerospace_certification_formal_methods.md` — 航空航天认证与形式化方法 (Aerospace Certification & Formal Methods)
- `concept/04_formal/04_model_checking/22_modern_verification_tools.md` — 现代 Rust 验证工具生态（2025-2026）
- … 共 51 篇

### L05（19 篇）

- `concept/05_comparative/00_paradigms/03_paradigm_matrix.md` — Paradigm Matrix: Multi-Language Formal Comparison（多语言范式对比矩阵）
- `concept/05_comparative/00_paradigms/05_execution_model_isomorphism.md` — Rust 执行模型同构性矩阵：同步 · 异步 · 并发 · 并行
- `concept/05_comparative/00_paradigms/16_cpp_rust_surface_features.md` — C++ vs Rust：构造、运算符、RTTI、友元
- `concept/05_comparative/01_systems_languages/01_rust_vs_cpp.md` — Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>
- `concept/05_comparative/01_systems_languages/02_rust_vs_go.md` — Rust vs Go：线性所有权 vs CSP 过程逻辑
- `concept/05_comparative/01_systems_languages/09_rust_vs_swift.md` — Rust vs Swift：现代系统语言的两种路径
- `concept/05_comparative/01_systems_languages/10_rust_vs_zig.md` — Rust vs Zig：现代系统语言的两种哲学
- `concept/05_comparative/01_systems_languages/18_cpp_abi_object_model.md` — Rust vs C++：ABI、对象模型与内存布局
- `concept/05_comparative/01_systems_languages/19_rust_vs_ruby.md` — Rust vs Ruby：性能与表达力的两极
- `concept/05_comparative/02_managed_languages/06_rust_vs_java.md` — Rust vs Java：系统编程与托管运行时的范式对比
- `concept/05_comparative/02_managed_languages/07_rust_vs_python.md` — Rust vs Python：系统编程与动态脚本的对照分析
- `concept/05_comparative/02_managed_languages/08_rust_vs_javascript.md` — Rust vs JavaScript：系统编程与脚本执行的范式差异
- `concept/05_comparative/02_managed_languages/11_rust_vs_kotlin.md` — Rust vs Kotlin：静态安全的两种路径
- `concept/05_comparative/02_managed_languages/12_rust_vs_scala.md` — Rust vs Scala：类型系统的两种哲学
- `concept/05_comparative/02_managed_languages/13_rust_vs_csharp.md` — Rust vs C#：托管与原生之路
- `concept/05_comparative/02_managed_languages/14_rust_vs_elixir.md` — Rust vs Elixir 对比分析
- `concept/05_comparative/02_managed_languages/15_rust_vs_typescript.md` — Rust vs TypeScript：静态类型系统的两种哲学 —— 编译期证明与渐进式工程
- `concept/05_comparative/03_domain_comparisons/04_safety_boundaries.md` — Rust 安全保证的边界条件全景（Safety Boundary Panorama）
- `concept/05_comparative/03_domain_comparisons/17_quiz_rust_vs_systems.md` — 测验：Rust vs 系统编程语言（L5 试点扩展）

### L06（86 篇）

- `concept/06_ecosystem/00_toolchain/01_toolchain.md` — Toolchain（工具链与 Cargo）
- `concept/06_ecosystem/00_toolchain/13_logging_observability.md` — 日志与可观测性：Rust 服务端监控生态
- `concept/06_ecosystem/00_toolchain/28_devops_and_ci_cd.md` — DevOps 与 CI/CD：Rust 的持续交付工程实践
- `concept/06_ecosystem/00_toolchain/45_compiler_internals.md` — Rust 编译器内部原理
- `concept/06_ecosystem/00_toolchain/47_compiler_infrastructure.md` — Rust 编译器基础设施深度解析
- `concept/06_ecosystem/00_toolchain/57_quiz_toolchain.md` — 测验：Rust 工具链（L6 试点扩展）
- `concept/06_ecosystem/00_toolchain/58_platform_rust_integration.md` — 将 Rust 集成到现有平台
- `concept/06_ecosystem/00_toolchain/67_llvm_backend_and_codegen.md` — Rust 编译器的 LLVM 后端与代码生成
- `concept/06_ecosystem/00_toolchain/68_rustc_driver_and_stable_mir.md` — rustc Driver、Interface 与 Stable MIR
- `concept/06_ecosystem/00_toolchain/69_compiler_diagnostics_and_ui_tests.md` — rustc 编译器诊断与 UI Tests
- `concept/06_ecosystem/00_toolchain/70_rustc_bootstrap.md` — rustc 自举（Bootstrap）
- `concept/06_ecosystem/00_toolchain/71_compiler_testing.md` — rustc 编译器测试体系
- `concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md` — Rustdoc 1.96 变更
- `concept/06_ecosystem/00_toolchain/79_development_tools.md` — Rust 常用开发工具
- `concept/06_ecosystem/01_cargo/09_cargo_script.md` — Cargo Script 脚本化 Rust
- `concept/06_ecosystem/01_cargo/10_public_private_deps.md` — Cargo 公共与私有依赖
- `concept/06_ecosystem/01_cargo/59_cargo_build_scripts.md` — Cargo Build Scripts（`build.rs`）
- `concept/06_ecosystem/01_cargo/60_cargo_dependency_resolution.md` — Cargo 依赖解析
- `concept/06_ecosystem/01_cargo/61_cargo_source_replacement.md` — Cargo Source Replacement 与 Vendoring
- `concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md` — Cargo Registry 与包发布
- `concept/06_ecosystem/01_cargo/63_cargo_authentication_and_cache.md` — Cargo 认证与构建缓存
- `concept/06_ecosystem/01_cargo/64_cargo_manifest_reference.md` — Cargo Manifest 参考速查
- `concept/06_ecosystem/01_cargo/65_cargo_profiles_and_lints.md` — Cargo Profiles 与 Lints
- `concept/06_ecosystem/01_cargo/66_cargo_subcommands_and_plugins.md` — Cargo 子命令与插件生态
- `concept/06_ecosystem/01_cargo/72_cargo_security_cves.md` — Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223
- `concept/06_ecosystem/01_cargo/76_cargo_196_features.md` — Cargo 1.96 新特性与工具链变更
- `concept/06_ecosystem/01_cargo/78_cargo_workspaces.md` — Cargo Workspaces（工作区）
- `concept/06_ecosystem/01_cargo/80_cargo_getting_started.md` — Cargo 入门（Cargo Getting Started）
- `concept/06_ecosystem/01_cargo/81_cargo_workflow.md` — Cargo 工作流（Cargo Workflow）
- `concept/06_ecosystem/01_cargo/82_cargo_guide_practices.md` — Cargo 指南实践（Cargo Guide Practices）
- … 共 86 篇

### L07（54 篇）

- `concept/07_future/00_version_tracking/05_rust_version_tracking.md` — Rust 形式模型演进跟踪（1.79–1.97+）
- `concept/07_future/00_version_tracking/50_nightly_rust.md` — Rust 的发布流程与 Nightly Rust
- `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` — Rust 1.95.0 稳定特性
- `concept/07_future/00_version_tracking/rust_1_96_stabilized.md` — Rust 1.96 稳定特性（当前 patch 1.96.1）
- `concept/07_future/00_version_tracking/rust_1_97_preview.md` — Rust 1.97.0 前沿特性预览（Beta）
- `concept/07_future/00_version_tracking/rust_1_97_stabilized.md` — Rust 1.97.0 稳定特性
- `concept/07_future/00_version_tracking/rust_1_98_preview.md` — Rust 1.98+ 前沿特性预览
- `concept/07_future/01_edition_roadmap/19_rust_edition_preview.md` — Rust 2024 Edition (1.85.0+ stable)
- `concept/07_future/01_edition_roadmap/23_rust_edition_guide.md` — Rust Edition 机制与迁移指南
- `concept/07_future/01_edition_roadmap/44_edition_guide.md` — Edition 2024 完全指南：新特性与迁移策略
- `concept/07_future/02_stabilized_features/borrow_sanitizer.md` — BorrowSanitizer：动态别名规则验证工具
- `concept/07_future/03_preview_features/04_effects_system.md` — Effects System: Concept Pre-study（效果系统：概念预研）
- `concept/07_future/03_preview_features/07_mcdc_coverage_preview.md` — MC/DC Coverage 概念预研：安全关键 Rust 的覆盖率验证
- `concept/07_future/03_preview_features/08_safety_tags_preview.md` — Safety Tags 概念预研：Unsafe 契约的机器可读标注
- `concept/07_future/03_preview_features/09_parallel_frontend_preview.md` — 并行 前端编译预研：Rust 编译器 的多核扩展
- `concept/07_future/03_preview_features/10_derive_coerce_pointee_preview.md` — 派生 CoercePointee 预研：智能指针的自动类型强制
- `concept/07_future/03_preview_features/11_const_trait_impl_preview.md` — Const Trait Impl 预研：常量上下文中的 Trait 泛化
- `concept/07_future/03_preview_features/12_return_type_notation_preview.md` — Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界
- `concept/07_future/03_preview_features/13_unsafe_fields_preview.md` — Unsafe Fields 预研：字段级安全边界的精确标注
- `concept/07_future/03_preview_features/14_lifetime_capture_preview.md` — Lifetime Capture in `impl Trait` Preview
- `concept/07_future/03_preview_features/15_pin_ergonomics_preview.md` — Pin Ergonomics 与 Reborrow Traits 预研：超越 `Pin::as_mut`
- `concept/07_future/03_preview_features/16_type_alias_impl_trait_preview.md` — TAIT Preview
- `concept/07_future/03_preview_features/17_const_trait_preview.md` — Const Trait 实现预览
- `concept/07_future/03_preview_features/18_async_drop_preview.md` — Async Drop：异步资源的优雅销毁
- `concept/07_future/03_preview_features/20_borrowsanitizer_preview.md` — BorrowSanitizer 概念预研：运行时借用检查工业化
- `concept/07_future/03_preview_features/22_gen_blocks_preview.md` — Generator Blocks（gen）预览
- `concept/07_future/03_preview_features/25_open_enums_preview.md` — Open Enums 概念预研：从 `#[non_exhaustive]` 到可扩展枚举
- `concept/07_future/03_preview_features/26_specialization_preview.md` — Specialization：Trait 实现的精确化与重叠解析
- `concept/07_future/03_preview_features/27_compile_time_execution.md` — 编译期执行与常量求值
- `concept/07_future/03_preview_features/30_stable_abi_preview.md` — Stable ABI Preview
- … 共 54 篇

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

> 共 357 个 concept 文件未被权威来源主题直接命中。这些多为项目特色的中文学习路径、对比分析、决策树或生态 deep-dive。

- `concept/00_meta/00_framework/03_bloom_taxonomy.md` — Bloom Taxonomy（Bloom 分类法）
- `concept/00_meta/00_framework/boundary_extension_tree.md` — Rust 安全边界扩展推理树
- `concept/00_meta/00_framework/cognitive_dimension_matrix.md` — Rust 知识体系双维认知矩阵（Krathwohl × Bloom）
- `concept/00_meta/00_framework/competency_graph.md` — Rust 知识体系能力图谱（Competency Graph）
- `concept/00_meta/00_framework/comprehensive_rust_mapping.md` — Comprehensive Rust 课程映射
- `concept/00_meta/00_framework/concept_definition_decision_forest.md` — Rust 知识体系概念定义判定森林（Concept Definition Decision Forest）
- `concept/00_meta/00_framework/cpp_rust_engineering_roadmap.md` — C/C++ → Rust 工程层对比路线图
- `concept/00_meta/00_framework/decidability_spectrum.md` — Rust 编译期可判定性谱系全景（Decidability Spectrum）
- `concept/00_meta/00_framework/expressiveness_multiview.md` — Rust 语义表达力多视角深化（Multiview Expressiveness Analysis）
- `concept/00_meta/00_framework/fault_tree_analysis_collection.md` — Rust 知识体系失效分析树集（Fault Tree Analysis Collection）
- `concept/00_meta/00_framework/methodology.md` — 方法论：思维表征与知识结构规范
- `concept/00_meta/00_framework/paradigm_transition_matrix.md` — Rust 范式转换模式矩阵（Paradigm Transition Matrix）
- `concept/00_meta/00_framework/pattern_semantic_space_index.md` — 模式语义空间索引：设计模式在概念体系中的坐标
- `concept/00_meta/00_framework/pl_foundations_roadmap.md` — 通用 PL 基座路线图：Rust 在编程语言坐标系中的位置
- `concept/00_meta/00_framework/semantic_expressiveness.md` — Rust Semantic Expressiveness: A Panoramic Survey（Rust 语义表达力全景梳理）
- `concept/00_meta/00_framework/semantic_space.md` — Rust 表征空间（Semantic / Representational Space）
- `concept/00_meta/00_framework/theorem_inference_forest.md` — Rust 知识体系定理推理森林
- `concept/00_meta/00_framework/todos.md` — 全局待办清单（Global TODO Tracker）
- `concept/00_meta/01_terminology/bilingual_template.md` — Concept 文件双语模板（Bilingual Template）
- `concept/00_meta/01_terminology/bilingual_template_v2.md` — Concept 文件双语模板 v2（Bilingual Template v2）
- `concept/00_meta/01_terminology/terminology_glossary.md` — Rust 核心术语英中对照表
- `concept/00_meta/02_sources/authority_source_map.md` — 权威来源映射表（Authority Source Map）
- `concept/00_meta/02_sources/rustbelt_predicate_map.md` — RustBelt 谓词映射图（RustBelt Predicate Map）
- `concept/00_meta/02_sources/sources.md` — 权威来源清单与知识来源关系分析
- `concept/00_meta/02_sources/topic_authority_alignment_map.md` — 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)
- `concept/00_meta/03_audit/08_concept_audit_guide.md` — Concept Audit Guide（概念审计指南）
- `concept/00_meta/03_audit/asp_marking_guide.md` — Rust 知识体系 A/S/P 三维认知标记规范
- `concept/00_meta/03_audit/audit_checklist.md` — 概念一致性检查清单（Concept Consistency Audit Checklist）
- `concept/00_meta/03_audit/concept_consistency_audit_checklist.md` — 概念一致性（Coherence）检查清单
- `concept/00_meta/03_audit/grading_system.md` — 内容分级与受众标签体系
- `concept/00_meta/03_audit/quality_dashboard_v2.md` — Rust 知识体系思维表征覆盖率仪表板（Quality Dashboard v2）
- `concept/00_meta/03_audit/template_deduplication_guide.md` — 模板去同质化指南
- `concept/00_meta/04_navigation/05_cross_reference_matrix.md` — Cross Reference Matrix（交叉引用矩阵）
- `concept/00_meta/04_navigation/career_landscape.md` — Rust 职业市场全景：2026 年数据与分析
- `concept/00_meta/04_navigation/concept_index.md` — 全局概念索引（Concept Index）
- `concept/00_meta/04_navigation/foundations_gap_closure_index.md` — 基础知识缺口补全总索引
- `concept/00_meta/04_navigation/inter_layer_map.md` — 跨层知识图谱（Inter-Layer Dependency Map）
- `concept/00_meta/04_navigation/inter_layer_topology.md` — Rust 知识体系跨层依赖与蕴含拓扑图
- `concept/00_meta/04_navigation/intra_layer_model_map.md` — Rust 知识体系层次内模型间映射图
- `concept/00_meta/04_navigation/learning_mvp_path.md` — MVP 学习路径：从零到多线程 CLI（40 小时）
- … 共 357 项

## 5. 重复/需合并主题提示

> 未检测到明显标题重复。

## 6. 维护机制

1. 每季度运行 `python scripts/topic_authority_aligner.py --phase all` 更新本文件。
2. 新缺口优先进入 `reports/TOPIC_ALIGNMENT_AND_GAP_PLAN_*.md` 任务池。
3. 已确认覆盖的缺口从本文件移除或标记为 `verified-covered`。
