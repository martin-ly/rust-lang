# 主题-权威来源对齐图谱 (Topic-Authority Alignment Map)
>
> 生成时间：2026-07-02 03:29
> 工具：`scripts/topic_authority_aligner.py` | 数据来源：Rust 官方文档、形式化/验证生态、工业生态、项目路线图

## 1. 当前项目概念层级（L0-L7）

### L00（50 篇）

- `concept/00_meta/03_bloom_taxonomy.md` — Bloom Taxonomy（Bloom 分类法）
- `concept/00_meta/05_cross_reference_matrix.md` — Cross Reference Matrix（交叉引用矩阵）
- `concept/00_meta/08_concept_audit_guide.md` — Concept Audit Guide（概念审计指南）
- `concept/00_meta/asp_marking_guide.md` — Rust 知识体系 A/S/P 三维认知标记规范
- `concept/00_meta/audit_checklist.md` — 概念一致性检查清单（Concept Consistency Audit Checklist）
- `concept/00_meta/authority_source_map.md` — 权威来源映射表（Authority Source Map）
- `concept/00_meta/bilingual_template.md` — Concept 文件双语模板（Bilingual Template）
- `concept/00_meta/boundary_extension_tree.md` — Rust 安全边界扩展推理树
- `concept/00_meta/career_landscape.md` — Rust 职业市场全景：2026 年数据与分析
- `concept/00_meta/cognitive_dimension_matrix.md` — Rust 知识体系双维认知矩阵（Krathwohl × Bloom）
- `concept/00_meta/competency_graph.md` — Rust 知识体系能力图谱（Competency Graph）
- `concept/00_meta/comprehensive_rust_mapping.md` — Comprehensive Rust 课程映射
- `concept/00_meta/concept_consistency_audit_checklist.md` — 概念一致性（Coherence）检查清单
- `concept/00_meta/concept_definition_decision_forest.md` — Rust 知识体系概念定义判定森林（Concept Definition Decision Forest）
- `concept/00_meta/concept_index.md` — 全局概念索引（Concept Index）
- `concept/00_meta/cpp_rust_engineering_roadmap.md` — C/C++ → Rust 工程层对比路线图
- `concept/00_meta/decidability_spectrum.md` — Rust 编译期可判定性谱系全景（Decidability Spectrum）
- `concept/00_meta/expressiveness_multiview.md` — Rust 语义表达力多视角深化（Multiview Expressiveness Analysis）
- `concept/00_meta/fault_tree_analysis_collection.md` — Rust 知识体系失效分析树集（Fault Tree Analysis Collection）
- `concept/00_meta/foundations_gap_closure_index.md` — 基础知识缺口补全总索引
- `concept/00_meta/grading_system.md` — 内容分级与受众标签体系
- `concept/00_meta/inter_layer_map.md` — 跨层知识图谱（Inter-Layer Dependency Map）
- `concept/00_meta/inter_layer_topology.md` — Rust 知识体系跨层依赖与蕴含拓扑图
- `concept/00_meta/intra_layer_model_map.md` — Rust 知识体系层次内模型间映射图
- `concept/00_meta/kg_ontology_v2.md` — Rust 知识体系知识图谱本体规范（Knowledge Graph Ontology）
- `concept/00_meta/kg_ontology_v2.md` — Rust 知识体系知识图谱本体规范 v2.0（RDF 1.2 / RDF-star / SKOS 对齐版）
- `concept/00_meta/kg_tlo_alignment.md` — Rust 知识体系顶层本体（TLO）对齐
- `concept/00_meta/knowledge_mindmap.md` — Rust 知识体系全局思维导图（Knowledge Mindmap）
- `concept/00_meta/learning_guide.md` — Rust 知识体系学习指南（Learning Guide）
- `concept/00_meta/learning_mvp_path.md` — MVP 学习路径：从零到多线程 CLI（40 小时）
- … 共 50 篇

### L01（35 篇）

- `concept/01_foundation/00_pl_prerequisites.md` — 编程语言理论基础（PL Prerequisites）
- `concept/01_foundation/00_start.md` — Rust 起步指南
- `concept/01_foundation/01_ownership.md` — Ownership（所有权）
- `concept/01_foundation/02_borrowing.md` — Borrowing（借用）
- `concept/01_foundation/03_lifetimes.md` — Lifetimes（生命周期）
- `concept/01_foundation/03_lifetimes_advanced.md` — Lifetimes 高级主题
- `concept/01_foundation/04_type_system.md` — Type System Basics（类型系统基础）
- `concept/01_foundation/05_never_type.md` — Never Type (`!`)：底类型与穷尽性
- `concept/01_foundation/05_reference_semantics.md` — 引用语义：自动解引用、Deref 强制与类型转换
- `concept/01_foundation/06_zero_cost_abstractions.md` — 零成本抽象：Rust 的性能哲学
- `concept/01_foundation/07_control_flow.md` — 控制流：表达式导向的流程控制
- `concept/01_foundation/08_collections.md` — 集合类型：Rust 标准库的数据结构谱系
- `concept/01_foundation/09_strings_and_text.md` — 字符串与文本：Rust 的 Unicode 处理与格式化系统
- `concept/01_foundation/32_error_handling_basics.md` — Rust 错误处理基础
- `concept/01_foundation/10_numerics.md` — 数值类型与运算：从整数到浮点的完整图景
- `concept/01_foundation/11_modules_and_paths.md` — 模块系统与路径：Rust 的代码组织哲学
- `concept/01_foundation/12_attributes_and_macros.md` — 属性与声明宏：编译期元编程基础
- `concept/01_foundation/13_panic_and_abort.md` — Panic 与 Abort：不可恢复错误的处理机制
- `concept/01_foundation/14_coercion_and_casting.md` — 类型强制与转换：显式与隐式的边界
- `concept/01_foundation/15_closure_basics.md` — 闭包基础：捕获环境与匿名函数
- `concept/01_foundation/16_testing_basics.md` — 测试基础：从单元测试到集成测试
- `concept/01_foundation/17_collections_advanced.md` — 高级集合类型：BTreeMap、VecDeque、BinaryHeap 与自定义 Hasher 深度分析
- `concept/01_foundation/18_strings_and_encoding.md` — 字符串与编码：Rust 的文本处理类型系统
- `concept/01_foundation/19_value_vs_reference_semantics.md` — 值语义 vs 引用语义：从 C++、Java、Python 到 Rust
- `concept/01_foundation/20_variable_model.md` — 变量模型：从通用 PL 视角看 Rust 的所有权
- `concept/01_foundation/21_effects_and_purity.md` — 副作用与纯度：从引用透明到 Rust 的所有权效果
- `concept/01_foundation/22_data_abstraction_spectrum.md` — 数据抽象谱系：从 C struct 到 Rust enum + trait
- `concept/01_foundation/23_move_semantics.md` — Move 语义：C++ 与 Rust 的资源转移模型
- `concept/01_foundation/33_quiz_ownership_borrowing.md` — 测验：所有权、借用与生命周期（试点）
- `concept/01_foundation/24_quiz_type_system.md` — 测验：类型系统（试点扩展）
- … 共 35 篇

### L02（30 篇）

- `concept/02_intermediate/01_traits.md` — Traits（Trait 系统）
- `concept/02_intermediate/02_generics.md` — Generics（泛型系统）
- `concept/02_intermediate/03_memory_management.md` — Memory Management（内存管理）
- `concept/02_intermediate/04_error_handling.md` — Error Handling（错误处理）
- `concept/02_intermediate/05_assert_matches.md` — `assert_matches!`：模式匹配断言的形式化语义
- `concept/02_intermediate/06_range_types.md` — Rust 范围类型语义：`std::ops::Range` → `core::range`
- `concept/02_intermediate/07_closure_types.md` — 闭包类型系统：Fn、FnMut、FnOnce 的捕获语义
- `concept/02_intermediate/08_interior_mutability.md` — 内部可变性：编译期规则的运行时逃逸
- `concept/02_intermediate/09_serde_patterns.md` — Serde 序列化模式：Rust 的类型驱动数据转换
- `concept/02_intermediate/10_module_system.md` — 模块系统：Rust 的代码组织与可见性规则
- `concept/02_intermediate/11_cow_and_borrowed.md` — Cow：写时克隆与零拷贝抽象
- `concept/02_intermediate/12_smart_pointers.md` — 智能指针：堆内存管理与共享语义
- `concept/02_intermediate/13_dsl_and_embedding.md` — DSL 与嵌入 式设计：Rust 中的领域特定语言
- `concept/02_intermediate/14_newtype_and_wrapper.md` — Newtype 与包装器模式：类型安全的零成本抽象
- `concept/02_intermediate/16_error_handling_deep_dive.md` — 错误处理深入：从 Result 到自定义错误生态
- `concept/02_intermediate/15_iterator_patterns.md` — Rust 迭代器模式
- `concept/02_intermediate/17_macro_patterns.md` — 宏模式：编译期代码生成的工程实践
- `concept/02_intermediate/18_lifetimes_advanced.md` — 生命周期高级主题：从 HRTB 到自引用类型
- `concept/02_intermediate/19_advanced_traits.md` — 高级 Trait 主题：从关联类型到特化
- `concept/02_intermediate/20_type_system_advanced.md` — 高级类型系统：从关联类型到类型级编程
- `concept/02_intermediate/21_metaprogramming.md` — 元编程：Rust 的编译期代码生成与变换
- `concept/02_intermediate/22_api_naming_conventions.md` — Rust API 命名约定
- `concept/02_intermediate/23_quiz_traits_and_generics.md` — 测验：Trait 与泛型（试点扩展）
- `concept/02_intermediate/24_quiz_memory_management.md` — 测验：内存管理（L2 试点扩展）
- `concept/02_intermediate/25_rtti_and_dynamic_typing.md` — RTTI 与动态类型识别：从 C++ 到 Rust
- `concept/02_intermediate/26_c_preprocessor_vs_rust_macros.md` — C 预处理器 vs Rust 宏：从文本替换到语法树
- `concept/02_intermediate/27_exception_safety_rust_cpp.md` — 异常安全：C++ 与 Rust 的错误处理哲学
- `concept/02_intermediate/28_construction_and_initialization.md` — 构造与初始化：C++ 的构造函数 vs Rust 的结构体字面量
- `concept/02_intermediate/29_friend_vs_module_privacy.md` — 友元 vs 模块可见性：C++ 的 `friend` 与 Rust 的隐私边界
- `concept/02_intermediate/30_quiz_cpp_rust_foundations.md` — 测验：C/C++ → Rust 基础知识对比

### L03（27 篇）

- `concept/03_advanced/00_before_formal.md` — 是否需要进入 L4 形式化层？
- `concept/03_advanced/01_concurrency.md` — Concurrency（并发模型）
- `concept/03_advanced/02_async.md` — Async/Await（异步编程）
- `concept/03_advanced/02_async_advanced.md` — Async/Await 高级主题
- `concept/03_advanced/26_async_patterns.md` — 异步模式：从 Future 到生产级并发
- `concept/03_advanced/03_unsafe.md` — Unsafe Rust 安全编程
- `concept/03_advanced/04_macros.md` — Macros（宏系统）
- `concept/03_advanced/05_rust_ffi.md` — Rust FFI：与外部代码的安全边界
- `concept/03_advanced/06_pin_unpin.md` — Pin 与 Unpin：自引用类型的不动性保证
- `concept/03_advanced/07_proc_macro.md` — 过程宏：编译期代码生成的元编程工具
- `concept/03_advanced/08_nll_and_polonius.md` — NLL 与 Polonius：借用检查器的演进
- `concept/03_advanced/09_ffi_advanced.md` — FFI 高级主题：跨语言边界的安全与性能
- `concept/03_advanced/10_concurrency_patterns.md` — 并发 模式：从消息 传递到锁自由的数据结构
- `concept/03_advanced/11_atomics_and_memory_ordering.md` — 原子操作与内存序：无锁并发的精确控制
- `concept/03_advanced/12_unsafe_rust_patterns.md` — Unsafe Rust 模式：安全抽象的核心技术
- `concept/03_advanced/13_inline_assembly.md` — 内联汇编 (Inline Assembly)
- `concept/03_advanced/14_custom_allocators.md` — 自定义分配器与内存布局优化
- `concept/03_advanced/15_zero_copy_parsing.md` — 零拷贝解析与序列化优化
- `concept/03_advanced/16_lock_free.md` — 无锁编程与内存模型
- `concept/03_advanced/17_type_erasure.md` — 类型擦除与动态分发
- `concept/03_advanced/18_network_programming.md` — Rust 网络编程：Tokio TCP/UDP、异步 IO 与 Tower 服务抽象
- `concept/03_advanced/19_parallel_distributed_pattern_spectrum.md` — 并行与分布式模式谱系：从线程池到共识算法
- `concept/03_advanced/20_stream_processing_semantics.md` — 流处理语义：从 Dataflow Model 到 Differential Dataflow
- `concept/03_advanced/21_quiz_concurrency_async.md` — 测验：并发与异步（L3 试点扩展）
- `concept/03_advanced/22_quiz_unsafe.md` — 测验：Unsafe Rust（L3 试点扩展）
- `concept/03_advanced/23_quiz_macros.md` — 测验：宏系统（L3 试点扩展）
- `concept/03_advanced/24_async_closures.md` — Async Closures（异步闭包）

### L04（35 篇）

- `concept/04_formal/01_linear_logic.md` — Linear Logic & Affine Logic（线性逻辑与仿射逻辑）
- `concept/04_formal/02_type_theory.md` — Type Theory（类型论基础）
- `concept/04_formal/03_ownership_formal.md` — Ownership Formalization（所有权形式化）
- `concept/04_formal/04_rustbelt.md` — RustBelt & Verification Toolchain（RustBelt 与验证工具链）
- `concept/04_formal/05_verification_toolchain.md` — Verification Toolchain Selection Guide（验证工具链选择指南）
- `concept/04_formal/06_subtype_variance.md` — 子类型与变型：Rust 类型系统中的协变、逆变与不变
- `concept/04_formal/08_type_inference.md` — 类型推断：Hindley-Milner 算法与 Rust 的工业实现
- `concept/04_formal/09_linear_logic_applications.md` — 线性逻辑在 Rust 中的工程应用
- `concept/04_formal/10_category_theory.md` — 范畴论与 Rust：从函子到单子
- `concept/04_formal/11_separation_logic.md` — 分离逻辑：Rust 所有权的形式化根基
- `concept/04_formal/12_denotational_semantics.md` — 指称语义与领域理论
- `concept/04_formal/13_formal_methods.md` — 形式化方法在 Rust 中的应用
- `concept/04_formal/14_lambda_calculus.md` — Lambda 演算与 Rust 计算模型
- `concept/04_formal/15_hoare_logic.md` — Hoare 逻辑：程序验证的形式化基础与 Rust 契约
- `concept/04_formal/16_aerospace_certification_formal_methods.md` — 航空航天认证与形式化方法 (Aerospace Certification & Formal Methods)
- `concept/04_formal/17_operational_semantics.md` — 操作语义：程序行为的形式化定义
- `concept/04_formal/18_evaluation_strategies.md` — 求值策略：Call-by-Value, Call-by-Name, Call-by-Need
- `concept/04_formal/19_rustc_query_system.md` — Rustc 查询系统与增量编译
- `concept/04_formal/20_axiomatic_semantics.md` — Axiomatic Semantics（公理语义）
- `concept/04_formal/21_type_semantics.md` — Type Semantics（类型语义）
- `concept/04_formal/22_modern_verification_tools.md` — 现代 Rust 验证工具生态（2025-2026）
- `concept/04_formal/23_programming_language_foundations.md` — 通用程序语言理论基础：Rust 的 PL 基座
- `concept/04_formal/24_autoverus.md` — AutoVerus / Verus 自动证明生态
- `concept/04_formal/24_quiz_formal_methods.md` — 测验：形式化方法概念（L4 试点扩展）
- `concept/04_formal/26_trait_solver_in_rustc.md` — rustc 中的 Trait Solver
- `concept/04_formal/27_type_checking_and_inference.md` — rustc 类型检查与类型推断
- `concept/04_formal/28_borrow_checking_decidability.md` — Borrow Checking Decidability（借用检查可判定性）
- `concept/04_formal/29_type_inference_complexity.md` — Type Inference Complexity（类型推断复杂度）
- `concept/04_formal/30_aeneas_symbolic_semantics.md` — Aeneas Symbolic Semantics（Aeneas 符号化语义）
- `concept/04_formal/31_miri.md` — Miri：Rust 未定义行为动态检测器
- … 共 35 篇

### L05（19 篇）

- `concept/05_comparative/01_rust_vs_cpp.md` — Rust vs C++：形式系统模型 vs 机制工程模型 —— 全面分析论证>
- `concept/05_comparative/18_cpp_abi_object_model.md` — Rust vs C++：ABI、对象模型与内存布局
- `concept/05_comparative/02_rust_vs_go.md` — Rust vs Go：线性所有权 vs CSP 过程逻辑
- `concept/05_comparative/03_paradigm_matrix.md` — Paradigm Matrix: Multi-Language Formal Comparison（多语言范式对比矩阵）
- `concept/05_comparative/04_safety_boundaries.md` — Rust 安全保证的边界条件全景（Safety Boundary Panorama）
- `concept/05_comparative/05_execution_model_isomorphism.md` — Rust 执行模型同构性矩阵：同步 · 异步 · 并发 · 并行
- `concept/05_comparative/06_rust_vs_java.md` — Rust vs Java：系统编程与托管运行时的范式对比
- `concept/05_comparative/07_rust_vs_python.md` — Rust vs Python：系统编程与动态脚本的对照分析
- `concept/05_comparative/08_rust_vs_javascript.md` — Rust vs JavaScript：系统编程与脚本执行的范式差异
- `concept/05_comparative/08_rust_vs_ruby.md` — Rust vs Ruby：性能与表达力的两极
- `concept/05_comparative/09_rust_vs_swift.md` — Rust vs Swift：现代系统语言的两种路径
- `concept/05_comparative/10_rust_vs_zig.md` — Rust vs Zig：现代系统语言的两种哲学
- `concept/05_comparative/11_rust_vs_kotlin.md` — Rust vs Kotlin：静态安全的两种路径
- `concept/05_comparative/12_rust_vs_scala.md` — Rust vs Scala：类型系统的两种哲学
- `concept/05_comparative/13_rust_vs_csharp.md` — Rust vs C#：托管与原生之路
- `concept/05_comparative/14_rust_vs_elixir.md` — Rust vs Elixir 对比分析
- `concept/05_comparative/15_rust_vs_typescript.md` — Rust vs TypeScript：静态类型系统的两种哲学 —— 编译期证明与渐进式工程
- `concept/05_comparative/16_cpp_rust_surface_features.md` — C++ vs Rust：构造、运算符、RTTI、友元
- `concept/05_comparative/17_quiz_rust_vs_systems.md` — 测验：Rust vs 系统编程语言（L5 试点扩展）

### L06（75 篇）

- `concept/06_ecosystem/01_toolchain.md` — Toolchain（工具链与 Cargo）
- `concept/06_ecosystem/02_patterns.md` — Design Patterns（设计模式）
- `concept/06_ecosystem/03_core_crates.md` — Core Crates（核心开源库谱系）
- `concept/06_ecosystem/34_idioms_spectrum.md` — Rust 惯用法谱系全景（Idioms Spectrum）
- `concept/06_ecosystem/04_application_domains.md` — Application Domains（软件工程应用主题）
- `concept/06_ecosystem/44_formal_ecosystem_tower.md` — Formal Ecosystem Tower（Rust 生态形式化分层塔）
- `concept/06_ecosystem/05_system_design_principles.md` — Rust 系统设计原则与国际权威对齐
- `concept/06_ecosystem/06_blockchain.md` — Blockchain & Smart Contract Security（区块链与智能合约安全）
- `concept/06_ecosystem/07_game_ecs.md` — Game Development & ECS Architecture（游戏开发与 ECS 架构）
- `concept/06_ecosystem/08_wasi.md` — WASI & WebAssembly Component Model（WASI 与 WebAssembly 组件模型）
- `concept/06_ecosystem/09_cargo_script.md` — Cargo Script 脚本化 Rust
- `concept/06_ecosystem/10_public_private_deps.md` — Cargo 公共与私有依赖
- `concept/06_ecosystem/11_webassembly.md` — WebAssembly 生态：Rust 的浏览器外运行时
- `concept/06_ecosystem/12_testing_strategies.md` — Rust 测试策略：从单元测试到属性验证
- `concept/06_ecosystem/13_logging_observability.md` — 日志与可观测性：Rust 服务端监控生态
- `concept/06_ecosystem/14_documentation.md` — 文档生态：rustdoc、文档测试与 API 文档规范
- `concept/06_ecosystem/15_performance_optimization.md` — 性能优化：Rust 代码的测量与调优
- `concept/06_ecosystem/16_testing.md` — 测试生态：单元测试、集成测试与验证策略
- `concept/06_ecosystem/17_cross_compilation.md` — 交叉编译：多目标平台支持与条件编译
- `concept/06_ecosystem/18_distributed_systems.md` — 分布式 系统：Rust 在微服务 与集群中的工程实践
- `concept/06_ecosystem/19_security_practices.md` — 安全 实践：Rust 代码的防御性编程
- `concept/06_ecosystem/20_licensing_and_compliance.md` — 许可证与合规：Rust 项目的法律工程
- `concept/06_ecosystem/21_game_development.md` — Rust 游戏开发生态
- `concept/06_ecosystem/22_embedded_systems.md` — Rust 嵌入式系统开发
- `concept/06_ecosystem/23_database_access.md` — Rust 数据库访问生态
- `concept/06_ecosystem/24_cloud_native.md` — Rust 云原生生态
- `concept/06_ecosystem/72_cargo_security_cves.md` — Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223
- `concept/06_ecosystem/25_cli_development.md` — Rust CLI 开发生态
- `concept/06_ecosystem/26_game_development.md` — Rust 游戏开发
- `concept/06_ecosystem/27_web_frameworks.md` — Rust Web 框架对比与选型
- … 共 75 篇

### L07（53 篇）

- `concept/07_future/01_ai_integration.md` — AI × Rust：生成-验证闭环与确定性容器
- `concept/07_future/02_formal_methods.md` — Formal Methods Industrialization（形式化方法工业化）
- `concept/07_future/03_evolution.md` — Language Evolution（语言演进）
- `concept/07_future/04_effects_system.md` — Effects System: Concept Pre-study（效果系统：概念预研）
- `concept/07_future/05_rust_version_tracking.md` — Rust 形式模型演进跟踪（1.79–1.97+）
- `concept/07_future/07_mcdc_coverage_preview.md` — MC/DC Coverage 概念预研：安全关键 Rust 的覆盖率验证
- `concept/07_future/08_safety_tags_preview.md` — Safety Tags 概念预研：Unsafe 契约的机器可读标注
- `concept/07_future/09_parallel_frontend_preview.md` — 并行 前端编译预研：Rust 编译器 的多核扩展
- `concept/07_future/10_derive_coerce_pointee_preview.md` — 派生 CoercePointee 预研：智能指针的自动类型强制
- `concept/07_future/11_const_trait_impl_preview.md` — Const Trait Impl 预研：常量上下文中的 Trait 泛化
- `concept/07_future/11_stable_abi_preview.md` — Stable ABI Preview
- `concept/07_future/12_inline_const_pattern_preview.md` — Inline Const Pattern 预览（Rust 1.98+ Nightly）
- `concept/07_future/12_return_type_notation_preview.md` — Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界
- `concept/07_future/13_must_not_suspend_preview.md` — `must_not_suspend` Lint Preview
- `concept/07_future/13_unsafe_fields_preview.md` — Unsafe Fields 预研：字段级安全边界的精确标注
- `concept/07_future/35_ferrocene_preview.md` — Ferrocene 预研：Rust 的安全关键认证之路
- `concept/07_future/14_lifetime_capture_preview.md` — Lifetime Capture in `impl Trait` Preview
- `concept/07_future/22_gen_blocks_preview.md` — Gen Blocks 预研：超越异步的泛化生成器
- `concept/07_future/15_pin_ergonomics_preview.md` — Pin Ergonomics 与 Reborrow Traits 预研：超越 `Pin::as_mut`
- `concept/07_future/37_rpitit_preview.md` — 特质中返回位置 impl Trait（RPITIT）预览
- `concept/07_future/38_cranelift_backend_preview.md` — Cranelift 后端预研：Rust 编译器的快速调试编译
- `concept/07_future/16_type_alias_impl_trait_preview.md` — TAIT Preview
- `concept/07_future/17_arbitrary_self_types_preview.md` — Arbitrary Self Types 预览：自定义方法接收器
- `concept/07_future/17_const_trait_preview.md` — Const Trait 实现预览
- `concept/07_future/17_ergonomic_ref_counting_preview.md` — Ergonomic Ref-Counting 预研：人机工学引用计数
- `concept/07_future/17_rust_specification_preview.md` — Rust 语言规范预研：从参考文档到形式化规范
- `concept/07_future/18_async_drop_preview.md` — Async Drop：异步资源的优雅销毁
- `concept/07_future/42_field_projections_preview.md` — Field Projections 预览：安全的字段级投影
- `concept/07_future/19_rust_edition_preview.md` — Rust 2024 Edition (1.85.0+ stable)
- `concept/07_future/43_rust_for_linux.md` — Rust for Linux ：操作系统内核中的内存安全
- … 共 53 篇

### L0_meta（3 篇）

- `concept/sources/INDEX.md` — 权威来源索引库
- `concept/sources/rfc_index.md` — RFC 索引：关键设计提案跟踪
- `concept/sources/theorem_tier_spec.md` — 定理分级规范（Theorem Tier Specification）

## 2. 权威来源覆盖统计

| 来源类别 | 权威主题数 | 已对齐 | 缺口 | 覆盖率 |
|----------|-----------|--------|------|--------|
| official_docs | 973 | 744 | 229 | 76.5% |
| formal_verification | 12 | 7 | 5 | 58.3% |
| industrial_ecosystem | 25 | 14 | 11 | 56.0% |
| roadmap | 16 | 13 | 3 | 81.2% |

## 3. 未覆盖空间（按优先级分组）

> 注：以下缺口基于标题/路径关键词匹配，部分可能已被项目文件间接覆盖但标题未体现，需人工复核。

### P0 官方核心（78 项）

- **Using Structs to Structure Related Data** — The Rust Programming Language [https://doc.rust-lang.org/book/ch05-00-structs.html](https://doc.rust-lang.org/book/ch05-00-structs.html)
- **The `match` Control Flow Construct** — The Rust Programming Language [https://doc.rust-lang.org/book/ch06-02-match.html](https://doc.rust-lang.org/book/ch06-02-match.html)
- **Control Scope and Privacy with Modules** — The Rust Programming Language [https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html](https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html)
- **Paths for Referring to an Item in the Module Tree** — The Rust Programming Language [https://doc.rust-lang.org/book/ch07-03-paths-for-referring-to-an-item-in-the-module-tree.html](https://doc.rust-lang.org/book/ch07-03-paths-for-referring-to-an-item-in-the-module-tree.html)
- **Separating Modules into Different Files** — The Rust Programming Language [https://doc.rust-lang.org/book/ch07-05-separating-modules-into-different-files.html](https://doc.rust-lang.org/book/ch07-05-separating-modules-into-different-files.html)
- **Defining Shared Behavior with Traits** — The Rust Programming Language [https://doc.rust-lang.org/book/ch10-02-traits.html](https://doc.rust-lang.org/book/ch10-02-traits.html)
- **Installing Binaries with `cargo install`** — The Rust Programming Language [https://doc.rust-lang.org/book/ch14-04-installing-binaries.html](https://doc.rust-lang.org/book/ch14-04-installing-binaries.html)
- **Extending Cargo with Custom Commands** — The Rust Programming Language [https://doc.rust-lang.org/book/ch14-05-extending-cargo.html](https://doc.rust-lang.org/book/ch14-05-extending-cargo.html)
- **Using Trait Objects to Abstract over Shared Behavior** — The Rust Programming Language [https://doc.rust-lang.org/book/ch18-02-trait-objects.html](https://doc.rust-lang.org/book/ch18-02-trait-objects.html)
- **Behavior not considered unsafe** — The Rust Reference [https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html](https://doc.rust-lang.org/reference/behavior-not-considered-unsafe.html)
- **Macro follow-set ambiguity formal specification** — The Rust Reference [https://doc.rust-lang.org/reference/macro-ambiguity.html](https://doc.rust-lang.org/reference/macro-ambiguity.html)
- **Limits of Lifetimes** — The Rustonomicon [https://doc.rust-lang.org/nomicon/lifetime-mismatch.html](https://doc.rust-lang.org/nomicon/lifetime-mismatch.html)
- **Lifetime Elision** — The Rustonomicon [https://doc.rust-lang.org/nomicon/lifetime-elision.html](https://doc.rust-lang.org/nomicon/lifetime-elision.html)
- **Unbounded Lifetimes** — The Rustonomicon [https://doc.rust-lang.org/nomicon/unbounded-lifetimes.html](https://doc.rust-lang.org/nomicon/unbounded-lifetimes.html)
- **Higher-Rank Trait Bounds** — The Rustonomicon [https://doc.rust-lang.org/nomicon/hrtb.html](https://doc.rust-lang.org/nomicon/hrtb.html)
- **Splitting Borrows** — The Rustonomicon [https://doc.rust-lang.org/nomicon/borrow-splitting.html](https://doc.rust-lang.org/nomicon/borrow-splitting.html)
- **Ownership Based Resource Management** — The Rustonomicon [https://doc.rust-lang.org/nomicon/obrm.html](https://doc.rust-lang.org/nomicon/obrm.html)
- **First Steps with Cargo** — The Cargo Book [https://doc.rust-lang.org/cargo/getting-started/first-steps.html](https://doc.rust-lang.org/cargo/getting-started/first-steps.html)
- **Why Cargo Exists** — The Cargo Book [https://doc.rust-lang.org/cargo/guide/why-cargo-exists.html](https://doc.rust-lang.org/cargo/guide/why-cargo-exists.html)
- **Cargo Home** — The Cargo Book [https://doc.rust-lang.org/cargo/guide/cargo-home.html](https://doc.rust-lang.org/cargo/guide/cargo-home.html)
- **Cargo Targets** — The Cargo Book [https://doc.rust-lang.org/cargo/reference/cargo-targets.html](https://doc.rust-lang.org/cargo/reference/cargo-targets.html)
- **Cargo Commands** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/index.html](https://doc.rust-lang.org/cargo/commands/index.html)
- **cargo help** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-help.html](https://doc.rust-lang.org/cargo/commands/cargo-help.html)
- **cargo version** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-version.html](https://doc.rust-lang.org/cargo/commands/cargo-version.html)
- **cargo bench** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-bench.html](https://doc.rust-lang.org/cargo/commands/cargo-bench.html)
- **cargo check** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-check.html](https://doc.rust-lang.org/cargo/commands/cargo-check.html)
- **cargo clean** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-clean.html](https://doc.rust-lang.org/cargo/commands/cargo-clean.html)
- **cargo fetch** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-fetch.html](https://doc.rust-lang.org/cargo/commands/cargo-fetch.html)
- **cargo fmt** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-fmt.html](https://doc.rust-lang.org/cargo/commands/cargo-fmt.html)
- **cargo run** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-run.html](https://doc.rust-lang.org/cargo/commands/cargo-run.html)
- **cargo rustdoc** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-rustdoc.html](https://doc.rust-lang.org/cargo/commands/cargo-rustdoc.html)
- **cargo test** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-test.html](https://doc.rust-lang.org/cargo/commands/cargo-test.html)
- **cargo add** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-add.html](https://doc.rust-lang.org/cargo/commands/cargo-add.html)
- **cargo generate-lockfile** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-generate-lockfile.html](https://doc.rust-lang.org/cargo/commands/cargo-generate-lockfile.html)
- **cargo info** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-info.html](https://doc.rust-lang.org/cargo/commands/cargo-info.html)
- **cargo locate-project** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-locate-project.html](https://doc.rust-lang.org/cargo/commands/cargo-locate-project.html)
- **cargo metadata** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-metadata.html](https://doc.rust-lang.org/cargo/commands/cargo-metadata.html)
- **cargo pkgid** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-pkgid.html](https://doc.rust-lang.org/cargo/commands/cargo-pkgid.html)
- **cargo remove** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-remove.html](https://doc.rust-lang.org/cargo/commands/cargo-remove.html)
- **cargo tree** — The Cargo Book [https://doc.rust-lang.org/cargo/commands/cargo-tree.html](https://doc.rust-lang.org/cargo/commands/cargo-tree.html)
- … 共 78 项，详见 `tmp/topic_symmetric_diff.json`

### P1 形式化/验证（3 项）

- **Verus: Verified Rust for Low-Level Systems** — Theorem Proving [https://verus-lang.github.io/verus/](https://verus-lang.github.io/verus/)
- **Miri: Rust Interpreter for Undefined Behavior** — Undefined Behavior Detection [https://github.com/rust-lang/miri](https://github.com/rust-lang/miri)
- **Ferrocene: Rust for Safety-Critical Systems** — Safety Certification [https://ferrocene.dev/](https://ferrocene.dev/)

### P2 工业生态（8 项）

- **Using the tracing/logging instrumentation** — The rustc Book [https://doc.rust-lang.org/rustc/./tracing.html](https://doc.rust-lang.org/rustc/./tracing.html)
- **sqlx** — Database Driver [https://github.com/launchbadge/sqlx](https://github.com/launchbadge/sqlx)
- **Tauri** — GUI / Cross-platform [https://tauri.app/](https://tauri.app/)
- **Dioxus** — GUI / Cross-platform [https://dioxuslabs.com/](https://dioxuslabs.com/)
- **Leptos** — GUI / Web [https://leptos.dev/](https://leptos.dev/)
- **egui** — GUI / Immediate Mode [https://www.egui.rs/](https://www.egui.rs/)
- **PyO3** — Python Interop [https://pyo3.rs/](https://pyo3.rs/)
- **rayon** — Data Parallelism [https://docs.rs/rayon/latest/rayon/](https://docs.rs/rayon/latest/rayon/)

### P3 前沿探索（159 项）

- **Bringing Paths Into Scope with the `use` Keyword** — The Rust Programming Language [https://doc.rust-lang.org/book/ch07-04-bringing-paths-into-scope-with-the-use-keyword.html](https://doc.rust-lang.org/book/ch07-04-bringing-paths-into-scope-with-the-use-keyword.html)
- **Storing Lists of Values with Vectors** — The Rust Programming Language [https://doc.rust-lang.org/book/ch08-01-vectors.html](https://doc.rust-lang.org/book/ch08-01-vectors.html)
- **Storing UTF-8 Encoded Text with Strings** — The Rust Programming Language [https://doc.rust-lang.org/book/ch08-02-strings.html](https://doc.rust-lang.org/book/ch08-02-strings.html)
- **Storing Keys with Associated Values in Hash Maps** — The Rust Programming Language [https://doc.rust-lang.org/book/ch08-03-hash-maps.html](https://doc.rust-lang.org/book/ch08-03-hash-maps.html)
- **An I/O Project: Building a Command Line Program** — The Rust Programming Language [https://doc.rust-lang.org/book/ch12-00-an-io-project.html](https://doc.rust-lang.org/book/ch12-00-an-io-project.html)
- **Accepting Command Line Arguments** — The Rust Programming Language [https://doc.rust-lang.org/book/ch12-01-accepting-command-line-arguments.html](https://doc.rust-lang.org/book/ch12-01-accepting-command-line-arguments.html)
- **Adding Functionality with Test Driven Development** — The Rust Programming Language [https://doc.rust-lang.org/book/ch12-04-testing-the-librarys-functionality.html](https://doc.rust-lang.org/book/ch12-04-testing-the-librarys-functionality.html)
- **Redirecting Errors to Standard Error** — The Rust Programming Language [https://doc.rust-lang.org/book/ch12-06-writing-to-stderr-instead-of-stdout.html](https://doc.rust-lang.org/book/ch12-06-writing-to-stderr-instead-of-stdout.html)
- **Functional Language Features: Iterators and Closures** — The Rust Programming Language [https://doc.rust-lang.org/book/ch13-00-functional-features.html](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- **Processing a Series of Items with Iterators** — The Rust Programming Language [https://doc.rust-lang.org/book/ch13-02-iterators.html](https://doc.rust-lang.org/book/ch13-02-iterators.html)
- **Performance in Loops vs. Iterators** — The Rust Programming Language [https://doc.rust-lang.org/book/ch13-04-performance.html](https://doc.rust-lang.org/book/ch13-04-performance.html)
- **Using `Box<T>` to Point to Data on the Heap** — The Rust Programming Language [https://doc.rust-lang.org/book/ch15-01-box.html](https://doc.rust-lang.org/book/ch15-01-box.html)
- **Treating Smart Pointers Like Regular References** — The Rust Programming Language [https://doc.rust-lang.org/book/ch15-02-deref.html](https://doc.rust-lang.org/book/ch15-02-deref.html)
- **Using Threads to Run Code Simultaneously** — The Rust Programming Language [https://doc.rust-lang.org/book/ch16-01-threads.html](https://doc.rust-lang.org/book/ch16-01-threads.html)
- **Transfer Data Between Threads with Message Passing** — The Rust Programming Language [https://doc.rust-lang.org/book/ch16-02-message-passing.html](https://doc.rust-lang.org/book/ch16-02-message-passing.html)
- **Working With Any Number of Futures** — The Rust Programming Language [https://doc.rust-lang.org/book/ch17-03-more-futures.html](https://doc.rust-lang.org/book/ch17-03-more-futures.html)
- **Characteristics of Object-Oriented Languages** — The Rust Programming Language [https://doc.rust-lang.org/book/ch18-01-what-is-oo.html](https://doc.rust-lang.org/book/ch18-01-what-is-oo.html)
- **All the Places Patterns Can Be Used** — The Rust Programming Language [https://doc.rust-lang.org/book/ch19-01-all-the-places-for-patterns.html](https://doc.rust-lang.org/book/ch19-01-all-the-places-for-patterns.html)
- **Final Project: Building a Multithreaded Web Server** — The Rust Programming Language [https://doc.rust-lang.org/book/ch21-00-final-project-a-web-server.html](https://doc.rust-lang.org/book/ch21-00-final-project-a-web-server.html)
- **Building a Single-Threaded Web Server** — The Rust Programming Language [https://doc.rust-lang.org/book/ch21-01-single-threaded.html](https://doc.rust-lang.org/book/ch21-01-single-threaded.html)
- **From Single-Threaded to Multithreaded Server** — The Rust Programming Language [https://doc.rust-lang.org/book/ch21-02-multithreaded.html](https://doc.rust-lang.org/book/ch21-02-multithreaded.html)
- **Data Layout** — The Rustonomicon [https://doc.rust-lang.org/nomicon/data.html](https://doc.rust-lang.org/nomicon/data.html)
- **Exotically Sized Types** — The Rustonomicon [https://doc.rust-lang.org/nomicon/exotic-sizes.html](https://doc.rust-lang.org/nomicon/exotic-sizes.html)
- **Other reprs** — The Rustonomicon [https://doc.rust-lang.org/nomicon/other-reprs.html](https://doc.rust-lang.org/nomicon/other-reprs.html)
- **Subtyping and Variance** — The Rustonomicon [https://doc.rust-lang.org/nomicon/subtyping.html](https://doc.rust-lang.org/nomicon/subtyping.html)
- **Drop Check** — The Rustonomicon [https://doc.rust-lang.org/nomicon/dropck.html](https://doc.rust-lang.org/nomicon/dropck.html)
- **Type Conversions** — The Rustonomicon [https://doc.rust-lang.org/nomicon/conversions.html](https://doc.rust-lang.org/nomicon/conversions.html)
- **The Dot Operator** — The Rustonomicon [https://doc.rust-lang.org/nomicon/dot-operator.html](https://doc.rust-lang.org/nomicon/dot-operator.html)
- **Uninitialized Memory** — The Rustonomicon [https://doc.rust-lang.org/nomicon/uninitialized.html](https://doc.rust-lang.org/nomicon/uninitialized.html)
- **Drop Flags** — The Rustonomicon [https://doc.rust-lang.org/nomicon/drop-flags.html](https://doc.rust-lang.org/nomicon/drop-flags.html)
- **Exception Safety** — The Rustonomicon [https://doc.rust-lang.org/nomicon/exception-safety.html](https://doc.rust-lang.org/nomicon/exception-safety.html)
- **Implementing Vec** — The Rustonomicon [https://doc.rust-lang.org/nomicon/./vec/vec.html](https://doc.rust-lang.org/nomicon/./vec/vec.html)
- **Push and Pop** — The Rustonomicon [https://doc.rust-lang.org/nomicon/./vec/vec-push-pop.html](https://doc.rust-lang.org/nomicon/./vec/vec-push-pop.html)
- **Insert and Remove** — The Rustonomicon [https://doc.rust-lang.org/nomicon/./vec/vec-insert-remove.html](https://doc.rust-lang.org/nomicon/./vec/vec-insert-remove.html)
- **Final Code** — The Rustonomicon [https://doc.rust-lang.org/nomicon/./vec/vec-final.html](https://doc.rust-lang.org/nomicon/./vec/vec-final.html)
- **Base Code** — The Rustonomicon [https://doc.rust-lang.org/nomicon/./arc-mutex/arc-base.html](https://doc.rust-lang.org/nomicon/./arc-mutex/arc-base.html)
- **Final Code** — The Rustonomicon [https://doc.rust-lang.org/nomicon/./arc-mutex/arc-final.html](https://doc.rust-lang.org/nomicon/./arc-mutex/arc-final.html)
- **Beneath `std`** — The Rustonomicon [https://doc.rust-lang.org/nomicon/beneath-std.html](https://doc.rust-lang.org/nomicon/beneath-std.html)
- **Testcase: linked-list** — Rust By Example [https://doc.rust-lang.org/rust-by-example/custom_types/enum/testcase_linked_list.html](https://doc.rust-lang.org/rust-by-example/custom_types/enum/testcase_linked_list.html)
- **Searching through iterators** — Rust By Example [https://doc.rust-lang.org/rust-by-example/fn/closures/closure_examples/iter_find.html](https://doc.rust-lang.org/rust-by-example/fn/closures/closure_examples/iter_find.html)
- … 共 159 项，详见 `tmp/topic_symmetric_diff.json`

## 4. 项目独有主题（权威来源未直接强调）

> 共 234 个 concept 文件未被权威来源主题直接命中。这些多为项目特色的中文学习路径、对比分析、决策树或生态 deep-dive。

- `concept/00_meta/03_bloom_taxonomy.md` — Bloom Taxonomy（Bloom 分类法）
- `concept/00_meta/asp_marking_guide.md` — Rust 知识体系 A/S/P 三维认知标记规范
- `concept/00_meta/audit_checklist.md` — 概念一致性检查清单（Concept Consistency Audit Checklist）
- `concept/00_meta/bilingual_template.md` — Concept 文件双语模板（Bilingual Template）
- `concept/00_meta/career_landscape.md` — Rust 职业市场全景：2026 年数据与分析
- `concept/00_meta/cognitive_dimension_matrix.md` — Rust 知识体系双维认知矩阵（Krathwohl × Bloom）
- `concept/00_meta/competency_graph.md` — Rust 知识体系能力图谱（Competency Graph）
- `concept/00_meta/comprehensive_rust_mapping.md` — Comprehensive Rust 课程映射
- `concept/00_meta/concept_consistency_audit_checklist.md` — 概念一致性（Coherence）检查清单
- `concept/00_meta/concept_definition_decision_forest.md` — Rust 知识体系概念定义判定森林（Concept Definition Decision Forest）
- `concept/00_meta/cpp_rust_engineering_roadmap.md` — C/C++ → Rust 工程层对比路线图
- `concept/00_meta/decidability_spectrum.md` — Rust 编译期可判定性谱系全景（Decidability Spectrum）
- `concept/00_meta/expressiveness_multiview.md` — Rust 语义表达力多视角深化（Multiview Expressiveness Analysis）
- `concept/00_meta/fault_tree_analysis_collection.md` — Rust 知识体系失效分析树集（Fault Tree Analysis Collection）
- `concept/00_meta/foundations_gap_closure_index.md` — 基础知识缺口补全总索引
- `concept/00_meta/grading_system.md` — 内容分级与受众标签体系
- `concept/00_meta/inter_layer_map.md` — 跨层知识图谱（Inter-Layer Dependency Map）
- `concept/00_meta/inter_layer_topology.md` — Rust 知识体系跨层依赖与蕴含拓扑图
- `concept/00_meta/intra_layer_model_map.md` — Rust 知识体系层次内模型间映射图
- `concept/00_meta/kg_ontology_v2.md` — Rust 知识体系知识图谱本体规范 v2.0（RDF 1.2 / RDF-star / SKOS 对齐版）
- `concept/00_meta/kg_tlo_alignment.md` — Rust 知识体系顶层本体（TLO）对齐
- `concept/00_meta/knowledge_mindmap.md` — Rust 知识体系全局思维导图（Knowledge Mindmap）
- `concept/00_meta/learning_mvp_path.md` — MVP 学习路径：从零到多线程 CLI（40 小时）
- `concept/00_meta/methodology.md` — 方法论：思维表征与知识结构规范
- `concept/00_meta/navigation.md` — Rust 知识体系全景导航（Navigation Hub）
- `concept/00_meta/paradigm_transition_matrix.md` — Rust 范式转换模式矩阵（Paradigm Transition Matrix）
- `concept/00_meta/pattern_semantic_space_index.md` — 模式语义空间索引：设计模式在概念体系中的坐标
- `concept/00_meta/pl_foundations_roadmap.md` — 通用 PL 基座路线图：Rust 在编程语言坐标系中的位置
- `concept/00_meta/problem_graph.md` — Rust 知识体系问题图谱（Problem Graph）
- `concept/00_meta/quality_dashboard_v2.md` — Rust 知识体系思维表征覆盖率仪表板（Quality Dashboard v2）
- `concept/00_meta/rustbelt_predicate_map.md` — RustBelt 谓词映射图（RustBelt Predicate Map）
- `concept/00_meta/semantic_expressiveness.md` — Rust Semantic Expressiveness: A Panoramic Survey（Rust 语义表达力全景梳理）
- `concept/00_meta/semantic_space.md` — Rust 表征空间（Semantic / Representational Space）
- `concept/00_meta/template_deduplication_guide.md` — 模板去同质化指南
- `concept/00_meta/theorem_inference_forest.md` — Rust 知识体系定理推理森林
- `concept/00_meta/todos.md` — 全局待办清单（Global TODO Tracker）
- `concept/01_foundation/00_pl_prerequisites.md` — 编程语言理论基础（PL Prerequisites）
- `concept/01_foundation/01_ownership.md` — Ownership（所有权）
- `concept/01_foundation/02_borrowing.md` — Borrowing（借用）
- `concept/01_foundation/03_lifetimes.md` — Lifetimes（生命周期）
- … 共 234 项

## 5. 重复/需合并主题提示

> 未检测到明显标题重复。

## 6. 维护机制

1. 每季度运行 `python scripts/topic_authority_aligner.py --phase all` 更新本文件。
2. 新缺口优先进入 `reports/TOPIC_ALIGNMENT_AND_GAP_PLAN_*.md` 任务池。
3. 已确认覆盖的缺口从本文件移除或标记为 `verified-covered`。
