# 层内映射图谱（Intra-Layer Mapping Atlas）

> **EN**: Intra-Layer Mapping Atlas
> **Summary**: 每层内部核心模型/概念间的等价、蕴含、依赖、互斥关系，基于同层前置/后置引用与策展语义标注。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

**关系符号约定**（与 KG v3 属性对齐；推断规则见 `scripts/generate_knowledge_topology_atlas.py` `infer_relation`）：

- `→` dependsOn：源依赖目标（目标在源的前置元数据中）
- `⟸` rev-dependsOn：目标依赖源（源在目标的前置元数据中）
- `⟹` entails：源蕴含/导向目标（后置概念引用，默认）
- `⊑` refines：精化关系，名称含“进阶/机制/模式”的一侧精化另一侧（同主题目录）
- `⊥` mutexWith：两概念互斥（策展标注，依据见各行）
- `⇔` 对比/等价：对比型页面（vs/对比）间的对照关系
- `↔` 互参：互为后置概念的强互参关系

## L0 元信息层

本节专门讨论「L0 元信息层」下的层内引用关系。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | ⟹ | [全局概念索引](../../00_meta/04_navigation/03_concept_index.md) | 后置概念引用（蕴含/导向） |
| [International Authority Index](../../00_meta/02_sources/05_international_authority_index.md) | ⟹ | [Rust 知识体系全局思维导图](../../00_meta/00_framework/knowledge_mindmap.md) | 后置概念引用（蕴含/导向） |
| [模板去同质化指南](../../00_meta/03_audit/05_template_deduplication_guide.md) | ⟹ | [Rust 知识体系思维表征覆盖率仪表板](../../00_meta/03_audit/07_quality_dashboard_v2.md) | 后置概念引用（蕴含/导向） |
| [基础知识缺口补全总索引](../../00_meta/04_navigation/13_foundations_gap_closure_index.md) | ⟹ | [Concept Audit Guide](../../00_meta/03_audit/01_concept_audit_guide.md) | 后置概念引用（蕴含/导向） |
| [C/C++ → Rust 工程层对比路线图](../../00_meta/00_framework/cpp_rust_engineering_roadmap.md) | ⇔ | [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/00_framework/pattern_semantic_space_index.md) | 对比型页面（名称含 vs/对比） |
| [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/00_framework/pattern_semantic_space_index.md) | ⊑ | [语义桥：算法、设计模式与工作流模式的统一谱系](../../00_meta/00_framework/semantic_bridge_algorithms_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [通用 PL 基座路线图：Rust 在编程语言坐标系中的位置](../../00_meta/00_framework/pl_foundations_roadmap.md) | ⇔ | [C/C++ → Rust 工程层对比路线图](../../00_meta/00_framework/cpp_rust_engineering_roadmap.md) | 对比型页面（名称含 vs/对比） |
| [通用 PL 基座路线图：Rust 在编程语言坐标系中的位置](../../00_meta/00_framework/pl_foundations_roadmap.md) | ⊑ | [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/00_framework/pattern_semantic_space_index.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |

## L1 基础概念层

本节专门讨论「L1 基础概念层」下的层内引用关系。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ⟹ | [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 后置概念引用（蕴含/导向） |
| [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ⟹ | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 后置概念引用（蕴含/导向） |
| [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ⟹ | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | 后置概念引用（蕴含/导向） |
| [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ⟹ | [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | 后置概念引用（蕴含/导向） |
| [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ⟹ | [Rust 错误处理基础](../../01_foundation/08_error_handling/01_error_handling_basics.md) | 后置概念引用（蕴含/导向） |
| [Rust 起步指南](../../01_foundation/00_start/00_start.md) | ⟹ | [测试基础：从单元测试到集成测试](../../01_foundation/10_testing_basics/01_testing_basics.md) | 后置概念引用（蕴含/导向） |
| [字符串与文本：Rust 的 Unicode 处理与格式化系统](../../01_foundation/06_strings_and_text/01_strings_and_text.md) | ⟹ | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/01_collections.md) | 后置概念引用（蕴含/导向） |
| [Functions](../../01_foundation/07_modules_and_items/02_functions.md) | ⟹ | [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | 后置概念引用（蕴含/导向） |
| [Functions](../../01_foundation/07_modules_and_items/02_functions.md) | ⟹ | [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | 后置概念引用（蕴含/导向） |
| [模式匹配](../../01_foundation/04_control_flow/02_patterns.md) | ⟸ | [语句与表达式](../../01_foundation/04_control_flow/03_statements_and_expressions.md) | 源在目标的前置元数据中（目标依赖源） |
| [字符串与编码：Rust 的文本处理类型系统](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) | ⟹ | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/01_collections.md) | 后置概念引用（蕴含/导向） |
| [常用开发工具](../../01_foundation/10_testing_basics/02_useful_development_tools.md) | ⟹ | [测试基础：从单元测试到集成测试](../../01_foundation/10_testing_basics/01_testing_basics.md) | 后置概念引用（蕴含/导向） |
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/03_values_and_references/02_value_vs_reference_semantics.md) | ⇔ | [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | 对比型页面（名称含 vs/对比） |
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/03_values_and_references/02_value_vs_reference_semantics.md) | ⇔ | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 对比型页面（名称含 vs/对比） |
| [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/02_type_system/03_numerics.md) | ⟹ | [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/02_zero_cost_abstractions.md) | 后置概念引用（蕴含/导向） |
| [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/02_type_system/03_numerics.md) | ⟹ | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/01_collections.md) | 后置概念引用（蕴含/导向） |
| [语句与表达式](../../01_foundation/04_control_flow/03_statements_and_expressions.md) | ⟹ | [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | 后置概念引用（蕴含/导向） |
| [Use Declarations](../../01_foundation/07_modules_and_items/03_use_declarations.md) | ⟹ | [Preludes](../../01_foundation/07_modules_and_items/10_preludes.md) | 后置概念引用（蕴含/导向） |
| [变量模型：从通用 PL 视角看 Rust 的所有权](../../01_foundation/03_values_and_references/03_variable_model.md) | ⟹ | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 后置概念引用（蕴含/导向） |
| [副作用与纯度：从引用透明到 Rust 的所有权效果](../../01_foundation/00_start/04_effects_and_purity.md) | ⟹ | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 后置概念引用（蕴含/导向） |
| [Structs](../../01_foundation/07_modules_and_items/04_structs.md) | ⟸ | [Enumerations](../../01_foundation/07_modules_and_items/05_enumerations.md) | 源在目标的前置元数据中（目标依赖源） |
| [Structs](../../01_foundation/07_modules_and_items/04_structs.md) | ⟸ | [Implementations](../../01_foundation/07_modules_and_items/06_implementations.md) | 源在目标的前置元数据中（目标依赖源） |
| [Enumerations](../../01_foundation/07_modules_and_items/05_enumerations.md) | ⟹ | [Rust 错误处理基础](../../01_foundation/08_error_handling/01_error_handling_basics.md) | 后置概念引用（蕴含/导向） |
| [标准 I/O 与进程](../../01_foundation/00_start/05_std_io_and_process.md) | ⟹ | [测试基础：从单元测试到集成测试](../../01_foundation/10_testing_basics/01_testing_basics.md) | 后置概念引用（蕴含/导向） |
| [Rust 关键字](../../01_foundation/00_start/06_keywords.md) | ⟹ | [属性与声明宏：编译期元编程基础](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) | 后置概念引用（蕴含/导向） |
| [Rust 关键字](../../01_foundation/00_start/06_keywords.md) | ⟹ | [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | 后置概念引用（蕴含/导向） |
| [Rust 运算符与符号](../../01_foundation/00_start/07_operators_and_symbols.md) | → | [Type System Basics](../../01_foundation/02_type_system/01_type_system.md) | 目标在源的前置元数据中（源依赖目标） |
| [Crate 与源文件](../../01_foundation/07_modules_and_items/11_crates_and_source_files.md) | ⟸ | [项](../../01_foundation/07_modules_and_items/12_items.md) | 源在目标的前置元数据中（目标依赖源） |
| [测验：类型系统](../../01_foundation/11_quizzes/24_quiz_type_system.md) | ⟹ | [测验：所有权、借用与生命周期](../../01_foundation/11_quizzes/33_quiz_ownership_borrowing.md) | 后置概念引用（蕴含/导向） |
| [测验：所有权、借用与生命周期](../../01_foundation/11_quizzes/33_quiz_ownership_borrowing.md) | ⟹ | [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | 后置概念引用（蕴含/导向） |
| [Borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | ⊥ | [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | 策展互斥：move 与活跃借用互斥（01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md:946 “Rust 的所有权（Ownership）转移（move）与借用是互斥的”）（无直接引用边，语义补全） |
| [Rust 错误处理基础](../../01_foundation/08_error_handling/01_error_handling_basics.md) | ⊥ | [Panic 与 Abort：不可恢复错误的处理机制](../../01_foundation/08_error_handling/03_panic_and_abort.md) | 策展互斥：不可恢复(panic/abort)与可恢复(Result 传播)在同一错误现场二选一（01_foundation/08_error_handling/03_panic_and_abort.md:5 “不可恢复错误的处理机制”）（无直接引用边，语义补全） |

## L2 进阶概念层

本节专门讨论「L2 进阶概念层」下的层内引用关系。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [闭包类型系统：Fn、FnMut、FnOnce 的捕获语义](../../02_intermediate/04_types_and_conversions/02_closure_types.md) | ⟹ | [Generics](../../02_intermediate/01_generics/01_generics.md) | 后置概念引用（蕴含/导向） |
| [Const Generics（常量泛型）：值作为类型参数](../../02_intermediate/01_generics/02_const_generics.md) | ⟹ | [类型级编程 (Type-Level Programming)](../../02_intermediate/01_generics/03_type_level_programming.md) | 后置概念引用（蕴含/导向） |
| [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/06_macros_and_metaprogramming/02_dsl_and_embedding.md) | ⟹ | [Serde 序列化模式：Rust 的类型驱动数据转换](../../02_intermediate/00_traits/03_serde_patterns.md) | 后置概念引用（蕴含/导向） |
| [Rust API 命名约定](../../02_intermediate/05_modules_and_visibility/03_api_naming_conventions.md) | ⟹ | [高级类型系统：从关联类型到类型级编程](../../02_intermediate/04_types_and_conversions/04_type_system_advanced.md) | 后置概念引用（蕴含/导向） |
| [Cow：写时克隆与零拷贝抽象](../../02_intermediate/02_memory_management/03_cow_and_borrowed.md) | ⟹ | [Serde 序列化模式：Rust 的类型驱动数据转换](../../02_intermediate/00_traits/03_serde_patterns.md) | 后置概念引用（蕴含/导向） |
| [宏模式：编译期代码生成的工程实践](../../02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md) | ⊑ | [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/06_macros_and_metaprogramming/02_dsl_and_embedding.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Newtype 与包装器模式：类型安全的零成本抽象](../../02_intermediate/04_types_and_conversions/03_newtype_and_wrapper.md) | ⟹ | [智能指针：堆内存管理与共享语义](../../02_intermediate/02_memory_management/04_smart_pointers.md) | 后置概念引用（蕴含/导向） |
| [Panic 机制](../../02_intermediate/03_error_handling/03_panic.md) | ⊑ | [Error Handling](../../02_intermediate/03_error_handling/01_error_handling.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [异常安全：C++ 与 Rust 的错误处理哲学](../../02_intermediate/03_error_handling/04_exception_safety_rust_cpp.md) | ⊑ | [错误处理深入：从 Result 到自定义错误生态](../../02_intermediate/03_error_handling/02_error_handling_deep_dive.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [元编程：Rust 的编译期代码生成与变换](../../02_intermediate/06_macros_and_metaprogramming/04_metaprogramming.md) | ⟹ | [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/06_macros_and_metaprogramming/02_dsl_and_embedding.md) | 后置概念引用（蕴含/导向） |
| [智能指针：堆内存管理与共享语义](../../02_intermediate/02_memory_management/04_smart_pointers.md) | ⟹ | [Cow：写时克隆与零拷贝抽象](../../02_intermediate/02_memory_management/03_cow_and_borrowed.md) | 后置概念引用（蕴含/导向） |
| [C 预处理器 vs Rust 宏：从文本替换到语法树](../../02_intermediate/06_macros_and_metaprogramming/05_c_preprocessor_vs_rust_macros.md) | ⇔ | [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/06_macros_and_metaprogramming/02_dsl_and_embedding.md) | 对比型页面（名称含 vs/对比） |
| [RTTI 与动态类型识别：从 C++ 到 Rust](../../02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md) | ⟹ | [错误处理深入：从 Result 到自定义错误生态](../../02_intermediate/03_error_handling/02_error_handling_deep_dive.md) | 后置概念引用（蕴含/导向） |
| [RTTI 与动态类型识别：从 C++ 到 Rust](../../02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md) | ⟹ | [高级 Trait 主题：从关联类型到特化](../../02_intermediate/00_traits/04_advanced_traits.md) | 后置概念引用（蕴含/导向） |
| [可派生 Trait](../../02_intermediate/00_traits/06_derive_traits.md) | ⊑ | [高级 Trait 主题：从关联类型到特化](../../02_intermediate/00_traits/04_advanced_traits.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [联合体](../../02_intermediate/04_types_and_conversions/06_unions.md) | ⟹ | [内部可变性：编译期规则的运行时逃逸](../../02_intermediate/02_memory_management/02_interior_mutability.md) | 后置概念引用（蕴含/导向） |
| [类型转换](../../02_intermediate/04_types_and_conversions/07_type_conversions.md) | ⊑ | [Newtype 与包装器模式：类型安全的零成本抽象](../../02_intermediate/04_types_and_conversions/03_newtype_and_wrapper.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Memory Management](../../02_intermediate/02_memory_management/01_memory_management.md) | ⊥ | [联合体](../../02_intermediate/04_types_and_conversions/06_unions.md) | 策展互斥：union 默认不 drop 字段，与 RAII 自动析构纪律互斥（02_intermediate/04_types_and_conversions/06_unions.md:103/254 “默认不 drop 字段”）（无直接引用边，语义补全） |
| [类型级编程 (Type-Level Programming)](../../02_intermediate/01_generics/03_type_level_programming.md) | ⊥ | [RTTI 与动态类型识别：从 C++ 到 Rust](../../02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md) | 策展互斥：编译期类型计算与运行期类型识别互斥（02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md:212 “RTTI 是静态类型系统向运行时的有限泄漏”）（无直接引用边，语义补全） |

## L3 高级概念层

「L3 高级概念层」部分的核心主题是层内引用关系，本节展开说明。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [Rust 进程模型与生命周期](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) | ⟸ | [Rust 高级进程管理](../../03_advanced/08_process_ipc/02_advanced_process_management.md) | 源在目标的前置元数据中（目标依赖源） |
| [Rust 进程模型与生命周期](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) | ⟸ | [Rust 异步进程管理](../../03_advanced/08_process_ipc/03_async_process_management.md) | 源在目标的前置元数据中（目标依赖源） |
| [Rust 进程模型与生命周期](../../03_advanced/08_process_ipc/01_process_model_and_lifecycle.md) | ⟸ | [Rust 进程间通信机制](../../03_advanced/08_process_ipc/05_ipc_mechanisms.md) | 源在目标的前置元数据中（目标依赖源） |
| [Unsafe 集合内部实现：Vec、Arc、Mutex](../../03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md) | ⟹ | [自定义分配器与内存布局优化](../../03_advanced/06_low_level_patterns/01_custom_allocators.md) | 后置概念引用（蕴含/导向） |
| [Rust 高级进程管理](../../03_advanced/08_process_ipc/02_advanced_process_management.md) | ⊑ | [Rust 异步进程管理](../../03_advanced/08_process_ipc/03_async_process_management.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust 高级进程管理](../../03_advanced/08_process_ipc/02_advanced_process_management.md) | ⊑ | [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust 高级进程管理](../../03_advanced/08_process_ipc/02_advanced_process_management.md) | ⊑ | [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Send 与 Sync：Auto Trait 的并发安全契约](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md) | ⟹ | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | 后置概念引用（蕴含/导向） |
| [Send 与 Sync：Auto Trait 的并发安全契约](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md) | ⟹ | [原子操作与内存序：无锁并发的精确控制](../../03_advanced/00_concurrency/05_atomics_and_memory_ordering.md) | 后置概念引用（蕴含/导向） |
| [Send 与 Sync：Auto Trait 的并发安全契约](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md) | ⟹ | [无锁编程与内存模型](../../03_advanced/00_concurrency/06_lock_free.md) | 后置概念引用（蕴含/导向） |
| [Send 与 Sync：Auto Trait 的并发安全契约](../../03_advanced/00_concurrency/02_send_sync_auto_traits.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |
| [Unsafe 边界全景](../../03_advanced/02_unsafe/02_unsafe_boundary_panorama.md) | ↔ | [Async 边界全景](../../03_advanced/01_async/06_async_boundary_panorama.md) | 互为后置概念（互参） |
| [Rust 异步进程管理](../../03_advanced/08_process_ipc/03_async_process_management.md) | ⊑ | [Rust 进程间通信机制](../../03_advanced/08_process_ipc/05_ipc_mechanisms.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust 异步进程管理](../../03_advanced/08_process_ipc/03_async_process_management.md) | ⟹ | [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | 后置概念引用（蕴含/导向） |
| [Rust 异步进程管理](../../03_advanced/08_process_ipc/03_async_process_management.md) | ⟸ | [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | 源在目标的前置元数据中（目标依赖源） |
| [并发 模式：从消息 传递到锁自由的数据结构](../../03_advanced/00_concurrency/03_concurrency_patterns.md) | → | [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md) | 目标在源的前置元数据中（源依赖目标） |
| [Linkage](../../03_advanced/04_ffi/03_linkage.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |
| [NLL 与 Polonius：借用检查器的演进](../../03_advanced/02_unsafe/03_nll_and_polonius.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |
| [过程宏代码生成优化](../../03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md) | ⟹ | [生产级宏开发](../../03_advanced/03_proc_macros/05_production_grade_macro_development.md) | 后置概念引用（蕴含/导向） |
| [过程宏代码生成优化](../../03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md) | ⟹ | [宏调试与诊断](../../03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md) | 后置概念引用（蕴含/导向） |
| [Rust 跨平台进程管理](../../03_advanced/08_process_ipc/04_cross_platform_process_management.md) | ⊑ | [Rust 进程间通信机制](../../03_advanced/08_process_ipc/05_ipc_mechanisms.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust 跨平台进程管理](../../03_advanced/08_process_ipc/04_cross_platform_process_management.md) | ⟹ | [Rust 进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) | 后置概念引用（蕴含/导向） |
| [Rust 跨平台进程管理](../../03_advanced/08_process_ipc/04_cross_platform_process_management.md) | ⟹ | [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | 后置概念引用（蕴含/导向） |
| [宏调试与诊断](../../03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md) | ⟸ | [生产级宏开发](../../03_advanced/03_proc_macros/05_production_grade_macro_development.md) | 源在目标的前置元数据中（目标依赖源） |
| [Rust 网络编程：Tokio TCP/UDP、异步 IO 与 Tower 服务抽象](../../03_advanced/06_low_level_patterns/04_network_programming.md) | ⟹ | [无锁编程与内存模型](../../03_advanced/00_concurrency/06_lock_free.md) | 后置概念引用（蕴含/导向） |
| [Unsafe Rust 模式：安全抽象的核心技术](../../03_advanced/02_unsafe/04_unsafe_rust_patterns.md) | → | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 目标在源的前置元数据中（源依赖目标） |
| [Rust 进程间通信机制](../../03_advanced/08_process_ipc/05_ipc_mechanisms.md) | ⟸ | [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | 源在目标的前置元数据中（目标依赖源） |
| [Rust 进程间通信机制](../../03_advanced/08_process_ipc/05_ipc_mechanisms.md) | ⟸ | [Rust 进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) | 源在目标的前置元数据中（目标依赖源） |
| [Rust 进程间通信机制](../../03_advanced/08_process_ipc/05_ipc_mechanisms.md) | ⟸ | [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | 源在目标的前置元数据中（目标依赖源） |
| [Async 边界全景](../../03_advanced/01_async/06_async_boundary_panorama.md) | ⟹ | [Async 取消安全](../../03_advanced/01_async/05_async_cancellation_safety.md) | 后置概念引用（蕴含/导向） |
| [Async 边界全景](../../03_advanced/01_async/06_async_boundary_panorama.md) | ↔ | [Unsafe 边界全景](../../03_advanced/02_unsafe/02_unsafe_boundary_panorama.md) | 互为后置概念（互参） |
| [无锁编程与内存模型](../../03_advanced/00_concurrency/06_lock_free.md) | ⊑ | [并发 模式：从消息 传递到锁自由的数据结构](../../03_advanced/00_concurrency/03_concurrency_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [术语表 - C11 Macro System](../../03_advanced/03_proc_macros/06_macro_glossary.md) | ⟹ | [宏卫生性完整参考](../../03_advanced/03_proc_macros/09_macro_hygiene.md) | 后置概念引用（蕴含/导向） |
| [术语表 - C11 Macro System](../../03_advanced/03_proc_macros/06_macro_glossary.md) | ⟸ | [syn & quote 完整参考](../../03_advanced/03_proc_macros/08_syn_quote_reference.md) | 源在目标的前置元数据中（目标依赖源） |
| [Rust 内存模型](../../03_advanced/02_unsafe/06_memory_model.md) | ⟹ | [原子操作与内存序：无锁并发的精确控制](../../03_advanced/00_concurrency/05_atomics_and_memory_ordering.md) | 后置概念引用（蕴含/导向） |
| [Rust 内存模型](../../03_advanced/02_unsafe/06_memory_model.md) | ⟹ | [内联汇编 (Inline Assembly)](../../03_advanced/05_inline_assembly/01_inline_assembly.md) | 后置概念引用（蕴含/导向） |
| [所有权性能优化](../../03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md) | ⟹ | [零拷贝解析与序列化优化](../../03_advanced/06_low_level_patterns/02_zero_copy_parsing.md) | 后置概念引用（蕴含/导向） |
| [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | ⟹ | [Rust 进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) | 后置概念引用（蕴含/导向） |
| [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | ↔ | [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | 互为后置概念（互参） |
| [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | ↔ | [Rust 进程测试与基准](../../03_advanced/08_process_ipc/09_process_testing_and_benchmarking.md) | 互为后置概念（互参） |
| [常见问题 (FAQ) - C11 Macro System](../../03_advanced/03_proc_macros/07_macro_faq.md) | ⟹ | [宏卫生性完整参考](../../03_advanced/03_proc_macros/09_macro_hygiene.md) | 后置概念引用（蕴含/导向） |
| [常见问题 (FAQ) - C11 Macro System](../../03_advanced/03_proc_macros/07_macro_faq.md) | ⟹ | [生产级宏开发](../../03_advanced/03_proc_macros/05_production_grade_macro_development.md) | 后置概念引用（蕴含/导向） |
| [Rust 进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) | ⟹ | [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | 后置概念引用（蕴含/导向） |
| [Rust 进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) | ⟹ | [Rust 进程测试与基准](../../03_advanced/08_process_ipc/09_process_testing_and_benchmarking.md) | 后置概念引用（蕴含/导向） |
| [Rust 进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) | ↔ | [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | 互为后置概念（互参） |
| [Rust 运行时](../../03_advanced/06_low_level_patterns/07_rust_runtime.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |
| [Unsafe 参考](../../03_advanced/02_unsafe/07_unsafe_reference.md) | ⟹ | [内联汇编 (Inline Assembly)](../../03_advanced/05_inline_assembly/01_inline_assembly.md) | 后置概念引用（蕴含/导向） |
| [Unsafe 参考](../../03_advanced/02_unsafe/07_unsafe_reference.md) | ⟹ | [FFI 高级主题：跨语言边界的安全与性能](../../03_advanced/04_ffi/02_ffi_advanced.md) | 后置概念引用（蕴含/导向） |
| [Unsafe 参考](../../03_advanced/02_unsafe/07_unsafe_reference.md) | ⟹ | [自定义分配器与内存布局优化](../../03_advanced/06_low_level_patterns/01_custom_allocators.md) | 后置概念引用（蕴含/导向） |
| [内存分配与生命周期](../../03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md) | ⟹ | [自定义分配器与内存布局优化](../../03_advanced/06_low_level_patterns/01_custom_allocators.md) | 后置概念引用（蕴含/导向） |
| [内存分配与生命周期](../../03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md) | ⟹ | [Rust 运行时](../../03_advanced/06_low_level_patterns/07_rust_runtime.md) | 后置概念引用（蕴含/导向） |
| [Pin 与 Unpin：自引用类型的不动性保证](../../03_advanced/01_async/08_pin_unpin.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |
| [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | ↔ | [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | 互为后置概念（互参） |
| [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | ↔ | [Rust 进程测试与基准](../../03_advanced/08_process_ipc/09_process_testing_and_benchmarking.md) | 互为后置概念（互参） |
| [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | ↔ | [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | 互为后置概念（互参） |
| [syn & quote 完整参考](../../03_advanced/03_proc_macros/08_syn_quote_reference.md) | ⟹ | [生产级宏开发](../../03_advanced/03_proc_macros/05_production_grade_macro_development.md) | 后置概念引用（蕴含/导向） |
| [syn & quote 完整参考](../../03_advanced/03_proc_macros/08_syn_quote_reference.md) | ⟸ | [宏卫生性完整参考](../../03_advanced/03_proc_macros/09_macro_hygiene.md) | 源在目标的前置元数据中（目标依赖源） |
| [宏卫生性完整参考](../../03_advanced/03_proc_macros/09_macro_hygiene.md) | ⟹ | [生产级宏开发](../../03_advanced/03_proc_macros/05_production_grade_macro_development.md) | 后置概念引用（蕴含/导向） |
| [宏卫生性完整参考](../../03_advanced/03_proc_macros/09_macro_hygiene.md) | ⟹ | [宏调试与诊断](../../03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md) | 后置概念引用（蕴含/导向） |
| [Rust 进程测试与基准](../../03_advanced/08_process_ipc/09_process_testing_and_benchmarking.md) | ↔ | [Rust 进程监控与诊断](../../03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md) | 互为后置概念（互参） |
| [Rust 进程测试与基准](../../03_advanced/08_process_ipc/09_process_testing_and_benchmarking.md) | ↔ | [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | 互为后置概念（互参） |
| [Rust 进程测试与基准](../../03_advanced/08_process_ipc/09_process_testing_and_benchmarking.md) | ↔ | [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | 互为后置概念（互参） |
| [Stream 代数与背压：拉取式序列的形式刻画](../../03_advanced/01_async/09_stream_algebra_and_backpressure.md) | ↔ | [Executor 公平性与调度：Tokio 调度器 internals](../../03_advanced/01_async/10_executor_fairness_and_scheduling.md) | 互为后置概念（互参） |
| [Stream 代数与背压：拉取式序列的形式刻画](../../03_advanced/01_async/09_stream_algebra_and_backpressure.md) | ⟹ | [Async 取消安全](../../03_advanced/01_async/05_async_cancellation_safety.md) | 后置概念引用（蕴含/导向） |
| [变量](../../03_advanced/06_low_level_patterns/09_variables.md) | ⟸ | [内存分配与生命周期](../../03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md) | 源在目标的前置元数据中（目标依赖源） |
| [变量](../../03_advanced/06_low_level_patterns/09_variables.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |
| [Executor 公平性与调度：Tokio 调度器 internals](../../03_advanced/01_async/10_executor_fairness_and_scheduling.md) | ↔ | [Stream 代数与背压：拉取式序列的形式刻画](../../03_advanced/01_async/09_stream_algebra_and_backpressure.md) | 互为后置概念（互参） |
| [Executor 公平性与调度：Tokio 调度器 internals](../../03_advanced/01_async/10_executor_fairness_and_scheduling.md) | ⊑ | [Async 取消安全](../../03_advanced/01_async/05_async_cancellation_safety.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | ↔ | [Rust 进程性能工程](../../03_advanced/08_process_ipc/08_process_performance_engineering.md) | 互为后置概念（互参） |
| [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | ↔ | [Rust 进程安全与沙箱](../../03_advanced/08_process_ipc/07_process_security_and_sandboxing.md) | 互为后置概念（互参） |
| [Rust 现代进程管理库](../../03_advanced/08_process_ipc/10_modern_process_libraries.md) | ↔ | [Rust 进程测试与基准](../../03_advanced/08_process_ipc/09_process_testing_and_benchmarking.md) | 互为后置概念（互参） |
| [条件编译](../../03_advanced/03_proc_macros/11_conditional_compilation.md) | ⟹ | [FFI 高级主题：跨语言边界的安全与性能](../../03_advanced/04_ffi/02_ffi_advanced.md) | 后置概念引用（蕴含/导向） |
| [条件编译](../../03_advanced/03_proc_macros/11_conditional_compilation.md) | ⟹ | [Linkage](../../03_advanced/04_ffi/03_linkage.md) | 后置概念引用（蕴含/导向） |
| [Pin 投射反例集：unsafe 结构投射的 UB 目录与正确模式库](../../03_advanced/01_async/11_pin_projection_counterexamples.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |
| [Pin 投射反例集：unsafe 结构投射的 UB 目录与正确模式库](../../03_advanced/01_async/11_pin_projection_counterexamples.md) | ⊑ | [Async 取消安全](../../03_advanced/01_async/05_async_cancellation_safety.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Waker 契约深度解析：RawWakerVTable 实现与契约违反反例集](../../03_advanced/01_async/12_waker_contract_deep_dive.md) | ⊑ | [Executor 公平性与调度：Tokio 调度器 internals](../../03_advanced/01_async/10_executor_fairness_and_scheduling.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Waker 契约深度解析：RawWakerVTable 实现与契约违反反例集](../../03_advanced/01_async/12_waker_contract_deep_dive.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/02_unsafe/01_unsafe.md) | 后置概念引用（蕴含/导向） |

## L4 形式化理论层

本节聚焦「L4 形式化理论层」，核心内容为层内引用关系。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [指称语义与领域理论](../../04_formal/03_operational_semantics/01_denotational_semantics.md) | ⟹ | [范畴论与 Rust：从函子到单子](../../04_formal/00_type_theory/04_category_theory.md) | 后置概念引用（蕴含/导向） |
| [指称语义与领域理论](../../04_formal/03_operational_semantics/01_denotational_semantics.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [Linear Logic & Affine Logic](../../04_formal/01_ownership_logic/01_linear_logic.md) | ⟹ | [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | 后置概念引用（蕴含/导向） |
| [Linear Logic & Affine Logic](../../04_formal/01_ownership_logic/01_linear_logic.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [符号约定](../../04_formal/06_notation/01_notation.md) | ⟸ | [词法结构](../../04_formal/05_rustc_internals/10_lexical_structure.md) | 源在目标的前置元数据中（目标依赖源） |
| [Type Theory](../../04_formal/00_type_theory/01_type_theory.md) | ⟹ | [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | 后置概念引用（蕴含/导向） |
| [Type Theory](../../04_formal/00_type_theory/01_type_theory.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [Hoare 逻辑：程序验证的形式化基础与 Rust 契约](../../04_formal/03_operational_semantics/02_hoare_logic.md) | ⟹ | [分离逻辑：Rust 所有权的形式化根基](../../04_formal/02_separation_logic/02_separation_logic.md) | 后置概念引用（蕴含/导向） |
| [Hoare 逻辑：程序验证的形式化基础与 Rust 契约](../../04_formal/03_operational_semantics/02_hoare_logic.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | ⟸ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 源在目标的前置元数据中（目标依赖源） |
| [分离逻辑：Rust 所有权的形式化根基](../../04_formal/02_separation_logic/02_separation_logic.md) | ⟹ | [Verification Toolchain Selection Guide](../../04_formal/04_model_checking/01_verification_toolchain.md) | 后置概念引用（蕴含/导向） |
| [分离逻辑：Rust 所有权的形式化根基](../../04_formal/02_separation_logic/02_separation_logic.md) | ⟹ | [Type Theory](../../04_formal/00_type_theory/01_type_theory.md) | 后置概念引用（蕴含/导向） |
| [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/00_type_theory/02_subtype_variance.md) | ⟹ | [Type Theory](../../04_formal/00_type_theory/01_type_theory.md) | 后置概念引用（蕴含/导向） |
| [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/00_type_theory/02_subtype_variance.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [线性逻辑在 Rust 中的工程应用](../../04_formal/01_ownership_logic/03_linear_logic_applications.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [操作语义：程序行为的形式化定义](../../04_formal/03_operational_semantics/03_operational_semantics.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [操作语义：程序行为的形式化定义](../../04_formal/03_operational_semantics/03_operational_semantics.md) | ⟹ | [分离逻辑：Rust 所有权的形式化根基](../../04_formal/02_separation_logic/02_separation_logic.md) | 后置概念引用（蕴含/导向） |
| [rustc 中的 Trait Solver](../../04_formal/05_rustc_internals/03_trait_solver_in_rustc.md) | ⟹ | [Rustc 查询系统与增量编译](../../04_formal/05_rustc_internals/01_rustc_query_system.md) | 后置概念引用（蕴含/导向） |
| [rustc 中的 Trait Solver](../../04_formal/05_rustc_internals/03_trait_solver_in_rustc.md) | ⟹ | [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | 后置概念引用（蕴含/导向） |
| [类型推断：Hindley-Milner 算法与 Rust 的工业实现](../../04_formal/00_type_theory/03_type_inference.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [类型推断：Hindley-Milner 算法与 Rust 的工业实现](../../04_formal/00_type_theory/03_type_inference.md) | ⟹ | [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/00_type_theory/02_subtype_variance.md) | 后置概念引用（蕴含/导向） |
| [Borrow Checking Decidability](../../04_formal/01_ownership_logic/04_borrow_checking_decidability.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [Borrow Checking Decidability](../../04_formal/01_ownership_logic/04_borrow_checking_decidability.md) | ⟹ | [rustc 类型检查与类型推断](../../04_formal/00_type_theory/07_type_checking_and_inference.md) | 后置概念引用（蕴含/导向） |
| [Borrow Checking Decidability](../../04_formal/01_ownership_logic/04_borrow_checking_decidability.md) | ⟹ | [Tree Borrows 深度解析](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) | 后置概念引用（蕴含/导向） |
| [BorrowSanitizer 运行时别名模型检测](../../04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md) | ↔ | [AutoVerus / Verus 自动证明生态](../../04_formal/04_model_checking/07_autoverus.md) | 互为后置概念（互参） |
| [范畴论与 Rust：从函子到单子](../../04_formal/00_type_theory/04_category_theory.md) | ⟹ | [Linear Logic & Affine Logic](../../04_formal/01_ownership_logic/01_linear_logic.md) | 后置概念引用（蕴含/导向） |
| [范畴论与 Rust：从函子到单子](../../04_formal/00_type_theory/04_category_theory.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [求值策略：Call-by-Value, Call-by-Name, Call-by-Need](../../04_formal/03_operational_semantics/04_evaluation_strategies.md) | ⟹ | [Ownership Formalization](../../04_formal/01_ownership_logic/02_ownership_formal.md) | 后置概念引用（蕴含/导向） |
| [Rustc 名称解析与 HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) | ⟹ | [Rustc 查询系统与增量编译](../../04_formal/05_rustc_internals/01_rustc_query_system.md) | 后置概念引用（蕴含/导向） |
| [Rustc 名称解析与 HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) | ⟹ | [类型推断：Hindley-Milner 算法与 Rust 的工业实现](../../04_formal/00_type_theory/03_type_inference.md) | 后置概念引用（蕴含/导向） |
| [Rustc 名称解析与 HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) | ⟸ | [rustc 中的 Trait Solver](../../04_formal/05_rustc_internals/03_trait_solver_in_rustc.md) | 源在目标的前置元数据中（目标依赖源） |
| [Axiomatic Semantics](../../04_formal/03_operational_semantics/05_axiomatic_semantics.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [Axiomatic Semantics](../../04_formal/03_operational_semantics/05_axiomatic_semantics.md) | ⟹ | [分离逻辑：Rust 所有权的形式化根基](../../04_formal/02_separation_logic/02_separation_logic.md) | 后置概念引用（蕴含/导向） |
| [Axiomatic Semantics](../../04_formal/03_operational_semantics/05_axiomatic_semantics.md) | ⟹ | [Verification Toolchain Selection Guide](../../04_formal/04_model_checking/01_verification_toolchain.md) | 后置概念引用（蕴含/导向） |
| [Lambda 演算与 Rust 计算模型](../../04_formal/00_type_theory/05_lambda_calculus.md) | ⟹ | [范畴论与 Rust：从函子到单子](../../04_formal/00_type_theory/04_category_theory.md) | 后置概念引用（蕴含/导向） |
| [Lambda 演算与 Rust 计算模型](../../04_formal/00_type_theory/05_lambda_calculus.md) | ⟹ | [指称语义与领域理论](../../04_formal/03_operational_semantics/01_denotational_semantics.md) | 后置概念引用（蕴含/导向） |
| [Tree Borrows 深度解析](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) | ⟹ | [BorrowSanitizer 运行时别名模型检测](../../04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md) | 后置概念引用（蕴含/导向） |
| [Tree Borrows 深度解析](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) | ↔ | [Miri：Rust 未定义行为动态检测器](../../04_formal/04_model_checking/08_miri.md) | 互为后置概念（互参） |
| [未定义行为清单](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | ⟹ | [Miri：Rust 未定义行为动态检测器](../../04_formal/04_model_checking/08_miri.md) | 后置概念引用（蕴含/导向） |
| [未定义行为清单](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | ⟹ | [Tree Borrows 深度解析](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) | 后置概念引用（蕴含/导向） |
| [名称、作用域与解析](../../04_formal/05_rustc_internals/06_names_and_resolution.md) | ⟹ | [Rustc 名称解析与 HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) | 后置概念引用（蕴含/导向） |
| [名称、作用域与解析](../../04_formal/05_rustc_internals/06_names_and_resolution.md) | ⟸ | [名字参考](../../04_formal/05_rustc_internals/16_names_reference.md) | 源在目标的前置元数据中（目标依赖源） |
| [Type Semantics](../../04_formal/00_type_theory/06_type_semantics.md) | ⟹ | [Axiomatic Semantics](../../04_formal/03_operational_semantics/05_axiomatic_semantics.md) | 后置概念引用（蕴含/导向） |
| [Type Semantics](../../04_formal/00_type_theory/06_type_semantics.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/02_separation_logic/01_rustbelt.md) | 后置概念引用（蕴含/导向） |
| [AutoVerus / Verus 自动证明生态](../../04_formal/04_model_checking/07_autoverus.md) | ↔ | [BorrowSanitizer 运行时别名模型检测](../../04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md) | 互为后置概念（互参） |
| [Miri：Rust 未定义行为动态检测器](../../04_formal/04_model_checking/08_miri.md) | ↔ | [Tree Borrows 深度解析](../../04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) | 互为后置概念（互参） |
| [Miri：Rust 未定义行为动态检测器](../../04_formal/04_model_checking/08_miri.md) | ⟸ | [BorrowSanitizer 运行时别名模型检测](../../04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md) | 源在目标的前置元数据中（目标依赖源） |
| [Miri：Rust 未定义行为动态检测器](../../04_formal/04_model_checking/08_miri.md) | ⟹ | [现代 Rust 验证工具生态](../../04_formal/04_model_checking/04_modern_verification_tools.md) | 后置概念引用（蕴含/导向） |
| [Type Inference Complexity](../../04_formal/00_type_theory/08_type_inference_complexity.md) | ⟹ | [rustc 类型检查与类型推断](../../04_formal/00_type_theory/07_type_checking_and_inference.md) | 后置概念引用（蕴含/导向） |
| [Type Inference Complexity](../../04_formal/00_type_theory/08_type_inference_complexity.md) | ⟹ | [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/00_type_theory/02_subtype_variance.md) | 后置概念引用（蕴含/导向） |
| [类型布局](../../04_formal/05_rustc_internals/08_type_layout.md) | ⟹ | [未定义行为清单](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | 后置概念引用（蕴含/导向） |
| [析构函数与 Drop Scope](../../04_formal/05_rustc_internals/09_destructors.md) | ⟹ | [未定义行为清单](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | 后置概念引用（蕴含/导向） |
| [Kani：Rust 有界模型检查器](../../04_formal/04_model_checking/09_kani.md) | ⟹ | [Miri：Rust 未定义行为动态检测器](../../04_formal/04_model_checking/08_miri.md) | 后置概念引用（蕴含/导向） |
| [Kani：Rust 有界模型检查器](../../04_formal/04_model_checking/09_kani.md) | ⟹ | [BorrowSanitizer 运行时别名模型检测](../../04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md) | 后置概念引用（蕴含/导向） |
| [类型系统参考](../../04_formal/00_type_theory/09_type_system_reference.md) | ⟹ | [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/00_type_theory/02_subtype_variance.md) | 后置概念引用（蕴含/导向） |
| [类型系统参考](../../04_formal/00_type_theory/09_type_system_reference.md) | ⟹ | [未定义行为清单](../../04_formal/01_ownership_logic/06_behavior_considered_undefined.md) | 后置概念引用（蕴含/导向） |
| [类型系统参考](../../04_formal/00_type_theory/09_type_system_reference.md) | ⟹ | [Application Binary Interface](../../04_formal/05_rustc_internals/05_application_binary_interface.md) | 后置概念引用（蕴含/导向） |
| [词法结构](../../04_formal/05_rustc_internals/10_lexical_structure.md) | ⟹ | [名称、作用域与解析](../../04_formal/05_rustc_internals/06_names_and_resolution.md) | 后置概念引用（蕴含/导向） |
| [词法结构](../../04_formal/05_rustc_internals/10_lexical_structure.md) | ⟹ | [条目参考](../../04_formal/05_rustc_internals/11_items_reference.md) | 后置概念引用（蕴含/导向） |
| [条目参考](../../04_formal/05_rustc_internals/11_items_reference.md) | ⟸ | [属性](../../04_formal/05_rustc_internals/12_attributes.md) | 源在目标的前置元数据中（目标依赖源） |
| [语句与表达式参考](../../04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) | ↔ | [模式参考](../../04_formal/05_rustc_internals/14_patterns_reference.md) | 互为后置概念（互参） |
| [语句与表达式参考](../../04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) | ⟹ | [常量求值](../../04_formal/03_operational_semantics/07_constant_evaluation.md) | 后置概念引用（蕴含/导向） |
| [语句与表达式参考](../../04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) | ⟹ | [析构函数与 Drop Scope](../../04_formal/05_rustc_internals/09_destructors.md) | 后置概念引用（蕴含/导向） |
| [模式参考](../../04_formal/05_rustc_internals/14_patterns_reference.md) | ⊑ | [析构函数与 Drop Scope](../../04_formal/05_rustc_internals/09_destructors.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [模式参考](../../04_formal/05_rustc_internals/14_patterns_reference.md) | ↔ | [语句与表达式参考](../../04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) | 互为后置概念（互参） |
| [泛型编译器行为：单态化、分发与类型擦除](../../04_formal/05_rustc_internals/15_generics_compiler_behavior.md) | ⟹ | [rustc 中的 Trait Solver](../../04_formal/05_rustc_internals/03_trait_solver_in_rustc.md) | 后置概念引用（蕴含/导向） |
| [泛型编译器行为：单态化、分发与类型擦除](../../04_formal/05_rustc_internals/15_generics_compiler_behavior.md) | ⟹ | [类型布局](../../04_formal/05_rustc_internals/08_type_layout.md) | 后置概念引用（蕴含/导向） |
| [名字参考](../../04_formal/05_rustc_internals/16_names_reference.md) | ⟹ | [条目参考](../../04_formal/05_rustc_internals/11_items_reference.md) | 后置概念引用（蕴含/导向） |
| [名字参考](../../04_formal/05_rustc_internals/16_names_reference.md) | ⊑ | [模式参考](../../04_formal/05_rustc_internals/14_patterns_reference.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust Reference 附录](../../04_formal/05_rustc_internals/17_reference_appendices.md) | ⟹ | [语句与表达式参考](../../04_formal/05_rustc_internals/13_statements_and_expressions_reference.md) | 后置概念引用（蕴含/导向） |
| [Rust Reference 附录](../../04_formal/05_rustc_internals/17_reference_appendices.md) | ⊑ | [模式参考](../../04_formal/05_rustc_internals/14_patterns_reference.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |

## L5 对比分析层

本节聚焦「L5 对比分析层」，核心内容为层内引用关系。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [Rust vs Python：系统编程与动态脚本的对照分析](../../05_comparative/02_managed_languages/02_rust_vs_python.md) | ⇔ | [Rust vs Go：线性所有权 vs CSP 过程逻辑](../../05_comparative/01_systems_languages/03_rust_vs_go.md) | 对比型页面（名称含 vs/对比） |
| [Rust vs Python：系统编程与动态脚本的对照分析](../../05_comparative/02_managed_languages/02_rust_vs_python.md) | ⇔ | [Rust vs Java：系统编程与托管运行时的范式对比](../../05_comparative/02_managed_languages/01_rust_vs_java.md) | 对比型页面（名称含 vs/对比） |
| [C++ vs Rust：构造、运算符、RTTI、友元](../../05_comparative/00_paradigms/03_cpp_rust_surface_features.md) | ⇔ | [Rust vs C++：ABI、对象模型与内存布局](../../05_comparative/01_systems_languages/02_cpp_abi_object_model.md) | 对比型页面（名称含 vs/对比） |
| [Rust vs Go：线性所有权 vs CSP 过程逻辑](../../05_comparative/01_systems_languages/03_rust_vs_go.md) | ⇔ | [Paradigm Matrix: Multi-Language Formal Comparison](../../05_comparative/00_paradigms/01_paradigm_matrix.md) | 对比型页面（名称含 vs/对比） |
| [Rust vs Scala：类型系统的两种哲学](../../05_comparative/02_managed_languages/05_rust_vs_scala.md) | ⇔ | [Paradigm Matrix: Multi-Language Formal Comparison](../../05_comparative/00_paradigms/01_paradigm_matrix.md) | 对比型页面（名称含 vs/对比） |
| [Rust vs TypeScript：静态类型系统的两种哲学 —— 编译期证明与渐进式工程](../../05_comparative/02_managed_languages/08_rust_vs_typescript.md) | ⇔ | [Rust vs JavaScript：系统编程与脚本执行的范式差异](../../05_comparative/02_managed_languages/03_rust_vs_javascript.md) | 对比型页面（名称含 vs/对比） |

## L6 生态工程层

本节专门讨论「L6 生态工程层」下的层内引用关系。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [Rust 高级网络协议概览](../../06_ecosystem/12_networking/01_advanced_network_protocols.md) | ⟹ | [高性能网络服务架构 (High-Performance Network Service Architecture)](../../06_ecosystem/04_web_and_networking/08_high_performance_network_service_architecture.md) | 后置概念引用（蕴含/导向） |
| [Rust 高级网络协议概览](../../06_ecosystem/12_networking/01_advanced_network_protocols.md) | ↔ | [网络安全](../../06_ecosystem/12_networking/02_network_security.md) | 互为后置概念（互参） |
| [Blockchain & Smart Contract Security](../../06_ecosystem/11_domain_applications/01_blockchain.md) | ⟹ | [Formal Ecosystem Tower](../../06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md) | 后置概念引用（蕴含/导向） |
| [Blockchain & Smart Contract Security](../../06_ecosystem/11_domain_applications/01_blockchain.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [Core Crates](../../06_ecosystem/02_core_crates/01_core_crates.md) | ⟸ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 源在目标的前置元数据中（目标依赖源） |
| [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_domain_applications/03_webassembly.md) | 后置概念引用（蕴含/导向） |
| [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | ⟹ | [日志与可观测性：Rust 服务端监控生态](../../06_ecosystem/00_toolchain/02_logging_observability.md) | 后置概念引用（蕴含/导向） |
| [Formal Ecosystem Tower](../../06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [Formal Ecosystem Tower](../../06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md) | ⟹ | [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) | 后置概念引用（蕴含/导向） |
| [安全 实践：Rust 代码的防御性编程](../../06_ecosystem/07_security_and_cryptography/01_security_practices.md) | ⟹ | [Blockchain & Smart Contract Security](../../06_ecosystem/11_domain_applications/01_blockchain.md) | 后置概念引用（蕴含/导向） |
| [WASI & WebAssembly Component Model](../../06_ecosystem/05_systems_and_embedded/01_wasi.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [WASI & WebAssembly Component Model](../../06_ecosystem/05_systems_and_embedded/01_wasi.md) | ⟹ | [Formal Ecosystem Tower](../../06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md) | 后置概念引用（蕴含/导向） |
| [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_domain_applications/03_webassembly.md) | 后置概念引用（蕴含/导向） |
| [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | → | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 目标在源的前置元数据中（源依赖目标） |
| [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | ⟹ | [WASI & WebAssembly Component Model](../../06_ecosystem/05_systems_and_embedded/01_wasi.md) | 后置概念引用（蕴含/导向） |
| [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_domain_applications/03_webassembly.md) | 后置概念引用（蕴含/导向） |
| [Rust 数据库访问生态](../../06_ecosystem/06_data_and_distributed/02_database_access.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Rust 数据库访问生态](../../06_ecosystem/06_data_and_distributed/02_database_access.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [文档生态：rustdoc、文档测试与 API 文档规范](../../06_ecosystem/09_testing_and_quality/02_documentation.md) | ⟹ | [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) | 后置概念引用（蕴含/导向） |
| [文档生态：rustdoc、文档测试与 API 文档规范](../../06_ecosystem/09_testing_and_quality/02_documentation.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_domain_applications/03_webassembly.md) | 后置概念引用（蕴含/导向） |
| [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md) | ⟹ | [Rust 编译器内部原理](../../06_ecosystem/00_toolchain/04_compiler_internals.md) | 后置概念引用（蕴含/导向） |
| [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md) | ⟹ | [Security & Cryptography](../../06_ecosystem/07_security_and_cryptography/02_security_cryptography.md) | 后置概念引用（蕴含/导向） |
| [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md) | ⟹ | [Rust 嵌入式系统开发](../../06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) | 后置概念引用（蕴含/导向） |
| [Game Development & ECS Architecture](../../06_ecosystem/11_domain_applications/02_game_ecs.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [Game Development & ECS Architecture](../../06_ecosystem/11_domain_applications/02_game_ecs.md) | ⟹ | [Formal Ecosystem Tower](../../06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md) | 后置概念引用（蕴含/导向） |
| [日志与可观测性：Rust 服务端监控生态](../../06_ecosystem/00_toolchain/02_logging_observability.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_domain_applications/03_webassembly.md) | 后置概念引用（蕴含/导向） |
| [网络安全](../../06_ecosystem/12_networking/02_network_security.md) | ↔ | [Rust 高级网络协议概览](../../06_ecosystem/12_networking/01_advanced_network_protocols.md) | 互为后置概念（互参） |
| [网络安全](../../06_ecosystem/12_networking/02_network_security.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [Cargo `public = true` 与 Resolver v3](../../06_ecosystem/01_cargo/02_public_private_deps.md) | → | [Cargo Workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md) | 目标在源的前置元数据中（源依赖目标） |
| [Security & Cryptography](../../06_ecosystem/07_security_and_cryptography/02_security_cryptography.md) | ⟹ | [网络协议：QUIC/HTTP-3 与 Rust 实现](../../06_ecosystem/04_web_and_networking/07_network_protocols.md) | 后置概念引用（蕴含/导向） |
| [Security & Cryptography](../../06_ecosystem/07_security_and_cryptography/02_security_cryptography.md) | ⟹ | [Blockchain & Smart Contract Security](../../06_ecosystem/11_domain_applications/01_blockchain.md) | 后置概念引用（蕴含/导向） |
| [cargo vet 与供应链审计](../../06_ecosystem/07_security_and_cryptography/03_cargo_vet_supply_chain.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [自定义协议实现](../../06_ecosystem/12_networking/03_custom_protocol_implementation.md) | ⊑ | [Rust 高级网络协议概览](../../06_ecosystem/12_networking/01_advanced_network_protocols.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [自定义协议实现](../../06_ecosystem/12_networking/03_custom_protocol_implementation.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | 后置概念引用（蕴含/导向） |
| [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | ⟹ | [安全 实践：Rust 代码的防御性编程](../../06_ecosystem/07_security_and_cryptography/01_security_practices.md) | 后置概念引用（蕴含/导向） |
| [Rust 嵌入式系统开发](../../06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |
| [Rust 嵌入式系统开发](../../06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [Resolver v3 与 `public = true` 的 feature unification 演示](../../06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md) | ⟹ | [Cargo 1.96 新特性与工具链变更](../../06_ecosystem/01_cargo/04_cargo_196_features.md) | 后置概念引用（蕴含/导向） |
| [流处理生态：Rust 实现与工业系统全景](../../06_ecosystem/06_data_and_distributed/03_stream_processing_ecosystem.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [Rust Web 框架对比与选型](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) | ⇔ | [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | 对比型页面（名称含 vs/对比） |
| [Rust Web 框架对比与选型](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) | ⇔ | [Design Patterns](../../06_ecosystem/03_design_patterns/01_patterns.md) | 对比型页面（名称含 vs/对比） |
| [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_domain_applications/03_webassembly.md) | ⟹ | [WASI & WebAssembly Component Model](../../06_ecosystem/05_systems_and_embedded/01_wasi.md) | 后置概念引用（蕴含/导向） |
| [基准测试：Rust 代码性能测量与回归检测](../../06_ecosystem/09_testing_and_quality/04_benchmarking.md) | ⟹ | [算法工程实践 (Algorithm Engineering Practice)](../../06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md) | 后置概念引用（蕴含/导向） |
| [Rust CLI 开发生态](../../06_ecosystem/05_systems_and_embedded/04_cli_development.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Rust CLI 开发生态](../../06_ecosystem/05_systems_and_embedded/04_cli_development.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |
| [数据库系统：Rust 在存储引擎中的语义](../../06_ecosystem/06_data_and_distributed/04_database_systems.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [HTTP 客户端开发](../../06_ecosystem/04_web_and_networking/04_http_client_development.md) | ⇔ | [Rust Web 框架对比与选型](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) | 对比型页面（名称含 vs/对比） |
| [HTTP 客户端开发](../../06_ecosystem/04_web_and_networking/04_http_client_development.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [许可证与合规：Rust 项目的法律工程](../../06_ecosystem/11_domain_applications/04_licensing_and_compliance.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |
| [许可证与合规：Rust 项目的法律工程](../../06_ecosystem/11_domain_applications/04_licensing_and_compliance.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [Rust 网络编程快速入门](../../06_ecosystem/12_networking/04_network_programming_quick_start.md) | ⟹ | [高性能网络服务架构 (High-Performance Network Service Architecture)](../../06_ecosystem/04_web_and_networking/08_high_performance_network_service_architecture.md) | 后置概念引用（蕴含/导向） |
| [Rust 网络编程快速入门](../../06_ecosystem/12_networking/04_network_programming_quick_start.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [系统可组合性 (System Composability)](../../06_ecosystem/03_design_patterns/04_system_composability.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [Cargo Build Scripts](../../06_ecosystem/01_cargo/05_cargo_build_scripts.md) | ⟹ | [Cargo Registry 与包发布](../../06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) | 后置概念引用（蕴含/导向） |
| [Cargo Build Scripts](../../06_ecosystem/01_cargo/05_cargo_build_scripts.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [Rust 编译器基础设施深度解析](../../06_ecosystem/00_toolchain/05_compiler_infrastructure.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Data Engineering](../../06_ecosystem/06_data_and_distributed/05_data_engineering.md) | ⟹ | [流处理生态：Rust 实现与工业系统全景](../../06_ecosystem/06_data_and_distributed/03_stream_processing_ecosystem.md) | 后置概念引用（蕴含/导向） |
| [Data Engineering](../../06_ecosystem/06_data_and_distributed/05_data_engineering.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | 后置概念引用（蕴含/导向） |
| [Data Engineering](../../06_ecosystem/06_data_and_distributed/05_data_engineering.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Rust 游戏开发生态](../../06_ecosystem/11_domain_applications/05_game_development.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_domain_applications/03_webassembly.md) | 后置概念引用（蕴含/导向） |
| [Rust 游戏开发生态](../../06_ecosystem/11_domain_applications/05_game_development.md) | ⟹ | [Application Domains](../../06_ecosystem/06_data_and_distributed/01_application_domains.md) | 后置概念引用（蕴含/导向） |
| [Glommio 与 Thread-per-Core 异步运行时](../../06_ecosystem/04_web_and_networking/05_glommio_and_thread_per_core.md) | ⟹ | [高性能网络服务架构 (High-Performance Network Service Architecture)](../../06_ecosystem/04_web_and_networking/08_high_performance_network_service_architecture.md) | 后置概念引用（蕴含/导向） |
| [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) | ⟸ | [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/03_design_patterns/06_event_driven_architecture.md) | 源在目标的前置元数据中（目标依赖源） |
| [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | 后置概念引用（蕴含/导向） |
| [C10 Networks - Tier 2: 网络基础实践](../../06_ecosystem/12_networking/05_networking_basics.md) | ⟹ | [网络协议：QUIC/HTTP-3 与 Rust 实现](../../06_ecosystem/04_web_and_networking/07_network_protocols.md) | 后置概念引用（蕴含/导向） |
| [C10 Networks - Tier 2: 网络基础实践](../../06_ecosystem/12_networking/05_networking_basics.md) | ⇔ | [Rust Web 框架对比与选型](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) | 对比型页面（名称含 vs/对比） |
| [Cargo 依赖解析](../../06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) | ⟹ | [Cargo Build Scripts](../../06_ecosystem/01_cargo/05_cargo_build_scripts.md) | 后置概念引用（蕴含/导向） |
| [Cargo 依赖解析](../../06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) | ⟹ | [Cargo Registry 与包发布](../../06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) | 后置概念引用（蕴含/导向） |
| [Distributed Consensus](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) | ⟹ | [Blockchain & Smart Contract Security](../../06_ecosystem/11_domain_applications/01_blockchain.md) | 后置概念引用（蕴含/导向） |
| [Distributed Consensus](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | 后置概念引用（蕴含/导向） |
| [Distributed Consensus](../../06_ecosystem/06_data_and_distributed/06_distributed_consensus.md) | ⟹ | [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) | 后置概念引用（蕴含/导向） |
| [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/03_design_patterns/06_event_driven_architecture.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/03_design_patterns/06_event_driven_architecture.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | 后置概念引用（蕴含/导向） |
| [形式化网络协议理论](../../06_ecosystem/12_networking/06_formal_network_protocol_theory.md) | ⟹ | [自定义协议实现](../../06_ecosystem/12_networking/03_custom_protocol_implementation.md) | 后置概念引用（蕴含/导向） |
| [形式化网络协议理论](../../06_ecosystem/12_networking/06_formal_network_protocol_theory.md) | ⟹ | [网络安全](../../06_ecosystem/12_networking/02_network_security.md) | 后置概念引用（蕴含/导向） |
| [Robotics & ROS2 in Rust](../../06_ecosystem/05_systems_and_embedded/06_robotics.md) | ⟹ | [Rust 操作系统内核开发](../../06_ecosystem/05_systems_and_embedded/05_os_kernel.md) | 后置概念引用（蕴含/导向） |
| [Robotics & ROS2 in Rust](../../06_ecosystem/05_systems_and_embedded/06_robotics.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Robotics & ROS2 in Rust](../../06_ecosystem/05_systems_and_embedded/06_robotics.md) | ⟹ | [Machine Learning Ecosystem](../../06_ecosystem/11_domain_applications/13_machine_learning_ecosystem.md) | 后置概念引用（蕴含/导向） |
| [Robotics & ROS2 in Rust](../../06_ecosystem/05_systems_and_embedded/06_robotics.md) | ⟹ | [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md) | 后置概念引用（蕴含/导向） |
| [C10 Networks - Tier 2: WebSocket 实时通信](../../06_ecosystem/04_web_and_networking/06_websocket_realtime_communication.md) | ⟹ | [高性能网络服务架构 (High-Performance Network Service Architecture)](../../06_ecosystem/04_web_and_networking/08_high_performance_network_service_architecture.md) | 后置概念引用（蕴含/导向） |
| [C10 Networks - Tier 2: WebSocket 实时通信](../../06_ecosystem/04_web_and_networking/06_websocket_realtime_communication.md) | ⇔ | [Rust Web 框架对比与选型](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) | 对比型页面（名称含 vs/对比） |
| [算法与竞赛编程 (Algorithms & Competitive Programming)](../../06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md) | ⟹ | [Formal Ecosystem Tower](../../06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md) | 后置概念引用（蕴含/导向） |
| [算法与竞赛编程 (Algorithms & Competitive Programming)](../../06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Cargo Source Replacement 与 Vendoring](../../06_ecosystem/01_cargo/07_cargo_source_replacement.md) | ⟹ | [Cargo 认证与构建缓存](../../06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md) | 后置概念引用（蕴含/导向） |
| [Cargo Source Replacement 与 Vendoring](../../06_ecosystem/01_cargo/07_cargo_source_replacement.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [CQRS & Event Sourcing](../../06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [CQRS & Event Sourcing](../../06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md) | ⊑ | [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [CQRS & Event Sourcing](../../06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/04_web_and_networking/02_cloud_native.md) | 后置概念引用（蕴含/导向） |
| [网络协议：QUIC/HTTP-3 与 Rust 实现](../../06_ecosystem/04_web_and_networking/07_network_protocols.md) | ⟹ | [流处理生态：Rust 实现与工业系统全景](../../06_ecosystem/06_data_and_distributed/03_stream_processing_ecosystem.md) | 后置概念引用（蕴含/导向） |
| [网络协议：QUIC/HTTP-3 与 Rust 实现](../../06_ecosystem/04_web_and_networking/07_network_protocols.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [算法工程实践 (Algorithm Engineering Practice)](../../06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Architecture Patterns](../../06_ecosystem/03_design_patterns/08_architecture_patterns.md) | ⊑ | [CQRS & Event Sourcing](../../06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Architecture Patterns](../../06_ecosystem/03_design_patterns/08_architecture_patterns.md) | ⊑ | [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Architecture Patterns](../../06_ecosystem/03_design_patterns/08_architecture_patterns.md) | ⊑ | [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/03_design_patterns/06_event_driven_architecture.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [C-to-Rust Translation Ecosystem](../../06_ecosystem/05_systems_and_embedded/08_c_to_rust_translation.md) | ⟹ | [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md) | 后置概念引用（蕴含/导向） |
| [C-to-Rust Translation Ecosystem](../../06_ecosystem/05_systems_and_embedded/08_c_to_rust_translation.md) | ⟹ | [Rust 编译器内部原理](../../06_ecosystem/00_toolchain/04_compiler_internals.md) | 后置概念引用（蕴含/导向） |
| [Cargo Registry 与包发布](../../06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) | ⟹ | [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/01_cargo/13_cargo_security_cves.md) | 后置概念引用（蕴含/导向） |
| [Cargo Registry 与包发布](../../06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) | ⟹ | [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md) | 后置概念引用（蕴含/导向） |
| [高性能网络服务架构 (High-Performance Network Service Architecture)](../../06_ecosystem/04_web_and_networking/08_high_performance_network_service_architecture.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [将 Rust 集成到现有平台](../../06_ecosystem/00_toolchain/08_platform_rust_integration.md) | ⟹ | [Rust 工业应用案例研究](../../06_ecosystem/11_domain_applications/14_industrial_case_studies.md) | 后置概念引用（蕴含/导向） |
| [将 Rust 集成到现有平台](../../06_ecosystem/00_toolchain/08_platform_rust_integration.md) | ⟹ | [Rust 操作系统内核开发](../../06_ecosystem/05_systems_and_embedded/05_os_kernel.md) | 后置概念引用（蕴含/导向） |
| [Cargo 认证与构建缓存](../../06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md) | ⟹ | [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/01_cargo/13_cargo_security_cves.md) | 后置概念引用（蕴含/导向） |
| [Cargo 认证与构建缓存](../../06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [](../../06_ecosystem/11_domain_applications/09_data_structures_in_rust.md) | ⟹ | [算法工程实践 (Algorithm Engineering Practice)](../../06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md) | 后置概念引用（蕴含/导向） |
| [](../../06_ecosystem/11_domain_applications/09_data_structures_in_rust.md) | ⟹ | [算法与竞赛编程 (Algorithms & Competitive Programming)](../../06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md) | 后置概念引用（蕴含/导向） |
| [Embedded-HAL 1.0 迁移与 Embassy 生产状态](../../06_ecosystem/05_systems_and_embedded/09_embedded_hal_1_0_migration.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |
| [Rust 编译器的 LLVM 后端与代码生成](../../06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md) | ⟹ | [rustc Driver、Interface 与 Stable MIR](../../06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md) | 后置概念引用（蕴含/导向） |
| [Rust 编译器的 LLVM 后端与代码生成](../../06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/00_toolchain/05_compiler_infrastructure.md) | 后置概念引用（蕴含/导向） |
| [模式实现对比 (Pattern Implementation Comparison)](../../06_ecosystem/03_design_patterns/09_pattern_implementation_comparison.md) | ⇔ | [模式选择最佳实践 (Pattern Selection Best Practices)](../../06_ecosystem/03_design_patterns/10_pattern_selection_best_practices.md) | 对比型页面（名称含 vs/对比） |
| [模式实现对比 (Pattern Implementation Comparison)](../../06_ecosystem/03_design_patterns/09_pattern_implementation_comparison.md) | ⇔ | [工程实践与生产级模式](../../06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md) | 对比型页面（名称含 vs/对比） |
| [Reactive Programming & FRP](../../06_ecosystem/04_web_and_networking/09_reactive_programming.md) | ⟹ | [CQRS & Event Sourcing](../../06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md) | 后置概念引用（蕴含/导向） |
| [Reactive Programming & FRP](../../06_ecosystem/04_web_and_networking/09_reactive_programming.md) | ⟹ | [流处理生态：Rust 实现与工业系统全景](../../06_ecosystem/06_data_and_distributed/03_stream_processing_ecosystem.md) | 后置概念引用（蕴含/导向） |
| [Rust 算法复杂度分析](../../06_ecosystem/11_domain_applications/10_algorithm_complexity_analysis.md) | ⟹ | [算法与竞赛编程 (Algorithms & Competitive Programming)](../../06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md) | 后置概念引用（蕴含/导向） |
| [Rust 算法复杂度分析](../../06_ecosystem/11_domain_applications/10_algorithm_complexity_analysis.md) | ⟹ | [算法工程实践 (Algorithm Engineering Practice)](../../06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md) | 后置概念引用（蕴含/导向） |
| [Cargo Manifest 参考速查](../../06_ecosystem/01_cargo/10_cargo_manifest_reference.md) | ⟹ | [Cargo Profiles 与 Lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) | 后置概念引用（蕴含/导向） |
| [Cargo Manifest 参考速查](../../06_ecosystem/01_cargo/10_cargo_manifest_reference.md) | ⟹ | [Cargo Source Replacement 与 Vendoring](../../06_ecosystem/01_cargo/07_cargo_source_replacement.md) | 后置概念引用（蕴含/导向） |
| [模式选择最佳实践 (Pattern Selection Best Practices)](../../06_ecosystem/03_design_patterns/10_pattern_selection_best_practices.md) | ⊑ | [工程实践与生产级模式](../../06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [模式选择最佳实践 (Pattern Selection Best Practices)](../../06_ecosystem/03_design_patterns/10_pattern_selection_best_practices.md) | ⊑ | [Architecture Patterns](../../06_ecosystem/03_design_patterns/08_architecture_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [rustc Driver、Interface 与 Stable MIR](../../06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/00_toolchain/05_compiler_infrastructure.md) | 后置概念引用（蕴含/导向） |
| [rustc Driver、Interface 与 Stable MIR](../../06_ecosystem/00_toolchain/10_rustc_driver_and_stable_mir.md) | ⟹ | [rustc 编译器诊断与 UI Tests](../../06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md) | 后置概念引用（蕴含/导向） |
| [Target Tier 平台支持全景：分层保证与 1.90–1.97 变迁](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) | ↔ | [rustc / Cargo `-Z` 不稳定选项参考清单](../../06_ecosystem/00_toolchain/15_z_flags_reference.md) | 互为后置概念（互参） |
| [Target Tier 平台支持全景：分层保证与 1.90–1.97 变迁](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) | ⟹ | [WASI & WebAssembly Component Model](../../06_ecosystem/05_systems_and_embedded/01_wasi.md) | 后置概念引用（蕴含/导向） |
| [Cargo Profiles 与 Lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) | ⟹ | [Cargo 认证与构建缓存](../../06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md) | 后置概念引用（蕴含/导向） |
| [Cargo Profiles 与 Lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [rustc 编译器诊断与 UI Tests](../../06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md) | ⟹ | [rustc 自举](../../06_ecosystem/00_toolchain/12_rustc_bootstrap.md) | 后置概念引用（蕴含/导向） |
| [rustc 编译器诊断与 UI Tests](../../06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/00_toolchain/05_compiler_infrastructure.md) | 后置概念引用（蕴含/导向） |
| [前沿算法技术](../../06_ecosystem/11_domain_applications/11_cutting_edge_algorithms.md) | ⟹ | [Rust 量子计算生态](../../06_ecosystem/11_domain_applications/16_quantum_computing_rust.md) | 后置概念引用（蕴含/导向） |
| [前沿算法技术](../../06_ecosystem/11_domain_applications/11_cutting_edge_algorithms.md) | ⟹ | [Machine Learning Ecosystem](../../06_ecosystem/11_domain_applications/13_machine_learning_ecosystem.md) | 后置概念引用（蕴含/导向） |
| [形式化设计模式理论 (Formal Design Pattern Theory)](../../06_ecosystem/03_design_patterns/11_formal_design_pattern_theory.md) | ⟸ | [前沿研究与创新模式 (Frontier Research and Innovative Patterns)](../../06_ecosystem/03_design_patterns/12_frontier_research_and_innovative_patterns.md) | 源在目标的前置元数据中（目标依赖源） |
| [形式化设计模式理论 (Formal Design Pattern Theory)](../../06_ecosystem/03_design_patterns/11_formal_design_pattern_theory.md) | ⊑ | [模式组合代数：设计模式的结构化关联与冲突分析](../../06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Cargo 子命令与插件生态](../../06_ecosystem/01_cargo/12_cargo_subcommands_and_plugins.md) | ⟹ | [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/01_cargo/13_cargo_security_cves.md) | 后置概念引用（蕴含/导向） |
| [Cargo 子命令与插件生态](../../06_ecosystem/01_cargo/12_cargo_subcommands_and_plugins.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [形式化算法理论](../../06_ecosystem/11_domain_applications/12_formal_algorithm_theory.md) | ⟹ | [算法工程实践 (Algorithm Engineering Practice)](../../06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md) | 后置概念引用（蕴含/导向） |
| [前沿研究与创新模式 (Frontier Research and Innovative Patterns)](../../06_ecosystem/03_design_patterns/12_frontier_research_and_innovative_patterns.md) | ⊑ | [工程实践与生产级模式](../../06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [前沿研究与创新模式 (Frontier Research and Innovative Patterns)](../../06_ecosystem/03_design_patterns/12_frontier_research_and_innovative_patterns.md) | ⟹ | [Rust 工业应用案例研究](../../06_ecosystem/11_domain_applications/14_industrial_case_studies.md) | 后置概念引用（蕴含/导向） |
| [rustc 自举](../../06_ecosystem/00_toolchain/12_rustc_bootstrap.md) | ⟹ | [rustc 编译器测试体系](../../06_ecosystem/00_toolchain/13_compiler_testing.md) | 后置概念引用（蕴含/导向） |
| [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/01_cargo/13_cargo_security_cves.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |
| [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/01_cargo/13_cargo_security_cves.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [rustc 编译器测试体系](../../06_ecosystem/00_toolchain/13_compiler_testing.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/00_toolchain/05_compiler_infrastructure.md) | 后置概念引用（蕴含/导向） |
| [工程实践与生产级模式](../../06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md) | ⊑ | [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [工程实践与生产级模式](../../06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md) | ⊑ | [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/03_design_patterns/06_event_driven_architecture.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Machine Learning Ecosystem](../../06_ecosystem/11_domain_applications/13_machine_learning_ecosystem.md) | ⟹ | [Rust 嵌入式系统开发](../../06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) | 后置概念引用（蕴含/导向） |
| [Machine Learning Ecosystem](../../06_ecosystem/11_domain_applications/13_machine_learning_ecosystem.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Cargo Workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md) | ⟹ | [Cargo Profiles 与 Lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) | 后置概念引用（蕴含/导向） |
| [Cargo Workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md) | ⟹ | [Cargo Registry 与包发布](../../06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) | 后置概念引用（蕴含/导向） |
| [C09 设计模式 - 术语表](../../06_ecosystem/03_design_patterns/14_design_patterns_glossary.md) | ⊑ | [模式选择最佳实践 (Pattern Selection Best Practices)](../../06_ecosystem/03_design_patterns/10_pattern_selection_best_practices.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [C09 设计模式 - 术语表](../../06_ecosystem/03_design_patterns/14_design_patterns_glossary.md) | ⊑ | [形式化设计模式理论 (Formal Design Pattern Theory)](../../06_ecosystem/03_design_patterns/11_formal_design_pattern_theory.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust 常用开发工具](../../06_ecosystem/00_toolchain/14_development_tools.md) | ⟹ | [Cargo Profiles 与 Lints](../../06_ecosystem/01_cargo/11_cargo_profiles_and_lints.md) | 后置概念引用（蕴含/导向） |
| [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | ⟸ | [Cargo 工作流](../../06_ecosystem/01_cargo/16_cargo_workflow.md) | 源在目标的前置元数据中（目标依赖源） |
| [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | ⟹ | [Cargo 依赖解析](../../06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) | 后置概念引用（蕴含/导向） |
| [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | ⟹ | [Cargo Manifest 参考速查](../../06_ecosystem/01_cargo/10_cargo_manifest_reference.md) | 后置概念引用（蕴含/导向） |
| [C09 设计模式 - 常见问题](../../06_ecosystem/03_design_patterns/15_design_patterns_faq.md) | ⊑ | [模式选择最佳实践 (Pattern Selection Best Practices)](../../06_ecosystem/03_design_patterns/10_pattern_selection_best_practices.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [C09 设计模式 - 常见问题](../../06_ecosystem/03_design_patterns/15_design_patterns_faq.md) | ⊑ | [工程实践与生产级模式](../../06_ecosystem/03_design_patterns/13_engineering_and_production_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Game Engine Internals](../../06_ecosystem/11_domain_applications/15_game_engine_internals.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Game Engine Internals](../../06_ecosystem/11_domain_applications/15_game_engine_internals.md) | ⟹ | [Rust 嵌入式系统开发](../../06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) | 后置概念引用（蕴含/导向） |
| [rustc / Cargo `-Z` 不稳定选项参考清单](../../06_ecosystem/00_toolchain/15_z_flags_reference.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |
| [rustc / Cargo `-Z` 不稳定选项参考清单](../../06_ecosystem/00_toolchain/15_z_flags_reference.md) | ↔ | [Target Tier 平台支持全景：分层保证与 1.90–1.97 变迁](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) | 互为后置概念（互参） |
| [Cargo 工作流](../../06_ecosystem/01_cargo/16_cargo_workflow.md) | ⟸ | [Cargo 指南实践](../../06_ecosystem/01_cargo/17_cargo_guide_practices.md) | 源在目标的前置元数据中（目标依赖源） |
| [Cargo 工作流](../../06_ecosystem/01_cargo/16_cargo_workflow.md) | ⟹ | [Cargo Workspaces](../../06_ecosystem/01_cargo/14_cargo_workspaces.md) | 后置概念引用（蕴含/导向） |
| [Cargo 工作流](../../06_ecosystem/01_cargo/16_cargo_workflow.md) | ⟹ | [Cargo 依赖解析](../../06_ecosystem/01_cargo/06_cargo_dependency_resolution.md) | 后置概念引用（蕴含/导向） |
| [模式组合代数：设计模式的结构化关联与冲突分析](../../06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [模式组合代数：设计模式的结构化关联与冲突分析](../../06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md) | ⊑ | [Rust 系统设计原则与国际权威对齐](../../06_ecosystem/03_design_patterns/03_system_design_principles.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Cargo 指南实践](../../06_ecosystem/01_cargo/17_cargo_guide_practices.md) | ⟹ | [Cargo 配置与环境变量](../../06_ecosystem/01_cargo/18_cargo_configuration.md) | 后置概念引用（蕴含/导向） |
| [Cargo 指南实践](../../06_ecosystem/01_cargo/17_cargo_guide_practices.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [Cargo 指南实践](../../06_ecosystem/01_cargo/17_cargo_guide_practices.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/10_performance/01_performance_optimization.md) | 后置概念引用（蕴含/导向） |
| [Workflow Theory & Formalization](../../06_ecosystem/03_design_patterns/17_workflow_theory.md) | ⟹ | [CQRS & Event Sourcing](../../06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md) | 后置概念引用（蕴含/导向） |
| [Workflow Theory & Formalization](../../06_ecosystem/03_design_patterns/17_workflow_theory.md) | ⟹ | [Reactive Programming & FRP](../../06_ecosystem/04_web_and_networking/09_reactive_programming.md) | 后置概念引用（蕴含/导向） |
| [Workflow Theory & Formalization](../../06_ecosystem/03_design_patterns/17_workflow_theory.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [API Design Patterns](../../06_ecosystem/03_design_patterns/18_api_design_patterns.md) | ⊑ | [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/03_design_patterns/05_microservice_patterns.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [API Design Patterns](../../06_ecosystem/03_design_patterns/18_api_design_patterns.md) | ⊑ | [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/03_design_patterns/06_event_driven_architecture.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [API Design Patterns](../../06_ecosystem/03_design_patterns/18_api_design_patterns.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/04_web_and_networking/01_distributed_systems.md) | 后置概念引用（蕴含/导向） |
| [Cargo 配置与环境变量](../../06_ecosystem/01_cargo/18_cargo_configuration.md) | ⟸ | [Cargo 命令参考](../../06_ecosystem/01_cargo/19_cargo_commands_reference.md) | 源在目标的前置元数据中（目标依赖源） |
| [Cargo 配置与环境变量](../../06_ecosystem/01_cargo/18_cargo_configuration.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |
| [C12 WASM - 术语表](../../06_ecosystem/11_domain_applications/18_wasm_glossary.md) | ⟸ | [C12 WASM - 常见问题](../../06_ecosystem/11_domain_applications/19_wasm_faq.md) | 源在目标的前置元数据中（目标依赖源） |
| [C12 WASM - 术语表](../../06_ecosystem/11_domain_applications/18_wasm_glossary.md) | ⟹ | [C12 WASM - JavaScript 互操作](../../06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md) | 后置概念引用（蕴含/导向） |
| [Cargo 命令参考](../../06_ecosystem/01_cargo/19_cargo_commands_reference.md) | ↔ | [Cargo Manifest 目标与元数据](../../06_ecosystem/01_cargo/20_cargo_manifest_targets.md) | 互为后置概念（互参） |
| [Cargo 命令参考](../../06_ecosystem/01_cargo/19_cargo_commands_reference.md) | ↔ | [Cargo Registry 内部机制](../../06_ecosystem/01_cargo/21_cargo_registry_internals.md) | 互为后置概念（互参） |
| [Cargo 命令参考](../../06_ecosystem/01_cargo/19_cargo_commands_reference.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/00_toolchain/03_devops_and_ci_cd.md) | 后置概念引用（蕴含/导向） |
| [C12 WASM - 常见问题](../../06_ecosystem/11_domain_applications/19_wasm_faq.md) | ⟸ | [C12 WASM - JavaScript 互操作](../../06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md) | 源在目标的前置元数据中（目标依赖源） |
| [C12 WASM - 常见问题](../../06_ecosystem/11_domain_applications/19_wasm_faq.md) | ⊑ | [Rust WebAssembly 高级开发](../../06_ecosystem/11_domain_applications/17_webassembly_advanced.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Cargo Manifest 目标与元数据](../../06_ecosystem/01_cargo/20_cargo_manifest_targets.md) | ↔ | [Cargo 命令参考](../../06_ecosystem/01_cargo/19_cargo_commands_reference.md) | 互为后置概念（互参） |
| [Cargo Manifest 目标与元数据](../../06_ecosystem/01_cargo/20_cargo_manifest_targets.md) | ⟹ | [Cargo Build Scripts](../../06_ecosystem/01_cargo/05_cargo_build_scripts.md) | 后置概念引用（蕴含/导向） |
| [C12 WASM - JavaScript 互操作](../../06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md) | ⊑ | [Rust WebAssembly 高级开发](../../06_ecosystem/11_domain_applications/17_webassembly_advanced.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [C12 WASM - JavaScript 互操作](../../06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md) | ⇔ | [Rust Web 框架对比与选型](../../06_ecosystem/04_web_and_networking/03_web_frameworks.md) | 对比型页面（名称含 vs/对比） |
| [Cargo Registry 内部机制](../../06_ecosystem/01_cargo/21_cargo_registry_internals.md) | ↔ | [Cargo 命令参考](../../06_ecosystem/01_cargo/19_cargo_commands_reference.md) | 互为后置概念（互参） |
| [Cargo Registry 内部机制](../../06_ecosystem/01_cargo/21_cargo_registry_internals.md) | ⟹ | [安全 实践：Rust 代码的防御性编程](../../06_ecosystem/07_security_and_cryptography/01_security_practices.md) | 后置概念引用（蕴含/导向） |
| [AUTOSAR 与 Rust](../../06_ecosystem/11_domain_applications/22_autosar_and_rust.md) | ⟹ | [Rust 工业应用案例研究](../../06_ecosystem/11_domain_applications/14_industrial_case_studies.md) | 后置概念引用（蕴含/导向） |
| [AUTOSAR 与 Rust](../../06_ecosystem/11_domain_applications/22_autosar_and_rust.md) | ⟹ | [cargo vet 与供应链审计](../../06_ecosystem/07_security_and_cryptography/03_cargo_vet_supply_chain.md) | 后置概念引用（蕴含/导向） |
| [Cargo build-std](../../06_ecosystem/01_cargo/22_build_std.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) | 后置概念引用（蕴含/导向） |

## L7 前沿趋势层

「L7 前沿趋势层」部分的核心主题是层内引用关系，本节展开说明。

### 层内引用关系

| 源概念 | 关系 | 目标概念 | 依据 |
|:---|:---:|:---|:---|
| [Rust 2024 Edition (1.85.0+ stable)](../../07_future/01_edition_roadmap/01_rust_edition_preview.md) | ⟹ | [Edition 2024 完全指南：新特性与迁移策略](../../07_future/01_edition_roadmap/02_edition_guide.md) | 后置概念引用（蕴含/导向） |
| [Rust 2024 Edition (1.85.0+ stable)](../../07_future/01_edition_roadmap/01_rust_edition_preview.md) | ⊑ | [Rust Edition 机制与迁移指南](../../07_future/01_edition_roadmap/03_rust_edition_guide.md) | 同主题目录，一端为进阶/机制/模式（精化关系） |
| [Rust 2024 Edition (1.85.0+ stable)](../../07_future/01_edition_roadmap/01_rust_edition_preview.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [Edition 2024 完全指南：新特性与迁移策略](../../07_future/01_edition_roadmap/02_edition_guide.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [Rust Editions](../../07_future/00_version_tracking/02_editions.md) | ⟸ | [Rust 发布流程](../../07_future/00_version_tracking/03_rust_release_process.md) | 源在目标的前置元数据中（目标依赖源） |
| [Rust Editions](../../07_future/00_version_tracking/02_editions.md) | ⟹ | [Edition 2024 完全指南：新特性与迁移策略](../../07_future/01_edition_roadmap/02_edition_guide.md) | 后置概念引用（蕴含/导向） |
| [MC/DC Coverage 概念预研：安全关键 Rust 的覆盖率验证](../../07_future/03_preview_features/02_mcdc_coverage_preview.md) | ⟹ | [Formal Methods Industrialization](../../07_future/04_research_and_experimental/02_formal_methods.md) | 后置概念引用（蕴含/导向） |
| [Rust Edition 机制与迁移指南](../../07_future/01_edition_roadmap/03_rust_edition_guide.md) | → | [Edition 2024 完全指南：新特性与迁移策略](../../07_future/01_edition_roadmap/02_edition_guide.md) | 目标在源的前置元数据中（源依赖目标） |
| [Rust 发布流程](../../07_future/00_version_tracking/03_rust_release_process.md) | ⟹ | [Rust 的发布流程与 Nightly Rust](../../07_future/00_version_tracking/04_nightly_rust.md) | 后置概念引用（蕴含/导向） |
| [Rust 发布流程](../../07_future/00_version_tracking/03_rust_release_process.md) | ⟹ | [Rust 1.96 稳定特性](../../07_future/00_version_tracking/rust_1_96_stabilized.md) | 后置概念引用（蕴含/导向） |
| [Rust 发布流程](../../07_future/00_version_tracking/03_rust_release_process.md) | ⟹ | [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | 后置概念引用（蕴含/导向） |
| [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/03_preview_features/03_safety_tags_preview.md) | ⟹ | [Formal Methods Industrialization](../../07_future/04_research_and_experimental/02_formal_methods.md) | 后置概念引用（蕴含/导向） |
| [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/03_preview_features/03_safety_tags_preview.md) | ⟹ | [AI × Rust：生成-验证闭环与确定性容器](../../07_future/04_research_and_experimental/01_ai_integration.md) | 后置概念引用（蕴含/导向） |
| [Rust 的发布流程与 Nightly Rust](../../07_future/00_version_tracking/04_nightly_rust.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Rust 的发布流程与 Nightly Rust](../../07_future/00_version_tracking/04_nightly_rust.md) | ⟹ | [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | 后置概念引用（蕴含/导向） |
| [并行 前端编译预研：Rust 编译器 的多核扩展](../../07_future/03_preview_features/04_parallel_frontend_preview.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [Rust 2027 Edition 及未来路线图](../../07_future/01_edition_roadmap/04_roadmap.md) | ⟹ | [Formal Methods Industrialization](../../07_future/04_research_and_experimental/02_formal_methods.md) | 后置概念引用（蕴含/导向） |
| [Rust 2027 Edition 及未来路线图](../../07_future/01_edition_roadmap/04_roadmap.md) | ⟹ | [Rust 在 AI 与机器学习中的新兴角色](../../07_future/04_research_and_experimental/05_rust_in_ai.md) | 后置概念引用（蕴含/导向） |
| [Rust for Linux ：操作系统内核中的内存安全](../../07_future/04_research_and_experimental/04_rust_for_linux.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [派生 CoercePointee 预研：智能指针的自动类型强制](../../07_future/03_preview_features/05_derive_coerce_pointee_preview.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [Rust 在 AI 与机器学习中的新兴角色](../../07_future/04_research_and_experimental/05_rust_in_ai.md) | ⟹ | [AI × Rust：生成-验证闭环与确定性容器](../../07_future/04_research_and_experimental/01_ai_integration.md) | 后置概念引用（蕴含/导向） |
| [Rust 在 AI 与机器学习中的新兴角色](../../07_future/04_research_and_experimental/05_rust_in_ai.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [Const Trait Impl 预研：常量上下文中的 Trait 泛化](../../07_future/03_preview_features/06_const_trait_impl_preview.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [Rust for WebAssembly：从 wasm-bindgen 到前端框架的深度技术栈](../../07_future/04_research_and_experimental/06_rust_for_webassembly.md) | ⟹ | [Formal Methods Industrialization](../../07_future/04_research_and_experimental/02_formal_methods.md) | 后置概念引用（蕴含/导向） |
| [Stable ABI Preview](../../07_future/03_preview_features/07_stable_abi_preview.md) | ⟹ | [Rust for Linux ：操作系统内核中的内存安全](../../07_future/04_research_and_experimental/04_rust_for_linux.md) | 后置概念引用（蕴含/导向） |
| [Inline Const Pattern 预览](../../07_future/03_preview_features/08_inline_const_pattern_preview.md) | ↔ | [Const Trait 实现预览](../../07_future/03_preview_features/19_const_trait_preview.md) | 互为后置概念（互参） |
| [Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界](../../07_future/03_preview_features/09_return_type_notation_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界](../../07_future/03_preview_features/09_return_type_notation_preview.md) | ⟹ | [Async Drop：异步资源的优雅销毁](../../07_future/03_preview_features/22_async_drop_preview.md) | 后置概念引用（蕴含/导向） |
| [`must_not_suspend` Lint Preview](../../07_future/03_preview_features/10_must_not_suspend_preview.md) | ⟹ | [Async Drop：异步资源的优雅销毁](../../07_future/03_preview_features/22_async_drop_preview.md) | 后置概念引用（蕴含/导向） |
| [Unsafe Fields 预研：字段级安全边界的精确标注](../../07_future/03_preview_features/11_unsafe_fields_preview.md) | ⟹ | [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/03_preview_features/03_safety_tags_preview.md) | 后置概念引用（蕴含/导向） |
| [Ferrocene：已交付的 Rust 安全关键认证工具链](../../07_future/03_preview_features/12_ferrocene_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Lifetime Capture in `impl Trait` Preview](../../07_future/03_preview_features/13_lifetime_capture_preview.md) | ↔ | [特质中返回位置 impl Trait（RPITIT）预览](../../07_future/03_preview_features/15_rpitit_preview.md) | 互为后置概念（互参） |
| [Lifetime Capture in `impl Trait` Preview](../../07_future/03_preview_features/13_lifetime_capture_preview.md) | ⟹ | [Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界](../../07_future/03_preview_features/09_return_type_notation_preview.md) | 后置概念引用（蕴含/导向） |
| [Pin Ergonomics 与 Reborrow Traits 预研：超越 `Pin::as_mut`](../../07_future/03_preview_features/14_pin_ergonomics_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Pin Ergonomics 与 Reborrow Traits 预研：超越 `Pin::as_mut`](../../07_future/03_preview_features/14_pin_ergonomics_preview.md) | ⟹ | [Async Drop：异步资源的优雅销毁](../../07_future/03_preview_features/22_async_drop_preview.md) | 后置概念引用（蕴含/导向） |
| [特质中返回位置 impl Trait（RPITIT）预览](../../07_future/03_preview_features/15_rpitit_preview.md) | ↔ | [TAIT Preview](../../07_future/03_preview_features/17_type_alias_impl_trait_preview.md) | 互为后置概念（互参） |
| [特质中返回位置 impl Trait（RPITIT）预览](../../07_future/03_preview_features/15_rpitit_preview.md) | ↔ | [Lifetime Capture in `impl Trait` Preview](../../07_future/03_preview_features/13_lifetime_capture_preview.md) | 互为后置概念（互参） |
| [Cranelift 后端预研：Rust 编译器的快速调试编译](../../07_future/03_preview_features/16_cranelift_backend_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [TAIT Preview](../../07_future/03_preview_features/17_type_alias_impl_trait_preview.md) | ↔ | [特质中返回位置 impl Trait（RPITIT）预览](../../07_future/03_preview_features/15_rpitit_preview.md) | 互为后置概念（互参） |
| [TAIT Preview](../../07_future/03_preview_features/17_type_alias_impl_trait_preview.md) | ⟹ | [Const Trait 实现预览](../../07_future/03_preview_features/19_const_trait_preview.md) | 后置概念引用（蕴含/导向） |
| [Const Trait 实现预览](../../07_future/03_preview_features/19_const_trait_preview.md) | ⟹ | [Const Trait Impl 预研：常量上下文中的 Trait 泛化](../../07_future/03_preview_features/06_const_trait_impl_preview.md) | 后置概念引用（蕴含/导向） |
| [Const Trait 实现预览](../../07_future/03_preview_features/19_const_trait_preview.md) | ↔ | [Inline Const Pattern 预览](../../07_future/03_preview_features/08_inline_const_pattern_preview.md) | 互为后置概念（互参） |
| [Ergonomic Ref-Counting 预研：人机工学引用计数](../../07_future/03_preview_features/20_ergonomic_ref_counting_preview.md) | ⟹ | [Rust for Linux ：操作系统内核中的内存安全](../../07_future/04_research_and_experimental/04_rust_for_linux.md) | 后置概念引用（蕴含/导向） |
| [Rust 语言规范预研：从参考文档到形式化规范](../../07_future/03_preview_features/21_rust_specification_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Async Drop：异步资源的优雅销毁](../../07_future/03_preview_features/22_async_drop_preview.md) | ⟹ | [Gen Blocks 预研：超越异步的泛化生成器](../../07_future/03_preview_features/25_gen_blocks_preview.md) | 后置概念引用（蕴含/导向） |
| [BorrowSanitizer：动态别名规则验证工具](../../07_future/03_preview_features/24_borrow_sanitizer.md) | ⟹ | [Formal Methods Industrialization](../../07_future/04_research_and_experimental/02_formal_methods.md) | 后置概念引用（蕴含/导向） |
| [BorrowSanitizer：动态别名规则验证工具](../../07_future/03_preview_features/24_borrow_sanitizer.md) | ⟸ | [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/03_preview_features/03_safety_tags_preview.md) | 源在目标的前置元数据中（目标依赖源） |
| [BorrowSanitizer：动态别名规则验证工具](../../07_future/03_preview_features/24_borrow_sanitizer.md) | ↔ | [AutoVerus / Verus 预览跟踪](../../07_future/03_preview_features/33_autoverus_preview.md) | 互为后置概念（互参） |
| [Gen Blocks 预研：超越异步的泛化生成器](../../07_future/03_preview_features/25_gen_blocks_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [`std::autodiff`：Rust 官方自动微分前沿追踪](../../07_future/03_preview_features/26_std_autodiff_preview.md) | ⟹ | [Rust 在 AI 与机器学习中的新兴角色](../../07_future/04_research_and_experimental/05_rust_in_ai.md) | 后置概念引用（蕴含/导向） |
| [`std::autodiff`：Rust 官方自动微分前沿追踪](../../07_future/03_preview_features/26_std_autodiff_preview.md) | ⟹ | [Language Evolution](../../07_future/04_research_and_experimental/03_evolution.md) | 后置概念引用（蕴含/导向） |
| [WASM Target Evolution Preview](../../07_future/03_preview_features/28_wasm_target_evolution.md) | ⟹ | [Rust for WebAssembly：从 wasm-bindgen 到前端框架的深度技术栈](../../07_future/04_research_and_experimental/06_rust_for_webassembly.md) | 后置概念引用（蕴含/导向） |
| [AArch64 SVE / SME：可伸缩向量扩展预览](../../07_future/03_preview_features/29_aarch64_sve_sme_preview.md) | ⟹ | [Rust for Linux ：操作系统内核中的内存安全](../../07_future/04_research_and_experimental/04_rust_for_linux.md) | 后置概念引用（蕴含/导向） |
| [Rust in Space Preview](../../07_future/03_preview_features/30_rust_in_space.md) | ⟹ | [Rust for Linux ：操作系统内核中的内存安全](../../07_future/04_research_and_experimental/04_rust_for_linux.md) | 后置概念引用（蕴含/导向） |
| [Rust in Space Preview](../../07_future/03_preview_features/30_rust_in_space.md) | ⟹ | [Ferrocene：已交付的 Rust 安全关键认证工具链](../../07_future/03_preview_features/12_ferrocene_preview.md) | 后置概念引用（蕴含/导向） |
| [Specialization：Trait 实现的精确化与重叠解析](../../07_future/03_preview_features/31_specialization_preview.md) | ⟹ | [Const Trait Impl 预研：常量上下文中的 Trait 泛化](../../07_future/03_preview_features/06_const_trait_impl_preview.md) | 后置概念引用（蕴含/导向） |
| [Specialization：Trait 实现的精确化与重叠解析](../../07_future/03_preview_features/31_specialization_preview.md) | ⟹ | [Effects System: Concept Pre-study](../../07_future/03_preview_features/01_effects_system.md) | 后置概念引用（蕴含/导向） |
| [AutoVerus / Verus 预览跟踪](../../07_future/03_preview_features/33_autoverus_preview.md) | ⟹ | [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/03_preview_features/03_safety_tags_preview.md) | 后置概念引用（蕴含/导向） |
| [AutoVerus / Verus 预览跟踪](../../07_future/03_preview_features/33_autoverus_preview.md) | ↔ | [BorrowSanitizer：动态别名规则验证工具](../../07_future/03_preview_features/24_borrow_sanitizer.md) | 互为后置概念（互参） |
| [Open Enums 概念预研：从 `#[non_exhaustive]` 到可扩展枚举](../../07_future/03_preview_features/34_open_enums_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Open Enums 概念预研：从 `#[non_exhaustive]` 到可扩展枚举](../../07_future/03_preview_features/34_open_enums_preview.md) | ⟹ | [Effects System: Concept Pre-study](../../07_future/03_preview_features/01_effects_system.md) | 后置概念引用（蕴含/导向） |
| [f16 / f128 预研：半精度与四精度浮点类型](../../07_future/03_preview_features/35_f16_f128_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [f16 / f128 预研：半精度与四精度浮点类型](../../07_future/03_preview_features/35_f16_f128_preview.md) | ↔ | [Complex Numbers 预研：标准库复数类型](../../07_future/03_preview_features/38_complex_numbers_preview.md) | 互为后置概念（互参） |
| [UnsafePinned 预研：可变引用别名语义的精确标注](../../07_future/03_preview_features/36_unsafe_pinned_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Default Field Values 预研：结构体字段默认值](../../07_future/03_preview_features/37_default_field_values_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Complex Numbers 预研：标准库复数类型](../../07_future/03_preview_features/38_complex_numbers_preview.md) | ↔ | [f16 / f128 预研：半精度与四精度浮点类型](../../07_future/03_preview_features/35_f16_f128_preview.md) | 互为后置概念（互参） |
| [Complex Numbers 预研：标准库复数类型](../../07_future/03_preview_features/38_complex_numbers_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.97.0 特性 × 领域反查矩阵](../../07_future/00_version_tracking/feature_domain_matrix_197.md) | ⟹ | [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.97.0 特性 × 领域反查矩阵](../../07_future/00_version_tracking/feature_domain_matrix_197.md) | ⟹ | [Rust 1.98+ 前沿特性预览](../../07_future/00_version_tracking/rust_1_98_preview.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.97 兼容性迁移判定树](../../07_future/00_version_tracking/migration_197_decision_tree.md) | ⟹ | [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.97 兼容性迁移判定树](../../07_future/00_version_tracking/migration_197_decision_tree.md) | ⟹ | [Rust 1.98+ 前沿特性预览](../../07_future/00_version_tracking/rust_1_98_preview.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.90 网络特性参考](../../07_future/00_version_tracking/rust_1_90_stabilized.md) | ⟹ | [Rust 1.91 稳定特性](../../07_future/00_version_tracking/rust_1_91_stabilized.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.91 稳定特性](../../07_future/00_version_tracking/rust_1_91_stabilized.md) | ↔ | [Rust 1.92 稳定特性](../../07_future/00_version_tracking/rust_1_92_stabilized.md) | 互为后置概念（互参） |
| [Rust 1.91 稳定特性](../../07_future/00_version_tracking/rust_1_91_stabilized.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.92 稳定特性](../../07_future/00_version_tracking/rust_1_92_stabilized.md) | ↔ | [Rust 1.91 稳定特性](../../07_future/00_version_tracking/rust_1_91_stabilized.md) | 互为后置概念（互参） |
| [Rust 1.92 稳定特性](../../07_future/00_version_tracking/rust_1_92_stabilized.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.93 稳定特性](../../07_future/00_version_tracking/rust_1_93_stabilized.md) | ⟹ | [Rust 1.92 稳定特性](../../07_future/00_version_tracking/rust_1_92_stabilized.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.93 稳定特性](../../07_future/00_version_tracking/rust_1_93_stabilized.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/00_version_tracking/01_rust_version_tracking.md) | 后置概念引用（蕴含/导向） |
| [c10_networks - Rust 1.94 更新概览](../../07_future/00_version_tracking/rust_1_94_stabilized.md) | ⟹ | [Rust 1.95.0 稳定特性](../../07_future/00_version_tracking/rust_1_95_stabilized.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | ↔ | [Rust 1.97.0 稳定特性](../../07_future/00_version_tracking/rust_1_97_stabilized.md) | 互为后置概念（互参） |
| [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | ⟹ | [Rust 1.98+ 前沿特性预览](../../07_future/00_version_tracking/rust_1_98_preview.md) | 后置概念引用（蕴含/导向） |
| [Rust 1.97.0 稳定特性](../../07_future/00_version_tracking/rust_1_97_stabilized.md) | ↔ | [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | 互为后置概念（互参） |
| [Rust 1.97.0 稳定特性](../../07_future/00_version_tracking/rust_1_97_stabilized.md) | ⟹ | [Rust 1.98+ 前沿特性预览](../../07_future/00_version_tracking/rust_1_98_preview.md) | 后置概念引用（蕴含/导向） |

---

> 本文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 生成；请勿手工编辑，更新后重新运行生成脚本。
