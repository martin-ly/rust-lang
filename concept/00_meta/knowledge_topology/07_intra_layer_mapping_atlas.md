# 层内映射图谱（Intra-Layer Mapping Atlas）

> **EN**: Intra-Layer Mapping Atlas
> **Summary**: 每层内部核心模型/概念间的等价、蕴含、依赖、互斥关系，基于同层前置/后置引用。
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## L0 元信息层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [C/C++ → Rust 工程层对比路线图](../../00_meta/cpp_rust_engineering_roadmap.md) | ⟹ | [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/pattern_semantic_space_index.md) |
| [基础知识缺口补全总索引](../../00_meta/foundations_gap_closure_index.md) | ⟹ | [Concept Audit Guide](../../00_meta/08_concept_audit_guide.md) |
| [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/pattern_semantic_space_index.md) | ⟹ | [语义桥：算法、设计模式与工作流模式的统一谱系](../../00_meta/semantic_bridge_algorithms_patterns.md) |
| [通用 PL 基座路线图：Rust 在编程语言坐标系中的位置](../../00_meta/pl_foundations_roadmap.md) | ⟹ | [C/C++ → Rust 工程层对比路线图](../../00_meta/cpp_rust_engineering_roadmap.md) |
| [通用 PL 基座路线图：Rust 在编程语言坐标系中的位置](../../00_meta/pl_foundations_roadmap.md) | ⟹ | [模式语义空间索引：设计模式在概念体系中的坐标](../../00_meta/pattern_semantic_space_index.md) |
| [模板去同质化指南](../../00_meta/template_deduplication_guide.md) | ⟹ | [Rust 知识体系思维表征覆盖率仪表板](../../00_meta/quality_dashboard_v2.md) |

## L1 基础概念层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [Ownership](../../01_foundation/01_ownership.md) | ⟹ | [Borrowing](../../01_foundation/02_borrowing.md) |
| [Ownership](../../01_foundation/01_ownership.md) | ⟹ | [Lifetimes](../../01_foundation/03_lifetimes.md) |
| [字符串与文本：Rust 的 Unicode 处理与格式化系统](../../01_foundation/09_strings_and_text.md) | ⟹ | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/08_collections.md) |
| [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/10_numerics.md) | ⟹ | [零成本抽象：Rust 的性能哲学](../../01_foundation/06_zero_cost_abstractions.md) |
| [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/10_numerics.md) | ⟹ | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/08_collections.md) |
| [字符串与编码：Rust 的文本处理类型系统](../../01_foundation/18_strings_and_encoding.md) | ⟹ | [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/08_collections.md) |
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/19_value_vs_reference_semantics.md) | ⟹ | [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/23_move_semantics.md) |
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/19_value_vs_reference_semantics.md) | ⟹ | [Borrowing](../../01_foundation/02_borrowing.md) |
| [变量模型：从通用 PL 视角看 Rust 的所有权](../../01_foundation/20_variable_model.md) | ⟹ | [Borrowing](../../01_foundation/02_borrowing.md) |
| [副作用与纯度：从引用透明到 Rust 的所有权效果](../../01_foundation/21_effects_and_purity.md) | ⟹ | [Borrowing](../../01_foundation/02_borrowing.md) |
| [测验：类型系统](../../01_foundation/24_quiz_type_system.md) | ⟹ | [测验：所有权、借用与生命周期](../../01_foundation/33_quiz_ownership_borrowing.md) |
| [测验：所有权、借用与生命周期](../../01_foundation/33_quiz_ownership_borrowing.md) | ⟹ | [Borrowing](../../01_foundation/02_borrowing.md) |
| [Rust 关键字](../../01_foundation/36_keywords.md) | ⟹ | [属性与声明宏：编译期元编程基础](../../01_foundation/12_attributes_and_macros.md) |
| [Rust 关键字](../../01_foundation/36_keywords.md) | ⟹ | [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/11_modules_and_paths.md) |
| [Rust 运算符与符号](../../01_foundation/37_operators_and_symbols.md) | ⟹ | [Type System Basics](../../01_foundation/04_type_system.md) |
| [模式匹配](../../01_foundation/40_patterns.md) | ⟹ | [语句与表达式](../../01_foundation/41_statements_and_expressions.md) |
| [语句与表达式](../../01_foundation/41_statements_and_expressions.md) | ⟹ | [闭包基础：捕获环境与匿名函数](../../01_foundation/15_closure_basics.md) |
| [常用开发工具](../../01_foundation/42_useful_development_tools.md) | ⟹ | [测试基础：从单元测试到集成测试](../../01_foundation/16_testing_basics.md) |

## L2 进阶概念层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [Traits](../../02_intermediate/01_traits.md) | ⟹ | [Generics](../../02_intermediate/02_generics.md) |
| [Cow：写时克隆与零拷贝抽象](../../02_intermediate/11_cow_and_borrowed.md) | ⟹ | [Serde 序列化模式：Rust 的类型驱动数据转换](../../02_intermediate/09_serde_patterns.md) |
| [智能指针：堆内存管理与共享语义](../../02_intermediate/12_smart_pointers.md) | ⟹ | [Cow：写时克隆与零拷贝抽象](../../02_intermediate/11_cow_and_borrowed.md) |
| [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/13_dsl_and_embedding.md) | ⟹ | [Serde 序列化模式：Rust 的类型驱动数据转换](../../02_intermediate/09_serde_patterns.md) |
| [Newtype 与包装器模式：类型安全的零成本抽象](../../02_intermediate/14_newtype_and_wrapper.md) | ⟹ | [智能指针：堆内存管理与共享语义](../../02_intermediate/12_smart_pointers.md) |
| [宏模式：编译期代码生成的工程实践](../../02_intermediate/17_macro_patterns.md) | ⟹ | [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/13_dsl_and_embedding.md) |
| [元编程：Rust 的编译期代码生成与变换](../../02_intermediate/21_metaprogramming.md) | ⟹ | [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/13_dsl_and_embedding.md) |
| [Rust API 命名约定](../../02_intermediate/22_api_naming_conventions.md) | ⟹ | [高级类型系统：从关联类型到类型级编程](../../02_intermediate/20_type_system_advanced.md) |
| [RTTI 与动态类型识别：从 C++ 到 Rust](../../02_intermediate/25_rtti_and_dynamic_typing.md) | ⟹ | [错误处理深入：从 Result 到自定义错误生态](../../02_intermediate/16_error_handling_deep_dive.md) |
| [RTTI 与动态类型识别：从 C++ 到 Rust](../../02_intermediate/25_rtti_and_dynamic_typing.md) | ⟹ | [高级 Trait 主题：从关联类型到特化](../../02_intermediate/19_advanced_traits.md) |
| [C 预处理器 vs Rust 宏：从文本替换到语法树](../../02_intermediate/26_c_preprocessor_vs_rust_macros.md) | ⟹ | [DSL 与嵌入 式设计：Rust 中的领域特定语言](../../02_intermediate/13_dsl_and_embedding.md) |
| [异常安全：C++ 与 Rust 的错误处理哲学](../../02_intermediate/27_exception_safety_rust_cpp.md) | ⟹ | [错误处理深入：从 Result 到自定义错误生态](../../02_intermediate/16_error_handling_deep_dive.md) |
| [可派生 Trait](../../02_intermediate/31_derive_traits.md) | ⟹ | [高级 Trait 主题：从关联类型到特化](../../02_intermediate/19_advanced_traits.md) |
| [Rust Editions](../../02_intermediate/32_editions.md) | ⟹ | [Rust 发布流程](../../02_intermediate/33_rust_release_process.md) |

## L3 高级概念层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [Concurrency](../../03_advanced/01_concurrency.md) | ⟹ | [Async/Await](../../03_advanced/02_async.md) |
| [Pin 与 Unpin：自引用类型的不动性保证](../../03_advanced/06_pin_unpin.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/03_unsafe.md) |
| [NLL 与 Polonius：借用检查器的演进](../../03_advanced/08_nll_and_polonius.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/03_unsafe.md) |
| [并发 模式：从消息 传递到锁自由的数据结构](../../03_advanced/10_concurrency_patterns.md) | ⟹ | [Concurrency](../../03_advanced/01_concurrency.md) |
| [Unsafe Rust 模式：安全抽象的核心技术](../../03_advanced/12_unsafe_rust_patterns.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/03_unsafe.md) |
| [无锁编程与内存模型](../../03_advanced/16_lock_free.md) | ⟹ | [并发 模式：从消息 传递到锁自由的数据结构](../../03_advanced/10_concurrency_patterns.md) |
| [Rust 网络编程：Tokio TCP/UDP、异步 IO 与 Tower 服务抽象](../../03_advanced/18_network_programming.md) | ⟹ | [无锁编程与内存模型](../../03_advanced/16_lock_free.md) |
| [Linkage](../../03_advanced/27_linkage.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/03_unsafe.md) |
| [条件编译](../../03_advanced/28_conditional_compilation.md) | ⟹ | [FFI 高级主题：跨语言边界的安全与性能](../../03_advanced/09_ffi_advanced.md) |
| [条件编译](../../03_advanced/28_conditional_compilation.md) | ⟹ | [Linkage](../../03_advanced/27_linkage.md) |
| [Rust 内存模型](../../03_advanced/29_memory_model.md) | ⟹ | [原子操作与内存序：无锁并发的精确控制](../../03_advanced/11_atomics_and_memory_ordering.md) |
| [Rust 内存模型](../../03_advanced/29_memory_model.md) | ⟹ | [内联汇编 (Inline Assembly)](../../03_advanced/13_inline_assembly.md) |
| [Rust 运行时](../../03_advanced/30_rust_runtime.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/03_unsafe.md) |
| [Panic 机制](../../03_advanced/31_panic.md) | ⟹ | [FFI 高级主题：跨语言边界的安全与性能](../../03_advanced/09_ffi_advanced.md) |
| [内存分配与生命周期](../../03_advanced/32_memory_allocation_and_lifetime.md) | ⟹ | [自定义分配器与内存布局优化](../../03_advanced/14_custom_allocators.md) |
| [内存分配与生命周期](../../03_advanced/32_memory_allocation_and_lifetime.md) | ⟹ | [Rust 运行时](../../03_advanced/30_rust_runtime.md) |
| [变量](../../03_advanced/33_variables.md) | ⟹ | [内存分配与生命周期](../../03_advanced/32_memory_allocation_and_lifetime.md) |
| [变量](../../03_advanced/33_variables.md) | ⟹ | [Unsafe Rust 安全编程](../../03_advanced/03_unsafe.md) |
| [Unsafe 参考](../../03_advanced/35_unsafe_reference.md) | ⟹ | [内联汇编 (Inline Assembly)](../../03_advanced/13_inline_assembly.md) |
| [Unsafe 参考](../../03_advanced/35_unsafe_reference.md) | ⟹ | [FFI 高级主题：跨语言边界的安全与性能](../../03_advanced/09_ffi_advanced.md) |
| [Unsafe 参考](../../03_advanced/35_unsafe_reference.md) | ⟹ | [自定义分配器与内存布局优化](../../03_advanced/14_custom_allocators.md) |

## L4 形式化理论层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [Linear Logic & Affine Logic](../../04_formal/01_linear_logic.md) | ⟹ | [Ownership Formalization](../../04_formal/03_ownership_formal.md) |
| [Linear Logic & Affine Logic](../../04_formal/01_linear_logic.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [Type Theory](../../04_formal/02_type_theory.md) | ⟹ | [Ownership Formalization](../../04_formal/03_ownership_formal.md) |
| [Type Theory](../../04_formal/02_type_theory.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/06_subtype_variance.md) | ⟹ | [Type Theory](../../04_formal/02_type_theory.md) |
| [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/06_subtype_variance.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [类型推断：Hindley-Milner 算法与 Rust 的工业实现](../../04_formal/08_type_inference.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [类型推断：Hindley-Milner 算法与 Rust 的工业实现](../../04_formal/08_type_inference.md) | ⟹ | [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/06_subtype_variance.md) |
| [线性逻辑在 Rust 中的工程应用](../../04_formal/09_linear_logic_applications.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [范畴论与 Rust：从函子到单子](../../04_formal/10_category_theory.md) | ⟹ | [Linear Logic & Affine Logic](../../04_formal/01_linear_logic.md) |
| [范畴论与 Rust：从函子到单子](../../04_formal/10_category_theory.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [分离逻辑：Rust 所有权的形式化根基](../../04_formal/11_separation_logic.md) | ⟹ | [Verification Toolchain Selection Guide](../../04_formal/05_verification_toolchain.md) |
| [分离逻辑：Rust 所有权的形式化根基](../../04_formal/11_separation_logic.md) | ⟹ | [Type Theory](../../04_formal/02_type_theory.md) |
| [指称语义与领域理论](../../04_formal/12_denotational_semantics.md) | ⟹ | [范畴论与 Rust：从函子到单子](../../04_formal/10_category_theory.md) |
| [指称语义与领域理论](../../04_formal/12_denotational_semantics.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [Lambda 演算与 Rust 计算模型](../../04_formal/14_lambda_calculus.md) | ⟹ | [范畴论与 Rust：从函子到单子](../../04_formal/10_category_theory.md) |
| [Lambda 演算与 Rust 计算模型](../../04_formal/14_lambda_calculus.md) | ⟹ | [指称语义与领域理论](../../04_formal/12_denotational_semantics.md) |
| [Hoare 逻辑：程序验证的形式化基础与 Rust 契约](../../04_formal/15_hoare_logic.md) | ⟹ | [分离逻辑：Rust 所有权的形式化根基](../../04_formal/11_separation_logic.md) |
| [Hoare 逻辑：程序验证的形式化基础与 Rust 契约](../../04_formal/15_hoare_logic.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [操作语义：程序行为的形式化定义](../../04_formal/17_operational_semantics.md) | ⟹ | [RustBelt & Verification Toolchain](../../04_formal/04_rustbelt.md) |
| [操作语义：程序行为的形式化定义](../../04_formal/17_operational_semantics.md) | ⟹ | [分离逻辑：Rust 所有权的形式化根基](../../04_formal/11_separation_logic.md) |
| [rustc 中的 Trait Solver](../../04_formal/26_trait_solver_in_rustc.md) | ⟹ | [Rustc 查询系统与增量编译](../../04_formal/19_rustc_query_system.md) |
| [rustc 中的 Trait Solver](../../04_formal/26_trait_solver_in_rustc.md) | ⟹ | [Ownership Formalization](../../04_formal/03_ownership_formal.md) |
| [Miri：Rust 未定义行为动态检测器](../../04_formal/31_miri.md) | ⟹ | [Tree Borrows 深度解析](../../04_formal/36_tree_borrows_deep_dive.md) |
| [Miri：Rust 未定义行为动态检测器](../../04_formal/31_miri.md) | ⟹ | [BorrowSanitizer 运行时别名模型检测](../../04_formal/34_borrow_sanitizer_in_formal.md) |
| [Miri：Rust 未定义行为动态检测器](../../04_formal/31_miri.md) | ⟹ | [现代 Rust 验证工具生态](../../04_formal/22_modern_verification_tools.md) |
| [Kani：Rust 有界模型检查器](../../04_formal/32_kani.md) | ⟹ | [Miri：Rust 未定义行为动态检测器](../../04_formal/31_miri.md) |
| [Kani：Rust 有界模型检查器](../../04_formal/32_kani.md) | ⟹ | [BorrowSanitizer 运行时别名模型检测](../../04_formal/34_borrow_sanitizer_in_formal.md) |
| [Rustc 名称解析与 HIR](../../04_formal/35_name_resolution_and_hir.md) | ⟹ | [Rustc 查询系统与增量编译](../../04_formal/19_rustc_query_system.md) |
| [Rustc 名称解析与 HIR](../../04_formal/35_name_resolution_and_hir.md) | ⟹ | [类型推断：Hindley-Milner 算法与 Rust 的工业实现](../../04_formal/08_type_inference.md) |
| [Rustc 名称解析与 HIR](../../04_formal/35_name_resolution_and_hir.md) | ⟹ | [rustc 中的 Trait Solver](../../04_formal/26_trait_solver_in_rustc.md) |
| [未定义行为清单](../../04_formal/37_behavior_considered_undefined.md) | ⟹ | [Miri：Rust 未定义行为动态检测器](../../04_formal/31_miri.md) |
| [未定义行为清单](../../04_formal/37_behavior_considered_undefined.md) | ⟹ | [Tree Borrows 深度解析](../../04_formal/36_tree_borrows_deep_dive.md) |
| [名称、作用域与解析](../../04_formal/40_names_and_resolution.md) | ⟹ | [Rustc 名称解析与 HIR](../../04_formal/35_name_resolution_and_hir.md) |
| [类型布局](../../04_formal/42_type_layout.md) | ⟹ | [未定义行为清单](../../04_formal/37_behavior_considered_undefined.md) |
| [析构函数与 Drop Scope](../../04_formal/43_destructors.md) | ⟹ | [未定义行为清单](../../04_formal/37_behavior_considered_undefined.md) |
| [符号约定](../../04_formal/44_notation.md) | ⟹ | [词法结构](../../04_formal/45_lexical_structure.md) |
| [词法结构](../../04_formal/45_lexical_structure.md) | ⟹ | [名称、作用域与解析](../../04_formal/40_names_and_resolution.md) |
| [词法结构](../../04_formal/45_lexical_structure.md) | ⟹ | [条目参考](../../04_formal/46_items_reference.md) |
| [条目参考](../../04_formal/46_items_reference.md) | ⟹ | [属性](../../04_formal/47_attributes.md) |
| [语句与表达式参考](../../04_formal/48_statements_and_expressions_reference.md) | ⟹ | [模式参考](../../04_formal/49_patterns_reference.md) |
| [语句与表达式参考](../../04_formal/48_statements_and_expressions_reference.md) | ⟹ | [常量求值](../../04_formal/39_constant_evaluation.md) |
| [语句与表达式参考](../../04_formal/48_statements_and_expressions_reference.md) | ⟹ | [析构函数与 Drop Scope](../../04_formal/43_destructors.md) |
| [模式参考](../../04_formal/49_patterns_reference.md) | ⟹ | [析构函数与 Drop Scope](../../04_formal/43_destructors.md) |
| [模式参考](../../04_formal/49_patterns_reference.md) | ⟹ | [语句与表达式参考](../../04_formal/48_statements_and_expressions_reference.md) |
| [类型系统参考](../../04_formal/50_type_system_reference.md) | ⟹ | [子类型与变型：Rust 类型系统中的协变、逆变与不变](../../04_formal/06_subtype_variance.md) |
| [类型系统参考](../../04_formal/50_type_system_reference.md) | ⟹ | [未定义行为清单](../../04_formal/37_behavior_considered_undefined.md) |
| [类型系统参考](../../04_formal/50_type_system_reference.md) | ⟹ | [Application Binary Interface](../../04_formal/38_application_binary_interface.md) |
| [名字参考](../../04_formal/51_names_reference.md) | ⟹ | [条目参考](../../04_formal/46_items_reference.md) |
| [名字参考](../../04_formal/51_names_reference.md) | ⟹ | [模式参考](../../04_formal/49_patterns_reference.md) |
| [Rust Reference 附录](../../04_formal/52_reference_appendices.md) | ⟹ | [语句与表达式参考](../../04_formal/48_statements_and_expressions_reference.md) |
| [Rust Reference 附录](../../04_formal/52_reference_appendices.md) | ⟹ | [模式参考](../../04_formal/49_patterns_reference.md) |

## L5 对比分析层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [Rust vs Go：线性所有权 vs CSP 过程逻辑](../../05_comparative/02_rust_vs_go.md) | ⟹ | [Paradigm Matrix: Multi-Language Formal Comparison](../../05_comparative/03_paradigm_matrix.md) |
| [Rust vs Python：系统编程与动态脚本的对照分析](../../05_comparative/07_rust_vs_python.md) | ⟹ | [Rust vs Go：线性所有权 vs CSP 过程逻辑](../../05_comparative/02_rust_vs_go.md) |
| [Rust vs Python：系统编程与动态脚本的对照分析](../../05_comparative/07_rust_vs_python.md) | ⟹ | [Rust vs Java：系统编程与托管运行时的范式对比](../../05_comparative/06_rust_vs_java.md) |
| [Rust vs Scala：类型系统的两种哲学](../../05_comparative/12_rust_vs_scala.md) | ⟹ | [Paradigm Matrix: Multi-Language Formal Comparison](../../05_comparative/03_paradigm_matrix.md) |
| [Rust vs TypeScript：静态类型系统的两种哲学 —— 编译期证明与渐进式工程](../../05_comparative/15_rust_vs_typescript.md) | ⟹ | [Rust vs JavaScript：系统编程与脚本执行的范式差异](../../05_comparative/08_rust_vs_javascript.md) |
| [C++ vs Rust：构造、运算符、RTTI、友元](../../05_comparative/16_cpp_rust_surface_features.md) | ⟹ | [Rust vs C++：ABI、对象模型与内存布局](../../05_comparative/18_cpp_abi_object_model.md) |

## L6 生态工程层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [Core Crates](../../06_ecosystem/03_core_crates.md) | ⟹ | [Application Domains](../../06_ecosystem/04_application_domains.md) |
| [Blockchain & Smart Contract Security](../../06_ecosystem/06_blockchain.md) | ⟹ | [Formal Ecosystem Tower](../../06_ecosystem/44_formal_ecosystem_tower.md) |
| [WASI & WebAssembly Component Model](../../06_ecosystem/08_wasi.md) | ⟹ | [Application Domains](../../06_ecosystem/04_application_domains.md) |
| [WASI & WebAssembly Component Model](../../06_ecosystem/08_wasi.md) | ⟹ | [Formal Ecosystem Tower](../../06_ecosystem/44_formal_ecosystem_tower.md) |
| [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) | ⟹ | [WASI & WebAssembly Component Model](../../06_ecosystem/08_wasi.md) |
| [日志与可观测性：Rust 服务端监控生态](../../06_ecosystem/13_logging_observability.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) |
| [文档生态：rustdoc、文档测试与 API 文档规范](../../06_ecosystem/14_documentation.md) | ⟹ | [Toolchain](../../06_ecosystem/01_toolchain.md) |
| [文档生态：rustdoc、文档测试与 API 文档规范](../../06_ecosystem/14_documentation.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) |
| [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/17_cross_compilation.md) | ⟹ | [WASI & WebAssembly Component Model](../../06_ecosystem/08_wasi.md) |
| [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/17_cross_compilation.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) |
| [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) |
| [安全 实践：Rust 代码的防御性编程](../../06_ecosystem/19_security_practices.md) | ⟹ | [Blockchain & Smart Contract Security](../../06_ecosystem/06_blockchain.md) |
| [许可证与合规：Rust 项目的法律工程](../../06_ecosystem/20_licensing_and_compliance.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/17_cross_compilation.md) |
| [许可证与合规：Rust 项目的法律工程](../../06_ecosystem/20_licensing_and_compliance.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) |
| [Rust 游戏开发生态](../../06_ecosystem/21_game_development.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) |
| [Rust 嵌入式系统开发](../../06_ecosystem/22_embedded_systems.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/17_cross_compilation.md) |
| [Rust 数据库访问生态](../../06_ecosystem/23_database_access.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/15_performance_optimization.md) |
| [Rust 数据库访问生态](../../06_ecosystem/23_database_access.md) | ⟹ | [Application Domains](../../06_ecosystem/04_application_domains.md) |
| [Rust 云原生生态](../../06_ecosystem/24_cloud_native.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) |
| [Rust 云原生生态](../../06_ecosystem/24_cloud_native.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) |
| [Rust CLI 开发生态](../../06_ecosystem/25_cli_development.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/15_performance_optimization.md) |
| [Rust CLI 开发生态](../../06_ecosystem/25_cli_development.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/17_cross_compilation.md) |
| [Rust 游戏开发](../../06_ecosystem/26_game_development.md) | ⟹ | [WebAssembly 生态：Rust 的浏览器外运行时](../../06_ecosystem/11_webassembly.md) |
| [Rust 游戏开发](../../06_ecosystem/26_game_development.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/15_performance_optimization.md) |
| [Rust Web 框架对比与选型](../../06_ecosystem/27_web_frameworks.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/24_cloud_native.md) |
| [Rust Web 框架对比与选型](../../06_ecosystem/27_web_frameworks.md) | ⟹ | [Design Patterns](../../06_ecosystem/02_patterns.md) |
| [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/24_cloud_native.md) |
| [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) | ⟹ | [安全 实践：Rust 代码的防御性编程](../../06_ecosystem/19_security_practices.md) |
| [算法与竞赛编程 (Algorithms & Competitive Programming)](../../06_ecosystem/29_algorithms_competitive_programming.md) | ⟹ | [Formal Ecosystem Tower](../../06_ecosystem/44_formal_ecosystem_tower.md) |
| [算法与竞赛编程 (Algorithms & Competitive Programming)](../../06_ecosystem/29_algorithms_competitive_programming.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/15_performance_optimization.md) |
| [系统可组合性 (System Composability)](../../06_ecosystem/30_system_composability.md) | ⟹ | [Application Domains](../../06_ecosystem/04_application_domains.md) |
| [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/31_microservice_patterns.md) | ⟹ | [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/32_event_driven_architecture.md) |
| [微服务架构模式 (Microservice Architecture Patterns)](../../06_ecosystem/31_microservice_patterns.md) | ⟹ | [Rust 云原生生态](../../06_ecosystem/24_cloud_native.md) |
| [事件驱动架构 (Event-Driven Architecture)](../../06_ecosystem/32_event_driven_architecture.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) |
| [流处理生态：Rust 实现与工业系统全景](../../06_ecosystem/36_stream_processing_ecosystem.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) |
| [数据库系统：Rust 在存储引擎中的语义](../../06_ecosystem/37_database_systems.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) |
| [网络协议：QUIC/HTTP-3 与 Rust 实现](../../06_ecosystem/38_network_protocols.md) | ⟹ | [流处理生态：Rust 实现与工业系统全景](../../06_ecosystem/36_stream_processing_ecosystem.md) |
| [网络协议：QUIC/HTTP-3 与 Rust 实现](../../06_ecosystem/38_network_protocols.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) |
| [Formal Ecosystem Tower](../../06_ecosystem/44_formal_ecosystem_tower.md) | ⟹ | [Application Domains](../../06_ecosystem/04_application_domains.md) |
| [Formal Ecosystem Tower](../../06_ecosystem/44_formal_ecosystem_tower.md) | ⟹ | [Toolchain](../../06_ecosystem/01_toolchain.md) |
| [C-to-Rust Translation Ecosystem](../../06_ecosystem/56_c_to_rust_translation.md) | ⟹ | [Formal Verification Tools](../../06_ecosystem/74_formal_verification_tools.md) |
| [将 Rust 集成到现有平台](../../06_ecosystem/58_platform_rust_integration.md) | ⟹ | [Rust 工业应用案例研究](../../06_ecosystem/75_industrial_case_studies.md) |
| [将 Rust 集成到现有平台](../../06_ecosystem/58_platform_rust_integration.md) | ⟹ | [Rust 操作系统内核开发](../../06_ecosystem/39_os_kernel.md) |
| [Cargo Build Scripts](../../06_ecosystem/59_cargo_build_scripts.md) | ⟹ | [Cargo Registry 与包发布](../../06_ecosystem/62_cargo_registries_and_publishing.md) |
| [Cargo Build Scripts](../../06_ecosystem/59_cargo_build_scripts.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [Cargo 依赖解析](../../06_ecosystem/60_cargo_dependency_resolution.md) | ⟹ | [Cargo Build Scripts](../../06_ecosystem/59_cargo_build_scripts.md) |
| [Cargo 依赖解析](../../06_ecosystem/60_cargo_dependency_resolution.md) | ⟹ | [Cargo Registry 与包发布](../../06_ecosystem/62_cargo_registries_and_publishing.md) |
| [Cargo Source Replacement 与 Vendoring](../../06_ecosystem/61_cargo_source_replacement.md) | ⟹ | [Cargo 认证与构建缓存](../../06_ecosystem/63_cargo_authentication_and_cache.md) |
| [Cargo Source Replacement 与 Vendoring](../../06_ecosystem/61_cargo_source_replacement.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [Cargo Registry 与包发布](../../06_ecosystem/62_cargo_registries_and_publishing.md) | ⟹ | [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/72_cargo_security_cves.md) |
| [Cargo Registry 与包发布](../../06_ecosystem/62_cargo_registries_and_publishing.md) | ⟹ | [Toolchain](../../06_ecosystem/01_toolchain.md) |
| [Cargo 认证与构建缓存](../../06_ecosystem/63_cargo_authentication_and_cache.md) | ⟹ | [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/72_cargo_security_cves.md) |
| [Cargo 认证与构建缓存](../../06_ecosystem/63_cargo_authentication_and_cache.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [Cargo Manifest 参考速查](../../06_ecosystem/64_cargo_manifest_reference.md) | ⟹ | [Cargo Profiles 与 Lints](../../06_ecosystem/65_cargo_profiles_and_lints.md) |
| [Cargo Manifest 参考速查](../../06_ecosystem/64_cargo_manifest_reference.md) | ⟹ | [Cargo Source Replacement 与 Vendoring](../../06_ecosystem/61_cargo_source_replacement.md) |
| [Cargo Profiles 与 Lints](../../06_ecosystem/65_cargo_profiles_and_lints.md) | ⟹ | [Cargo 认证与构建缓存](../../06_ecosystem/63_cargo_authentication_and_cache.md) |
| [Cargo Profiles 与 Lints](../../06_ecosystem/65_cargo_profiles_and_lints.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [Cargo 子命令与插件生态](../../06_ecosystem/66_cargo_subcommands_and_plugins.md) | ⟹ | [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/72_cargo_security_cves.md) |
| [Cargo 子命令与插件生态](../../06_ecosystem/66_cargo_subcommands_and_plugins.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [Rust 编译器的 LLVM 后端与代码生成](../../06_ecosystem/67_llvm_backend_and_codegen.md) | ⟹ | [rustc Driver、Interface 与 Stable MIR](../../06_ecosystem/68_rustc_driver_and_stable_mir.md) |
| [Rust 编译器的 LLVM 后端与代码生成](../../06_ecosystem/67_llvm_backend_and_codegen.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/47_compiler_infrastructure.md) |
| [rustc Driver、Interface 与 Stable MIR](../../06_ecosystem/68_rustc_driver_and_stable_mir.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/47_compiler_infrastructure.md) |
| [rustc Driver、Interface 与 Stable MIR](../../06_ecosystem/68_rustc_driver_and_stable_mir.md) | ⟹ | [rustc 编译器诊断与 UI Tests](../../06_ecosystem/69_compiler_diagnostics_and_ui_tests.md) |
| [rustc 编译器诊断与 UI Tests](../../06_ecosystem/69_compiler_diagnostics_and_ui_tests.md) | ⟹ | [rustc 自举](../../06_ecosystem/70_rustc_bootstrap.md) |
| [rustc 编译器诊断与 UI Tests](../../06_ecosystem/69_compiler_diagnostics_and_ui_tests.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/47_compiler_infrastructure.md) |
| [rustc 自举](../../06_ecosystem/70_rustc_bootstrap.md) | ⟹ | [rustc 编译器测试体系](../../06_ecosystem/71_compiler_testing.md) |
| [rustc 编译器测试体系](../../06_ecosystem/71_compiler_testing.md) | ⟹ | [Rust 编译器基础设施深度解析](../../06_ecosystem/47_compiler_infrastructure.md) |
| [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/72_cargo_security_cves.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/17_cross_compilation.md) |
| [Cargo 安全公告：CVE-2026-5222 与 CVE-2026-5223](../../06_ecosystem/72_cargo_security_cves.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [模式组合代数：设计模式的结构化关联与冲突分析](../../06_ecosystem/73_pattern_composition_algebra.md) | ⟹ | [分布式 系统：Rust 在微服务 与集群中的工程实践](../../06_ecosystem/18_distributed_systems.md) |
| [模式组合代数：设计模式的结构化关联与冲突分析](../../06_ecosystem/73_pattern_composition_algebra.md) | ⟹ | [Rust 系统设计原则与国际权威对齐](../../06_ecosystem/05_system_design_principles.md) |
| [Cargo Workspaces](../../06_ecosystem/78_cargo_workspaces.md) | ⟹ | [Cargo Profiles 与 Lints](../../06_ecosystem/65_cargo_profiles_and_lints.md) |
| [Cargo Workspaces](../../06_ecosystem/78_cargo_workspaces.md) | ⟹ | [Cargo Registry 与包发布](../../06_ecosystem/62_cargo_registries_and_publishing.md) |
| [Rust 常用开发工具](../../06_ecosystem/79_development_tools.md) | ⟹ | [Cargo Profiles 与 Lints](../../06_ecosystem/65_cargo_profiles_and_lints.md) |
| [Cargo 入门](../../06_ecosystem/80_cargo_getting_started.md) | ⟹ | [Cargo 工作流](../../06_ecosystem/81_cargo_workflow.md) |
| [Cargo 入门](../../06_ecosystem/80_cargo_getting_started.md) | ⟹ | [Cargo 依赖解析](../../06_ecosystem/60_cargo_dependency_resolution.md) |
| [Cargo 入门](../../06_ecosystem/80_cargo_getting_started.md) | ⟹ | [Cargo Manifest 参考速查](../../06_ecosystem/64_cargo_manifest_reference.md) |
| [Cargo 工作流](../../06_ecosystem/81_cargo_workflow.md) | ⟹ | [Cargo 指南实践](../../06_ecosystem/82_cargo_guide_practices.md) |
| [Cargo 工作流](../../06_ecosystem/81_cargo_workflow.md) | ⟹ | [Cargo Workspaces](../../06_ecosystem/78_cargo_workspaces.md) |
| [Cargo 工作流](../../06_ecosystem/81_cargo_workflow.md) | ⟹ | [Cargo 依赖解析](../../06_ecosystem/60_cargo_dependency_resolution.md) |
| [Cargo 指南实践](../../06_ecosystem/82_cargo_guide_practices.md) | ⟹ | [Cargo 配置与环境变量](../../06_ecosystem/83_cargo_configuration.md) |
| [Cargo 指南实践](../../06_ecosystem/82_cargo_guide_practices.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [Cargo 指南实践](../../06_ecosystem/82_cargo_guide_practices.md) | ⟹ | [性能优化：Rust 代码的测量与调优](../../06_ecosystem/15_performance_optimization.md) |
| [Cargo 配置与环境变量](../../06_ecosystem/83_cargo_configuration.md) | ⟹ | [Cargo 命令参考](../../06_ecosystem/84_cargo_commands_reference.md) |
| [Cargo 配置与环境变量](../../06_ecosystem/83_cargo_configuration.md) | ⟹ | [交叉编译：多目标平台支持与条件编译](../../06_ecosystem/17_cross_compilation.md) |
| [Cargo 命令参考](../../06_ecosystem/84_cargo_commands_reference.md) | ⟹ | [Cargo Manifest 目标与元数据](../../06_ecosystem/85_cargo_manifest_targets.md) |
| [Cargo 命令参考](../../06_ecosystem/84_cargo_commands_reference.md) | ⟹ | [Cargo Registry 内部机制](../../06_ecosystem/86_cargo_registry_internals.md) |
| [Cargo 命令参考](../../06_ecosystem/84_cargo_commands_reference.md) | ⟹ | [DevOps 与 CI/CD：Rust 的持续交付工程实践](../../06_ecosystem/28_devops_and_ci_cd.md) |
| [Cargo Manifest 目标与元数据](../../06_ecosystem/85_cargo_manifest_targets.md) | ⟹ | [Cargo 命令参考](../../06_ecosystem/84_cargo_commands_reference.md) |
| [Cargo Manifest 目标与元数据](../../06_ecosystem/85_cargo_manifest_targets.md) | ⟹ | [Cargo Build Scripts](../../06_ecosystem/59_cargo_build_scripts.md) |
| [Cargo Registry 内部机制](../../06_ecosystem/86_cargo_registry_internals.md) | ⟹ | [Cargo 命令参考](../../06_ecosystem/84_cargo_commands_reference.md) |
| [Cargo Registry 内部机制](../../06_ecosystem/86_cargo_registry_internals.md) | ⟹ | [安全 实践：Rust 代码的防御性编程](../../06_ecosystem/19_security_practices.md) |

## L7 前沿趋势层

### 层内引用关系

| 源概念 | 关系 | 目标概念 |
|:---|:---:|:---|
| [MC/DC Coverage 概念预研：安全关键 Rust 的覆盖率验证](../../07_future/07_mcdc_coverage_preview.md) | ⟹ | [Formal Methods Industrialization](../../07_future/02_formal_methods.md) |
| [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/08_safety_tags_preview.md) | ⟹ | [Formal Methods Industrialization](../../07_future/02_formal_methods.md) |
| [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/08_safety_tags_preview.md) | ⟹ | [AI × Rust：生成-验证闭环与确定性容器](../../07_future/01_ai_integration.md) |
| [并行 前端编译预研：Rust 编译器 的多核扩展](../../07_future/09_parallel_frontend_preview.md) | ⟹ | [Language Evolution](../../07_future/03_evolution.md) |
| [派生 CoercePointee 预研：智能指针的自动类型强制](../../07_future/10_derive_coerce_pointee_preview.md) | ⟹ | [Language Evolution](../../07_future/03_evolution.md) |
| [Const Trait Impl 预研：常量上下文中的 Trait 泛化](../../07_future/11_const_trait_impl_preview.md) | ⟹ | [Language Evolution](../../07_future/03_evolution.md) |
| [Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界](../../07_future/12_return_type_notation_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/05_rust_version_tracking.md) |
| [Return Type Notation（RTN）预研：为 AFIT/RPITIT 返回类型添加边界](../../07_future/12_return_type_notation_preview.md) | ⟹ | [Async Drop：异步资源的优雅销毁](../../07_future/18_async_drop_preview.md) |
| [Unsafe Fields 预研：字段级安全边界的精确标注](../../07_future/13_unsafe_fields_preview.md) | ⟹ | [Safety Tags 概念预研：Unsafe 契约的机器可读标注](../../07_future/08_safety_tags_preview.md) |
| [Pin Ergonomics 与 Reborrow Traits 预研：超越 `Pin::as_mut`](../../07_future/15_pin_ergonomics_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/05_rust_version_tracking.md) |
| [Async Drop：异步资源的优雅销毁](../../07_future/18_async_drop_preview.md) | ⟹ | [Generator Blocks（gen）预览](../../07_future/22_gen_blocks_preview.md) |
| [Rust 2024 Edition (1.85.0+ stable)](../../07_future/19_rust_edition_preview.md) | ⟹ | [Edition 2024 完全指南：新特性与迁移策略](../../07_future/44_edition_guide.md) |
| [Rust 2024 Edition (1.85.0+ stable)](../../07_future/19_rust_edition_preview.md) | ⟹ | [Rust Edition 机制与迁移指南](../../07_future/23_rust_edition_guide.md) |
| [Rust 2024 Edition (1.85.0+ stable)](../../07_future/19_rust_edition_preview.md) | ⟹ | [Language Evolution](../../07_future/03_evolution.md) |
| [BorrowSanitizer 概念预研：运行时借用检查工业化](../../07_future/20_borrowsanitizer_preview.md) | ⟹ | [Formal Methods Industrialization](../../07_future/02_formal_methods.md) |
| [Rust 在 AI 与机器学习中的新兴角色](../../07_future/21_rust_in_ai.md) | ⟹ | [AI × Rust：生成-验证闭环与确定性容器](../../07_future/01_ai_integration.md) |
| [Rust 在 AI 与机器学习中的新兴角色](../../07_future/21_rust_in_ai.md) | ⟹ | [Language Evolution](../../07_future/03_evolution.md) |
| [Rust Edition 机制与迁移指南](../../07_future/23_rust_edition_guide.md) | ⟹ | [Edition 2024 完全指南：新特性与迁移策略](../../07_future/44_edition_guide.md) |
| [Rust 2027 Edition 及未来路线图](../../07_future/24_roadmap.md) | ⟹ | [Formal Methods Industrialization](../../07_future/02_formal_methods.md) |
| [Rust 2027 Edition 及未来路线图](../../07_future/24_roadmap.md) | ⟹ | [Rust 在 AI 与机器学习中的新兴角色](../../07_future/21_rust_in_ai.md) |
| [Open Enums 概念预研：从 `#[non_exhaustive]` 到可扩展枚举](../../07_future/25_open_enums_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/05_rust_version_tracking.md) |
| [Rust for WebAssembly：从 wasm-bindgen 到前端框架的深度技术栈](../../07_future/28_rust_for_webassembly.md) | ⟹ | [Formal Methods Industrialization](../../07_future/02_formal_methods.md) |
| [Ferrocene 预研：Rust 的安全关键认证之路](../../07_future/35_ferrocene_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/05_rust_version_tracking.md) |
| [Cranelift 后端预研：Rust 编译器的快速调试编译](../../07_future/38_cranelift_backend_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/05_rust_version_tracking.md) |
| [Ergonomic Ref-Counting 预研：人机工学引用计数](../../07_future/40_ergonomic_ref_counting_preview.md) | ⟹ | [Rust for Linux ：操作系统内核中的内存安全](../../07_future/43_rust_for_linux.md) |
| [Rust 语言规范预研：从参考文档到形式化规范](../../07_future/41_rust_specification_preview.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/05_rust_version_tracking.md) |
| [Rust for Linux ：操作系统内核中的内存安全](../../07_future/43_rust_for_linux.md) | ⟹ | [Language Evolution](../../07_future/03_evolution.md) |
| [Edition 2024 完全指南：新特性与迁移策略](../../07_future/44_edition_guide.md) | ⟹ | [Language Evolution](../../07_future/03_evolution.md) |
| [AArch64 SVE / SME：可伸缩向量扩展预览](../../07_future/48_aarch64_sve_sme_preview.md) | ⟹ | [Rust for Linux ：操作系统内核中的内存安全](../../07_future/43_rust_for_linux.md) |
| [Rust 的发布流程与 Nightly Rust](../../07_future/50_nightly_rust.md) | ⟹ | [Rust 形式模型演进跟踪](../../07_future/05_rust_version_tracking.md) |
| [Rust 的发布流程与 Nightly Rust](../../07_future/50_nightly_rust.md) | ⟹ | [Rust 1.97.0 稳定特性](../../07_future/rust_1_97_stabilized.md) |
| [BorrowSanitizer：动态别名规则验证工具](../../07_future/borrow_sanitizer.md) | ⟹ | [Formal Methods Industrialization](../../07_future/02_formal_methods.md) |
| [Rust 1.97 前沿特性预览](../../07_future/rust_1_97_preview.md) | ⟹ | [Rust 1.98+ 前沿特性预览](../../07_future/rust_1_98_preview.md) |
| [Rust 1.97.0 稳定特性](../../07_future/rust_1_97_stabilized.md) | ⟹ | [Rust 1.98+ 前沿特性预览](../../07_future/rust_1_98_preview.md) |
| [Rust 1.98+ 前沿特性预览](../../07_future/rust_1_98_preview.md) | ⟹ | [Rust 1.97 前沿特性预览](../../07_future/rust_1_97_preview.md) |

---

> **内容分级**: [元层]
