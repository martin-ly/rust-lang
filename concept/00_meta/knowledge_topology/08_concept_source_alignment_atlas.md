# 概念-权威来源对齐图谱（Concept-Source Alignment Atlas）

> **EN**: Concept-Source Alignment Atlas
> **Summary**: 每个核心概念与国际化权威来源的对齐：Rust Reference、TRPL、RFCs、学术、课程、工业、标准。
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、权威来源覆盖统计

| 来源层级 | 来源类型 | 引用次数 | 涉及概念数 |
|:---|:---|:---:|:---:|
| Lx_other | 其他 | 3522 | 288 |
| L1_specification | Rust Reference | 676 | 290 |
| L1_trpl | TRPL | 570 | 246 |
| L1_std | std docs | 287 | 96 |
| L1_github | Rust GitHub | 217 | 95 |
| L1_rustonomicon | Rustonomicon | 204 | 125 |
| L0_wikipedia | Wikipedia | 194 | 75 |
| L2_academic | 学术论文 | 184 | 57 |
| L1_rfc | RFCs | 155 | 68 |
| L1_blog | Rust Blog | 116 | 32 |
| L1_cargo | Cargo Book | 109 | 50 |
| L3_course | 顶尖课程 | 71 | 34 |
| L5_standard | 国际标准 | 38 | 18 |

## 二、各层级权威来源覆盖度

| 层级 | 概念数 | Rust Reference | TRPL | RFCs | 学术 | 课程 | 标准 |
|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| L0 元信息层 | 50 | 41 | 44 | 3 | 9 | 3 | 0 |
| L1 基础概念层 | 43 | 35 | 35 | 8 | 4 | 3 | 4 |
| L2 进阶概念层 | 33 | 24 | 27 | 10 | 2 | 0 | 0 |
| L3 高级概念层 | 36 | 33 | 23 | 14 | 3 | 6 | 2 |
| L4 形式化理论层 | 51 | 45 | 20 | 7 | 23 | 14 | 1 |
| L5 对比分析层 | 19 | 18 | 19 | 1 | 3 | 1 | 1 |
| L6 生态工程层 | 86 | 61 | 49 | 7 | 8 | 6 | 8 |
| L7 前沿趋势层 | 54 | 33 | 29 | 18 | 5 | 1 | 2 |

## 三、缺少权威来源的概念（需补全）

| 概念 | 层级 | 当前来源数 | 建议补全来源 |
|:---|:---:|:---:|:---|
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/19_value_vs_reference_semantics.md) | L1 基础概念层 | 0 | Rust Reference / TRPL |
| [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/23_move_semantics.md) | L1 基础概念层 | 0 | Rust Reference / TRPL |
| [测验：所有权、借用与生命周期](../../01_foundation/33_quiz_ownership_borrowing.md) | L1 基础概念层 | 2 | Rust Reference / TRPL |
| [编程语言理论基础](../../01_foundation/34_pl_prerequisites.md) | L1 基础概念层 | 2 | Rust Reference / TRPL |
| [Rust 关键字](../../01_foundation/36_keywords.md) | L1 基础概念层 | 2 | Rust Reference / TRPL |
| [Rust 运算符与符号](../../01_foundation/37_operators_and_symbols.md) | L1 基础概念层 | 1 | Rust Reference / TRPL |
| [Crate 与源文件](../../01_foundation/38_crates_and_source_files.md) | L1 基础概念层 | 1 | Rust Reference / TRPL |
| [项](../../01_foundation/39_items.md) | L1 基础概念层 | 1 | Rust Reference / TRPL |
| [模式匹配](../../01_foundation/40_patterns.md) | L1 基础概念层 | 1 | Rust Reference / TRPL |
| [语句与表达式](../../01_foundation/41_statements_and_expressions.md) | L1 基础概念层 | 1 | Rust Reference / TRPL |
| [Rust API 命名约定](../../02_intermediate/22_api_naming_conventions.md) | L2 进阶概念层 | 1 | Rust Reference / TRPL |
| [RTTI 与动态类型识别：从 C++ 到 Rust](../../02_intermediate/25_rtti_and_dynamic_typing.md) | L2 进阶概念层 | 0 | Rust Reference / TRPL |
| [C 预处理器 vs Rust 宏：从文本替换到语法树](../../02_intermediate/26_c_preprocessor_vs_rust_macros.md) | L2 进阶概念层 | 0 | Rust Reference / TRPL |
| [异常安全：C++ 与 Rust 的错误处理哲学](../../02_intermediate/27_exception_safety_rust_cpp.md) | L2 进阶概念层 | 0 | Rust Reference / TRPL |
| [构造与初始化：C++ 的构造函数 vs Rust 的结构体字面量](../../02_intermediate/28_construction_and_initialization.md) | L2 进阶概念层 | 0 | Rust Reference / TRPL |
| [友元 vs 模块可见性：C++ 的 `friend` 与 Rust 的隐私边界](../../02_intermediate/29_friend_vs_module_privacy.md) | L2 进阶概念层 | 0 | Rust Reference / TRPL |
| [可派生 Trait](../../02_intermediate/31_derive_traits.md) | L2 进阶概念层 | 1 | Rust Reference / TRPL |
| [是否需要进入 L4 形式化层？](../../03_advanced/00_before_formal.md) | L3 高级概念层 | 2 | Rust Reference / TRPL |
| [内联汇编 (Inline Assembly)](../../03_advanced/13_inline_assembly.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [Async Closures](../../03_advanced/24_async_closures.md) | L3 高级概念层 | 0 | Rust Reference / TRPL |
| [Linkage](../../03_advanced/27_linkage.md) | L3 高级概念层 | 2 | Rust Reference / TRPL |
| [条件编译](../../03_advanced/28_conditional_compilation.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [Rust 内存模型](../../03_advanced/29_memory_model.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [Rust 运行时](../../03_advanced/30_rust_runtime.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [Panic 机制](../../03_advanced/31_panic.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [内存分配与生命周期](../../03_advanced/32_memory_allocation_and_lifetime.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [变量](../../03_advanced/33_variables.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [可见性与隐私](../../03_advanced/34_visibility_and_privacy.md) | L3 高级概念层 | 1 | Rust Reference / TRPL |
| [Aeneas Symbolic Semantics](../../04_formal/30_aeneas_symbolic_semantics.md) | L4 形式化理论层 | 0 | Rust Reference + POPL/PLDI/RustBelt |
| [常量求值](../../04_formal/39_constant_evaluation.md) | L4 形式化理论层 | 1 | Rust Reference + POPL/PLDI/RustBelt |
| [特殊类型与 Trait](../../04_formal/41_special_types_and_traits.md) | L4 形式化理论层 | 1 | Rust Reference + POPL/PLDI/RustBelt |
| [类型布局](../../04_formal/42_type_layout.md) | L4 形式化理论层 | 1 | Rust Reference + POPL/PLDI/RustBelt |
| [析构函数与 Drop Scope](../../04_formal/43_destructors.md) | L4 形式化理论层 | 1 | Rust Reference + POPL/PLDI/RustBelt |
| [符号约定](../../04_formal/44_notation.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [词法结构](../../04_formal/45_lexical_structure.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [条目参考](../../04_formal/46_items_reference.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [属性](../../04_formal/47_attributes.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [语句与表达式参考](../../04_formal/48_statements_and_expressions_reference.md) | L4 形式化理论层 | 1 | Rust Reference + POPL/PLDI/RustBelt |
| [模式参考](../../04_formal/49_patterns_reference.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [类型系统参考](../../04_formal/50_type_system_reference.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [名字参考](../../04_formal/51_names_reference.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [Rust Reference 附录](../../04_formal/52_reference_appendices.md) | L4 形式化理论层 | 2 | Rust Reference + POPL/PLDI/RustBelt |
| [将 Rust 集成到现有平台](../../06_ecosystem/58_platform_rust_integration.md) | L6 生态工程层 | 1 | RFCs + 工业/标准来源 |
| [Cargo Manifest 参考速查](../../06_ecosystem/64_cargo_manifest_reference.md) | L6 生态工程层 | 2 | RFCs + 工业/标准来源 |
| [Cargo 1.96 新特性与工具链变更](../../06_ecosystem/76_cargo_196_features.md) | L6 生态工程层 | 1 | RFCs + 工业/标准来源 |
| [Rustdoc 1.96 变更](../../06_ecosystem/77_rustdoc_196_changes.md) | L6 生态工程层 | 1 | RFCs + 工业/标准来源 |
| [Cargo Workspaces](../../06_ecosystem/78_cargo_workspaces.md) | L6 生态工程层 | 1 | RFCs + 工业/标准来源 |
| [Cargo 入门](../../06_ecosystem/80_cargo_getting_started.md) | L6 生态工程层 | 1 | RFCs + 工业/标准来源 |
| [Cargo 工作流](../../06_ecosystem/81_cargo_workflow.md) | L6 生态工程层 | 2 | RFCs + 工业/标准来源 |
| [Cargo 指南实践](../../06_ecosystem/82_cargo_guide_practices.md) | L6 生态工程层 | 2 | RFCs + 工业/标准来源 |

---

> **内容分级**: [元层]
