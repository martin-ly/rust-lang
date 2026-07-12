# 缺口与行动计划（Gap and Action Plan）

> **EN**: Gap and Action Plan
> **Summary**: 基于拓扑抽取结果识别的当前缺口：来源覆盖、表征完整性、层间/层内映射、定义一致性。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、当前缺口概览

| 缺口类型 | 数量 | 说明 |
|:---|:---:|:---|
| 无权威来源标注 | 1 | 概念文件未引用任何外部权威来源 |
| 来源标注薄弱（≤2） | 0 | 概念文件仅引用 1–2 个来源 |
| 无定理链 | 211 | 概念文件缺少定理链 |
| 无 A/S/P 标记 | 242 | 概念文件缺少 A/S/P 维度标记 |
| 无知识表征章节 | 65 | 概念文件无决策树/矩阵/示例等表征 |

## 二、优先修复任务

本节围绕「优先修复任务」展开，依次讨论 P0：补全权威来源（L1–L4 核心概念）、P1：增强知识表征与P2：对齐国际标准。

### P0：补全权威来源（L1–L4 核心概念）

| 概念 | 层级 | 当前来源数 | 建议行动 |
|:---|:---:|:---:|:---|

### P1：增强知识表征

| 概念 | 层级 | 缺失表征 | 建议行动 |
|:---|:---:|:---|:---|
| [编程语言理论基础](../../01_foundation/00_start/01_pl_prerequisites.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 所有权-借用-生命周期知识图谱](../../01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Preludes](../../01_foundation/07_modules_and_items/10_preludes.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [错误处理控制流](../../01_foundation/08_error_handling/02_error_handling_control_flow.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：类型系统](../../01_foundation/11_quizzes/24_quiz_type_system.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：错误处理](../../01_foundation/11_quizzes/25_quiz_error_handling.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：模块系统与测试](../../01_foundation/11_quizzes/26_quiz_modules_testing.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：闭包与迭代器](../../01_foundation/11_quizzes/27_quiz_closures_iterators.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：通用 PL 基座](../../01_foundation/11_quizzes/29_quiz_pl_foundations.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：所有权、借用与生命周期](../../01_foundation/11_quizzes/33_quiz_ownership_borrowing.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：Trait 与泛型](../../02_intermediate/01_generics/04_quiz_traits_and_generics.md) | L2 进阶概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：内存管理](../../02_intermediate/02_memory_management/05_quiz_memory_management.md) | L2 进阶概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：C/C++ → Rust 基础知识对比](../../02_intermediate/09_quizzes/30_quiz_cpp_rust_foundations.md) | L2 进阶概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：并发与异步](../../03_advanced/00_concurrency/08_quiz_concurrency_async.md) | L3 高级概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Async 边界全景](../../03_advanced/01_async/06_async_boundary_panorama.md) | L3 高级概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Unsafe 边界全景](../../03_advanced/02_unsafe/02_unsafe_boundary_panorama.md) | L3 高级概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Unsafe Rust 模式：安全抽象的核心技术](../../03_advanced/02_unsafe/04_unsafe_rust_patterns.md) | L3 高级概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：Unsafe Rust](../../03_advanced/02_unsafe/05_quiz_unsafe.md) | L3 高级概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：宏系统](../../03_advanced/03_proc_macros/10_quiz_macros.md) | L3 高级概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [所有权性能优化](../../03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md) | L3 高级概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Safety Tags](../../04_formal/02_separation_logic/03_safety_tags_in_formal.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [形式化方法在 Rust 中的应用](../../04_formal/04_model_checking/02_formal_methods.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [通用程序语言理论基础：Rust 的 PL 基座](../../04_formal/04_model_checking/05_programming_language_foundations.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：形式化方法概念](../../04_formal/04_model_checking/06_quiz_formal_methods.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rustc 查询系统与增量编译](../../04_formal/05_rustc_internals/01_rustc_query_system.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rustc 名称解析与 HIR](../../04_formal/05_rustc_internals/04_name_resolution_and_hir.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：Rust vs 系统编程语言](../../05_comparative/03_domain_comparisons/02_quiz_rust_vs_systems.md) | L5 对比分析层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：Rust 工具链](../../06_ecosystem/00_toolchain/06_quiz_toolchain.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rustdoc 1.96–1.97 变更](../../06_ecosystem/00_toolchain/07_rustdoc_196_changes.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 编译器的 LLVM 后端与代码生成](../../06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |

### P2：对齐国际标准

针对以下主题补充 Unicode / ISO / IEEE / IETF / ABI 标准引用：

- 字符串与编码：`concept/01_foundation/18_strings_and_encoding.md` → Unicode Standard
- 内联汇编：`concept/03_advanced/13_inline_assembly.md` → Intel/ARM 架构手册
- 网络编程：`concept/03_advanced/18_network_programming.md` → IETF RFCs
- ABI：`concept/04_formal/38_application_binary_interface.md` → Itanium C++ ABI / System V AMD64 ABI
- 交叉编译/嵌入式：`concept/06_ecosystem/17_cross_compilation.md` / `22_embedded_systems.md` → 目标平台规范

## 三、自动化建议

1. 在 `kb_auditor.py` 中增加：概念文件必须引用至少一个 L1 来源。
2. 每月运行 `extract_concept_topology.py` + `generate_knowledge_topology_atlas.py` 生成图谱集。
3. 对新增文件自动检测是否包含决策树/矩阵/示例反例中的一种表征。

---

> 本文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 生成；请勿手工编辑，更新后重新运行生成脚本。
