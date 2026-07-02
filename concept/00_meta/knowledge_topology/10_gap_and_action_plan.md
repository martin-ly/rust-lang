# 缺口与行动计划（Gap and Action Plan）

> **EN**: Gap and Action Plan
> **Summary**: 基于拓扑抽取结果识别的当前缺口：来源覆盖、表征完整性、层间/层内映射、定义一致性。
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、当前缺口概览

| 缺口类型 | 数量 | 说明 |
|:---|:---:|:---|
| 无权威来源标注 | 11 | 概念文件未引用任何外部权威来源 |
| 来源标注薄弱（≤2） | 51 | 概念文件仅引用 1–2 个来源 |
| 无定理链 | 148 | 概念文件缺少定理链 |
| 无 A/S/P 标记 | 188 | 概念文件缺少 A/S/P 维度标记 |
| 无知识表征章节 | 254 | 概念文件无决策树/矩阵/示例等表征 |

## 二、优先修复任务

### P0：补全权威来源（L1–L4 核心概念）

| 概念 | 层级 | 当前来源数 | 建议行动 |
|:---|:---:|:---:|:---|
| [测验：所有权、借用与生命周期](../../01_foundation/33_quiz_ownership_borrowing.md) | L1 基础概念层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [编程语言理论基础](../../01_foundation/34_pl_prerequisites.md) | L1 基础概念层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [Rust 关键字](../../01_foundation/36_keywords.md) | L1 基础概念层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [Rust 运算符与符号](../../01_foundation/37_operators_and_symbols.md) | L1 基础概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [Crate 与源文件](../../01_foundation/38_crates_and_source_files.md) | L1 基础概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [项](../../01_foundation/39_items.md) | L1 基础概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [模式匹配](../../01_foundation/40_patterns.md) | L1 基础概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [语句与表达式](../../01_foundation/41_statements_and_expressions.md) | L1 基础概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [Rust API 命名约定](../../02_intermediate/22_api_naming_conventions.md) | L2 进阶概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [可派生 Trait](../../02_intermediate/31_derive_traits.md) | L2 进阶概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [是否需要进入 L4 形式化层？](../../03_advanced/00_before_formal.md) | L3 高级概念层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [内联汇编 (Inline Assembly)](../../03_advanced/13_inline_assembly.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [Linkage](../../03_advanced/27_linkage.md) | L3 高级概念层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [条件编译](../../03_advanced/28_conditional_compilation.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [Rust 内存模型](../../03_advanced/29_memory_model.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [Rust 运行时](../../03_advanced/30_rust_runtime.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [Panic 机制](../../03_advanced/31_panic.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [内存分配与生命周期](../../03_advanced/32_memory_allocation_and_lifetime.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [变量](../../03_advanced/33_variables.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [可见性与隐私](../../03_advanced/34_visibility_and_privacy.md) | L3 高级概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [常量求值](../../04_formal/39_constant_evaluation.md) | L4 形式化理论层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [特殊类型与 Trait](../../04_formal/41_special_types_and_traits.md) | L4 形式化理论层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [类型布局](../../04_formal/42_type_layout.md) | L4 形式化理论层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [析构函数与 Drop Scope](../../04_formal/43_destructors.md) | L4 形式化理论层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [符号约定](../../04_formal/44_notation.md) | L4 形式化理论层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [词法结构](../../04_formal/45_lexical_structure.md) | L4 形式化理论层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [条目参考](../../04_formal/46_items_reference.md) | L4 形式化理论层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [属性](../../04_formal/47_attributes.md) | L4 形式化理论层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |
| [语句与表达式参考](../../04_formal/48_statements_and_expressions_reference.md) | L4 形式化理论层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [模式参考](../../04_formal/49_patterns_reference.md) | L4 形式化理论层 | 2 | 补充 Rust Reference / TRPL / 学术来源 |

### P1：增强知识表征

| 概念 | 层级 | 缺失表征 | 建议行动 |
|:---|:---:|:---|:---|
| [Rust 起步指南](../../01_foundation/00_start.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/05_reference_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [零成本抽象：Rust 的性能哲学](../../01_foundation/06_zero_cost_abstractions.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [控制流：表达式导向的流程控制](../../01_foundation/07_control_flow.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/08_collections.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [字符串与文本：Rust 的 Unicode 处理与格式化系统](../../01_foundation/09_strings_and_text.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/10_numerics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/11_modules_and_paths.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [属性与声明宏：编译期元编程基础](../../01_foundation/12_attributes_and_macros.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Panic 与 Abort：不可恢复错误的处理机制](../../01_foundation/13_panic_and_abort.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [类型强制与转换：显式与隐式的边界](../../01_foundation/14_coercion_and_casting.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [闭包基础：捕获环境与匿名函数](../../01_foundation/15_closure_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测试基础：从单元测试到集成测试](../../01_foundation/16_testing_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [字符串与编码：Rust 的文本处理类型系统](../../01_foundation/18_strings_and_encoding.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/19_value_vs_reference_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/23_move_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：类型系统](../../01_foundation/24_quiz_type_system.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：错误处理](../../01_foundation/25_quiz_error_handling.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：模块系统与测试](../../01_foundation/26_quiz_modules_testing.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：闭包与迭代器](../../01_foundation/27_quiz_closures_iterators.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [所有权清单自测：Brown University Ownership Inventory](../../01_foundation/28_ownership_inventories_brown_book.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：通用 PL 基座](../../01_foundation/29_quiz_pl_foundations.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Never Type (`!`)：底类型与穷尽性](../../01_foundation/31_never_type.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 错误处理基础](../../01_foundation/32_error_handling_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：所有权、借用与生命周期](../../01_foundation/33_quiz_ownership_borrowing.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [编程语言理论基础](../../01_foundation/34_pl_prerequisites.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Preludes](../../01_foundation/35_preludes.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 关键字](../../01_foundation/36_keywords.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 运算符与符号](../../01_foundation/37_operators_and_symbols.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Crate 与源文件](../../01_foundation/38_crates_and_source_files.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |

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

> **内容分级**: [元层]
