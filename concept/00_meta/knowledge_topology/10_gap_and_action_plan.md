# 缺口与行动计划（Gap and Action Plan）

> **EN**: Gap and Action Plan
> **Summary**: 基于拓扑抽取结果识别的当前缺口：来源覆盖、表征完整性、层间/层内映射、定义一致性。 Current gaps identified from topology extraction: source coverage, representation completeness, inter/intra-layer mappings, and definition consistency.
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、当前缺口概览

| 缺口类型 | 数量 | 说明 |
|:---|:---:|:---|
| 无权威来源标注 | 0 | 概念文件未引用任何外部权威来源 |
| 来源标注薄弱（≤2） | 0 | 概念文件仅引用 1–2 个来源 |
| 无定理链 | 148 | 概念文件缺少定理链 |
| 无 A/S/P 标记 | 188 | 概念文件缺少 A/S/P 维度标记 |
| 无知识表征章节 | 254 | 概念文件无决策树/矩阵/示例等表征 |

## 二、优先修复任务

### P0：补全权威来源（L1–L4 核心概念）

| 概念 | 层级 | 当前来源数 | 建议行动 |
|:---|:---:|:---:|:---|

### P1：增强知识表征

| 概念 | 层级 | 缺失表征 | 建议行动 |
|:---|:---:|:---|:---|
| [Rust 起步指南](../../01_foundation/00_start/00_start.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/03_values_and_references/05_reference_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/06_zero_cost_abstractions.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [控制流：表达式导向的流程控制](../../01_foundation/04_control_flow/07_control_flow.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/08_collections.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [字符串与文本：Rust 的 Unicode 处理与格式化系统](../../01_foundation/06_strings_and_text/09_strings_and_text.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/02_type_system/10_numerics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/11_modules_and_paths.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [属性与声明宏：编译期元编程基础](../../01_foundation/09_macros_basics/12_attributes_and_macros.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Panic 与 Abort：不可恢复错误的处理机制](../../01_foundation/08_error_handling/13_panic_and_abort.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [类型强制与转换：显式与隐式的边界](../../01_foundation/02_type_system/14_coercion_and_casting.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/15_closure_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测试基础：从单元测试到集成测试](../../01_foundation/10_testing_basics/16_testing_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [字符串与编码：Rust 的文本处理类型系统](../../01_foundation/06_strings_and_text/18_strings_and_encoding.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/03_values_and_references/19_value_vs_reference_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：类型系统](../../01_foundation/11_quizzes/24_quiz_type_system.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：错误处理](../../01_foundation/11_quizzes/25_quiz_error_handling.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：模块系统与测试](../../01_foundation/11_quizzes/26_quiz_modules_testing.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：闭包与迭代器](../../01_foundation/11_quizzes/27_quiz_closures_iterators.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [所有权清单自测：Brown University Ownership Inventory](../../01_foundation/01_ownership_borrow_lifetime/28_ownership_inventories_brown_book.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：通用 PL 基座](../../01_foundation/11_quizzes/29_quiz_pl_foundations.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Never Type (`!`)：底类型与穷尽性](../../01_foundation/02_type_system/31_never_type.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 错误处理基础](../../01_foundation/08_error_handling/32_error_handling_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [测验：所有权、借用与生命周期](../../01_foundation/11_quizzes/33_quiz_ownership_borrowing.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [编程语言理论基础](../../01_foundation/00_start/34_pl_prerequisites.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Preludes](../../01_foundation/07_modules_and_items/35_preludes.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 关键字](../../01_foundation/00_start/36_keywords.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 运算符与符号](../../01_foundation/00_start/37_operators_and_symbols.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Crate 与源文件](../../01_foundation/07_modules_and_items/38_crates_and_source_files.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |

### P2：对齐国际标准

针对以下主题补充 Unicode / ISO / IEEE / IETF / ABI 标准引用：

- 字符串与编码：`concept/01_foundation/06_strings_and_text/18_strings_and_encoding.md` → Unicode Standard
- 内联汇编：`concept/03_advanced/05_inline_assembly/13_inline_assembly.md` → Intel/ARM 架构手册
- 网络编程：`concept/03_advanced/06_low_level_patterns/18_network_programming.md` → IETF RFCs
- ABI：`concept/04_formal/38_application_binary_interface.md` → Itanium C++ ABI / System V AMD64 ABI
- 交叉编译/嵌入式：`concept/06_ecosystem/17_cross_compilation.md` / `22_embedded_systems.md` → 目标平台规范

## 三、自动化建议

1. 在 `kb_auditor.py` 中增加：概念文件必须引用至少一个 L1 来源。
2. 每月运行 `extract_concept_topology.py` + `generate_knowledge_topology_atlas.py` 生成图谱集。
3. 对新增文件自动检测是否包含决策树/矩阵/示例反例中的一种表征。

---

> **内容分级**: [元层]
