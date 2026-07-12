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
| 无权威来源标注 | 0 | 概念文件未引用任何外部权威来源 |
| 来源标注薄弱（≤2） | 2 | 概念文件仅引用 1–2 个来源 |
| 无定理链 | 201 | 概念文件缺少定理链 |
| 无 A/S/P 标记 | 239 | 概念文件缺少 A/S/P 维度标记 |
| 无知识表征章节 | 289 | 概念文件无决策树/矩阵/示例等表征 |

## 二、优先修复任务

本节围绕「优先修复任务」展开，依次讨论 P0：补全权威来源（L1–L4 核心概念）、P1：增强知识表征与P2：对齐国际标准。

### P0：补全权威来源（L1–L4 核心概念）

| 概念 | 层级 | 当前来源数 | 建议行动 |
|:---|:---:|:---:|:---|
| [生命周期高级主题：从 HRTB 到自引用类型](../../01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | L2 进阶概念层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |
| [Safety Tags（安全标签）预览](../../07_future/03_preview_features/03_safety_tags_preview.md) | L7 前沿趋势层 | 1 | 补充 Rust Reference / TRPL / 学术来源 |

### P1：增强知识表征

| 概念 | 层级 | 缺失表征 | 建议行动 |
|:---|:---:|:---|:---|
| [零成本抽象：Rust 的性能哲学](../../01_foundation/00_start/02_zero_cost_abstractions.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [闭包基础：捕获环境与匿名函数](../../01_foundation/00_start/03_closure_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [编程语言理论基础](../../01_foundation/00_start/01_pl_prerequisites.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 关键字](../../01_foundation/00_start/06_keywords.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 运算符与符号](../../01_foundation/00_start/07_operators_and_symbols.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 所有权-借用-生命周期知识图谱](../../01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Move 语义：C++ 与 Rust 的资源转移模型](../../01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [所有权清单自测：Brown University Ownership Inventory](../../01_foundation/01_ownership_borrow_lifetime/06_ownership_inventories_brown_book.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [数值类型与运算：从整数到浮点的完整图景](../../01_foundation/02_type_system/03_numerics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [类型强制与转换：显式与隐式的边界](../../01_foundation/02_type_system/04_coercion_and_casting.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Never Type (`!`)：底类型与穷尽性](../../01_foundation/02_type_system/02_never_type.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [引用语义：自动解引用、Deref 强制与类型转换](../../01_foundation/03_values_and_references/01_reference_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [值语义 vs 引用语义：从 C++、Java、Python 到 Rust](../../01_foundation/03_values_and_references/02_value_vs_reference_semantics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [控制流：表达式导向的流程控制](../../01_foundation/04_control_flow/01_control_flow.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [模式匹配](../../01_foundation/04_control_flow/02_patterns.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [语句与表达式](../../01_foundation/04_control_flow/03_statements_and_expressions.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [集合类型：Rust 标准库的数据结构谱系](../../01_foundation/05_collections/01_collections.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [字符串与文本：Rust 的 Unicode 处理与格式化系统](../../01_foundation/06_strings_and_text/01_strings_and_text.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [字符串与编码：Rust 的文本处理类型系统](../../01_foundation/06_strings_and_text/02_strings_and_encoding.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [模块系统与路径：Rust 的代码组织哲学](../../01_foundation/07_modules_and_items/01_modules_and_paths.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Functions](../../01_foundation/07_modules_and_items/02_functions.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Use Declarations](../../01_foundation/07_modules_and_items/03_use_declarations.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Structs](../../01_foundation/07_modules_and_items/04_structs.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Enumerations](../../01_foundation/07_modules_and_items/05_enumerations.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Implementations](../../01_foundation/07_modules_and_items/06_implementations.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Preludes](../../01_foundation/07_modules_and_items/10_preludes.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Panic 与 Abort：不可恢复错误的处理机制](../../01_foundation/08_error_handling/03_panic_and_abort.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 错误处理基础](../../01_foundation/08_error_handling/01_error_handling_basics.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [错误处理控制流](../../01_foundation/08_error_handling/02_error_handling_control_flow.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [属性与声明宏：编译期元编程基础](../../01_foundation/09_macros_basics/01_attributes_and_macros.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |

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
