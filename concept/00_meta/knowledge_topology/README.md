# 知识体系拓扑图谱集（Knowledge Topology Atlas）

> **EN**: Knowledge Topology Atlas
> **Summary**: Rust 知识体系的全局拓扑视图：概念定义、属性关系、场景决策树、示例反例、逻辑推理、层间/层内映射、权威来源对齐。
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [研究者]
> **内容分级**: [元层]
> **定位**: 本目录是 `concept/` 的元层索引，帮助学习者从多个维度（定义、属性、场景、推理、来源）快速定位和理解 Rust 概念。
>
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/)

---

## 图谱集目录

| 文件 | 主题 | 覆盖范围 |
|:---|:---|:---|
| [01_concept_definition_atlas.md](01_concept_definition_atlas.md) | 概念定义图谱 | 全部 493 个核心概念的中英名称、层级、定义、同义/反义 |
| [02_attribute_relationship_atlas.md](02_attribute_relationship_atlas.md) | 属性关系图谱 | 概念属性矩阵与属性间约束 |
| [03_scenario_decision_tree_atlas.md](03_scenario_decision_tree_atlas.md) | 场景决策树图谱 | 开发场景 → 决策 → Rust 概念/工具（策展决策树 + 数据驱动索引覆盖 284 个概念） |
| [04_example_counterexample_atlas.md](04_example_counterexample_atlas.md) | 示例与反例图谱 | 按概念组织的示例、反例、边界示例（数据驱动索引覆盖 330 个概念） |
| [05_logical_reasoning_atlas.md](05_logical_reasoning_atlas.md) | 逻辑推理图谱 | 定理链、推理规则、形式化对应 |
| [06_inter_layer_mapping_atlas.md](06_inter_layer_mapping_atlas.md) | 层间映射图谱 | L0–L7 依赖、蕴含、反馈关系（前置/后置元数据 + 相关概念节引用，307 个概念有相关链接） |
| [07_intra_layer_mapping_atlas.md](07_intra_layer_mapping_atlas.md) | 层内映射图谱 | 每层内部模型/概念间关系 |
| [08_concept_source_alignment_atlas.md](08_concept_source_alignment_atlas.md) | 概念-权威来源对齐图谱 | 每个核心概念 ↔ 国际化权威来源 |
| [09_reasoning_judgment_tree_atlas.md](09_reasoning_judgment_tree_atlas.md) | 推理判定树图谱 | 编译错误/运行时问题 → 根因 → 修复策略（数据驱动索引覆盖 387 个概念） |
| [10_gap_and_action_plan.md](10_gap_and_action_plan.md) | 缺口与行动计划 | 当前缺口、优先级、修复任务 |

## 深度表征覆盖统计（自动生成）

> 口径：`extract_concept_topology.py` 从 `concept/**/*.md` 抽取的表征信号（章节标题 + compile_fail 块 + mermaid 判定节点 + 定理链元数据）。

| 表征类型 | 覆盖概念数 | 占全部 493 概念 |
|:---|:---:|:---:|
| 示例/反例（04 atlas 索引） | 330 | 66.9% |
| 场景/决策（03 atlas 索引） | 284 | 57.6% |
| 推理/判定（09 atlas 索引） | 387 | 78.5% |
| 相关概念节引用（06 atlas 扩展边源） | 307 | 62.3% |

## 使用建议

1. **快速定位概念**：从 `01_concept_definition_atlas.md` 按层级或字母检索。
2. **理解概念关系**：查看 `06_inter_layer_mapping_atlas.md` 和 `07_intra_layer_mapping_atlas.md`。
3. **解决实际问题**：查看 `03_scenario_decision_tree_atlas.md` 和 `09_reasoning_judgment_tree_atlas.md`。
4. **验证权威来源**：查看 `08_concept_source_alignment_atlas.md`。

## 维护规则

- 本目录文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 生成，**只重生成、不手改**。
- 数据驱动页（01/02/06/07/08/10/README）的人工策展内容已固化进生成器模板与规则。
- 混合生成页（03/04/09）：人工策展头 + `<!-- GENERATED-INDEX -->` 标记处的数据驱动索引节；人工部分的单一事实源是 `scripts/templates/atlas_pages/`，索引节由 `extract_concept_topology.py` 的表征信号驱动。
- 纯人工策展页（05）的单一事实源是 `scripts/templates/atlas_pages/`，生成器原样拷贝；修改请改模板后重跑。
- 当 `concept/` 文件更新后，应先运行 `scripts/extract_concept_topology.py` 刷新 `tmp/concept_topology_raw.json`，再运行本生成脚本并审阅变更。

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)
