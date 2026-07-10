# 拓扑图谱实质质量（语义质量门 P0-2/P0-4）

**日期**: 2026-07-11  **扫描**: 13 atlas 文件  **有问题**: 5

| 指标 | 值 | 阈值 | 判定 |
|---|:---:|:---:|:---:|
| T1 定义列套话率 | 25.5% (100/392) | <10% | FAIL |
| T2 关系最高频占比 | ⟹ 99.2% | <95% | FAIL |
| T3 跳出叶子率 | 16.6% (31/187) | <20% | pass |
| T3 根因死端 | 0 | 0 | pass |
| T4 判定定量占比 | 57.8% (26/45) | >=50% | pass |
| T5 单元格泄漏 | 5 | 0 | FAIL |
| T6 占位字样 | 6 | 0 | FAIL |

## 各文件问题

- `concept/00_meta/knowledge_topology/01_concept_definition_atlas.md`
  - T1: 定义列套话率 25.5% (100/392)
  - T6: 占位字样 2 处
- `concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md`
  - T5: 单元格泄漏 5 处
  - T6: 占位字样 3 处
- `concept/00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md`
  - T2: 关系塌缩: ⟹ 占 99.2% ({'→': 2, '⟹': 244})
- `concept/00_meta/knowledge_topology/08_concept_source_alignment_atlas.md`
  - T6: 占位字样 1 处
- `concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md`
  - T3: 跳出叶子率 23.5% (20/85)
  - T4: 判定定量占比 23.8% (5/21)

## T1 定义列套话样例

- `[Cross Reference Matrix](../04_navigatio` → 「—」
- `[Concept Audit Guide](../03_audit/concep` → 「Concept Audit Guide. Core Rust concept.」
- `[Rust 知识体系 A/S/P 三维认知标记规范](../03_audit/a` → 「Asp Marking Guide. Core Rust concept.」
- `[概念一致性检查清单](../03_audit/audit_checklist.` → 「Audit Checklist. Core Rust concept.」
- `[权威来源映射表](../02_sources/authority_source` → 「Authority Source Map. Core Rust concept.」
- `[Rust 职业市场全景：2026 年数据与分析](../04_navigati` → 「Career Landscape. Core Rust concept.」
- `[Rust 知识体系双维认知矩阵](../00_framework/cognit` → 「Cognitive Dimension Matrix. Core Rust concept.」
- `[Rust 知识体系能力图谱](../00_framework/competen` → 「Competency Graph. Core Rust concept.」
- `[Comprehensive Rust 课程映射](../00_framewor` → 「Comprehensive Rust Mapping. Core Rust concept.」
- `[概念一致性（Coherence）检查清单](../03_audit/conce` → 「—」
- `[Rust 知识体系学习指南](../04_navigation/learnin` → 「Learning Guide. Core Rust concept.」
- `[MVP 学习路径：从零到多线程 CLI](../04_navigation/l` → 「Learning Mvp Path. Core Rust concept.」

## WOULD-FAIL（--strict 阻断）

- T1 定义套话率 25.5% >=10%
- T2 关系塌缩 ⟹ 99.2% >=95%
- T5 抽取泄漏 5 >0
- T6 占位字样 6 >0

## 机器可读

- JSON: `reports/TOPOLOGY_QUALITY_2026-07-11.json`
