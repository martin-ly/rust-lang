# 拓扑图谱实质质量（语义质量门 P0-2/P0-4）

**日期**: 2026-07-12  **扫描**: 13 atlas 文件  **有问题**: 5

| 指标 | 值 | 阈值 | 判定 |
|---|:---:|:---:|:---:|
| T1 定义列套话率 | 7.0% (27/384) | <10% | pass |
| T2 关系最高频占比 | ⟹ 99.2% | <95% | FAIL |
| T3 跳出叶子率 | 16.6% (31/187) | <20% | pass |
| T3 根因死端 | 0 | 0 | pass |
| T4 判定定量占比 | 57.8% (26/45) | >=50% | pass |
| T5 单元格泄漏 | 5 | 0 | FAIL |
| T6 占位字样 | 6 | 0 | FAIL |

## 各文件问题

- `concept/00_meta/knowledge_topology/01_concept_definition_atlas.md`
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

- `数量` → 「数量」
- `13` → 「13」
- `9` → 「9」
- `35` → 「35」
- `81` → 「81」
- `244` → 「244」
- `被引用次数` → 「被引用次数」
- `22` → 「22」
- `16` → 「16」
- `16` → 「16」
- `16` → 「16」
- `14` → 「14」

## WOULD-FAIL（--strict 阻断）

- T2 关系塌缩 ⟹ 99.2% >=95%
- T5 抽取泄漏 5 >0
- T6 占位字样 6 >0

## 机器可读

- JSON: `reports/TOPOLOGY_QUALITY_2026-07-12.json`
