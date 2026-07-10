# 元数据一致性基线（语义质量门 P0-1）

**日期**: 2026-07-11  **扫描**: 474 concept 活跃文件（排除 archive）  **模式**: warning（不阻断）

| 规则 | 命中文件 | 占比 | 阈值 | 判定 |
|---|:---:|:---:|:---:|:---:|
| D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥 | 64 | 13.5% | >0 | FAIL |
| D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7） | 103 (基=296) | 21.7% | >=5% | FAIL |
| D3 关键字段同文件重声明 | 88 | 18.6% | >0 | FAIL |
| D4 文首块 Rust 版本号自矛盾 | 1 | 0.2% | >0 | FAIL |
| D5 稳定层正文残留 nightly/preview/unstable | 112 | 23.6% | >0 | FAIL |
| D6 Summary 低信息量模板套话 | 108 | 22.8% | >=3% | FAIL |

**受影响文件总数**: 302 / 474

## 各类 Top 样例

### D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥（64）

- `concept/00_meta/00_framework/methodology.md` — Bloom [2, 3] 与 层次定位/层级 [1] 无交集
- `concept/00_meta/00_framework/pl_foundations_roadmap.md` — Bloom [2, 3, 4] 与 层次定位/层级 [1] 无交集
- `concept/00_meta/00_framework/semantic_bridge_algorithms_patterns.md` — Bloom [4, 5, 6] 与 层次定位/层级 [0] 无交集
- `concept/00_meta/01_terminology/bilingual_template_v2.md` — Bloom [1, 2, 3, 4, 5, 6] 与 层次定位/层级 [0] 无交集
- `concept/00_meta/04_navigation/foundations_gap_closure_index.md` — Bloom [5] 与 层次定位/层级 [0] 无交集
- `concept/01_foundation/00_start/21_effects_and_purity.md` — Bloom [2, 3, 4, 5] 与 层次定位/层级 [1] 无交集
- `concept/01_foundation/00_start/47_std_io_and_process.md` — Bloom [2, 3] 与 层次定位/层级 [1] 无交集
- `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` — Bloom [2, 3, 4] 与 层次定位/层级 [1] 无交集
- `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` — Bloom [2, 3, 4, 5] 与 层次定位/层级 [1] 无交集
- `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` — Bloom [2, 3, 4, 5] 与 层次定位/层级 [1] 无交集
- `concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md` — Bloom [2, 3, 4] 与 层次定位/层级 [1] 无交集
- `concept/01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md` — Bloom 多区间冲突: ['L4-L5', 'L2-L4', 'L4-L5']

### D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7）（103）

- `concept/00_meta/04_navigation/foundations_gap_closure_index.md` — A/S/P=S 允许 [2, 3, 4] 与 Bloom [5] 无交集
- `concept/01_foundation/05_collections/08_collections.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/01_foundation/06_strings_and_text/09_strings_and_text.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/01_foundation/10_testing_basics/16_testing_basics.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/01_foundation/10_testing_basics/42_useful_development_tools.md` — A/S/P=P 允许 [4, 5, 6, 7] 与 Bloom [1, 2] 无交集
- `concept/02_intermediate/00_traits/09_serde_patterns.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/02_intermediate/01_generics/02_generics.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4, 5] 无交集
- `concept/02_intermediate/03_error_handling/04_error_handling.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/02_intermediate/03_error_handling/27_exception_safety_rust_cpp.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集
- `concept/02_intermediate/06_macros_and_metaprogramming/05_assert_matches.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/03_advanced/02_process_ipc/02_advanced_process_management.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集
- `concept/03_advanced/02_process_ipc/03_async_process_management.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集

### D3 关键字段同文件重声明（88）

- `concept/00_meta/03_audit/asp_marking_guide.md` — Bloom 层级 声明 2 次: ['Meta', 'L2-L6']
- `concept/00_meta/03_audit/grading_system.md` — 内容分级 声明 2 次: ['[综述级]', '[实验级]']
- `concept/00_meta/knowledge_topology/01_concept_definition_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/03_scenario_decision_tree_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/04_example_counterexample_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/05_logical_reasoning_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/06_inter_layer_mapping_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/08_concept_source_alignment_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']
- `concept/00_meta/knowledge_topology/10_gap_and_action_plan.md` — 内容分级 声明 2 次: ['[元层]', '[元层]']

### D4 文首块 Rust 版本号自矛盾（1）

- `concept/01_foundation/05_collections/08_collections.md` — 版本字段 distinct minor [85, 97]: 1.97.0+ (Edition 2024) 1.85.0+ Stable · [来源: [Rust 1.85.0 Release Notes](https:/

### D5 稳定层正文残留 nightly/preview/unstable（112）

- `concept/SUMMARY.md` — 稳定层 nightly/preview 关键词 11 处
- `concept/00_meta/00_framework/cognitive_dimension_matrix.md` — 稳定层 nightly/preview 关键词 2 处
- `concept/00_meta/00_framework/expressiveness_multiview.md` — 稳定层 nightly/preview 关键词 2 处
- `concept/00_meta/00_framework/semantic_expressiveness.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/00_meta/00_framework/semantic_space.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/00_meta/00_framework/todos.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/00_meta/01_terminology/terminology_glossary.md` — 稳定层 nightly/preview 关键词 18 处
- `concept/00_meta/02_sources/sources.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/00_meta/02_sources/topic_authority_alignment_map.md` — 稳定层 nightly/preview 关键词 4 处
- `concept/00_meta/03_audit/asp_marking_guide.md` — 稳定层 nightly/preview 关键词 1 处
- `concept/00_meta/03_audit/grading_system.md` — 稳定层 nightly/preview 关键词 8 处
- `concept/00_meta/04_navigation/quick_reference.md` — 稳定层 nightly/preview 关键词 2 处

### D6 Summary 低信息量模板套话（108）

- `concept/SUMMARY.md` — Summary 为空
- `concept/00_meta/00_framework/cognitive_dimension_matrix.md` — 套话: Cognitive Dimension Matrix. Core Rust concept.
- `concept/00_meta/00_framework/competency_graph.md` — 套话: Competency Graph. Core Rust concept.
- `concept/00_meta/00_framework/comprehensive_rust_mapping.md` — 套话: Comprehensive Rust Mapping. Core Rust concept.
- `concept/00_meta/00_framework/concept_definition_decision_forest.md` — 套话: Concept Definition Decision Forest. Core Rust concept.
- `concept/00_meta/00_framework/decidability_spectrum.md` — 套话: Decidability Spectrum. Core Rust concept.
- `concept/00_meta/00_framework/expressiveness_multiview.md` — 套话: Expressiveness Multiview. Core Rust concept.
- `concept/00_meta/00_framework/fault_tree_analysis_collection.md` — 套话: Fault Tree Analysis Collection. Core Rust concept.
- `concept/00_meta/00_framework/knowledge_mindmap.md` — 套话: Knowledge Mindmap. Core Rust concept.
- `concept/00_meta/00_framework/paradigm_transition_matrix.md` — 套话: Paradigm Transition Matrix. Core Rust concept.
- `concept/00_meta/00_framework/semantic_space.md` — 套话: Semantic Space. Core Rust concept.
- `concept/00_meta/00_framework/theorem_inference_forest.md` — 套话: Theorem Inference Forest. Core Rust concept.

## WOULD-FAIL（接入 CI strict 时将阻断）

- D1 Bloom互斥 64 (>0)
- D2 A/S/P脱节 103/296 (>=5%)
- D3 字段重声明 88 (>0)
- D4 版本自矛盾 1 (>0)
- D5 稳定层nightly残留 112 (>0)
- D6 Summary套话 108 (22.8%>=3%)

## 机器可读

- JSON: `reports/METADATA_CONSISTENCY_BASELINE_2026-07-11.json`
