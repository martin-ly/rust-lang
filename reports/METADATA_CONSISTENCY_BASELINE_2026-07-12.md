# 元数据一致性基线（语义质量门 P0-1）

**日期**: 2026-07-12  **扫描**: 480 concept 活跃文件（排除 archive）  **模式**: warning（不阻断）

| 规则 | 命中文件 | 占比 | 阈值 | 判定 |
|---|:---:|:---:|:---:|:---:|
| D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥 | 0 | 0.0% | >0 | pass |
| D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7） | 98 (基=297) | 20.4% | >=5% | FAIL |
| D3 关键字段同文件重声明 | 0 | 0.0% | >0 | pass |
| D4 文首块 Rust 版本号自矛盾 | 1 | 0.2% | >0 | FAIL |
| D5 稳定层正文残留 nightly/preview/unstable | 112 | 23.3% | >0 | FAIL |
| D6 Summary 低信息量模板套话 | 11 | 2.3% | >=3% | pass |

**受影响文件总数**: 190 / 480

## 各类 Top 样例

### D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥（0）

### D2 A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7）（98）

- `concept/00_meta/04_navigation/foundations_gap_closure_index.md` — A/S/P=S 允许 [2, 3, 4] 与 Bloom [0] 无交集
- `concept/01_foundation/05_collections/08_collections.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/01_foundation/06_strings_and_text/09_strings_and_text.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/01_foundation/10_testing_basics/16_testing_basics.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/01_foundation/10_testing_basics/42_useful_development_tools.md` — A/S/P=P 允许 [4, 5, 6, 7] 与 Bloom [1, 2] 无交集
- `concept/02_intermediate/00_traits/09_serde_patterns.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/02_intermediate/06_macros_and_metaprogramming/05_assert_matches.md` — A/S/P=A 允许 [1, 2] 与 Bloom [3, 4] 无交集
- `concept/03_advanced/02_process_ipc/02_advanced_process_management.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集
- `concept/03_advanced/02_process_ipc/03_async_process_management.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集
- `concept/03_advanced/02_process_ipc/06_process_monitoring_and_diagnostics.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集
- `concept/03_advanced/02_process_ipc/07_process_security_and_sandboxing.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集
- `concept/03_advanced/02_process_ipc/08_process_performance_engineering.md` — A/S/P=A 允许 [1, 2] 与 Bloom [4, 5] 无交集

### D3 关键字段同文件重声明（0）

### D4 文首块 Rust 版本号自矛盾（1）

- `concept/02_intermediate/00_traits/40_generic_associated_types.md` — 版本字段 distinct minor [65, 97]: 1.97.0+ (Edition 2024) · GATs MVP 自 **1.65** (2022-11) 稳定

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

### D6 Summary 低信息量模板套话（11）

- `concept/SUMMARY.md` — Summary 为空
- `concept/00_meta/02_sources/authority_source_map.md` — 套话: Authority Source Map. Core Rust concept.
- `concept/00_meta/03_audit/concept_audit_guide.md` — 套话: Concept Audit Guide. Core Rust concept.
- `concept/02_intermediate/00_traits/18_lifetimes_advanced.md` — Summary 为空
- `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` — Summary 为空
- `concept/06_ecosystem/01_cargo/59_cargo_build_scripts.md` — 套话: A comprehensive guide to `build.rs`: when it runs, how to pa
- `concept/06_ecosystem/01_cargo/87_build_std.md` — 套话: A comprehensive guide to Cargo's unstable `build-std` featur
- `concept/06_ecosystem/09_testing_and_quality/17_benchmarking.md` — 套话: Core Rust concept covering statistical benchmarking with Cri
- `concept/07_future/00_version_tracking/migration_197_decision_tree.md` — Summary 为空
- `concept/07_future/03_preview_features/31_safety_tags_preview.md` — Summary 为空
- `concept/07_future/04_research_and_experimental/02_formal_methods.md` — 套话: Formal Methods. Core Rust concept covering practical example

## WOULD-FAIL（接入 CI strict 时将阻断）

- D2 A/S/P脱节 98/297 (>=5%)
- D4 版本自矛盾 1 (>0)
- D5 稳定层nightly残留 112 (>0)

## 机器可读

- JSON: `reports/METADATA_CONSISTENCY_BASELINE_2026-07-12.json`
