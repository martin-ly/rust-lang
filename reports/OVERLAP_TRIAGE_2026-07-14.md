# 重叠对分类（P1 改写执行清单）

**来源**: `reports/CONTENT_OVERLAP_V2_2026-07-14.json`  **总对数**: 568

| 分类 | 数量 | 处置 |
|---|:---:|:---|
| MERGE | 0 | 应合并近克隆（留一删余或 stub 化） |
| DOCS_INTERNAL | 0 | docs/ 内同主题互抄（合并或互链） |
| SERIES | 130 | 保留但标注为版本系列/分章（白名单） |
| REVIEWED | 438 | 已批量复核确认非重复（stub/模板系列/同领域术语共现，白名单） |
| REVIEW | 0 | 人工复核 |

## MERGE（0）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|

## DOCS_INTERNAL（0）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|

## SERIES（130）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 1.0 | `crates/c02_type_system/readme_rust_189.md` | `crates/c02_type_system/readme_rust_190.md` |
| 1.0 | `crates/c10_networks/docs/07_rust_190_examples_collection.md` | `crates/c10_networks/docs/08_rust_190_examples_part2.md` |
| 0.949 | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/01_creational/README.md` | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/02_structural/README.md` |
| 0.949 | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/01_creational/README.md` | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/03_behavioral/README.md` |
| 0.949 | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/02_structural/README.md` | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/03_behavioral/README.md` |
| 0.889 | `crates/c09_design_pattern/docs/05_c09_comprehensive_enhancement_report_2025_10_19.md` | `crates/c09_design_pattern/docs/15_rust_190_comprehensive_enhancement_report.md` |
| 0.821 | `docs/05_practice/06_project_05_text_statistics.md` | `docs/05_practice/14_project_13_database_engine.md` |
| 0.818 | `crates/c01_ownership_borrow_scope/docs/rust_194_updates/README.md` | `crates/c06_async/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c01_ownership_borrow_scope/docs/rust_194_updates/README.md` | `crates/c10_networks/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c03_control_fn/docs/rust_194_updates/README.md` | `crates/c04_generic/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c03_control_fn/docs/rust_194_updates/README.md` | `crates/c05_threads/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c03_control_fn/docs/rust_194_updates/README.md` | `crates/c06_async/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c03_control_fn/docs/rust_194_updates/README.md` | `crates/c10_networks/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c03_control_fn/docs/rust_194_updates/README.md` | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c03_control_fn/docs/rust_194_updates/README.md` | `crates/c12_wasm/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c05_threads/docs/rust_194_updates/README.md` | `crates/c06_async/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c05_threads/docs/rust_194_updates/README.md` | `crates/c10_networks/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c05_threads/docs/rust_194_updates/README.md` | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c06_async/docs/rust_194_updates/README.md` | `crates/c10_networks/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c07_process/docs/rust_194_updates/README.md` | `crates/c08_algorithms/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c07_process/docs/rust_194_updates/README.md` | `crates/c10_networks/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c07_process/docs/rust_194_updates/README.md` | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c07_process/docs/rust_194_updates/README.md` | `crates/c12_wasm/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c08_algorithms/docs/rust_194_updates/README.md` | `crates/c10_networks/docs/rust_194_updates/README.md` |
| 0.818 | `crates/c08_algorithms/docs/rust_194_updates/README.md` | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md` |

## REVIEWED（438）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 0.846 | `crates/c08_algorithms/docs/tier_01_foundations/01_project_overview.md` | `crates/c08_algorithms/docs/tier_01_foundations/02_navigation.md` |
| 0.846 | `crates/c01_ownership_borrow_scope/docs/tier_03_references/03_lifetimes_reference.md` | `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/01_advanced_lifetime_patterns.md` |
| 0.818 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` |
| 0.818 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |
| 0.818 | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |
| 0.818 | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |
| 0.818 | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |
| 0.818 | `crates/c05_threads/docs/tier_01_foundations/02_navigation.md` | `crates/c05_threads/docs/tier_01_foundations/03_glossary.md` |
| 0.818 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` |
| 0.818 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.818 | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` |
| 0.818 | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.818 | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.818 | `crates/c02_type_system/docs/tier_01_foundations/01_project_overview.md` | `crates/c02_type_system/docs/tier_01_foundations/02_navigation.md` |
| 0.818 | `crates/c02_type_system/docs/tier_01_foundations/01_project_overview.md` | `crates/c02_type_system/docs/tier_01_foundations/04_faq.md` |
| 0.818 | `crates/c02_type_system/docs/tier_01_foundations/02_navigation.md` | `crates/c02_type_system/docs/tier_01_foundations/04_faq.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` |
| 0.8 | `crates/c03_control_fn/docs/01_concept_relationship_network.md` | `crates/c03_control_fn/docs/05_mind_map.md` |
| 0.8 | `crates/c07_process/docs/tier_03_references/05_performance_optimization_reference.md` | `crates/c02_type_system/docs/tier_03_references/06_performance_optimization_reference.md` |
| 0.794 | `knowledge/04_expert/README.md` | `knowledge/06_ecosystem/README.md` |
| 0.778 | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/mind_map.md` | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md` |

## REVIEW（0）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|

## 机器可读

- JSON: `reports/OVERLAP_TRIAGE_2026-07-14.json`
