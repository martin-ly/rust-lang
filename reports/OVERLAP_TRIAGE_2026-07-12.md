# 重叠对分类（P1 改写执行清单）

**来源**: `reports/CONTENT_OVERLAP_V2_2026-07-12.json`  **总对数**: 559

| 分类 | 数量 | 处置 |
|---|:---:|:---|
| MERGE | 5 | 应合并近克隆（留一删余或 stub 化） |
| DOCS_INTERNAL | 49 | docs/ 内同主题互抄（合并或互链） |
| SERIES | 18 | 保留但标注为版本系列/分章（白名单） |
| REVIEW | 487 | 人工复核 |

## MERGE（5）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 0.949 | `docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/README.md` | `docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/README.md` |
| 0.949 | `docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/README.md` | `docs/research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/README.md` |
| 0.949 | `docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/README.md` | `docs/research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/README.md` |
| 0.855 | `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` | `concept/07_future/03_preview_features/31_safety_tags_preview.md` |
| 0.855 | `concept/07_future/03_preview_features/31_safety_tags_preview.md` | `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md` |

## DOCS_INTERNAL（49）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 0.821 | `docs/03_practice/03_project_05_text_statistics.md` | `docs/03_practice/03_project_13_database_engine.md` |
| 0.806 | `docs/03_practice/03_project_07_chat_server.md` | `docs/03_practice/03_project_11_web_server.md` |
| 0.793 | `docs/03_practice/03_project_05_text_statistics.md` | `docs/03_practice/03_project_12_wasm_app.md` |
| 0.767 | `docs/03_practice/03_project_12_wasm_app.md` | `docs/03_practice/03_project_13_database_engine.md` |
| 0.75 | `docs/research_notes/software_design_theory/02_workflow/README.md` | `docs/research_notes/software_design_theory/05_distributed/README.md` |
| 0.742 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_08_cache_system.md` |
| 0.742 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_09_log_parser.md` |
| 0.742 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_10_data_pipeline.md` |
| 0.742 | `docs/03_practice/03_project_08_cache_system.md` | `docs/03_practice/03_project_09_log_parser.md` |
| 0.742 | `docs/03_practice/03_project_08_cache_system.md` | `docs/03_practice/03_project_10_data_pipeline.md` |
| 0.742 | `docs/03_practice/03_project_09_log_parser.md` | `docs/03_practice/03_project_10_data_pipeline.md` |
| 0.733 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_05_text_statistics.md` |
| 0.733 | `docs/03_practice/03_project_05_text_statistics.md` | `docs/03_practice/03_project_08_cache_system.md` |
| 0.733 | `docs/03_practice/03_project_05_text_statistics.md` | `docs/03_practice/03_project_09_log_parser.md` |
| 0.733 | `docs/03_practice/03_project_05_text_statistics.md` | `docs/03_practice/03_project_10_data_pipeline.md` |
| 0.719 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_04_password_generator.md` |
| 0.719 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_06_concurrent_downloader.md` |
| 0.719 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_07_chat_server.md` |
| 0.719 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_11_web_server.md` |
| 0.719 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_14_async_runtime.md` |
| 0.719 | `docs/03_practice/03_project_03_calculator.md` | `docs/03_practice/03_project_15_distributed_system.md` |
| 0.719 | `docs/03_practice/03_project_04_password_generator.md` | `docs/03_practice/03_project_08_cache_system.md` |
| 0.719 | `docs/03_practice/03_project_04_password_generator.md` | `docs/03_practice/03_project_09_log_parser.md` |
| 0.719 | `docs/03_practice/03_project_04_password_generator.md` | `docs/03_practice/03_project_10_data_pipeline.md` |
| 0.719 | `docs/03_practice/03_project_06_concurrent_downloader.md` | `docs/03_practice/03_project_08_cache_system.md` |

## SERIES（18）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 1.0 | `crates/c02_type_system/readme_rust_189.md` | `crates/c02_type_system/readme_rust_190.md` |
| 1.0 | `crates/c10_networks/docs/rust_190_examples_collection.md` | `crates/c10_networks/docs/rust_190_examples_part2.md` |
| 0.8 | `crates/c09_design_pattern/docs/c09_comprehensive_enhancement_report_2025_10_19.md` | `crates/c09_design_pattern/docs/enhancement_summary_2025_10_19.md` |
| 0.75 | `crates/c01_ownership_borrow_scope/docs/role_based_navigation.md` | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c08_algorithms/rust_192_c08_update_summary.md` | `crates/c12_wasm/rust_192_c12_update_summary.md` |
| 0.667 | `crates/c12_wasm/rust_192_c12_update_summary.md` | `crates/c08_algorithms/rust_192_c08_update_summary.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/mind_map.md` | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md` | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md` | `crates/c01_ownership_borrow_scope/docs/visualization_index.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.615 | `crates/c01_ownership_borrow_scope/docs/00_master_index.md` | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md` |
| 0.615 | `crates/c09_design_pattern/docs/00_master_index.md` | `crates/c09_design_pattern/docs/c09_comprehensive_enhancement_report_2025_10_19.md` |
| 0.615 | `crates/c09_design_pattern/docs/00_master_index.md` | `crates/c09_design_pattern/docs/enhancement_summary_2025_10_19.md` |
| 0.565 | `crates/c06_async/rust_192_c06_update_summary.md` | `crates/c08_algorithms/rust_192_c08_update_summary.md` |
| 0.514 | `crates/c06_async/rust_192_c06_update_summary.md` | `crates/c11_macro_system_proc/rust_192_c11_update_summary.md` |
| 0.507 | `crates/c06_async/rust_192_c06_update_summary.md` | `crates/c12_wasm/rust_192_c12_update_summary.md` |
| 0.5 | `crates/c12_wasm/rust_192_comprehensive_update_report.md` | `crates/c12_wasm/rust_192_update_summary.md` |

## REVIEW（487）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 0.846 | `crates/c01_ownership_borrow_scope/docs/tier_03_references/03_lifetimes_reference.md` | `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/01_advanced_lifetime_patterns.md` |
| 0.833 | `crates/c08_algorithms/docs/tier_01_foundations/01_project_overview.md` | `crates/c08_algorithms/docs/tier_01_foundations/02_navigation.md` |
| 0.818 | `crates/c07_process/docs/view01.md` | `crates/c07_process/docs/view02.md` |
| 0.818 | `crates/c07_process/docs/view01.md` | `crates/c07_process/docs/view04.md` |
| 0.818 | `crates/c07_process/docs/view02.md` | `crates/c07_process/docs/view04.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/mind_map.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/mind_map.md` | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/mind_map.md` | `crates/c01_ownership_borrow_scope/docs/visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/mind_map.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md` | `crates/c01_ownership_borrow_scope/docs/visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/visualization_index.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` |
| 0.8 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` |
| 0.8 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` | `crates/c04_generic/docs/tier_01_foundations/04_faq.md` |

## 机器可读

- JSON: `reports/OVERLAP_TRIAGE_2026-07-12.json`
