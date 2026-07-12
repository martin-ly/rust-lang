# 重叠对分类（P1 改写执行清单）

**来源**: `reports/CONTENT_OVERLAP_V2_2026-07-12.json`  **总对数**: 552

| 分类 | 数量 | 处置 |
|---|:---:|:---|
| MERGE | 5 | 应合并近克隆（留一删余或 stub 化） |
| DOCS_INTERNAL | 49 | docs/ 内同主题互抄（合并或互链） |
| SERIES | 24 | 保留但标注为版本系列/分章（白名单） |
| REVIEW | 474 | 人工复核 |

## MERGE（5）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 0.949 | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/01_creational/README.md` | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/03_behavioral/README.md` |
| 0.949 | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/02_structural/README.md` | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/03_behavioral/README.md` |
| 0.949 | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/01_creational/README.md` | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/02_structural/README.md` |
| 0.902 | `concept/04_formal/04_model_checking/07_autoverus.md` | `concept/07_future/03_preview_features/33_autoverus_preview.md` |
| 0.902 | `concept/07_future/03_preview_features/33_autoverus_preview.md` | `concept/04_formal/04_model_checking/07_autoverus.md` |

## DOCS_INTERNAL（49）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 0.821 | `docs/05_practice/06_project_05_text_statistics.md` | `docs/05_practice/14_project_13_database_engine.md` |
| 0.806 | `docs/05_practice/08_project_07_chat_server.md` | `docs/05_practice/12_project_11_web_server.md` |
| 0.793 | `docs/05_practice/06_project_05_text_statistics.md` | `docs/05_practice/13_project_12_wasm_app.md` |
| 0.767 | `docs/05_practice/13_project_12_wasm_app.md` | `docs/05_practice/14_project_13_database_engine.md` |
| 0.75 | `docs/12_research_notes/08_software_design_theory/02_workflow/README.md` | `docs/12_research_notes/08_software_design_theory/07_distributed/README.md` |
| 0.742 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/09_project_08_cache_system.md` |
| 0.742 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/10_project_09_log_parser.md` |
| 0.742 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/11_project_10_data_pipeline.md` |
| 0.742 | `docs/05_practice/09_project_08_cache_system.md` | `docs/05_practice/10_project_09_log_parser.md` |
| 0.742 | `docs/05_practice/09_project_08_cache_system.md` | `docs/05_practice/11_project_10_data_pipeline.md` |
| 0.742 | `docs/05_practice/10_project_09_log_parser.md` | `docs/05_practice/11_project_10_data_pipeline.md` |
| 0.733 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/06_project_05_text_statistics.md` |
| 0.733 | `docs/05_practice/06_project_05_text_statistics.md` | `docs/05_practice/09_project_08_cache_system.md` |
| 0.733 | `docs/05_practice/06_project_05_text_statistics.md` | `docs/05_practice/10_project_09_log_parser.md` |
| 0.733 | `docs/05_practice/06_project_05_text_statistics.md` | `docs/05_practice/11_project_10_data_pipeline.md` |
| 0.719 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/05_project_04_password_generator.md` |
| 0.719 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/07_project_06_concurrent_downloader.md` |
| 0.719 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/08_project_07_chat_server.md` |
| 0.719 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/12_project_11_web_server.md` |
| 0.719 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/15_project_14_async_runtime.md` |
| 0.719 | `docs/05_practice/04_project_03_calculator.md` | `docs/05_practice/16_project_15_distributed_system.md` |
| 0.719 | `docs/05_practice/05_project_04_password_generator.md` | `docs/05_practice/09_project_08_cache_system.md` |
| 0.719 | `docs/05_practice/05_project_04_password_generator.md` | `docs/05_practice/10_project_09_log_parser.md` |
| 0.719 | `docs/05_practice/05_project_04_password_generator.md` | `docs/05_practice/11_project_10_data_pipeline.md` |
| 0.719 | `docs/05_practice/07_project_06_concurrent_downloader.md` | `docs/05_practice/09_project_08_cache_system.md` |

## SERIES（24）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 1.0 | `crates/c02_type_system/readme_rust_189.md` | `crates/c02_type_system/readme_rust_190.md` |
| 1.0 | `crates/c02_type_system/readme_rust_190.md` | `crates/c02_type_system/readme_rust_189.md` |
| 1.0 | `crates/c10_networks/docs/07_rust_190_examples_collection.md` | `crates/c10_networks/docs/08_rust_190_examples_part2.md` |
| 0.889 | `crates/c09_design_pattern/docs/05_c09_comprehensive_enhancement_report_2025_10_19.md` | `crates/c09_design_pattern/docs/15_rust_190_comprehensive_enhancement_report.md` |
| 0.8 | `crates/c09_design_pattern/docs/05_c09_comprehensive_enhancement_report_2025_10_19.md` | `crates/c09_design_pattern/docs/07_enhancement_summary_2025_10_19.md` |
| 0.75 | `crates/c01_ownership_borrow_scope/docs/07_role_based_navigation.md` | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c12_wasm/rust_192_c12_update_summary.md` | `crates/c08_algorithms/rust_192_c08_update_summary.md` |
| 0.667 | `crates/c08_algorithms/rust_192_c08_update_summary.md` | `crates/c12_wasm/rust_192_c12_update_summary.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md` | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md` |
| 0.667 | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.615 | `crates/c01_ownership_borrow_scope/docs/00_master_index.md` | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md` |
| 0.615 | `crates/c09_design_pattern/docs/00_master_index.md` | `crates/c09_design_pattern/docs/05_c09_comprehensive_enhancement_report_2025_10_19.md` |
| 0.615 | `crates/c09_design_pattern/docs/00_master_index.md` | `crates/c09_design_pattern/docs/07_enhancement_summary_2025_10_19.md` |
| 0.571 | `crates/c07_process/docs/14_c07_process_completion_summary_2025_10_19.md` | `crates/c07_process/docs/tier_01_foundations/02_navigation.md` |
| 0.565 | `crates/c06_async/rust_192_c06_update_summary.md` | `crates/c08_algorithms/rust_192_c08_update_summary.md` |
| 0.521 | `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` | `docs/03_reference/quick_reference/19_rust_195_features_cheatsheet.md` |
| 0.521 | `docs/03_reference/quick_reference/19_rust_195_features_cheatsheet.md` | `concept/07_future/00_version_tracking/rust_1_95_stabilized.md` |
| 0.514 | `crates/c11_macro_system_proc/rust_192_c11_update_summary.md` | `crates/c06_async/rust_192_c06_update_summary.md` |
| 0.514 | `crates/c06_async/rust_192_c06_update_summary.md` | `crates/c11_macro_system_proc/rust_192_c11_update_summary.md` |
| 0.507 | `crates/c06_async/rust_192_c06_update_summary.md` | `crates/c12_wasm/rust_192_c12_update_summary.md` |
| 0.5 | `crates/c12_wasm/rust_192_comprehensive_update_report.md` | `crates/c12_wasm/rust_192_update_summary.md` |

## REVIEW（474）Top 25

| sim | 文件1 | 文件2 |
|:---:|:---|:---|
| 0.846 | `crates/c01_ownership_borrow_scope/docs/tier_03_references/03_lifetimes_reference.md` | `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/01_advanced_lifetime_patterns.md` |
| 0.833 | `crates/c08_algorithms/docs/tier_01_foundations/01_project_overview.md` | `crates/c08_algorithms/docs/tier_01_foundations/02_navigation.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md` | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c05_threads/docs/tier_01_foundations/02_navigation.md` | `crates/c05_threads/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c04_generic/docs/00_master_index.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md` | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md` |
| 0.8 | `crates/c03_control_fn/docs/01_concept_relationship_network.md` | `crates/c03_control_fn/docs/05_mind_map.md` |
| 0.794 | `knowledge/04_expert/README.md` | `knowledge/06_ecosystem/README.md` |
| 0.778 | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/mind_map.md` | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md` |
| 0.778 | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/one_page_summary.md` | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md` |
| 0.759 | `knowledge/04_expert/academic/README.md` | `knowledge/04_expert/miri/README.md` |
| 0.759 | `knowledge/04_expert/miri/README.md` | `knowledge/06_ecosystem/deployment/README.md` |
| 0.727 | `crates/c01_ownership_borrow_scope/docs/00_master_index.md` | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md` |
| 0.727 | `crates/c01_ownership_borrow_scope/docs/00_master_index.md` | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md` |
| 0.727 | `crates/c01_ownership_borrow_scope/docs/00_master_index.md` | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md` |

## 机器可读

- JSON: `reports/OVERLAP_TRIAGE_2026-07-12.json`
