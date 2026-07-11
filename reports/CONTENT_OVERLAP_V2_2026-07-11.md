# 内容重叠检测 v2（语义质量门 P0-3）

**日期**: 2026-07-11  **扫描**: 1901 文件（concept/knowledge/docs/content/crates，排除 archive/book/target）
**纳入索引**: 1412（已剔除真 stub/空关键词）  **候选对(共享>=5词)**: 533367
**阈值**: 0.5  **命中对**: 558（同目录 548 / 跨目录 10）

> 本版修正旧版『0 重复』假象：全文关键词（非前50）、纳入 crates、不豁免假 stub、同目录也检、去掉标题 x1.5 主导。

## Top 60 重复对

| sim | kw | title | 共享词 | 同目录 | 文件1（行） | 文件2（行） |
|:---:|:---:|:---:|:---:|:---:|:---|:---|
| 1.0 | 0.376 | 1.0 | 81 | Y | `crates/c02_type_system/readme_rust_189.md`(489) | `crates/c02_type_system/readme_rust_190.md`(1582) |
| 1.0 | 1.0 | 1.0 | 7 | Y | `crates/c01_ownership_borrow_scope/docs/c01_ownership/quick_reference.md`(24) | `crates/c01_ownership_borrow_scope/docs/tier_03_references/04_drop_and_raii_reference.md`(23) |
| 1.0 | 0.357 | 1.0 | 7 | Y | `crates/c10_networks/docs/rust_190_examples_collection.md`(857) | `crates/c10_networks/docs/rust_190_examples_part2.md`(857) |
| 1.0 | 1.0 | 1.0 | 5 | Y | `crates/c03_control_fn/docs/knowledge_graph.md`(15) | `crates/c03_control_fn/docs/mind_map.md`(15) |
| 1.0 | 1.0 | 1.0 | 5 | Y | `crates/c03_control_fn/docs/knowledge_graph.md`(15) | `crates/c03_control_fn/docs/multidimensional_matrix.md`(15) |
| 1.0 | 1.0 | 1.0 | 5 | Y | `crates/c03_control_fn/docs/mind_map.md`(15) | `crates/c03_control_fn/docs/multidimensional_matrix.md`(15) |
| 0.949 | 0.949 | 0.0 | 17 | Y | `docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/README.md`(140) | `docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/README.md`(145) |
| 0.949 | 0.949 | 0.0 | 17 | Y | `docs/research_notes/software_design_theory/01_design_patterns_formal/01_creational/README.md`(140) | `docs/research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/README.md`(153) |
| 0.949 | 0.949 | 0.0 | 13 | Y | `docs/research_notes/software_design_theory/01_design_patterns_formal/02_structural/README.md`(145) | `docs/research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/README.md`(153) |
| 0.855 | 0.855 | 0.75 | 41 | Y | `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md`(187) | `concept/07_future/03_preview_features/31_safety_tags_preview.md`(166) |
| 0.855 | 0.855 | 0.75 | 9 | Y | `concept/07_future/03_preview_features/31_safety_tags_preview.md`(166) | `concept/04_formal/02_separation_logic/33_safety_tags_in_formal.md`(187) |
| 0.846 | 0.846 | 0.667 | 6 | Y | `crates/c01_ownership_borrow_scope/docs/tier_03_references/03_lifetimes_reference.md`(24) | `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/01_advanced_lifetime_patterns.md`(24) |
| 0.833 | 0.833 | 0.5 | 7 | Y | `crates/c08_algorithms/docs/tier_01_foundations/01_project_overview.md`(15) | `crates/c08_algorithms/docs/tier_01_foundations/02_navigation.md`(15) |
| 0.821 | 0.821 | 0.333 | 9 | Y | `docs/03_practice/03_project_05_text_statistics.md`(108) | `docs/03_practice/03_project_13_database_engine.md`(108) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c07_process/docs/view01.md`(15) | `crates/c07_process/docs/view02.md`(15) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/view01.md`(15) | `crates/c07_process/docs/view04.md`(15) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/view02.md`(15) | `crates/c07_process/docs/view04.md`(15) |
| 0.806 | 0.806 | 0.2 | 11 | Y | `docs/03_practice/03_project_07_chat_server.md`(115) | `docs/03_practice/03_project_11_web_server.md`(113) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/mind_map.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/visualization_index.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/mind_map.md`(15) | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/mind_map.md`(15) | `crates/c01_ownership_borrow_scope/docs/visualization_index.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/mind_map.md`(15) | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md`(15) | `crates/c01_ownership_borrow_scope/docs/visualization_index.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/multidimensional_matrix.md`(15) | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/visualization_index.md`(15) | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.5 | 5 | Y | `crates/c04_generic/docs/00_master_index.md`(15) | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(15) |
| 0.8 | 0.8 | 0.5 | 5 | Y | `crates/c04_generic/docs/00_master_index.md`(15) | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(15) |
| 0.8 | 0.8 | 0.5 | 5 | Y | `crates/c04_generic/docs/00_master_index.md`(15) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.5 | 5 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(15) | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(15) |
| 0.8 | 0.8 | 0.5 | 5 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(15) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.5 | 5 | Y | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(15) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.5 | 5 | Y | `crates/c05_threads/docs/tier_01_foundations/02_navigation.md`(15) | `crates/c05_threads/docs/tier_01_foundations/03_glossary.md`(15) |
| 0.8 | 0.8 | 0.333 | 5 | Y | `crates/c09_design_pattern/docs/c09_comprehensive_enhancement_report_2025_10_19.md`(15) | `crates/c09_design_pattern/docs/enhancement_summary_2025_10_19.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c03_control_fn/docs/concept_relationship_network.md`(15) | `crates/c03_control_fn/docs/knowledge_graph.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c03_control_fn/docs/concept_relationship_network.md`(15) | `crates/c03_control_fn/docs/mind_map.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c03_control_fn/docs/concept_relationship_network.md`(15) | `crates/c03_control_fn/docs/multidimensional_matrix.md`(15) |
| 0.8 | 0.8 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_03_references/05_performance_optimization_reference.md`(15) | `crates/c07_process/docs/tier_03_references/05_performance_optimization_reference.md`(15) |
| 0.794 | 0.794 | 0.5 | 30 | Y | `concept/04_formal/04_model_checking/24_autoverus.md`(196) | `concept/07_future/03_preview_features/33_autoverus_preview.md`(173) |
| 0.794 | 0.794 | 0.0 | 12 | Y | `knowledge/04_expert/README.md`(114) | `knowledge/06_ecosystem/README.md`(140) |
| 0.794 | 0.794 | 0.5 | 8 | Y | `concept/07_future/03_preview_features/33_autoverus_preview.md`(173) | `concept/04_formal/04_model_checking/24_autoverus.md`(196) |
| 0.793 | 0.793 | 0.25 | 9 | Y | `docs/03_practice/03_project_05_text_statistics.md`(108) | `docs/03_practice/03_project_12_wasm_app.md`(113) |
| 0.778 | 0.778 | 0.667 | 5 | Y | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/mind_map.md`(19) | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md`(19) |
| 0.778 | 0.778 | 0.571 | 5 | Y | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/one_page_summary.md`(19) | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md`(19) |
| 0.767 | 0.767 | 0.25 | 9 | Y | `docs/03_practice/03_project_12_wasm_app.md`(113) | `docs/03_practice/03_project_13_database_engine.md`(108) |
| 0.759 | 0.759 | 0.0 | 7 | Y | `knowledge/04_expert/academic/README.md`(79) | `knowledge/04_expert/miri/README.md`(79) |
| 0.759 | 0.759 | 0.0 | 7 | Y | `knowledge/04_expert/miri/README.md`(79) | `knowledge/06_ecosystem/deployment/README.md`(73) |
| 0.75 | 0.75 | 0.0 | 12 | Y | `docs/research_notes/software_design_theory/02_workflow/README.md`(120) | `docs/research_notes/software_design_theory/05_distributed/README.md`(135) |
| 0.75 | 0.75 | 0.25 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/role_based_navigation.md`(15) | `crates/c01_ownership_borrow_scope/docs/rust_190_comprehensive_mindmap.md`(15) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/03_practice/03_project_03_calculator.md`(116) | `docs/03_practice/03_project_08_cache_system.md`(121) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/03_practice/03_project_03_calculator.md`(116) | `docs/03_practice/03_project_09_log_parser.md`(116) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/03_practice/03_project_03_calculator.md`(116) | `docs/03_practice/03_project_10_data_pipeline.md`(120) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/03_practice/03_project_08_cache_system.md`(121) | `docs/03_practice/03_project_09_log_parser.md`(116) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/03_practice/03_project_08_cache_system.md`(121) | `docs/03_practice/03_project_10_data_pipeline.md`(120) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/03_practice/03_project_09_log_parser.md`(116) | `docs/03_practice/03_project_10_data_pipeline.md`(120) |
| 0.733 | 0.733 | 0.333 | 8 | Y | `docs/03_practice/03_project_03_calculator.md`(116) | `docs/03_practice/03_project_05_text_statistics.md`(108) |
| 0.733 | 0.733 | 0.333 | 8 | Y | `docs/03_practice/03_project_05_text_statistics.md`(108) | `docs/03_practice/03_project_08_cache_system.md`(121) |
| 0.733 | 0.733 | 0.333 | 8 | Y | `docs/03_practice/03_project_05_text_statistics.md`(108) | `docs/03_practice/03_project_09_log_parser.md`(116) |

## 机器可读

- JSON: `reports/CONTENT_OVERLAP_V2_2026-07-11.json`
