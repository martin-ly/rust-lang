# 内容重叠检测 v2（语义质量门 P0-3）

**日期**: 2026-07-21  **扫描**: 1841 文件（concept/knowledge/docs/content/crates，排除 archive/book/target）
**纳入索引**: 1432（已剔除真 stub/空关键词）  **候选对(共享>=5词)**: 561015
**阈值**: 0.5  **命中对**: 509（同目录 509 / 跨目录 0）

> 本版修正旧版『0 重复』假象：全文关键词（非前50）、纳入 crates、不豁免假 stub、同目录也检、去掉标题 x1.5 主导。

## Top 60 重复对

| sim | kw | title | 共享词 | 同目录 | 文件1（行） | 文件2（行） |
|:---:|:---:|:---:|:---:|:---:|:---|:---|
| 1.0 | 0.357 | 1.0 | 7 | Y | `crates/c10_networks/docs/07_rust_190_examples_collection.md`(857) | `crates/c10_networks/docs/08_rust_190_examples_part2.md`(857) |
| 0.846 | 0.846 | 0.5 | 8 | Y | `crates/c08_algorithms/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c08_algorithms/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.846 | 0.846 | 0.667 | 6 | Y | `crates/c01_ownership_borrow_scope/docs/tier_03_references/03_lifetimes_reference.md`(24) | `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/01_advanced_lifetime_patterns.md`(24) |
| 0.821 | 0.821 | 0.333 | 8 | Y | `docs/05_practice/14_project_13_database_engine.md`(108) | `docs/05_practice/06_project_05_text_statistics.md`(108) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c05_threads/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c05_threads/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c04_generic/docs/tier_04_rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c05_threads/docs/tier_04_rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c06_async/docs/tier_04_rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c08_algorithms/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c10_networks/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c12_wasm/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c04_generic/docs/tier_04_rust_194_updates/README.md`(22) | `crates/c06_async/docs/tier_04_rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c05_threads/docs/tier_04_rust_194_updates/README.md`(22) | `crates/c06_async/docs/tier_04_rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c05_threads/docs/tier_04_rust_194_updates/README.md`(22) | `crates/c12_wasm/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c08_algorithms/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c10_networks/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c12_wasm/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c10_networks/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c12_wasm/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c11_macro_system_proc/docs/tier_04_rust_194_updates/README.md`(21) | `crates/c12_wasm/docs/tier_04_rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c02_type_system/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.818 | 0.818 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c02_type_system/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c02_type_system/docs/tier_01_foundations/04_faq.md`(22) |
| 0.806 | 0.806 | 0.2 | 10 | Y | `docs/05_practice/12_project_11_web_server.md`(113) | `docs/05_practice/08_project_07_chat_server.md`(115) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md`(15) | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md`(15) | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md`(15) | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md`(15) |
| 0.8 | 0.8 | 0.333 | 5 | Y | `crates/c09_design_pattern/docs/05_c09_comprehensive_enhancement_report_2025_10_19.md`(15) | `crates/c09_design_pattern/docs/07_enhancement_summary_2025_10_19.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c03_control_fn/docs/01_concept_relationship_network.md`(15) | `crates/c03_control_fn/docs/05_mind_map.md`(15) |
| 0.8 | 0.8 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_03_references/06_performance_optimization_reference.md`(15) | `crates/c07_process/docs/tier_03_references/05_performance_optimization_reference.md`(15) |
| 0.793 | 0.793 | 0.25 | 9 | Y | `docs/05_practice/13_project_12_wasm_app.md`(113) | `docs/05_practice/06_project_05_text_statistics.md`(108) |
| 0.778 | 0.778 | 0.667 | 5 | Y | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/mind_map.md`(19) | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md`(19) |
| 0.778 | 0.778 | 0.571 | 5 | Y | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/one_page_summary.md`(19) | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md`(19) |
| 0.767 | 0.767 | 0.25 | 9 | Y | `docs/05_practice/13_project_12_wasm_app.md`(113) | `docs/05_practice/14_project_13_database_engine.md`(108) |
| 0.75 | 0.75 | 0.0 | 11 | Y | `docs/12_research_notes/08_software_design_theory/02_workflow/README.md`(120) | `docs/12_research_notes/08_software_design_theory/07_distributed/README.md`(135) |
| 0.75 | 0.75 | 0.0 | 6 | Y | `crates/c01_ownership_borrow_scope/docs/00_master_index.md`(22) | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.75 | 0.75 | 0.25 | 6 | Y | `crates/c01_ownership_borrow_scope/docs/07_role_based_navigation.md`(15) | `crates/c01_ownership_borrow_scope/docs/08_rust_190_comprehensive_mindmap.md`(15) |
| 0.75 | 0.75 | 0.4 | 6 | Y | `crates/c05_threads/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c05_threads/docs/tier_01_foundations/04_faq.md`(22) |
| 0.75 | 0.75 | 0.4 | 6 | Y | `crates/c05_threads/docs/tier_01_foundations/03_glossary.md`(22) | `crates/c05_threads/docs/tier_01_foundations/04_faq.md`(22) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/05_practice/04_project_03_calculator.md`(116) | `docs/05_practice/09_project_08_cache_system.md`(121) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/05_practice/04_project_03_calculator.md`(116) | `docs/05_practice/10_project_09_log_parser.md`(116) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/05_practice/04_project_03_calculator.md`(116) | `docs/05_practice/11_project_10_data_pipeline.md`(120) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/05_practice/09_project_08_cache_system.md`(121) | `docs/05_practice/10_project_09_log_parser.md`(116) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/05_practice/09_project_08_cache_system.md`(121) | `docs/05_practice/11_project_10_data_pipeline.md`(120) |
| 0.742 | 0.742 | 0.333 | 9 | Y | `docs/05_practice/10_project_09_log_parser.md`(116) | `docs/05_practice/11_project_10_data_pipeline.md`(120) |
| 0.733 | 0.733 | 0.333 | 8 | Y | `docs/05_practice/04_project_03_calculator.md`(116) | `docs/05_practice/06_project_05_text_statistics.md`(108) |
| 0.733 | 0.733 | 0.333 | 8 | Y | `docs/05_practice/06_project_05_text_statistics.md`(108) | `docs/05_practice/09_project_08_cache_system.md`(121) |
| 0.733 | 0.733 | 0.333 | 8 | Y | `docs/05_practice/06_project_05_text_statistics.md`(108) | `docs/05_practice/10_project_09_log_parser.md`(116) |

## 机器可读

- JSON: `reports/CONTENT_OVERLAP_V2_2026-07-21.json`
