# 内容重叠检测 v2（语义质量门 P0-3）

**日期**: 2026-07-14  **扫描**: 1948 文件（concept/knowledge/docs/content/crates，排除 archive/book/target）
**纳入索引**: 1453（已剔除真 stub/空关键词）  **候选对(共享>=5词)**: 582465
**阈值**: 0.5  **命中对**: 568（同目录 558 / 跨目录 10）

> 本版修正旧版『0 重复』假象：全文关键词（非前50）、纳入 crates、不豁免假 stub、同目录也检、去掉标题 x1.5 主导。

## Top 60 重复对

| sim | kw | title | 共享词 | 同目录 | 文件1（行） | 文件2（行） |
|:---:|:---:|:---:|:---:|:---:|:---|:---|
| 1.0 | 0.376 | 1.0 | 79 | Y | `crates/c02_type_system/readme_rust_189.md`(489) | `crates/c02_type_system/readme_rust_190.md`(1582) |
| 1.0 | 0.357 | 1.0 | 7 | Y | `crates/c10_networks/docs/07_rust_190_examples_collection.md`(857) | `crates/c10_networks/docs/08_rust_190_examples_part2.md`(857) |
| 0.949 | 0.949 | 0.0 | 16 | Y | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/01_creational/README.md`(140) | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/02_structural/README.md`(145) |
| 0.949 | 0.949 | 0.0 | 16 | Y | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/01_creational/README.md`(140) | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/03_behavioral/README.md`(153) |
| 0.949 | 0.949 | 0.0 | 12 | Y | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/02_structural/README.md`(145) | `docs/12_research_notes/08_software_design_theory/01_design_patterns_formal/03_behavioral/README.md`(153) |
| 0.889 | 0.889 | 0.5 | 5 | Y | `crates/c09_design_pattern/docs/05_c09_comprehensive_enhancement_report_2025_10_19.md`(15) | `crates/c09_design_pattern/docs/15_rust_190_comprehensive_enhancement_report.md`(15) |
| 0.846 | 0.846 | 0.5 | 8 | Y | `crates/c08_algorithms/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c08_algorithms/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.846 | 0.846 | 0.667 | 6 | Y | `crates/c01_ownership_borrow_scope/docs/tier_03_references/03_lifetimes_reference.md`(24) | `crates/c01_ownership_borrow_scope/docs/tier_04_advanced/01_advanced_lifetime_patterns.md`(24) |
| 0.821 | 0.821 | 0.333 | 9 | Y | `docs/05_practice/06_project_05_text_statistics.md`(108) | `docs/05_practice/14_project_13_database_engine.md`(108) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c05_threads/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c05_threads/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 6 | Y | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) | `crates/c04_generic/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/rust_194_updates/README.md`(22) | `crates/c06_async/docs/rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/rust_194_updates/README.md`(22) | `crates/c10_networks/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/rust_194_updates/README.md`(21) | `crates/c04_generic/docs/rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/rust_194_updates/README.md`(21) | `crates/c05_threads/docs/rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/rust_194_updates/README.md`(21) | `crates/c06_async/docs/rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/rust_194_updates/README.md`(21) | `crates/c10_networks/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/rust_194_updates/README.md`(21) | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c03_control_fn/docs/rust_194_updates/README.md`(21) | `crates/c12_wasm/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c05_threads/docs/rust_194_updates/README.md`(22) | `crates/c06_async/docs/rust_194_updates/README.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c05_threads/docs/rust_194_updates/README.md`(22) | `crates/c10_networks/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c05_threads/docs/rust_194_updates/README.md`(22) | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c06_async/docs/rust_194_updates/README.md`(22) | `crates/c10_networks/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/rust_194_updates/README.md`(21) | `crates/c08_algorithms/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/rust_194_updates/README.md`(21) | `crates/c10_networks/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/rust_194_updates/README.md`(21) | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c07_process/docs/rust_194_updates/README.md`(21) | `crates/c12_wasm/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c08_algorithms/docs/rust_194_updates/README.md`(21) | `crates/c10_networks/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c08_algorithms/docs/rust_194_updates/README.md`(21) | `crates/c11_macro_system_proc/docs/rust_194_updates/README.md`(21) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c04_generic/docs/00_master_index.md`(22) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c04_generic/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.5 | 5 | Y | `crates/c04_generic/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c04_generic/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.818 | 0.818 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c02_type_system/docs/tier_01_foundations/02_navigation.md`(22) |
| 0.818 | 0.818 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_01_foundations/01_project_overview.md`(22) | `crates/c02_type_system/docs/tier_01_foundations/04_faq.md`(22) |
| 0.818 | 0.818 | 0.333 | 5 | Y | `crates/c02_type_system/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c02_type_system/docs/tier_01_foundations/04_faq.md`(22) |
| 0.806 | 0.806 | 0.2 | 11 | Y | `docs/05_practice/08_project_07_chat_server.md`(115) | `docs/05_practice/12_project_11_web_server.md`(113) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/01_concept_relationship_network.md`(15) | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md`(15) | `crates/c01_ownership_borrow_scope/docs/04_multidimensional_matrix.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c01_ownership_borrow_scope/docs/03_mind_map.md`(15) | `crates/c01_ownership_borrow_scope/docs/15_visualization_index.md`(15) |
| 0.8 | 0.8 | 0.0 | 5 | Y | `crates/c03_control_fn/docs/01_concept_relationship_network.md`(15) | `crates/c03_control_fn/docs/05_mind_map.md`(15) |
| 0.8 | 0.8 | 0.333 | 5 | Y | `crates/c07_process/docs/tier_03_references/05_performance_optimization_reference.md`(15) | `crates/c02_type_system/docs/tier_03_references/06_performance_optimization_reference.md`(15) |
| 0.794 | 0.794 | 0.0 | 12 | Y | `knowledge/04_expert/README.md`(114) | `knowledge/06_ecosystem/README.md`(140) |
| 0.793 | 0.793 | 0.25 | 8 | Y | `docs/05_practice/06_project_05_text_statistics.md`(108) | `docs/05_practice/13_project_12_wasm_app.md`(113) |
| 0.778 | 0.778 | 0.667 | 5 | Y | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/mind_map.md`(19) | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md`(19) |
| 0.778 | 0.778 | 0.571 | 5 | Y | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/one_page_summary.md`(19) | `crates/c11_macro_system_proc/c11_macro_system_proc_macros/docs/README.md`(19) |
| 0.767 | 0.767 | 0.25 | 9 | Y | `docs/05_practice/13_project_12_wasm_app.md`(113) | `docs/05_practice/14_project_13_database_engine.md`(108) |
| 0.759 | 0.759 | 0.0 | 7 | Y | `knowledge/04_expert/academic/README.md`(79) | `knowledge/04_expert/miri/README.md`(79) |
| 0.759 | 0.759 | 0.0 | 7 | Y | `knowledge/04_expert/miri/README.md`(79) | `knowledge/06_ecosystem/deployment/README.md`(73) |
| 0.75 | 0.75 | 0.0 | 11 | Y | `docs/12_research_notes/08_software_design_theory/02_workflow/README.md`(120) | `docs/12_research_notes/08_software_design_theory/07_distributed/README.md`(135) |
| 0.75 | 0.75 | 0.0 | 6 | Y | `crates/c01_ownership_borrow_scope/docs/00_master_index.md`(22) | `crates/c01_ownership_borrow_scope/docs/tier_01_foundations/03_glossary.md`(22) |
| 0.75 | 0.75 | 0.4 | 6 | Y | `crates/c05_threads/docs/tier_01_foundations/02_navigation.md`(22) | `crates/c05_threads/docs/tier_01_foundations/04_faq.md`(22) |
| 0.75 | 0.75 | 0.4 | 6 | Y | `crates/c05_threads/docs/tier_01_foundations/03_glossary.md`(22) | `crates/c05_threads/docs/tier_01_foundations/04_faq.md`(22) |

## 机器可读

- JSON: `reports/CONTENT_OVERLAP_V2_2026-07-14.json`
