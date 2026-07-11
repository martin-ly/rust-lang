# 一次性战役脚本归档（2026-07-12，P3-6 大扫除）

> **归档原因**：以下 97 个文件（96 脚本 + 1 数据文件）为针对特定批次/战役的一次性脚本（硬编码路径、替换表或特定版本窗口），使命已完成。
> **移动前核查**：已 grep 确认无质量门（run_quality_gates.sh）、CI workflows、pre-commit 钩子或其他脚本 import 引用；
> 活跃文档中的路径引用已更新为归档路径（见 docs/research_notes/10_authoritative_source_100_percent_roadmap.md、
> concept/00_meta/knowledge_topology/kg_ontology_v2.md、concept/00_meta/03_audit/template_deduplication_guide.md、
> docs/04_research/README.md、scripts/check_template_cliches.py、scripts/maintenance/archive_health_check.py）。
> ⚠️ 归档脚本只读、不再维护；CHANGELOG.md 中的历史记录保留原始路径。

## 来源分布

- 原 scripts/ 根目录：58 个（fix_*/add_*/batch_*/bulk_*/cleanup_*/generate_en_skeleton 等，含配套数据文件 temp_external_link_replacements.json）
- 原 scripts/maintenance/：27 个（bulk_add_*、p1/p2_coverage_sprint、fix_never_type、fix_async_drop_refs、rust_197_release_day.py 等）
- 原 scripts/fixes/：12 个（fix_p0/p1/p2_*、recover_*、append_* 等）

## 完整清单

- add_backward_l2l3.py
- add_backward_reasoning.py
- add_c_class_content_grade.py
- add_cross_references.py
- add_kg_layer_domain.py
- add_missing_sources.py
- add_sources.py
- add_summary_entries.py
- append_comparative_xlang.py
- append_docs_authority.py
- append_metadata_behavioral.py
- apply_formal_upgrade.py
- apply_link_replacements.py
- archive_deprecated_content.py
- archive_research_notes_candidates.py
- archive_research_notes_peripheral.py
- auto_add_structure.py
- batch_add_grading_labels.py
- batch_archive_c_class.py
- batch_fix_dual_labels.py
- batch_version_refresh.py
- bulk_active_ecosystem_update.py
- bulk_add_knowledge_module8.py
- bulk_add_p1_to_alignment_docs.py
- bulk_add_p1p2_by_family.py
- bulk_append_counterexample_authority_sources.py
- bulk_archive_warning.py
- cleanup_cheatsheets.py
- cleanup_mechanical_citations.py
- cleanup_title_embedded_citations.py
- compact_blank_lines.py
- deepen_summaries.py
- enhance_summaries.py
- extend_unsafe_2024.py
- final_bilingual_fix.py
- fix_404_links.py
- fix_archive_c_class_links.py
- fix_archived_research_notes_links.py
- fix_async_drop_refs.py
- fix_authority_url_placeholders.py
- fix_backward_chains.py
- fix_bad_summaries.py
- fix_bilingual_annotations.py
- fix_cargo_resolver.py
- fix_code_blocks.py
- fix_concept_en_titles.py
- fix_concept_i18n_metadata_v2.py
- fix_concept_source_placeholders.py
- fix_coq_skeleton_links.py
- fix_coverage_and_refs.py
- fix_dangling_renames.py
- fix_dead_links_v3.py
- fix_docs_anchor_links.py
- fix_docs_links_correct.py
- fix_docs_remaining_links.py
- fix_docs_research_notes_paths.py
- fix_docs_source_placeholders.py
- fix_dot_anchor_links.py
- fix_final_broken_links.py
- fix_future_summaries.py
- fix_generic_source_placeholders.py
- fix_grading_tags.py
- fix_i18n_quality.py
- fix_inter_layer_refs.py
- fix_kb_quality_issues.py
- fix_last_anchor_links.py
- fix_links.py
- fix_meta_source_placeholders.py
- fix_meta_summaries.py
- fix_metadata_d3.py
- fix_never_type.py
- fix_p0_authority_links.py
- fix_p0_root_fallbacks.py
- fix_p1_academic_links.py
- fix_p2_community_links.py
- fix_p2_remaining.py
- fix_quick_reference_anchors.py
- fix_remaining_anchors.py
- fix_remaining_source_placeholders.py
- fix_rod_readme_links.py
- fix_root_source_links.py
- fix_templated_chains.py
- fix_unsafe_numbering.py
- generate_en_skeleton.py
- improve_active_metadata.py
- migrate_archive.py
- migrate_kg_v1_to_v2.py
- p1_coverage_sprint.py
- p2_coverage_sprint.py
- rebuild_concept_headers.py
- recover_docsrs_deep_links.py
- recover_p0_authority_links.py
- remove_status_toc_entries.py
- replace_placeholder_generic.py
- rust_197_release_day.py
- temp_external_link_replacements.json
- upgrade_cheatsheets.py
