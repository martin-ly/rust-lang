# crates/ 深层权威覆盖审计报告

**EN**: Crates Deep Authority Coverage Audit
**Summary**: 扫描 crates/ 下全部 .md（含 docs/ 与非 docs/），统计权威覆盖结构、stub 质量、内容扩展机会与非 docs/ 文件治理建议。只读审计，不改正文。

> 生成日期: 2026-07-14
> 扫描范围: `crates/` 下全部 `*.md` = **845** 个
> 复现命令: `python tmp/crates_deep_audit.py`

## 1. 总体统计

### 1.1 docs/ 内分类统计

- 扫描 docs/ md 文件: **576**
  - `stub`: **509**
  - `content`: **64**
  - `index_readme`: **2**
  - `code_listing`: **1**

| crate | stub | content | quiz | index_readme | code_listing |
|:---|---:|---:|---:|---:|---:|
| c01_ownership_borrow_scope | 52 | 5 | 0 | 0 | 0 |
| c02_type_system | 35 | 4 | 0 | 0 | 0 |
| c03_control_fn | 39 | 4 | 0 | 0 | 1 |
| c04_generic | 34 | 2 | 0 | 0 | 0 |
| c05_threads | 37 | 4 | 0 | 0 | 0 |
| c06_async | 40 | 4 | 0 | 0 | 0 |
| c07_process | 50 | 13 | 0 | 0 | 0 |
| c08_algorithms | 33 | 9 | 0 | 0 | 0 |
| c09_design_pattern | 43 | 4 | 0 | 0 | 0 |
| c10_networks | 36 | 10 | 0 | 0 | 0 |
| c11_macro_system_proc | 33 | 1 | 0 | 0 | 0 |
| c12_wasm | 56 | 3 | 0 | 0 | 0 |
| c13_embedded | 6 | 0 | 0 | 0 | 0 |
| c14_semantic_web | 1 | 0 | 0 | 0 | 0 |
| c15_verification_tools | 0 | 0 | 0 | 1 | 0 |
| c16_gui | 0 | 0 | 0 | 1 | 0 |
| c17_resolver_v3_public_demo | 0 | 1 | 0 | 0 | 0 |
| common | 7 | 0 | 0 | 0 | 0 |
| integration_tests | 7 | 0 | 0 | 0 | 0 |

### 1.2 非 docs/ 文件分类统计

| 分类 | 文件数 | 总字节 | 说明 |
|:---|---:|---:|:---|
| CHANGELOG | 6 | 47389 | 版本变更日志 |
| CONTRIBUTING | 6 | 69405 | 贡献指南 |
| examples/README | 12 | 81811 | examples 目录说明 |
| README | 25 | 250145 | crate 根 README |
| reports | 128 | 1544948 | crate 历史报告 |
| src/README | 10 | 24386 | src 子目录说明 |
| tests/README | 10 | 23982 | tests 目录说明 |
| other | 71 | 672774 | 其他根级文档/指南 |
| INDEX | 1 | 18732 | crate 根索引 |

## 2. stub 质量检查

- docs/ stub 总数: **509**
- 无 canonical 链接的 stub: **0**
- 含失效 canonical 链接的 stub: **0**

> ✅ 所有 stub 的 canonical 链接在抽样口径下均可解析。

### 与 concept/ 重复正文抽样检查（30 个最长 stub）

- 抽样数: **30**
- 疑似残留 ≥3 段/标题重复的 stub: **0**

> ✅ 30 个最长 stub 与 concept/ 权威页无 ≥3 段/标题的精确重复，去重基本到位。

## 3. docs/ 内容页扩展机会

> 口径：分类为非 content，字数 >500，且非纯代码清单/索引（即排除 `code_listing`、`index_readme`）。

- 候选数: **1**

| 文件 | 分类 | 字数 | 建议 |
|:---|:---|---:|:---|
| `crates/c05_threads/docs/03_message_passing.md` | stub | 507 | 如保留大纲则维持 stub；如含独特 crate 实践则重写为 content 并补 authority 链接 |

## 4. 非 docs/ 文件治理建议

- 建议归档/转为 stub 的历史报告类文件: **158**
- 建议迁移到 `docs/` 或改为 stub 的通用概念指南: **36**
- 其他待复核文件（Top 20）: **5**

### 4.1 建议归档或 stub 的历史报告

| 文件 | 大小(B) | 字数 | 最近 concept 匹配 | 相似度 |
|:---|---:|---:|:---|---:|
| `crates/c06_async/reports/FINAL_COMPREHENSIVE_SUMMARY_2025_10_06.md` | 25857 | 5349 | `concept/06_ecosystem/03_design_patterns/14_design_patterns_glossary.md` | 0.023 |
| `crates/c02_type_system/final_delivery_report_2025_10_22.md` | 25149 | 4460 | `` | 0.0 |
| `crates/c08_algorithms/reports/FINAL_COMPREHENSIVE_SUMMARY.md` | 23724 | 4172 | `concept/06_ecosystem/03_design_patterns/14_design_patterns_glossary.md` | 0.014 |
| `crates/c06_async/reports/COMPREHENSIVE_ASYNC_SUMMARY_2025_10_04.md` | 22354 | 3947 | `concept/04_formal/01_ownership_logic/03_linear_logic_applications.md` | 0.011 |
| `crates/c06_async/reports/SESSION_PROGRESS_2025_10_06_PART3.md` | 21358 | 4499 | `` | 0.0 |
| `crates/c10_networks/reports/C10_COMPREHENSIVE_ENHANCEMENT_REPORT_2025_10_19.md` | 21231 | 4152 | `concept/00_meta/01_terminology/01_terminology_glossary.md` | 0.014 |
| `crates/c06_async/reports/ASYNC_COMPREHENSIVE_ENHANCEMENT_REPORT_2025.md` | 20939 | 3673 | `concept/02_intermediate/00_traits/02_dispatch_mechanisms.md` | 0.008 |
| `crates/c06_async/reports/RUST_ASYNC_ECOSYSTEM_COMPREHENSIVE_SUMMARY_2025.md` | 19721 | 3434 | `concept/01_foundation/04_control_flow/01_control_flow.md` | 0.009 |
| `crates/c04_generic/reports/KNOWLEDGE_SYSTEM_COMPLETION_REPORT_2025_10_19.md` | 19509 | 4421 | `concept/00_meta/01_terminology/01_terminology_glossary.md` | 0.014 |
| `crates/c08_algorithms/reports/COMPREHENSIVE_ENHANCEMENT_COMPLETE_REPORT.md` | 19306 | 3986 | `concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md` | 0.013 |
| `crates/c03_control_fn/reports/FINAL_PROJECT_COMPLETION_SUMMARY.md` | 19218 | 4290 | `` | 0.0 |
| `crates/c06_async/reports/PROJECT_FINAL_COMPLETION_REPORT_2025_10_06.md` | 19186 | 3913 | `concept/00_meta/01_terminology/01_terminology_glossary.md` | 0.013 |
| `crates/c08_algorithms/reports/COMPREHENSIVE_ENHANCEMENT_REPORT.md` | 19127 | 4236 | `` | 0.0 |
| `crates/c06_async/reports/RUST_190_ASYNC_FINAL_COMPREHENSIVE_REPORT_2025.md` | 18878 | 3611 | `` | 0.0 |
| `crates/c06_async/reports/KNOWLEDGE_SYSTEM_COMPLETION_REPORT_2025_10_19.md` | 18365 | 3886 | `` | 0.0 |
| `crates/c12_wasm/wasmedge_2025_advancement_report.md` | 18334 | 3058 | `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | 0.015 |
| `crates/c06_async/reports/COMPLETION_SUMMARY_2025_10_04.md` | 18217 | 3400 | `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | 0.005 |
| `crates/c08_algorithms/reports/FINAL_PROJECT_STATUS.md` | 18038 | 4359 | `concept/07_future/00_version_tracking/rust_1_90_stabilized.md` | 0.011 |
| `crates/c03_control_fn/reports/RUST_190_ENHANCEMENT_COMPLETION_REPORT.md` | 17836 | 3902 | `concept/07_future/00_version_tracking/rust_1_91_stabilized.md` | 0.006 |
| `crates/c06_async/reports/RUST_190_ASYNC_ECOSYSTEM_COMPREHENSIVE_ANALYSIS_2025.md` | 17534 | 3508 | `` | 0.0 |
| `crates/c06_async/reports/COMPREHENSIVE_PROJECT_COMPLETION_REPORT.md` | 17359 | 2916 | `` | 0.0 |
| `crates/c06_async/reports/FINAL_COMPLETION_REPORT_2025_10_04.md` | 17020 | 3546 | `concept/06_ecosystem/04_web_and_networking/07_network_protocols.md` | 0.02 |
| `crates/c01_ownership_borrow_scope/reports/RUST_190_LATEST_FEATURES_ENHANCEMENT_REPORT.md` | 16947 | 3319 | `concept/07_future/00_version_tracking/rust_1_91_stabilized.md` | 0.007 |
| `crates/c08_algorithms/reports/PROJECT_COMPLETION_REPORT.md` | 16395 | 3662 | `concept/07_future/00_version_tracking/rust_1_90_stabilized.md` | 0.011 |
| `crates/c01_ownership_borrow_scope/reports/RUST_190_COMPREHENSIVE_PROGRESS_REPORT.md` | 16345 | 3122 | `` | 0.0 |
| `crates/c11_macro_system_proc/c11_macro_module_phase1_completion_report_2025_10_20.md` | 16207 | 3338 | `concept/06_ecosystem/01_cargo/16_cargo_workflow.md` | 0.013 |
| `crates/c11_macro_system_proc/c11_macro_module_phase3_progress_report_2025_10_20.md` | 15890 | 3324 | `` | 0.0 |
| `crates/c10_networks/reports/NETWORK_RUNTIME_COMPARISON_ANALYSIS.md` | 15889 | 3109 | `` | 0.0 |
| `crates/c06_async/reports/SESSION_PROGRESS_2025_10_06_PART2.md` | 15871 | 3070 | `` | 0.0 |
| `crates/c12_wasm/project_advancement_2025_10_30.md` | 15590 | 2880 | `` | 0.0 |

### 4.2 建议迁移到 docs/ 或 stub 化的 crate 根级通用指南

| 文件 | 大小(B) | 字数 | 最近 concept 匹配 | 相似度 |
|:---|---:|---:|:---|---:|
| `crates/c02_type_system/best_practices_guide.md` | 24528 | 3877 | `concept/01_foundation/10_testing_basics/02_useful_development_tools.md` | 0.022 |
| `crates/c06_async/async_programming_comprehensive_review_readme_2025_10_06.md` | 20578 | 4083 | `concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md` | 0.01 |
| `crates/c08_algorithms/leetcode_implementation_complete.md` | 19880 | 3671 | `` | 0.0 |
| `crates/c02_type_system/api_documentation.md` | 19529 | 2884 | `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | 0.018 |
| `crates/c10_networks/documentation_reorganization_complete.md` | 16027 | 2860 | `` | 0.0 |
| `crates/c06_async/async_theory_comprehensive_guide.md` | 14481 | 2355 | `concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md` | 0.011 |
| `crates/c02_type_system/cargo_package_management_guide.md` | 13636 | 2445 | `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | 0.014 |
| `crates/c06_async/glommio_integration_2025_10_30.md` | 13446 | 2568 | `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | 0.017 |
| `crates/c02_type_system/dispatch_mechanisms_supplement_2025_10_19.md` | 13418 | 2855 | `concept/03_advanced/02_unsafe/00_before_formal.md` | 0.017 |
| `crates/c02_type_system/readme_rust_189.md` | 13052 | 2619 | `concept/03_advanced/08_process_ipc/08_process_performance_engineering.md` | 0.015 |
| `crates/c09_design_pattern/implementation_roadmap.md` | 12556 | 2835 | `` | 0.0 |
| `crates/c06_async/quick_start_guide_2025.md` | 12361 | 2533 | `concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md` | 0.01 |
| `crates/c08_algorithms/documentation_reorganization_complete.md` | 11019 | 2078 | `` | 0.0 |
| `crates/c12_wasm/rust_192_comprehensive_update_report.md` | 10587 | 1902 | `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | 0.006 |
| `crates/c06_async/knowledge_base_update_notes_2025_10_19.md` | 10305 | 2096 | `concept/03_advanced/06_low_level_patterns/07_rust_runtime.md` | 0.02 |
| `crates/c04_generic/demo_script.md` | 10201 | 2224 | `concept/06_ecosystem/00_toolchain/14_development_tools.md` | 0.009 |
| `crates/c06_async/community_contribution_guide.md` | 10165 | 2012 | `` | 0.0 |
| `crates/c10_networks/deployment_guide.md` | 9731 | 1898 | `concept/04_formal/05_rustc_internals/01_rustc_query_system.md` | 0.014 |
| `crates/c12_wasm/wasmedge_2025_quick_start.md` | 9396 | 1582 | `concept/07_future/00_version_tracking/rust_1_92_stabilized.md` | 0.015 |
| `crates/c10_networks/SECURITY.md` | 9100 | 2115 | `concept/06_ecosystem/12_networking/02_network_security.md` | 0.015 |
| `crates/c12_wasm/quick_start_2025_latest.md` | 8814 | 1513 | `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | 0.015 |
| `crates/c06_async/readme_async_ecosystem.md` | 8616 | 1935 | `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | 0.02 |
| `crates/module_cross_reference.md` | 8615 | 864 | `` | 0.0 |
| `crates/c08_algorithms/reorganization_plan.md` | 8192 | 932 | `` | 0.0 |
| `crates/c12_wasm/quick_start.md` | 7903 | 1281 | `concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md` | 0.011 |
| `crates/c09_design_pattern/exercises/01_pattern_implementations.md` | 7840 | 1048 | `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | 0.04 |
| `crates/c10_networks/exercises/01_tcp_server.md` | 5744 | 813 | `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | 0.042 |
| `crates/c12_wasm/fix_completed.md` | 5708 | 1131 | `concept/06_ecosystem/01_cargo/16_cargo_workflow.md` | 0.019 |
| `crates/c02_type_system/rust_190_feature_inventory_report.md` | 5545 | 1050 | `concept/06_ecosystem/01_cargo/16_cargo_workflow.md` | 0.024 |
| `crates/c12_wasm/exercises/01_wasm_bindings.md` | 5534 | 685 | `concept/07_future/00_version_tracking/rust_1_94_stabilized.md` | 0.042 |

### 4.3 其他待复核非 docs/ 文件

| 文件 | 分类 | 大小(B) | 字数 | 最近 concept 匹配 | 相似度 |
|:---|:---|---:|---:|:---|---:|
| `crates/c02_type_system/examples_and_use_cases.md` | other | 619 | 109 | `` | 0.0 |
| `crates/c02_type_system/readme_rust_190.md` | other | 730 | 113 | `` | 0.0 |
| `crates/c02_type_system/tutorial_guide.md` | other | 2916 | 446 | `` | 0.0 |
| `crates/c09_design_pattern/09_design_patterns.md` | other | 604 | 100 | `` | 0.0 |
| `crates/c11_macro_system_proc/module_reports_standard.md` | other | 1090 | 225 | `` | 0.0 |

## 5. 重点问题清单（Top 20）

1. **crate 根级通用概念指南未纳入 docs/**: `crates/c02_type_system/best_practices_guide.md` (3877 字)
2. **crate 根级通用概念指南未纳入 docs/**: `crates/c06_async/async_programming_comprehensive_review_readme_2025_10_06.md` (4083 字)
3. **crate 根级通用概念指南未纳入 docs/**: `crates/c08_algorithms/leetcode_implementation_complete.md` (3671 字)
4. **历史报告未归档**: `crates/c06_async/reports/FINAL_COMPREHENSIVE_SUMMARY_2025_10_06.md` (5349 字)
5. **历史报告未归档**: `crates/c02_type_system/final_delivery_report_2025_10_22.md` (4460 字)
6. **长 stub 存在内容扩展/裁剪空间**: `crates/c05_threads/docs/03_message_passing.md` (507 字)

## 6. 验证命令

```bash
# 复跑本审计
python tmp/crates_deep_audit.py

# 知识体系一致性（死链/跨层）
python scripts/kb_auditor.py

# mdbook 构建
mdbook build
```

---
*由 `tmp/crates_deep_audit.py` 生成*
