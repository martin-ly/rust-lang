# concept/ 权威层 · 国际化权威来源覆盖率（2026-07-11）

**EN**: Concept-layer International Authority Coverage
**Summary**: 复用 maintenance P0/P1/P2 权威域分级，把审计扩展到 concept/ 权威层；量化覆盖率与缺口，为『对齐网络上的国际化权威相关内容』提供机器可复核基线。仅审计，不改正文。

> 生成: 2026-07-11 · 扫描 concept/ 活跃 md: **460**（排除 archive/SUMMARY/README）
> P0 官方 / P1 学术形式化 / P2 社区生态，域定义复用 `scripts/maintenance/authority_coverage_dashboard.py`

## 总体覆盖率

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方（doc.rust-lang.org / rust-lang.github.io / rustc-dev-guide / ferrocene） | 460 | 100.0% |
| P1 学术/形式化（RustBelt/arxiv/acm/ieee/springer/aeneas …） | 430 | 93.5% |
| P2 社区/生态（verus/creusot/docs.rs/crates.io/blog.rust-lang.org …） | 367 | 79.8% |
| **任一权威（P0∪P1∪P2）** | **460** | **100.0%** |
| 无任何国际权威引用（缺口） | 0 | 0.0% |

## 内容页口径覆盖率（排除 00_meta 工具页 / quiz / placeholders / sources 索引）

> 内容页 **382** 页。00_meta 为知识库内部工具/导航/审计页，非 Rust 概念内容，其权威基线为 P0 官方文档；P1/P2 学术生态来源对其不适用，故单列口径。

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方 | 382 | 100.0% |
| P1 学术/形式化 | 371 | 97.1% |
| P2 社区/生态 | 358 | 93.7% |
| **任一权威** | **382** | **100.0%** |

内容页 P1 缺口（11）: `concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md` · `concept/01_foundation/06_strings_and_text/46_formatting_and_display.md` · `concept/01_foundation/08_error_handling/33_error_handling_control_flow.md` · `concept/01_foundation/10_testing_basics/42_useful_development_tools.md` · `concept/05_comparative/01_systems_languages/01_rust_vs_cpp.md` · `concept/06_ecosystem/05_systems_and_embedded/57_embedded_hal_1_0_migration.md` · `concept/07_future/00_version_tracking/feature_domain_matrix_197.md` · `concept/07_future/00_version_tracking/migration_197_decision_tree.md` · `concept/07_future/00_version_tracking/rust_1_97_preview.md` · `concept/07_future/03_preview_features/04_effects_system.md` · `concept/07_future/03_preview_features/22_gen_blocks_preview.md`

内容页 P2 缺口（24）: `concept/01_foundation/00_start/00_start.md` · `concept/01_foundation/00_start/21_effects_and_purity.md` · `concept/01_foundation/00_start/34_pl_prerequisites.md` · `concept/01_foundation/00_start/37_operators_and_symbols.md` · `concept/01_foundation/01_ownership_borrow_lifetime/00_ownership_borrow_lifetime_knowledge_map.md` · `concept/01_foundation/02_type_system/04_type_system.md` · `concept/01_foundation/02_type_system/14_coercion_and_casting.md` · `concept/01_foundation/02_type_system/22_data_abstraction_spectrum.md` · `concept/01_foundation/02_type_system/31_never_type.md` · `concept/01_foundation/04_control_flow/07_control_flow.md` · `concept/01_foundation/04_control_flow/40_patterns.md` · `concept/01_foundation/04_control_flow/41_statements_and_expressions.md` · `concept/02_intermediate/04_types_and_conversions/06_range_types.md` · `concept/02_intermediate/04_types_and_conversions/25_rtti_and_dynamic_typing.md` · `concept/02_intermediate/04_types_and_conversions/35_unions.md` · `concept/02_intermediate/04_types_and_conversions/37_type_conversions.md` · `concept/03_advanced/06_low_level_patterns/33_variables.md` · `concept/05_comparative/00_paradigms/16_cpp_rust_surface_features.md` · `concept/05_comparative/01_systems_languages/19_rust_vs_ruby.md` · `concept/05_comparative/02_managed_languages/06_rust_vs_java.md` · `concept/05_comparative/02_managed_languages/07_rust_vs_python.md` · `concept/05_comparative/02_managed_languages/08_rust_vs_javascript.md` · `concept/05_comparative/02_managed_languages/14_rust_vs_elixir.md` · `concept/06_ecosystem/11_domain_applications/75_industrial_case_studies.md`

## 按层级覆盖率

| 层级 | 页数 | P0 命中 | P0% | 任一权威 | 任一% |
|:---|---:|---:|---:|---:|---:|
| L0 | 60 | 60 | 100.0% | 60 | 100.0% |
| L1 | 55 | 55 | 100.0% | 55 | 100.0% |
| L2 | 38 | 38 | 100.0% | 38 | 100.0% |
| L3 | 57 | 57 | 100.0% | 57 | 100.0% |
| L4 | 53 | 53 | 100.0% | 53 | 100.0% |
| L5 | 19 | 19 | 100.0% | 19 | 100.0% |
| L6 | 115 | 115 | 100.0% | 115 | 100.0% |
| L7 | 60 | 60 | 100.0% | 60 | 100.0% |
| L? | 3 | 3 | 100.0% | 3 | 100.0% |

## 核心缺口（L1-L4 且 无 P0 官方国际权威）

共 **0** 页。下表为前 60（按层级、页长降序，优先补权威来源小节）。

| 层级 | 文件 | 行数 |
|:---|:---|---:|

## 方法学与诚信

- 域分级来自现有 `maintenance/authority_coverage_dashboard.py`（单一来源），未新造口径。
- 『命中』= 正文含对应域的 URL 子串（`re.search`）；不区分链接/正文引用，偏宽松（覆盖率可能略高估，缺口清单偏保守可信）。
- 本审计只读，不修改任何文件；补缺口应基于 `concept/00_meta/02_sources/authority_source_map.md` 已核验映射 + 官方 URL，仅追加 References，不改正文事实。

---
*由 `scripts/check_concept_authority_coverage.py` 生成*
