# concept/ 权威层 · 国际化权威来源覆盖率（2026-07-11）

**EN**: Concept-layer International Authority Coverage
**Summary**: 复用 maintenance P0/P1/P2 权威域分级，把审计扩展到 concept/ 权威层；量化覆盖率与缺口，为『对齐网络上的国际化权威相关内容』提供机器可复核基线。仅审计，不改正文。

> 生成: 2026-08-04 · 扫描 concept/ 活跃 md: **780**（排除 archive/SUMMARY/README）
> P0 官方 / P1 学术形式化 / P2 社区生态，域定义复用 `scripts/maintenance/authority_coverage_dashboard.py`

## 总体覆盖率

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方（doc.rust-lang.org / rust-lang.github.io / rustc-dev-guide / ferrocene） | 764 | 97.9% |
| P1 学术/形式化（RustBelt/arxiv/acm/ieee/springer/aeneas …） | 708 | 90.8% |
| P2 社区/生态（verus/creusot/docs.rs/crates.io/blog.rust-lang.org …） | 687 | 88.1% |
| **任一权威（P0∪P1∪P2）** | **777** | **99.6%** |
| 无任何国际权威引用（缺口） | 3 | 0.4% |

## 内容页口径覆盖率（排除 00_meta 工具页 / quiz / placeholders / sources 索引）

> 内容页 **679** 页。00_meta 为知识库内部工具/导航/审计页，非 Rust 概念内容，其权威基线为 P0 官方文档；P1/P2 学术生态来源对其不适用，故单列口径。

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方 | 669 | 98.5% |
| P1 学术/形式化 | 649 | 95.6% |
| P2 社区/生态 | 663 | 97.6% |
| **任一权威** | **677** | **99.7%** |

内容页 P1 缺口（30）: `concept/04_formal/11_computational_models/17_aeneas_verification_pipeline.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/01_iterator_chains.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/02_error_propagation.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/03_into_from_asref.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/04_newtype.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/05_typestate.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/06_raii_cleanup.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/07_builder.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/08_defer.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/01_segment_tree.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/02_trie.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/03_union_find.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/04_graph_algorithms.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/05_lock_free_data_structures.md` · `concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/01_strategy.md` · `concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/02_command.md` · `concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/03_visitor.md` · `concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/04_state_machine.md` · `concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/05_adapter.md` · `concept/05_comparative/05_idioms_patterns_architecture/03_design_patterns/06_decorator.md` · `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/01_hexagonal_clean_architecture.md` · `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/02_cqrs_event_sourcing.md` · `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/03_microservices.md` · `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/05_plugin_system.md` · `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/06_event_bus.md` · `concept/06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md` · `concept/06_ecosystem/05_systems_and_embedded/54_linker_scripts_and_memory_layout.md` · `concept/06_ecosystem/05_systems_and_embedded/55_rtic_vs_embassy_real_time_frameworks.md` · `concept/06_ecosystem/05_systems_and_embedded/56_rust_for_linux_kernel_module_basics.md` · `concept/06_ecosystem/14_enterprise_architecture/08_microservices_patterns_in_rust.md`

内容页 P2 缺口（16）: `concept/04_formal/11_computational_models/12_linear_logic_and_ownership.md` · `concept/04_formal/11_computational_models/14_effect_handlers_and_rust_limited_effects.md` · `concept/04_formal/11_computational_models/15_refinement_types_and_flux.md` · `concept/04_formal/11_computational_models/16_rustbelt_ownership_logic.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/02_error_propagation.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/03_into_from_asref.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/04_newtype.md` · `concept/05_comparative/05_idioms_patterns_architecture/01_idioms/06_raii_cleanup.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/01_segment_tree.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/02_trie.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/03_union_find.md` · `concept/05_comparative/05_idioms_patterns_architecture/02_algorithms/04_graph_algorithms.md` · `concept/05_comparative/05_idioms_patterns_architecture/04_architecture/04_actor.md` · `concept/06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md` · `concept/06_ecosystem/05_systems_and_embedded/55_rtic_vs_embassy_real_time_frameworks.md` · `concept/06_ecosystem/05_systems_and_embedded/56_rust_for_linux_kernel_module_basics.md`

## 按层级覆盖率

| 层级 | 页数 | P0 命中 | P0% | 任一权威 | 任一% |
|:---|---:|---:|---:|---:|---:|
| L0 | 76 | 75 | 98.7% | 75 | 98.7% |
| L1 | 60 | 60 | 100.0% | 60 | 100.0% |
| L2 | 45 | 45 | 100.0% | 45 | 100.0% |
| L3 | 78 | 78 | 100.0% | 78 | 100.0% |
| L4 | 131 | 131 | 100.0% | 131 | 100.0% |
| L5 | 55 | 49 | 89.1% | 55 | 100.0% |
| L6 | 257 | 249 | 96.9% | 255 | 99.2% |
| L7 | 75 | 74 | 98.7% | 75 | 100.0% |
| L? | 3 | 3 | 100.0% | 3 | 100.0% |

## 核心缺口（L1-L4 且 无 P0 官方国际权威）

共 **0** 页。下表为前 60（按层级、页长降序，优先补权威来源小节）。

| 层级 | 文件 | 行数 |
|:---|:---|---:|

## 方法学与诚信

- 域分级来自现有 `maintenance/authority_coverage_dashboard.py`（单一来源），未新造口径。
- 『命中』= 正文含对应域的 URL 子串（`re.search`）；不区分链接/正文引用，偏宽松（覆盖率可能略高估，缺口清单偏保守可信）。
- 本审计只读，不修改任何文件；补缺口应基于 `concept/00_meta/02_sources/01_authority_source_map.md` 已核验映射 + 官方 URL，仅追加 References，不改正文事实。

---
*由 `scripts/check_concept_authority_coverage.py` 生成*