# concept/ 权威层 · 国际化权威来源覆盖率（2026-07-11）

**EN**: Concept-layer International Authority Coverage
**Summary**: 复用 maintenance P0/P1/P2 权威域分级，把审计扩展到 concept/ 权威层；量化覆盖率与缺口，为『对齐网络上的国际化权威相关内容』提供机器可复核基线。仅审计，不改正文。

> 生成: 2026-08-01 · 扫描 concept/ 活跃 md: **658**（排除 archive/SUMMARY/README）
> P0 官方 / P1 学术形式化 / P2 社区生态，域定义复用 `scripts/maintenance/authority_coverage_dashboard.py`

## 总体覆盖率

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方（doc.rust-lang.org / rust-lang.github.io / rustc-dev-guide / ferrocene） | 631 | 95.9% |
| P1 学术/形式化（RustBelt/arxiv/acm/ieee/springer/aeneas …） | 580 | 88.1% |
| P2 社区/生态（verus/creusot/docs.rs/crates.io/blog.rust-lang.org …） | 568 | 86.3% |
| **任一权威（P0∪P1∪P2）** | **658** | **100.0%** |
| 无任何国际权威引用（缺口） | 0 | 0.0% |

## 内容页口径覆盖率（排除 00_meta 工具页 / quiz / placeholders / sources 索引）

> 内容页 **563** 页。00_meta 为知识库内部工具/导航/审计页，非 Rust 概念内容，其权威基线为 P0 官方文档；P1/P2 学术生态来源对其不适用，故单列口径。

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方 | 541 | 96.1% |
| P1 学术/形式化 | 523 | 92.9% |
| P2 社区/生态 | 547 | 97.2% |
| **任一权威** | **563** | **100.0%** |

内容页 P1 缺口（40）: `concept/01_foundation/00_start/09_fearless_refactoring.md` · `concept/02_intermediate/04_types_and_conversions/02_closure_types.md` · `concept/02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md` · `concept/02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md` · `concept/03_advanced/04_ffi/07_ffi_patterns.md` · `concept/06_ecosystem/02_core_crates/02_serde.md` · `concept/06_ecosystem/02_core_crates/03_tokio.md` · `concept/06_ecosystem/02_core_crates/04_clap.md` · `concept/06_ecosystem/02_core_crates/05_tracing.md` · `concept/06_ecosystem/02_core_crates/06_reqwest.md` · `concept/06_ecosystem/02_core_crates/07_axum.md` · `concept/06_ecosystem/02_core_crates/08_sqlx.md` · `concept/06_ecosystem/03_design_patterns/24_repository_and_unit_of_work.md` · `concept/06_ecosystem/03_design_patterns/25_hexagonal_ports_and_adapters.md` · `concept/06_ecosystem/03_design_patterns/26_circuit_breaker.md` · `concept/06_ecosystem/03_design_patterns/27_bulkhead.md` · `concept/06_ecosystem/03_design_patterns/28_retry.md` · `concept/06_ecosystem/03_design_patterns/29_saga.md` · `concept/06_ecosystem/03_design_patterns/30_outbox.md` · `concept/06_ecosystem/03_design_patterns/31_object_pool.md` · `concept/06_ecosystem/03_design_patterns/32_typestate_deep_dive.md` · `concept/06_ecosystem/03_design_patterns/33_anti_patterns.md` · `concept/06_ecosystem/03_design_patterns/34_ownership_as_resource_management.md` · `concept/06_ecosystem/03_design_patterns/35_scope_guard_and_deferred_cleanup.md` · `concept/06_ecosystem/04_web_and_networking/11_kubernetes_rust.md` · `concept/06_ecosystem/05_systems_and_embedded/23_no_std_and_bare_metal_idioms.md` · `concept/06_ecosystem/05_systems_and_embedded/24_embedded_hal_and_driver_idioms.md` · `concept/06_ecosystem/05_systems_and_embedded/25_memory_mapped_peripherals_and_typestate.md` · `concept/06_ecosystem/05_systems_and_embedded/26_embedded_rtos_and_safety_critical_frameworks.md` · `concept/06_ecosystem/05_systems_and_embedded/27_no_std_startup_runtime_deep_dive.md`

内容页 P2 缺口（16）: `concept/01_foundation/00_start/08_compile_time_correctness.md` · `concept/01_foundation/00_start/09_fearless_refactoring.md` · `concept/02_intermediate/04_types_and_conversions/02_closure_types.md` · `concept/02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md` · `concept/02_intermediate/07_iterators_and_closures/02_closures.md` · `concept/03_advanced/05_inline_assembly/02_inline_assembly_extended.md` · `concept/04_formal/03_operational_semantics/10_minirust.md` · `concept/04_formal/03_operational_semantics/11_async_state_machine_semantics.md` · `concept/04_formal/03_operational_semantics/12_pin_and_self_referential_semantics.md` · `concept/04_formal/07_concurrency_semantics/08_send_sync_semantics.md` · `concept/04_formal/09_system_semantics/07_concurrent_and_parallel_semantics.md` · `concept/04_formal/09_system_semantics/08_memory_ordering_and_atomics.md` · `concept/04_formal/13_semantic_engineering/07_kg_owl_shacl_semantics.md` · `concept/06_ecosystem/03_design_patterns/34_ownership_as_resource_management.md` · `concept/07_future/00_version_tracking/feature_domain_matrix_198.md` · `concept/07_future/00_version_tracking/migration_198_decision_tree.md`

## 按层级覆盖率

| 层级 | 页数 | P0 命中 | P0% | 任一权威 | 任一% |
|:---|---:|---:|---:|---:|---:|
| L0 | 71 | 71 | 100.0% | 71 | 100.0% |
| L1 | 60 | 60 | 100.0% | 60 | 100.0% |
| L2 | 45 | 45 | 100.0% | 45 | 100.0% |
| L3 | 77 | 77 | 100.0% | 77 | 100.0% |
| L4 | 110 | 110 | 100.0% | 110 | 100.0% |
| L5 | 27 | 27 | 100.0% | 27 | 100.0% |
| L6 | 189 | 163 | 86.2% | 189 | 100.0% |
| L7 | 76 | 75 | 98.7% | 76 | 100.0% |
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

## 附：crates/*/docs 权威覆盖（--include-crates 扩展）

> 扫描 crates docs md **568**（含嵌套子 crate）；stub/重定向 504，纯索引 README 2，代码清单页 0，quiz 0。

- 非 stub 内容页 **62** 个，有国际权威来源引用 **62** 个（**100.0%**）。
- 权威域口径为 crates 扩展集（P0/P1/P2 超集 + tokio.rs/rustwasm/rust-embedded/webassembly.org/w3.org/egui/kani/aeneas 等生态权威），见脚本 `CRATES_AUTH_RE`。
- 分类口径（stub 标记/纯索引 README/代码清单豁免）与 `tmp/crates_docs_authority_full.py` 一致。

| crate | 内容页 | 已覆盖 |
|:---|---:|---:|
| c01_ownership_borrow_scope | 5 | 5 |
| c02_type_system | 4 | 4 |
| c03_control_fn | 5 | 5 |
| c04_generic | 2 | 2 |
| c05_threads | 4 | 4 |
| c06_async | 4 | 4 |
| c07_process | 13 | 13 |
| c08_algorithms | 6 | 6 |
| c09_design_pattern | 4 | 4 |
| c10_networks | 10 | 10 |
| c11_macro_system_proc | 1 | 1 |
| c12_wasm | 3 | 3 |
| c17_resolver_v3_public_demo | 1 | 1 |


### crates stub canonical 链接健康度

- **dead_canonical = 0** ✅ 所有 stub 中的 `concept/` canonical 链接均解析到真实文件。

登记跳过（非 stub 但不计入内容页分母）: `crates/c15_verification_tools/docs/README.md`（index_readme） · `crates/c16_gui/docs/README.md`（index_readme）
