# concept/ 权威层 · 国际化权威来源覆盖率（2026-07-11）

**EN**: Concept-layer International Authority Coverage
**Summary**: 复用 maintenance P0/P1/P2 权威域分级，把审计扩展到 concept/ 权威层；量化覆盖率与缺口，为『对齐网络上的国际化权威相关内容』提供机器可复核基线。仅审计，不改正文。

> 生成: 2026-07-21 · 扫描 concept/ 活跃 md: **522**（排除 archive/SUMMARY/README）
> P0 官方 / P1 学术形式化 / P2 社区生态，域定义复用 `scripts/maintenance/authority_coverage_dashboard.py`

## 总体覆盖率

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方（doc.rust-lang.org / rust-lang.github.io / rustc-dev-guide / ferrocene） | 517 | 99.0% |
| P1 学术/形式化（RustBelt/arxiv/acm/ieee/springer/aeneas …） | 466 | 89.3% |
| P2 社区/生态（verus/creusot/docs.rs/crates.io/blog.rust-lang.org …） | 435 | 83.3% |
| **任一权威（P0∪P1∪P2）** | **522** | **100.0%** |
| 无任何国际权威引用（缺口） | 0 | 0.0% |

## 内容页口径覆盖率（排除 00_meta 工具页 / quiz / placeholders / sources 索引）

> 内容页 **432** 页。00_meta 为知识库内部工具/导航/审计页，非 Rust 概念内容，其权威基线为 P0 官方文档；P1/P2 学术生态来源对其不适用，故单列口径。

| 维度 | 命中页 | 覆盖率 |
|:---|---:|---:|
| P0 官方 | 432 | 100.0% |
| P1 学术/形式化 | 412 | 95.4% |
| P2 社区/生态 | 418 | 96.8% |
| **任一权威** | **432** | **100.0%** |

内容页 P1 缺口（20）: `concept/01_foundation/04_control_flow/03_let_chains.md` · `concept/01_foundation/04_control_flow/05_let_else.md` · `concept/02_intermediate/00_traits/08_negative_impls.md` · `concept/02_intermediate/00_traits/09_associated_type_defaults.md` · `concept/02_intermediate/01_generics/05_const_generics_and_trait_objects.md` · `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` · `concept/03_advanced/02_unsafe/08_async_in_unsafe_contexts.md` · `concept/03_advanced/04_ffi/04_async_ffi_boundary.md` · `concept/03_advanced/04_ffi/05_unsafe_extern_blocks.md` · `concept/04_formal/00_type_theory/10_dependent_refinement_types.md` · `concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md` · `concept/04_formal/07_concurrency_semantics/05_stm_semantics.md` · `concept/05_comparative/01_systems_languages/07_rust_vs_ada_spark.md` · `concept/05_comparative/01_systems_languages/08_rust_vs_d.md` · `concept/05_comparative/01_systems_languages/09_rust_vs_nim.md` · `concept/06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md` · `concept/07_future/00_version_tracking/rust_1_97_1.md` · `concept/07_future/00_version_tracking/rust_1_98_stabilized.md` · `concept/07_future/00_version_tracking/rust_1_99_preview.md` · `concept/07_future/02_preview_features/19_const_trait_preview.md`

内容页 P2 缺口（14）: `concept/02_intermediate/00_traits/08_negative_impls.md` · `concept/02_intermediate/00_traits/09_associated_type_defaults.md` · `concept/02_intermediate/01_generics/05_const_generics_and_trait_objects.md` · `concept/03_advanced/00_concurrency/04_send_sync_boundaries.md` · `concept/03_advanced/01_async/15_state_machine_semantics.md` · `concept/03_advanced/02_unsafe/08_async_in_unsafe_contexts.md` · `concept/03_advanced/04_ffi/05_unsafe_extern_blocks.md` · `concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md` · `concept/05_comparative/00_paradigms/05_language_semantic_model_matrix.md` · `concept/05_comparative/02_managed_languages/09_rust_vs_haskell.md` · `concept/05_comparative/02_managed_languages/11_rust_vs_fsharp.md` · `concept/06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md` · `concept/07_future/00_version_tracking/rust_1_98_stabilized.md` · `concept/07_future/02_preview_features/19_const_trait_preview.md`

## 按层级覆盖率

| 层级 | 页数 | P0 命中 | P0% | 任一权威 | 任一% |
|:---|---:|---:|---:|---:|---:|
| L0 | 66 | 66 | 100.0% | 66 | 100.0% |
| L1 | 57 | 57 | 100.0% | 57 | 100.0% |
| L2 | 41 | 41 | 100.0% | 41 | 100.0% |
| L3 | 72 | 72 | 100.0% | 72 | 100.0% |
| L4 | 59 | 59 | 100.0% | 59 | 100.0% |
| L5 | 27 | 27 | 100.0% | 27 | 100.0% |
| L6 | 129 | 125 | 96.9% | 129 | 100.0% |
| L7 | 68 | 67 | 98.5% | 68 | 100.0% |
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
