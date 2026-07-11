# 国际化权威来源 URL 健康（2026-07-11）

**EN**: International Authority URL Health
**Summary**: 仅检查 P0/P1/P2 权威域 URL 的有效性，验证『对齐国际化权威』不仅是『有引用』且『引用有效』。带缓存，可增量。**口径**：403/418 及 crates.io 的 404 单列 anti_bot（站点对脚本 UA 反爬，链接本身可能有效，需浏览器人工复核），不计入失效 bad。

> 扫描 concept/+knowledge/+docs/ 权威域唯一 URL: **1976** · 真失效（不含反爬）: **0** · 反爬 403/418: **56** · crates.io 反爬 404: **4**

| 分级 | 真失效（不含反爬） | 反爬 403/418 | crates.io 反爬 404 |
|:---|---:|---:|---:|
| P0 | 0 | 0 | 0 |
| P1 | 0 | 56 | 0 |
| P2 | 0 | 0 | 4 |

✅ 本次扫描的权威域 URL 无真失效（2xx/3xx；403 反爬已单列）。

## 反爬 403/418（前 40，链接可能有效，需浏览器人工复核，不计入失效）

| 分级 | 状态 | URL | 引用文件（≤3） |
|:---|:---|:---|:---|
| P1 | 403 | <https://cacm.acm.org/> | concept/05_comparative/00_paradigms/03_paradigm_matrix.md |
| P1 | 403 | <https://cacm.acm.org/magazines/2021/4/251364-safe-systems-programming-in-rust/> | docs/research_notes/formal_methods/10_ownership_model.md |
| P1 | 403 | <https://dl.acm.org/> | concept/00_meta/03_audit/audit_checklist.md; concept/05_comparative/01_systems_languages/02_rust_vs_go.md; docs/00_meta/00_annual_review_template.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/1273496.1273513> | docs/research_notes/software_design_theory/07_crate_architectures/30_meilisearch_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/138403.138440> | docs/research_notes/10_advanced_data_structures_guide.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/143165.143169> | concept/01_foundation/00_start/21_effects_and_purity.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/1640089.1640095> | concept/06_ecosystem/03_design_patterns/02_patterns.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/2452376.2452396> | concept/03_advanced/06_low_level_patterns/20_stream_processing_semantics.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/248052.248106> | concept/03_advanced/00_concurrency/16_lock_free.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/2517349.2522738> | concept/03_advanced/06_low_level_patterns/20_stream_processing_semantics.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/2628136.2628161> | concept/01_foundation/00_start/21_effects_and_purity.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/263690.263806> | docs/research_notes/software_design_theory/07_crate_architectures/30_meilisearch_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/2660193.2660205> | docs/research_notes/software_design_theory/07_crate_architectures/33_sentry_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/2674005.2674994> | docs/research_notes/10_cache_eviction_policies_guide.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/2741948.2741950> | docs/research_notes/software_design_theory/07_crate_architectures/34_metrics_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3093744.3093746> | docs/research_notes/software_design_theory/07_crate_architectures/28_lapin_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3149.214121> | concept/06_ecosystem/06_data_and_distributed/50_distributed_consensus.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3158154> | concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md; concept/03_advanced/00_concurrency/22_cross_platform_concurrency.md; concept/03_advanced/07_unsafe_internals/37_unsafe_collections_internals.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3186725> | docs/research_notes/software_design_theory/07_crate_architectures/32_vector_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3190508.3190528> | docs/research_notes/software_design_theory/07_crate_architectures/34_metrics_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/324133.324234> | docs/research_notes/software_design_theory/07_crate_architectures/13_rayon_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3290380> | concept/04_formal/00_type_theory/02_type_theory.md; concept/04_formal/01_ownership_logic/01_linear_logic.md; concept/04_formal/01_ownership_logic/03_ownership_formal.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3296957.3190648> | docs/research_notes/software_design_theory/07_crate_architectures/31_surrealdb_architecture.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3360573> | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3371073> | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3371109> | concept/03_advanced/06_low_level_patterns/36_ownership_performance_optimization.md; docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3473597> | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3510457.3513031> | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3547647> | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/355592.365646> | concept/01_foundation/00_start/34_pl_prerequisites.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/356635.356640> | concept/06_ecosystem/10_performance/15_performance_optimization.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/357172.357176> | concept/06_ecosystem/06_data_and_distributed/50_distributed_consensus.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3591283> | concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md; concept/03_advanced/06_low_level_patterns/36_ownership_performance_optimization.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3591285> | concept/02_intermediate/00_traits/01_traits.md; concept/04_formal/05_rustc_internals/45_lexical_structure.md; concept/04_formal/05_rustc_internals/53_generics_compiler_behavior.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/359576.359585> | concept/01_foundation/00_start/47_std_io_and_process.md; concept/02_intermediate/00_traits/33_rust_release_process.md; concept/03_advanced/00_concurrency/22_cross_platform_concurrency.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3656422> | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3689738> | concept/04_formal/03_operational_semantics/17_operational_semantics.md; concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3704886> | concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/3735592> | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | <https://dl.acm.org/doi/10.1145/512644.512645> | concept/02_intermediate/06_macros_and_metaprogramming/36_attributes_by_category.md; concept/03_advanced/03_proc_macros/29_proc_macro_code_generation_optimization.md; concept/03_advanced/03_proc_macros/30_macro_debugging_and_diagnostics.md |

## crates.io 反爬 404（前 40，真实 crate/根页在浏览器中通常可达，不计入失效）

| 分级 | URL | 引用文件（≤3） |
|:---|:---|:---|
| P2 | <https://crates.io/policies> | concept/06_ecosystem/01_cargo/62_cargo_registries_and_publishing.md; concept/06_ecosystem/07_security_and_cryptography/19_security_practices.md; docs/research_notes/10_cicd_supply_chain_alignment.md |
| P2 | <https://crates.io/security> | docs/research_notes/10_crate_architecture_authoritative_alignment.md |
| P2 | <https://crates.io/settings/tokens> | docs/research_notes/10_cicd_supply_chain_alignment.md |
| P2 | <https://crates.io/svelte/> | concept/06_ecosystem/07_security_and_cryptography/19_security_practices.md |

## 诚信

- 仅查 P0/P1/P2 权威域（单一来源：maintenance/authority_coverage_dashboard.py）；不查其它外部域。
- 403/418 及 crates.io 404 不视为『被对齐内容失效』：链接本身可能有效，仅是脚本 UA 被拦，需浏览器人工复核后决定是否保留。
- 瞬时网络抖动可能导致个别误判；真失效项需人工/后台查证新址后替换，勿据此脚本自动删正文。

*由 `scripts/check_authority_link_health.py` 生成*
