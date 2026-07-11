# 国际化权威来源 URL 健康（2026-07-11）

**EN**: International Authority URL Health
**Summary**: 仅检查 P0/P1/P2 权威域 URL 的有效性，验证『对齐国际化权威』不仅是『有引用』且『引用有效』。带缓存，可增量。**口径**：403/418 及 crates.io 的 404 单列 anti_bot（站点对脚本 UA 反爬，链接本身可能有效，需浏览器人工复核），不计入失效 bad。

> 扫描 concept/+knowledge/+docs/ 权威域唯一 URL: **2097** · 真失效（不含反爬）: **25** · 反爬 403/418: **54** · crates.io 反爬 404: **52**

| 分级 | 真失效（不含反爬） | 反爬 403/418 | crates.io 反爬 404 |
|:---|---:|---:|---:|
| P0 | 2 | 0 | 9 |
| P1 | 0 | 54 | 0 |
| P2 | 23 | 0 | 43 |

## 真失效清单（前 80，需查证新址后替换）
| 分级 | 状态 | 错误 | URL | 引用文件（≤5） |
|:---|:---|:---|:---|:---|
| P0 | None | TimeoutError:The read operation timed out | https://doc.rust-lang.org/reference/items/functions.html | concept/01_foundation/00_start/21_effects_and_purity.md; concept/01_foundation/07_modules_and_items/12_functions.md; concept/01_foundation/11_quizzes/25_quiz_error_handling.md; concept/01_foundation/11_quizzes/33_quiz_ownership_borrowing.md; concept/02_intermediate/03_error_handling/04_error_handling.md |
| P0 | None | URLError:[SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://rust-lang.github.io/wg-async/ | concept/07_future/03_preview_features/18_async_drop_preview.md |
| P2 | 404 | HTTPError | https://blog.rust-lang.org/2023/06/01/ | concept/00_meta/00_framework/decidability_spectrum.md |
| P2 | 404 | HTTPError | https://blog.rust-lang.org/inside-rust/2023/02/23/keyword-generics-progress-report.html | concept/07_future/03_preview_features/04_effects_system.md |
| P2 | 404 | HTTPError | https://docs.rs/lapin/latest/lapin/publisher_confirm/ | docs/research_notes/software_design_theory/07_crate_architectures/28_lapin_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/ndarray/latest/ndarray/doc/ndarray/struct.ArrayBase.html | docs/research_notes/software_design_theory/07_crate_architectures/14_nalgebra_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/ntex/latest/ntex/web/struct.Error.html | docs/research_notes/software_design_theory/07_crate_architectures/40_ntex_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/ort/latest/ort/value/struct.Tensor.html | docs/research_notes/software_design_theory/07_crate_architectures/35_ort_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/raii/latest/raii/ | concept/00_meta/00_framework/theorem_inference_forest.md |
| P2 | 404 | HTTPError | https://docs.rs/ratatui/latest/ratatui/terminal/struct.Terminal.html | docs/research_notes/software_design_theory/07_crate_architectures/20_ratatui_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/rdkafka/latest/rdkafka/producer/type.FutureProducer.html | docs/research_notes/software_design_theory/07_crate_architectures/26_kafka_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/rustc/latest/rustc/ | docs/02_reference/02_error_code_mapping.md |
| P2 | 404 | HTTPError | https://docs.rs/surrealdb/latest/surrealdb/connection/trait.Connection.html | docs/research_notes/software_design_theory/07_crate_architectures/31_surrealdb_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/tract-onnx/latest/tract_onnx/struct.Onnx.html | docs/research_notes/software_design_theory/07_crate_architectures/36_tract_architecture.md |
| P2 | 404 | HTTPError | https://docs.rs/vector/latest/vector/trait.Vector.html | docs/research_notes/software_design_theory/07_crate_architectures/32_vector_architecture.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verus/tree/main/source/rust_verify/example | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/ | docs/05_guides/05_verus_practical_guide.md; docs/research_notes/10_tools_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/concurrency.html | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/ghost.html | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/install.html | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/limitations.html | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/loops.html | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/mut-ref.html | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/guide/spec.html | docs/05_guides/05_verus_practical_guide.md |
| P2 | 404 | HTTPError | https://github.com/verus-lang/verusverus/verusdoc/vstd/ | docs/research_notes/10_tools_guide.md |

## 反爬 403/418（前 40，链接可能有效，需浏览器人工复核，不计入失效）
| 分级 | 状态 | URL | 引用文件（≤3） |
|:---|:---|:---|:---|
| P1 | 403 | https://cacm.acm.org/ | concept/05_comparative/00_paradigms/03_paradigm_matrix.md |
| P1 | 403 | https://cacm.acm.org/magazines/2021/4/251364-safe-systems-programming-in-rust/ | docs/research_notes/formal_methods/10_ownership_model.md |
| P1 | 403 | https://dl.acm.org/ | concept/00_meta/03_audit/audit_checklist.md; concept/05_comparative/01_systems_languages/02_rust_vs_go.md; docs/00_meta/00_annual_review_template.md |
| P1 | 403 | https://dl.acm.org/doi/10.1109/TSE.1982.235252 | concept/06_ecosystem/03_design_patterns/41_workflow_theory.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/1273496.1273513 | docs/research_notes/software_design_theory/07_crate_architectures/30_meilisearch_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/138403.138440 | docs/research_notes/10_advanced_data_structures_guide.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/143165.143169 | concept/01_foundation/00_start/21_effects_and_purity.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/1640089.1640095 | concept/06_ecosystem/03_design_patterns/02_patterns.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/2452376.2452396 | concept/03_advanced/06_low_level_patterns/20_stream_processing_semantics.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/248052.248106 | concept/03_advanced/00_concurrency/16_lock_free.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/2517349.2522738 | concept/03_advanced/06_low_level_patterns/20_stream_processing_semantics.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/2628136.2628161 | concept/01_foundation/00_start/21_effects_and_purity.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/263690.263806 | docs/research_notes/software_design_theory/07_crate_architectures/30_meilisearch_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/2660193.2660205 | docs/research_notes/software_design_theory/07_crate_architectures/33_sentry_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/2674005.2674994 | docs/research_notes/10_cache_eviction_policies_guide.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/2741948.2741950 | docs/research_notes/software_design_theory/07_crate_architectures/34_metrics_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3093744.3093746 | docs/research_notes/software_design_theory/07_crate_architectures/28_lapin_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3149.214121 | concept/06_ecosystem/06_data_and_distributed/50_distributed_consensus.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3158154 | concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md; concept/04_formal/00_type_theory/02_type_theory.md; concept/04_formal/01_ownership_logic/01_linear_logic.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3186725 | docs/research_notes/software_design_theory/07_crate_architectures/32_vector_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3190508.3190528 | docs/research_notes/software_design_theory/07_crate_architectures/34_metrics_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/324133.324234 | docs/research_notes/software_design_theory/07_crate_architectures/13_rayon_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3290380 | concept/04_formal/00_type_theory/02_type_theory.md; concept/04_formal/01_ownership_logic/01_linear_logic.md; concept/04_formal/01_ownership_logic/03_ownership_formal.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3296957.3190648 | docs/research_notes/software_design_theory/07_crate_architectures/31_surrealdb_architecture.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3360573 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3371073 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3371109 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3473597 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3510457.3513031 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3547647 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/355592.365646 | concept/01_foundation/00_start/34_pl_prerequisites.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/356635.356640 | concept/06_ecosystem/10_performance/15_performance_optimization.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/357172.357176 | concept/06_ecosystem/06_data_and_distributed/50_distributed_consensus.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3591283 | concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3591285 | concept/02_intermediate/00_traits/01_traits.md; docs/05_guides/05_verus_practical_guide.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3656422 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3689738 | concept/04_formal/03_operational_semantics/17_operational_semantics.md; concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3704886 | concept/06_ecosystem/08_formal_verification/74_formal_verification_tools.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/3735592 | docs/research_notes/10_academic_papers_alignment.md |
| P1 | 403 | https://dl.acm.org/doi/10.1145/567446.567462 | concept/06_ecosystem/03_design_patterns/41_workflow_theory.md |

## crates.io 反爬 404（前 40，真实 crate/根页在浏览器中通常可达，不计入失效）
| 分级 | URL | 引用文件（≤3） |
|:---|:---|:---|
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/1590-generic-associated-types.md | docs/research_notes/10_learning_and_interview_alignment.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/1665.md | concept/00_meta/00_framework/theorem_inference_forest.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/2616-iterable.md | docs/03_practice/03_project_11_web_server.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/2645-transparent-enums.md | docs/research_notes/10_rfc_alignment_index.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/3101-reserved-prefix.md | docs/research_notes/10_rfc_alignment_index.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/3185-async-drop.md | docs/research_notes/10_rfc_alignment_index.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/3271-rustdoc-json.md | concept/06_ecosystem/00_toolchain/77_rustdoc_196_changes.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/3516-gen-blocks.md | docs/research_notes/10_async_ecosystem_alignment.md; docs/research_notes/10_version_evolution_alignment.md |
| P0 | https://github.com/rust-lang/rfcs/blob/master/text/3560-alignment.md | docs/04_rust_language_feature_comprehensive_inventory_2026.md |
| P2 | https://crates.io | concept/06_ecosystem/02_core_crates/03_core_crates.md; concept/06_ecosystem/08_formal_verification/44_formal_ecosystem_tower.md; concept/07_future/00_version_tracking/rust_1_90_stabilized.md |
| P2 | https://crates.io/ | concept/02_intermediate/03_error_handling/04_error_handling.md; concept/03_advanced/00_concurrency/01_concurrency.md; concept/03_advanced/02_process_ipc/08_process_performance_engineering.md |
| P2 | https://crates.io/categories/database | knowledge/06_ecosystem/databases/README.md |
| P2 | https://crates.io/crates/askama | docs/research_notes/software_design_theory/07_crate_architectures/41_askama_architecture.md |
| P2 | https://crates.io/crates/cached | docs/research_notes/10_cache_eviction_policies_guide.md |
| P2 | https://crates.io/crates/cargo-local-registry | concept/06_ecosystem/01_cargo/61_cargo_source_replacement.md |
| P2 | https://crates.io/crates/dynosaur | concept/03_advanced/01_async/02_async.md |
| P2 | https://crates.io/crates/effect-monad | concept/06_ecosystem/03_design_patterns/39_frontier_research_and_innovative_patterns.md |
| P2 | https://crates.io/crates/frunk | concept/02_intermediate/01_generics/39_type_level_programming.md |
| P2 | https://crates.io/crates/generic-array | concept/02_intermediate/01_generics/39_type_level_programming.md |
| P2 | https://crates.io/crates/kube | docs/research_notes/software_design_theory/07_crate_architectures/27_kube_rs_architecture.md |
| P2 | https://crates.io/crates/lapin | docs/research_notes/software_design_theory/07_crate_architectures/28_lapin_architecture.md |
| P2 | https://crates.io/crates/lru | docs/research_notes/10_cache_eviction_policies_guide.md |
| P2 | https://crates.io/crates/maud | docs/research_notes/software_design_theory/07_crate_architectures/42_maud_architecture.md |
| P2 | https://crates.io/crates/meilisearch-sdk | docs/research_notes/software_design_theory/07_crate_architectures/30_meilisearch_architecture.md |
| P2 | https://crates.io/crates/metrics | docs/research_notes/software_design_theory/07_crate_architectures/34_metrics_architecture.md |
| P2 | https://crates.io/crates/metrics-exporter-prometheus | docs/research_notes/software_design_theory/07_crate_architectures/34_metrics_architecture.md |
| P2 | https://crates.io/crates/mongodb | docs/research_notes/software_design_theory/07_crate_architectures/23_mongodb_architecture.md |
| P2 | https://crates.io/crates/ntex | docs/research_notes/software_design_theory/07_crate_architectures/40_ntex_architecture.md |
| P2 | https://crates.io/crates/ort | docs/research_notes/software_design_theory/07_crate_architectures/35_ort_architecture.md |
| P2 | https://crates.io/crates/q1tsim | concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md |
| P2 | https://crates.io/crates/qforge | concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md |
| P2 | https://crates.io/crates/qip | concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md |
| P2 | https://crates.io/crates/quantrs2 | concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md |
| P2 | https://crates.io/crates/rdkafka | docs/research_notes/software_design_theory/07_crate_architectures/26_kafka_architecture.md |
| P2 | https://crates.io/crates/redis | docs/research_notes/software_design_theory/07_crate_architectures/22_redis_architecture.md |
| P2 | https://crates.io/crates/regex | docs/research_notes/software_design_theory/07_crate_architectures/24_regex_architecture.md |
| P2 | https://crates.io/crates/roqoqo | concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md |
| P2 | https://crates.io/crates/rustls-post-quantum | concept/06_ecosystem/11_domain_applications/51_quantum_computing_rust.md |
| P2 | https://crates.io/crates/salvo | docs/research_notes/software_design_theory/07_crate_architectures/39_salvo_architecture.md |
| P2 | https://crates.io/crates/sentry | docs/research_notes/software_design_theory/07_crate_architectures/33_sentry_architecture.md |

## 诚信
- 仅查 P0/P1/P2 权威域（单一来源：maintenance/authority_coverage_dashboard.py）；不查其它外部域。
- 403/418 及 crates.io 404 不视为『被对齐内容失效』：链接本身可能有效，仅是脚本 UA 被拦，需浏览器人工复核后决定是否保留。
- 瞬时网络抖动可能导致个别误判；真失效项需人工/后台查证新址后替换，勿据此脚本自动删正文。

*由 `scripts/check_authority_link_health.py` 生成*