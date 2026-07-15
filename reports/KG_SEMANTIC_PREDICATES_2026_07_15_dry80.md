# KG 语义谓词实例化报告（l5, l6_concept, l7, l3_rem）

**日期**: 2026_07_15_dry80  
**模式**: dry-run（未写回）  
**置信度阈值**: 0.8  
**处理实体数**: 226  **处理关系数**: 4412

## 1. 各批次通用谓词残留

| 批次 | 实体数 | 关系数 | 通用谓词残留 | 占比 |
|:---|---:|---:|---:|---:|
| `l5` | 20 | 546 | 326 | 59.71% |
| `l6_concept` | 99 | 1842 | 1122 | 60.91% |
| `l7` | 65 | 1166 | 690 | 59.18% |
| `l3_rem` | 42 | 858 | 312 | 36.36% |

- 处理批次内通用谓词总计残留: **2450**
- 因低于置信度阈值跳过: **393**

## 2. 改动统计

- 修改的关系数: 579

## 3. 全局 @type 分布前后对比

| 谓词 | 修改前 | 修改后 | Δ |
|:---|---:|---:|---:|
| `ex:RelationAnnotation` | 3876 | 3297 | -579 |
| `ex:entails` | 2493 | 2884 | +391 |
| `ex:dependsOn` | 1474 | 1583 | +109 |
| `ex:refines` | 121 | 173 | +52 |
| `ex:equivalentTo` | 13 | 35 | +22 |
| `ex:enables` | 9 | 14 | +5 |
| `ex:mutexWith` | 3 | 3 | +0 |

## 4. 改动样例（前 50 条）

| @id | 主语路径 | 宾语路径 | 旧谓词 | 新谓词 | 规则 | 置信度 |
|:---|:---|:---|:---|:---|:---|---:|
| `_:rel420` | `03_advanced/00_concurrency/04_send_sync_boundaries.md` | `03_advanced/00_concurrency/05_cross_platform_concurrency.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel422` | `03_advanced/00_concurrency/05_cross_platform_concurrency.md` | `07_future/04_research_and_experimental/04_rust_for_linux.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel524` | `03_advanced/03_proc_macros/02_proc_macro.md` | `03_advanced/03_proc_macros/01_macros.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel528` | `03_advanced/03_proc_macros/02_proc_macro.md` | `06_ecosystem/03_design_patterns/01_patterns.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel529` | `03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md` | `03_advanced/03_proc_macros/02_proc_macro.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel532` | `03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md` | `03_advanced/03_proc_macros/05_production_grade_macro_development.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel533` | `03_advanced/03_proc_macros/03_proc_macro_code_generation_optimization.md` | `03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel534` | `03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md` | `03_advanced/03_proc_macros/02_proc_macro.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel536` | `03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md` | `03_advanced/03_proc_macros/05_production_grade_macro_development.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel537` | `03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md` | `06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel538` | `03_advanced/03_proc_macros/05_production_grade_macro_development.md` | `03_advanced/03_proc_macros/02_proc_macro.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel539` | `03_advanced/03_proc_macros/05_production_grade_macro_development.md` | `07_future/02_preview_features/27_cargo_semver_checks_preview.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel540` | `03_advanced/03_proc_macros/06_macro_glossary.md` | `03_advanced/03_proc_macros/09_macro_hygiene.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel541` | `03_advanced/03_proc_macros/06_macro_glossary.md` | `03_advanced/03_proc_macros/08_syn_quote_reference.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel542` | `03_advanced/03_proc_macros/07_macro_faq.md` | `03_advanced/03_proc_macros/09_macro_hygiene.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel543` | `03_advanced/03_proc_macros/07_macro_faq.md` | `03_advanced/03_proc_macros/05_production_grade_macro_development.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel544` | `03_advanced/03_proc_macros/08_syn_quote_reference.md` | `03_advanced/03_proc_macros/05_production_grade_macro_development.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel545` | `03_advanced/03_proc_macros/08_syn_quote_reference.md` | `03_advanced/03_proc_macros/09_macro_hygiene.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel546` | `03_advanced/03_proc_macros/09_macro_hygiene.md` | `03_advanced/03_proc_macros/05_production_grade_macro_development.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel547` | `03_advanced/03_proc_macros/09_macro_hygiene.md` | `03_advanced/03_proc_macros/04_macro_debugging_and_diagnostics.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel568` | `03_advanced/05_inline_assembly/01_inline_assembly.md` | `06_ecosystem/05_systems_and_embedded/02_cross_compilation.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel571` | `03_advanced/05_inline_assembly/01_inline_assembly.md` | `07_future/04_research_and_experimental/04_rust_for_linux.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel572` | `03_advanced/05_inline_assembly/01_inline_assembly.md` | `07_future/04_research_and_experimental/04_rust_for_linux.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel576` | `03_advanced/06_low_level_patterns/01_custom_allocators.md` | `06_ecosystem/10_performance/01_performance_optimization.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel577` | `03_advanced/06_low_level_patterns/01_custom_allocators.md` | `06_ecosystem/06_data_and_distributed/01_application_domains.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel579` | `03_advanced/06_low_level_patterns/02_zero_copy_parsing.md` | `06_ecosystem/10_performance/01_performance_optimization.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel581` | `03_advanced/06_low_level_patterns/03_type_erasure.md` | `06_ecosystem/10_performance/01_performance_optimization.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel585` | `03_advanced/06_low_level_patterns/04_network_programming.md` | `06_ecosystem/04_web_and_networking/03_web_frameworks.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel588` | `03_advanced/06_low_level_patterns/05_stream_processing_semantics.md` | `06_ecosystem/06_data_and_distributed/03_stream_processing_ecosystem.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel592` | `03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md` | `06_ecosystem/10_performance/01_performance_optimization.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel593` | `03_advanced/06_low_level_patterns/06_ownership_performance_optimization.md` | `03_advanced/06_low_level_patterns/02_zero_copy_parsing.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel594` | `03_advanced/06_low_level_patterns/07_rust_runtime.md` | `06_ecosystem/05_systems_and_embedded/03_embedded_systems.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel598` | `03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md` | `03_advanced/06_low_level_patterns/01_custom_allocators.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel599` | `03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md` | `03_advanced/06_low_level_patterns/07_rust_runtime.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel600` | `03_advanced/06_low_level_patterns/09_variables.md` | `03_advanced/06_low_level_patterns/08_memory_allocation_and_lifetime.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel604` | `03_advanced/06_low_level_patterns/10_visibility_and_privacy.md` | `07_future/02_preview_features/27_cargo_semver_checks_preview.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel605` | `03_advanced/06_low_level_patterns/10_visibility_and_privacy.md` | `05_comparative/03_domain_comparisons/01_safety_boundaries.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel609` | `03_advanced/07_unsafe_internals/01_unsafe_collections_internals.md` | `03_advanced/06_low_level_patterns/01_custom_allocators.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel612` | `03_advanced/08_process_ipc/01_process_model_and_lifecycle.md` | `03_advanced/08_process_ipc/02_advanced_process_management.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel613` | `03_advanced/08_process_ipc/01_process_model_and_lifecycle.md` | `03_advanced/08_process_ipc/03_async_process_management.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel614` | `03_advanced/08_process_ipc/01_process_model_and_lifecycle.md` | `03_advanced/08_process_ipc/05_ipc_mechanisms.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel615` | `03_advanced/08_process_ipc/02_advanced_process_management.md` | `03_advanced/08_process_ipc/03_async_process_management.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel616` | `03_advanced/08_process_ipc/02_advanced_process_management.md` | `03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel617` | `03_advanced/08_process_ipc/02_advanced_process_management.md` | `03_advanced/08_process_ipc/08_process_performance_engineering.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel618` | `03_advanced/08_process_ipc/03_async_process_management.md` | `03_advanced/08_process_ipc/05_ipc_mechanisms.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel619` | `03_advanced/08_process_ipc/03_async_process_management.md` | `03_advanced/08_process_ipc/06_process_monitoring_and_diagnostics.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel620` | `03_advanced/08_process_ipc/03_async_process_management.md` | `03_advanced/08_process_ipc/10_modern_process_libraries.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel621` | `03_advanced/08_process_ipc/04_cross_platform_process_management.md` | `03_advanced/08_process_ipc/05_ipc_mechanisms.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel622` | `03_advanced/08_process_ipc/04_cross_platform_process_management.md` | `03_advanced/08_process_ipc/07_process_security_and_sandboxing.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel623` | `03_advanced/08_process_ipc/04_cross_platform_process_management.md` | `03_advanced/08_process_ipc/10_modern_process_libraries.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |

## 5. 结论

⚠️ 处理批次内仍有 2450 条通用谓词（低于阈值 393 条），需进一步处理。

## 6. 机器可读

- JSON: `reports/KG_SEMANTIC_PREDICATES_2026_07_15_dry80.json`