# KG 语义谓词实例化报告（l1, l2, async, unsafe, formal, l5, l6_concept, l7, l3_rem, meta_navigation, ecosystem, future, rustc_internals, framework）

**日期**: 2026-07-16  
**模式**: 已写回 kg_data_v3.json  
**置信度阈值**: 0.75  
**处理实体数**: 487  **处理关系数**: 17165

## 1. 各批次通用谓词残留

| 批次 | 实体数 | 关系数 | 通用谓词残留 | 占比 |
|:---|---:|---:|---:|---:|
| `l1` | 51 | 1452 | 67 | 4.61% |
| `l2` | 40 | 1142 | 44 | 3.85% |
| `async` | 14 | 494 | 17 | 3.44% |
| `unsafe` | 9 | 355 | 11 | 3.10% |
| `formal` | 61 | 1265 | 44 | 3.48% |
| `l5` | 27 | 668 | 21 | 3.14% |
| `l6_concept` | 103 | 1950 | 124 | 6.36% |
| `l7` | 66 | 1271 | 57 | 4.48% |
| `l3_rem` | 43 | 899 | 47 | 5.23% |
| `meta_navigation` | 29 | 3372 | 55 | 1.63% |
| `ecosystem` | 126 | 2263 | 126 | 5.57% |
| `future` | 66 | 1271 | 57 | 4.48% |
| `rustc_internals` | 17 | 288 | 5 | 1.74% |
| `framework` | 21 | 475 | 11 | 2.32% |

- 处理批次内通用谓词总计残留: **686**
- 因低于置信度阈值跳过: **0**

## 2. 改动统计

- 修改的关系数: 6034

## 3. 全局 @type 分布前后对比

| 谓词 | 修改前 | 修改后 | Δ |
|:---|---:|---:|---:|
| `ex:relatedTo` | 1113 | 6263 | +5150 |
| `ex:dependsOn` | 498 | 818 | +320 |
| `ex:entails` | 188 | 752 | +564 |
| `ex:RelationAnnotation` | 6597 | 563 | -6034 |

## 4. 改动样例（前 50 条）

| @id | 主语路径 | 宾语路径 | 旧谓词 | 新谓词 | 规则 | 置信度 |
|:---|:---|:---|:---|:---|:---|---:|
| `_:rel1` | `00_meta/00_framework/comprehensive_rust_mapping.md` | `00_meta/04_navigation/07_learning_guide.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel2` | `00_meta/00_framework/comprehensive_rust_mapping.md` | `00_meta/00_framework/bloom_taxonomy.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel3` | `00_meta/00_framework/comprehensive_rust_mapping.md` | `06_ecosystem/06_data_and_distributed/01_application_domains.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel4` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `05_comparative/01_systems_languages/01_rust_vs_cpp.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel5` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `01_foundation/03_values_and_references/03_variable_model.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel6` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `00_meta/00_framework/pattern_semantic_space_index.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel7` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `05_comparative/01_systems_languages/02_cpp_abi_object_model.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel8` | `00_meta/00_framework/pattern_semantic_space_index.md` | `06_ecosystem/03_design_patterns/01_patterns.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel9` | `00_meta/00_framework/pattern_semantic_space_index.md` | `01_foundation/02_type_system/01_type_system.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel10` | `00_meta/00_framework/pattern_semantic_space_index.md` | `06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel11` | `00_meta/00_framework/pattern_semantic_space_index.md` | `00_meta/00_framework/semantic_bridge_algorithms_patterns.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel12` | `00_meta/00_framework/pl_foundations_roadmap.md` | `01_foundation/02_type_system/01_type_system.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel13` | `00_meta/00_framework/pl_foundations_roadmap.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel14` | `00_meta/00_framework/pl_foundations_roadmap.md` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel15` | `00_meta/00_framework/pl_foundations_roadmap.md` | `00_meta/00_framework/pattern_semantic_space_index.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel16` | `00_meta/00_framework/semantic_bridge_algorithms_patterns.md` | `06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel17` | `00_meta/00_framework/semantic_bridge_algorithms_patterns.md` | `06_ecosystem/03_design_patterns/16_pattern_composition_algebra.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel21` | `00_meta/02_sources/05_international_authority_index.md` | `00_meta/04_navigation/03_concept_index.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel22` | `00_meta/02_sources/05_international_authority_index.md` | `00_meta/00_framework/knowledge_mindmap.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel26` | `00_meta/04_navigation/02_career_landscape.md` | `00_meta/00_framework/bloom_taxonomy.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel27` | `00_meta/04_navigation/02_career_landscape.md` | `06_ecosystem/06_data_and_distributed/01_application_domains.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel28` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/00_framework/pl_foundations_roadmap.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel29` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel30` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/00_framework/pattern_semantic_space_index.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel31` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/03_audit/01_concept_audit_guide.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel33` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `00_meta/knowledge_topology/01_concept_definition_atlas.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel34` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `00_meta/knowledge_topology/06_inter_layer_mapping_atlas.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel35` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `04_formal/07_concurrency_semantics/04_algebraic_effects.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel36` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `04_formal/00_type_theory/10_dependent_refinement_types.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel37` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel38` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `05_comparative/00_paradigms/05_language_semantic_model_matrix.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel44` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `05_comparative/01_systems_languages/01_rust_vs_cpp.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel45` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `06_ecosystem/00_toolchain/01_toolchain.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel49` | `01_foundation/00_start/03_closure_basics.md` | `02_intermediate/07_iterators_and_closures/01_iterator_patterns.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel51` | `01_foundation/00_start/03_closure_basics.md` | `02_intermediate/04_types_and_conversions/02_closure_types.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel53` | `01_foundation/00_start/04_effects_and_purity.md` | `04_formal/03_operational_semantics/04_evaluation_strategies.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel56` | `01_foundation/00_start/04_effects_and_purity.md` | `07_future/02_preview_features/01_effects_system.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel58` | `01_foundation/00_start/05_std_io_and_process.md` | `01_foundation/08_error_handling/01_error_handling_basics.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel60` | `01_foundation/00_start/05_std_io_and_process.md` | `01_foundation/06_strings_and_text/01_strings_and_text.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel62` | `01_foundation/00_start/05_std_io_and_process.md` | `06_ecosystem/06_data_and_distributed/01_application_domains.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel63` | `01_foundation/00_start/05_std_io_and_process.md` | `01_foundation/10_testing_basics/01_testing_basics.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel64` | `01_foundation/00_start/06_keywords.md` | `01_foundation/09_macros_basics/01_attributes_and_macros.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel65` | `01_foundation/00_start/06_keywords.md` | `01_foundation/07_modules_and_items/01_modules_and_paths.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel68` | `01_foundation/00_start/07_operators_and_symbols.md` | `03_advanced/03_proc_macros/01_macros.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel82` | `01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md` | `00_meta/04_navigation/07_learning_guide.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel89` | `01_foundation/02_type_system/02_never_type.md` | `01_foundation/08_error_handling/01_error_handling_basics.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel94` | `01_foundation/02_type_system/03_numerics.md` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel95` | `01_foundation/02_type_system/03_numerics.md` | `01_foundation/05_collections/01_collections.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel106` | `01_foundation/02_type_system/05_data_abstraction_spectrum.md` | `03_advanced/06_low_level_patterns/03_type_erasure.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel114` | `01_foundation/03_values_and_references/02_value_vs_reference_semantics.md` | `00_meta/04_navigation/07_learning_guide.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |

## 5. 结论

⚠️ 处理批次内仍有 686 条通用谓词（低于阈值 0 条），需进一步处理。

## 6. 机器可读

- JSON: `reports/KG_SEMANTIC_PREDICATES_2026-07-16.json`