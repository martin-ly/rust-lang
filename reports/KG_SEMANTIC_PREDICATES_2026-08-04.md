# KG 语义谓词实例化报告（l1, l2, async, unsafe, formal, l5, l6_concept, l7, l3_rem, meta_navigation, ecosystem, future, rustc_internals, framework）

**日期**: 2026-08-04  
**模式**: 已写回 kg_data_v3.json  
**置信度阈值**: 0.75  
**处理实体数**: 618  **处理关系数**: 20805

## 1. 各批次通用谓词残留

| 批次 | 实体数 | 关系数 | 通用谓词残留 | 占比 |
|:---|---:|---:|---:|---:|
| `l1` | 54 | 1576 | 68 | 4.31% |
| `l2` | 44 | 1305 | 47 | 3.60% |
| `async` | 16 | 571 | 19 | 3.33% |
| `unsafe` | 12 | 434 | 24 | 5.53% |
| `formal` | 104 | 1948 | 81 | 4.16% |
| `l5` | 27 | 718 | 22 | 3.06% |
| `l6_concept` | 160 | 2750 | 155 | 5.64% |
| `l7` | 74 | 1489 | 94 | 6.31% |
| `l3_rem` | 44 | 936 | 45 | 4.81% |
| `meta_navigation` | 30 | 3575 | 63 | 1.76% |
| `ecosystem` | 188 | 3087 | 157 | 5.09% |
| `future` | 75 | 1501 | 94 | 6.26% |
| `rustc_internals` | 17 | 309 | 5 | 1.62% |
| `framework` | 24 | 606 | 50 | 8.25% |

- 处理批次内通用谓词总计残留: **924**
- 因低于置信度阈值跳过: **0**

## 2. 改动统计

- 修改的关系数: 9541

## 3. 全局 @type 分布前后对比

| 谓词 | 修改前 | 修改后 | Δ |
|:---|---:|---:|---:|
| `ex:relatedTo` | 0 | 7062 | +7062 |
| `ex:entails` | 0 | 1168 | +1168 |
| `ex:dependsOn` | 0 | 1090 | +1090 |
| `ex:RelationAnnotation` | 10304 | 763 | -9541 |
| `ex:equivalentTo` | 0 | 98 | +98 |
| `ex:refines` | 0 | 63 | +63 |
| `ex:enables` | 0 | 43 | +43 |
| `ex:mutexWith` | 0 | 9 | +9 |
| `ex:instanceOf` | 0 | 6 | +6 |
| `ex:counterExample` | 0 | 2 | +2 |

## 4. 改动样例（前 50 条）

| @id | 主语路径 | 宾语路径 | 旧谓词 | 新谓词 | 规则 | 置信度 |
|:---|:---|:---|:---|:---|:---|---:|
| `_:rel1` | `00_meta/00_framework/comprehensive_rust_mapping.md` | `00_meta/04_navigation/07_learning_guide.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel2` | `00_meta/00_framework/comprehensive_rust_mapping.md` | `00_meta/00_framework/bloom_taxonomy.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel3` | `00_meta/00_framework/comprehensive_rust_mapping.md` | `06_ecosystem/06_data_and_distributed/01_application_domains.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel4` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `05_comparative/01_systems_languages/01_rust_vs_cpp.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel5` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `01_foundation/03_values_and_references/03_variable_model.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel6` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `00_meta/00_framework/pattern_semantic_space_index.md` | `ex:entails` | `ex:equivalentTo` | atlas-semantic | 0.95 |
| `_:rel7` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `05_comparative/01_systems_languages/02_cpp_abi_object_model.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel8` | `00_meta/00_framework/pattern_semantic_space_index.md` | `06_ecosystem/03_design_patterns/01_patterns.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel9` | `00_meta/00_framework/pattern_semantic_space_index.md` | `01_foundation/02_type_system/01_type_system.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel10` | `00_meta/00_framework/pattern_semantic_space_index.md` | `04_formal/00_type_theory/12_pattern_composition_algebra.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel11` | `00_meta/00_framework/pl_foundations_roadmap.md` | `01_foundation/02_type_system/01_type_system.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel12` | `00_meta/00_framework/pl_foundations_roadmap.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel13` | `00_meta/00_framework/pl_foundations_roadmap.md` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `ex:entails` | `ex:equivalentTo` | atlas-semantic | 0.95 |
| `_:rel14` | `00_meta/00_framework/pl_foundations_roadmap.md` | `00_meta/00_framework/pattern_semantic_space_index.md` | `ex:entails` | `ex:refines` | atlas-semantic | 0.95 |
| `_:rel15` | `00_meta/00_framework/rust_api_guidelines_canonical.md` | `01_foundation/02_type_system/01_type_system.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel16` | `00_meta/00_framework/rust_api_guidelines_canonical.md` | `02_intermediate/00_traits/01_traits.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel17` | `00_meta/00_framework/rust_api_guidelines_canonical.md` | `02_intermediate/03_error_handling/01_error_handling.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel18` | `00_meta/00_framework/rust_api_guidelines_canonical.md` | `01_foundation/05_collections/03_iterator_idioms.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel19` | `00_meta/00_framework/rust_api_guidelines_canonical.md` | `06_ecosystem/03_design_patterns/02_idioms_spectrum.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel20` | `00_meta/00_framework/rust_api_guidelines_canonical.md` | `06_ecosystem/11_domain_applications/08_algorithm_engineering_practice.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel21` | `00_meta/00_framework/semantic_bridge_algorithms_patterns.md` | `06_ecosystem/11_domain_applications/07_algorithms_competitive_programming.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel22` | `00_meta/00_framework/semantic_bridge_algorithms_patterns.md` | `04_formal/00_type_theory/12_pattern_composition_algebra.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel23` | `00_meta/00_framework/semantic_layer_alignment_index.md` | `00_meta/00_framework/semantic_space.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel24` | `00_meta/00_framework/semantic_layer_alignment_index.md` | `06_ecosystem/14_enterprise_architecture/01_enterprise_architecture_frameworks.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel25` | `00_meta/00_framework/semantic_model_reasoning_methodology.md` | `00_meta/00_framework/semantic_space.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel26` | `00_meta/00_framework/semantic_model_reasoning_methodology.md` | `04_formal/00_type_theory/01_type_theory.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel30` | `00_meta/02_sources/05_international_authority_index.md` | `00_meta/04_navigation/03_concept_index.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel31` | `00_meta/02_sources/05_international_authority_index.md` | `00_meta/00_framework/knowledge_mindmap.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel35` | `00_meta/02_sources/06_external_authority_topic_index.md` | `00_meta/04_navigation/03_concept_index.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel36` | `00_meta/02_sources/06_external_authority_topic_index.md` | `00_meta/00_framework/todos.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel40` | `00_meta/04_navigation/02_career_landscape.md` | `00_meta/00_framework/bloom_taxonomy.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel41` | `00_meta/04_navigation/02_career_landscape.md` | `06_ecosystem/06_data_and_distributed/01_application_domains.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel42` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/00_framework/pl_foundations_roadmap.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel43` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/00_framework/cpp_rust_engineering_roadmap.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel44` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/00_framework/pattern_semantic_space_index.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel45` | `00_meta/04_navigation/13_foundations_gap_closure_index.md` | `00_meta/03_audit/01_concept_audit_guide.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel47` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `00_meta/knowledge_topology/01_concept_definition_atlas.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel48` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `00_meta/knowledge_topology/06_inter_layer_mapping_atlas.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel49` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `04_formal/07_concurrency_semantics/04_algebraic_effects.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel50` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `04_formal/00_type_theory/10_dependent_refinement_types.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel51` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel52` | `00_meta/knowledge_topology/11_semantic_model_atlas.md` | `05_comparative/00_paradigms/05_language_semantic_model_matrix.md` | `ex:entails` | `ex:entails` | existing-semantic | 1.00 |
| `_:rel53` | `01_foundation/00_start/01_pl_prerequisites.md` | `02_intermediate/00_traits/01_traits.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel54` | `01_foundation/00_start/01_pl_prerequisites.md` | `02_intermediate/01_generics/01_generics.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel55` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | `ex:dependsOn` | `ex:dependsOn` | existing-semantic | 1.00 |
| `_:rel56` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `02_intermediate/01_generics/01_generics.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel57` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `02_intermediate/00_traits/01_traits.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |
| `_:rel58` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `05_comparative/01_systems_languages/01_rust_vs_cpp.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel59` | `01_foundation/00_start/02_zero_cost_abstractions.md` | `06_ecosystem/00_toolchain/01_toolchain.md` | `ex:entails` | `ex:entails` | atlas-semantic | 0.95 |
| `_:rel60` | `01_foundation/00_start/03_closure_basics.md` | `02_intermediate/00_traits/01_traits.md` | `ex:dependsOn` | `ex:dependsOn` | atlas-semantic | 0.95 |

## 5. 结论

⚠️ 处理批次内仍有 924 条通用谓词（低于阈值 0 条），需进一步处理。

## 6. 机器可读

- JSON: `reports/KG_SEMANTIC_PREDICATES_2026-08-04.json`