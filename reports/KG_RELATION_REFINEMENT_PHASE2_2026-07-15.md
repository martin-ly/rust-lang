# KG 关系语义精化报告 Phase 2

**日期**: 2026-07-15  **模式**: dry-run（未写回）
**实体数**: 512  **关系数**: 7132 → 7132
**改动数**: 405

## 目标

将 `ex:relatedTo` 占比从 21.9% 进一步压到 <20%。
精化后：`ex:relatedTo` = 1154 / 7132 = **16.2%**

## 规则

| 规则 | 语义 | 说明 |
|:---|:---|:---|
| R6-index-meta-hasPart | hasPart | SUMMARY/README/atlas/navigation 指向 00_meta 内非索引/非映射页 |
| R6b-index-mapping-hasPart | hasPart | 索引页指向 roadmap/gap_and_action_plan 等 mapping 页 |
| R7-atlas-hub-hasPart | hasPart | 01_concept_definition_atlas.md 指向同目录 02-09 atlas |
| R8-hub-content-hasPart | hasPart | 同目录同层：00_**knowledge_map 或 01** 概览指向更高编号内容 |
| R9-quiz-appliesTo | appliesTo | 同目录同层测验页指向非测验概念页 |
| R10-atlas-adjacent-refines | refines | 00_meta/knowledge_topology/ 内相邻编号 atlas 文件 |
| R11-curated-appliesTo | appliesTo | 人工策展的技术/概念 → 领域对 |
| R12-readme-entails | entails | 跨层 README.md → README.md（低层→高层） |

## 谓词分布前后对比

### 全局 KG

| 谓词 | 前 | 后 | Δ |
|:---|---:|---:|---:|
| ex:hasPart | 3146 | 3520 | +374 |
| ex:dependsOn | 1299 | 1299 | +0 |
| ex:relatedTo | 1559 | 1154 | -405 |
| ex:entails | 1016 | 1019 | +3 |
| ex:refines | 81 | 88 | +7 |
| ex:appliesTo | 3 | 24 | +21 |
| ex:instanceOf | 13 | 13 | +0 |
| ex:mutexWith | 10 | 10 | +0 |
| ex:counterExample | 5 | 5 | +0 |

## 关键指标

- `ex:relatedTo` 占比：21.9% → 16.2%
- `ex:relatedTo` 数量：1559 → 1154 (Δ -405)
- 新增/转换谓词：hasPart / refines / appliesTo / entails

## 逐边改动摘要（前 200 条）

| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |
|:---|:---|:---|:---|:---|:---|
| R11-curated-appliesTo | retyped relatedTo | ex:MicroservicePatterns | ex:appliesTo | ex:DistributedSystems | 06_ecosystem/03_design_patterns/05_microservice_patterns.md 微服务模式应用于分布式系统 |
| R11-curated-appliesTo | retyped relatedTo | ex:EventDrivenArchitecture | ex:appliesTo | ex:CloudNative | 06_ecosystem/03_design_patterns/06_event_driven_architecture.md 事件驱动架构应用于云原生 |
| R11-curated-appliesTo | retyped relatedTo | ex:CqrsEventSourcing | ex:appliesTo | ex:DistributedSystems | 06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md CQRS/事件溯源应用于分布式系统 |
| R11-curated-appliesTo | retyped relatedTo | ex:CqrsEventSourcing | ex:appliesTo | ex:CloudNative | 06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md CQRS/事件溯源应用于云原生 |
| R11-curated-appliesTo | retyped relatedTo | ex:AdvancedWebAssemblyDevelopmentWithRust | ex:appliesTo | ex:WebAssembly | 06_ecosystem/11_domain_applications/17_webassembly_advanced.md 高级 WebAssembly 开发应用于 WebAssembly 领域 |
| R11-curated-appliesTo | retyped relatedTo | ex:Robotics | ex:appliesTo | ex:EmbeddedSystems | 06_ecosystem/11_domain_applications/06_robotics.md 机器人开发应用于嵌入式系统 |
| R11-curated-appliesTo | retyped relatedTo | ex:EmbeddedGraphicsDevelopmentWithRust | ex:appliesTo | ex:EmbeddedSystems | 06_ecosystem/11_domain_applications/07_embedded_graphics.md 嵌入式图形开发应用于嵌入式系统 |
| R11-curated-appliesTo | retyped relatedTo | ex:GameEngineInternals | ex:appliesTo | ex:GameDevelopment | 06_ecosystem/11_domain_applications/15_game_engine_internals.md 游戏引擎内部机制应用于游戏开发 |
| R11-curated-appliesTo | retyped relatedTo | ex:CrossPlatformConcurrency | ex:appliesTo | ex:Concurrency | 03_advanced/00_concurrency/04_cross_platform_concurrency.md 跨平台并发应用于并发领域 |
| R11-curated-appliesTo | retyped relatedTo | ex:AsyncProcessManagementInRust | ex:appliesTo | ex:AsyncProgramming | 03_advanced/08_process_ipc/03_async_process_management.md 异步进程管理应用于异步编程 |
| R11-curated-appliesTo | retyped relatedTo | ex:InterProcessCommunicationMechanismsInRust | ex:appliesTo | ex:Concurrency | 03_advanced/08_process_ipc/05_ipc_mechanisms.md 进程间通信机制应用于并发领域 |
| R11-curated-appliesTo | retyped relatedTo | ex:DataEngineering | ex:appliesTo | ex:MachineLearningEcosystem | 06_ecosystem/11_domain_applications/05_data_engineering.md 数据工程应用于机器学习生态 |
| R11-curated-appliesTo | retyped relatedTo | ex:ZeroCopyParsing | ex:appliesTo | ex:SafeAndEffectiveUnsafeRust | 03_advanced/06_low_level_patterns/02_zero_copy_parsing.md 零拷贝解析应用于 unsafe Rust 实践 |
| R12-readme-entails | retyped relatedTo | ex:Readme_03advanced | ex:entails | ex:FormalMethods_04formal | 跨层 README 导航：L3 03_advanced/README.md → L4 04_formal/README.md |
| R12-readme-entails | retyped relatedTo | ex:Readme_03advanced | ex:entails | ex:Readme_05comparativ | 跨层 README 导航：L3 03_advanced/README.md → L5 05_comparative/README.md |
| R12-readme-entails | retyped relatedTo | ex:Readme_03advanced | ex:entails | ex:Readme_06ecosystem | 跨层 README 导航：L3 03_advanced/README.md → L6 06_ecosystem/README.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:Generics_01generics | ex:appliesTo | ex:Generics | 测验 04_quiz_traits_and_generics.md 应用于评估概念 01_generics.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:Concurrency_00concurrenc_2 | ex:appliesTo | ex:Concurrency_00concurrenc | 测验 08_quiz_concurrency_async.md 应用于评估概念 03_concurrency_patterns.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:Concurrency_00concurrenc_2 | ex:appliesTo | ex:LockingPrimitives | 测验 08_quiz_concurrency_async.md 应用于评估概念 06_lock_free.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:UnsafeRust_02unsafe | ex:appliesTo | ex:SafeAndEffectiveUnsafeRust | 测验 05_quiz_unsafe.md 应用于评估概念 01_unsafe.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:Macros_03procmacros_1 | ex:appliesTo | ex:Macros_03procmacros | 测验 10_quiz_macros.md 应用于评估概念 01_macros.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:Macros_03procmacros_1 | ex:appliesTo | ex:ProceduralMacros | 测验 10_quiz_macros.md 应用于评估概念 02_proc_macro.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:FormalMethods_04modelcheck_1 | ex:appliesTo | ex:VerificationToolchain | 测验 06_quiz_formal_methods.md 应用于评估概念 01_verification_toolchain.md |
| R9-quiz-appliesTo | retyped relatedTo | ex:Toolchain_00toolchain | ex:appliesTo | ex:Toolchain | 测验 06_quiz_toolchain.md 应用于评估概念 01_toolchain.md |
| R10-atlas-adjacent-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:AttributeRelationshipAtlas | L0 atlas 相邻文件：01_concept_definition_atlas.md → 02_attribute_relationship_atlas.md |
| R10-atlas-adjacent-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:ConceptDefinitionAtlas | L0 atlas 相邻文件：02_attribute_relationship_atlas.md → 01_concept_definition_atlas.md |
| R10-atlas-adjacent-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:ScenarioDecisionTreeAtlas | L0 atlas 相邻文件：02_attribute_relationship_atlas.md → 03_scenario_decision_tree_atlas.md |
| R10-atlas-adjacent-refines | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:refines | ex:AttributeRelationshipAtlas | L0 atlas 相邻文件：03_scenario_decision_tree_atlas.md → 02_attribute_relationship_atlas.md |
| R10-atlas-adjacent-refines | retyped relatedTo | ex:ExampleAndCounterexampleAtlas | ex:refines | ex:ScenarioDecisionTreeAtlas | L0 atlas 相邻文件：04_example_counterexample_atlas.md → 03_scenario_decision_tree_atlas.md |
| R10-atlas-adjacent-refines | retyped relatedTo | ex:ExampleAndCounterexampleAtlas | ex:refines | ex:LogicalReasoningAtlas | L0 atlas 相邻文件：04_example_counterexample_atlas.md → 05_logical_reasoning_atlas.md |
| R10-atlas-adjacent-refines | retyped relatedTo | ex:LogicalReasoningAtlas | ex:refines | ex:InterLayerMappingAtlas | L0 atlas 相邻文件：05_logical_reasoning_atlas.md → 06_inter_layer_mapping_atlas.md |
| R7-atlas-hub-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ScenarioDecisionTreeAtlas | 概念定义图谱包含专题图谱：01 → 03 |
| R7-atlas-hub-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ExampleAndCounterexampleAtlas | 概念定义图谱包含专题图谱：01 → 04 |
| R7-atlas-hub-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:LogicalReasoningAtlas | 概念定义图谱包含专题图谱：01 → 05 |
| R7-atlas-hub-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:InterLayerMappingAtlas | 概念定义图谱包含专题图谱：01 → 06 |
| R7-atlas-hub-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:IntraLayerMappingAtlas | 概念定义图谱包含专题图谱：01 → 07 |
| R7-atlas-hub-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ConceptSourceAlignmentAtlas | 概念定义图谱包含专题图谱：01 → 08 |
| R7-atlas-hub-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ReasoningJudgmentTreeAtlas | 概念定义图谱包含专题图谱：01 → 09 |
| R8-hub-content-hasPart | retyped relatedTo | ex:PlPrerequisites | ex:hasPart | ex:EffectsAndPurity | 同目录同层概览/知识图谱 01_pl_prerequisites.md 包含子主题 04_effects_and_purity.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:OwnershipBorrowingLifetimesKnowledgeMap | ex:hasPart | ex:MoveSemantics | 同目录同层概览/知识图谱 00_ownership_borrow_lifetime_knowledge_map.md 包含子主题 05_move_semantics.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:OwnershipBorrowingLifetimesKnowledgeMap | ex:hasPart | ex:LifetimesAdvanced | 同目录同层概览/知识图谱 00_ownership_borrow_lifetime_knowledge_map.md 包含子主题 04_lifetimes_advanced.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Ownership | ex:hasPart | ex:LifetimesAdvanced | 同目录同层概览/知识图谱 01_ownership.md 包含子主题 04_lifetimes_advanced.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Ownership | ex:hasPart | ex:BrownUniversityOwnershipInventory | 同目录同层概览/知识图谱 01_ownership.md 包含子主题 06_ownership_inventories_brown_book.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:TypeSystem | ex:hasPart | ex:CoercionAndCasting | 同目录同层概览/知识图谱 01_type_system.md 包含子主题 04_coercion_and_casting.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:TypeSystem | ex:hasPart | ex:DataAbstractionSpectrum | 同目录同层概览/知识图谱 01_type_system.md 包含子主题 05_data_abstraction_spectrum.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:ControlFlow | ex:hasPart | ex:StatementsAndExpressions | 同目录同层概览/知识图谱 01_control_flow.md 包含子主题 03_statements_and_expressions.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Modules | ex:hasPart | ex:Items | 同目录同层概览/知识图谱 01_modules_and_paths.md 包含子主题 12_items.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Modules | ex:hasPart | ex:UseDeclarations | 同目录同层概览/知识图谱 01_modules_and_paths.md 包含子主题 03_use_declarations.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Modules | ex:hasPart | ex:Structs | 同目录同层概览/知识图谱 01_modules_and_paths.md 包含子主题 04_structs.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Modules | ex:hasPart | ex:Enumerations | 同目录同层概览/知识图谱 01_modules_and_paths.md 包含子主题 05_enumerations.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Traits | ex:hasPart | ex:GenericAssociatedTypesGATs | 同目录同层概览/知识图谱 01_traits.md 包含子主题 07_generic_associated_types.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Traits | ex:hasPart | ex:Traits_00traits | 同目录同层概览/知识图谱 01_traits.md 包含子主题 04_advanced_traits.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Generics | ex:hasPart | ex:Generics_01generics | 同目录同层概览/知识图谱 01_generics.md 包含子主题 04_quiz_traits_and_generics.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Generics | ex:hasPart | ex:TypeLevelProgramming | 同目录同层概览/知识图谱 01_generics.md 包含子主题 03_type_level_programming.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:MemoryManagement | ex:hasPart | ex:MemoryManagement_02memorymana | 同目录同层概览/知识图谱 01_memory_management.md 包含子主题 05_quiz_memory_management.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Modules_05modulesand | ex:hasPart | ex:IdiomaticRustAPINamingConventions | 同目录同层概览/知识图谱 01_module_system.md 包含子主题 03_api_naming_conventions.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Concurrency | ex:hasPart | ex:Concurrency_00concurrenc_2 | 同目录同层概览/知识图谱 01_concurrency.md 包含子主题 08_quiz_concurrency_async.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:AsyncProgramming | ex:hasPart | ex:AsyncCancellationSafety | 同目录同层概览/知识图谱 01_async.md 包含子主题 05_async_cancellation_safety.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:AsyncProgramming | ex:hasPart | ex:WakerContractDeepDive | 同目录同层概览/知识图谱 01_async.md 包含子主题 12_waker_contract_deep_dive.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:AsyncProgramming | ex:hasPart | ex:PinAndUnpin | 同目录同层概览/知识图谱 01_async.md 包含子主题 08_pin_unpin.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:AsyncProgramming | ex:hasPart | ex:StreamAlgebraAndBackpressure | 同目录同层概览/知识图谱 01_async.md 包含子主题 09_stream_algebra_and_backpressure.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:AsyncProgramming | ex:hasPart | ex:ExecutorFairnessAndScheduling | 同目录同层概览/知识图谱 01_async.md 包含子主题 10_executor_fairness_and_scheduling.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:AsyncProgramming | ex:hasPart | ex:PinProjectionCounterexamples | 同目录同层概览/知识图谱 01_async.md 包含子主题 11_pin_projection_counterexamples.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:AsyncProgramming | ex:hasPart | ex:AsyncBoundaryPanorama | 同目录同层概览/知识图谱 01_async.md 包含子主题 06_async_boundary_panorama.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:SafeAndEffectiveUnsafeRust | ex:hasPart | ex:UnsafeRust_02unsafe | 同目录同层概览/知识图谱 01_unsafe.md 包含子主题 05_quiz_unsafe.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Macros_03procmacros | ex:hasPart | ex:Macros_03procmacros_1 | 同目录同层概览/知识图谱 01_macros.md 包含子主题 10_quiz_macros.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:VerificationToolchain | ex:hasPart | ex:FormalMethods_04modelcheck_1 | 同目录同层概览/知识图谱 01_verification_toolchain.md 包含子主题 06_quiz_formal_methods.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:RustVsC | ex:hasPart | ex:RustVsGo | 同目录同层概览/知识图谱 01_rust_vs_cpp.md 包含子主题 03_rust_vs_go.md |
| R8-hub-content-hasPart | retyped relatedTo | ex:Toolchain | ex:hasPart | ex:Toolchain_00toolchain | 同目录同层概览/知识图谱 01_toolchain.md 包含子主题 06_quiz_toolchain.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:BoundaryExtensionTree | ex:hasPart | ex:Methodology | 索引页 boundary_extension_tree.md 包含元数据页 methodology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:BoundaryExtensionTree | ex:hasPart | ex:CrossLayerDependencyAndImplicationTopology | 索引页 boundary_extension_tree.md 包含元数据页 05_inter_layer_topology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:BoundaryExtensionTree | ex:hasPart | ex:IntraLayerModelMap | 索引页 boundary_extension_tree.md 包含元数据页 06_intra_layer_model_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:BoundaryExtensionTree | ex:hasPart | ex:TheoremInferenceForest | 索引页 boundary_extension_tree.md 包含元数据页 theorem_inference_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:KnowledgeMindmap | 索引页 09_navigation.md 包含元数据页 knowledge_mindmap.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:Methodology | 索引页 09_navigation.md 包含元数据页 methodology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:LearningGuide | 索引页 09_navigation.md 包含元数据页 07_learning_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:Sources | 索引页 09_navigation.md 包含元数据页 03_sources.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:InterLayerMap | 索引页 09_navigation.md 包含元数据页 04_inter_layer_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:CrossLayerDependencyAndImplicationTopology | 索引页 09_navigation.md 包含元数据页 05_inter_layer_topology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:IntraLayerModelMap | 索引页 09_navigation.md 包含元数据页 06_intra_layer_model_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:TheoremInferenceForest | 索引页 09_navigation.md 包含元数据页 theorem_inference_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:BoundaryExtensionTree | 索引页 09_navigation.md 包含元数据页 boundary_extension_tree.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:SemanticSpace | 索引页 09_navigation.md 包含元数据页 semantic_space.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:SemanticExpressiveness | 索引页 09_navigation.md 包含元数据页 semantic_expressiveness.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:DecidabilitySpectrum | 索引页 09_navigation.md 包含元数据页 decidability_spectrum.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:ExpressivenessMultiview | 索引页 09_navigation.md 包含元数据页 expressiveness_multiview.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:CognitiveDimensionMatrix | 索引页 09_navigation.md 包含元数据页 cognitive_dimension_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:AspMarkingGuide | 索引页 09_navigation.md 包含元数据页 02_asp_marking_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:ConceptDefinitionDecisionForest | 索引页 09_navigation.md 包含元数据页 concept_definition_decision_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:FaultTreeAnalysisCollection | 索引页 09_navigation.md 包含元数据页 fault_tree_analysis_collection.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:QualityDashboardV2 | 索引页 09_navigation.md 包含元数据页 07_quality_dashboard_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:ProblemGraph | 索引页 09_navigation.md 包含元数据页 10_problem_graph.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:CompetencyGraph | 索引页 09_navigation.md 包含元数据页 competency_graph.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:KnowledgeGraphOntologyV20 | 索引页 09_navigation.md 包含元数据页 kg_ontology_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:RustBelt | 索引页 09_navigation.md 包含元数据页 02_rustbelt_predicate_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:ParadigmTransitionMatrix | 索引页 09_navigation.md 包含元数据页 paradigm_transition_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:Navigation | ex:hasPart | ex:AuditChecklist | 索引页 09_navigation.md 包含元数据页 03_audit_checklist.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:BloomTaxonomy | 索引页 01_concept_definition_atlas.md 包含元数据页 bloom_taxonomy.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:BoundaryExtensionTree | 索引页 01_concept_definition_atlas.md 包含元数据页 boundary_extension_tree.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:CognitiveDimensionMatrix | 索引页 01_concept_definition_atlas.md 包含元数据页 cognitive_dimension_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:CompetencyGraph | 索引页 01_concept_definition_atlas.md 包含元数据页 competency_graph.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ConceptDefinitionDecisionForest | 索引页 01_concept_definition_atlas.md 包含元数据页 concept_definition_decision_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:DecidabilitySpectrum | 索引页 01_concept_definition_atlas.md 包含元数据页 decidability_spectrum.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ExpressivenessMultiview | 索引页 01_concept_definition_atlas.md 包含元数据页 expressiveness_multiview.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:FaultTreeAnalysisCollection | 索引页 01_concept_definition_atlas.md 包含元数据页 fault_tree_analysis_collection.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:KnowledgeMindmap | 索引页 01_concept_definition_atlas.md 包含元数据页 knowledge_mindmap.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:Methodology | 索引页 01_concept_definition_atlas.md 包含元数据页 methodology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ParadigmTransitionMatrix | 索引页 01_concept_definition_atlas.md 包含元数据页 paradigm_transition_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:PatternSemanticSpaceIndex | 索引页 01_concept_definition_atlas.md 包含元数据页 pattern_semantic_space_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:AlgorithmsPatternsSemanticBridge | 索引页 01_concept_definition_atlas.md 包含元数据页 semantic_bridge_algorithms_patterns.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:SemanticExpressiveness | 索引页 01_concept_definition_atlas.md 包含元数据页 semantic_expressiveness.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:SemanticSpace | 索引页 01_concept_definition_atlas.md 包含元数据页 semantic_space.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:TheoremInferenceForest | 索引页 01_concept_definition_atlas.md 包含元数据页 theorem_inference_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:GlobalTheoremChainRegistry | 索引页 01_concept_definition_atlas.md 包含元数据页 theorem_registry.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:Todos | 索引页 01_concept_definition_atlas.md 包含元数据页 todos.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:TerminologyGlossary | 索引页 01_concept_definition_atlas.md 包含元数据页 01_terminology_glossary.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:BilingualConceptTemplateV2 | 索引页 01_concept_definition_atlas.md 包含元数据页 02_bilingual_template_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:BilingualConceptTemplate | 索引页 01_concept_definition_atlas.md 包含元数据页 03_bilingual_template.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:AuthoritySourceMap | 索引页 01_concept_definition_atlas.md 包含元数据页 01_authority_source_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:RustBelt | 索引页 01_concept_definition_atlas.md 包含元数据页 02_rustbelt_predicate_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:Sources | 索引页 01_concept_definition_atlas.md 包含元数据页 03_sources.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:TopicAuthorityAlignmentMap | 索引页 01_concept_definition_atlas.md 包含元数据页 04_topic_authority_alignment_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:InternationalAuthorityIndex | 索引页 01_concept_definition_atlas.md 包含元数据页 05_international_authority_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ConceptAuditGuide | 索引页 01_concept_definition_atlas.md 包含元数据页 01_concept_audit_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:AspMarkingGuide | 索引页 01_concept_definition_atlas.md 包含元数据页 02_asp_marking_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:AuditChecklist | 索引页 01_concept_definition_atlas.md 包含元数据页 03_audit_checklist.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ConceptConsistencyAuditChecklist | 索引页 01_concept_definition_atlas.md 包含元数据页 04_concept_consistency_audit_checklist.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:TemplateDeduplicationGuide | 索引页 01_concept_definition_atlas.md 包含元数据页 05_template_deduplication_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:GradingSystem | 索引页 01_concept_definition_atlas.md 包含元数据页 06_grading_system.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:QualityDashboardV2 | 索引页 01_concept_definition_atlas.md 包含元数据页 07_quality_dashboard_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:CrossReferenceMatrix | 索引页 01_concept_definition_atlas.md 包含元数据页 01_cross_reference_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:CareerLandscape | 索引页 01_concept_definition_atlas.md 包含元数据页 02_career_landscape.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ConceptIndex | 索引页 01_concept_definition_atlas.md 包含元数据页 03_concept_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:InterLayerMap | 索引页 01_concept_definition_atlas.md 包含元数据页 04_inter_layer_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:CrossLayerDependencyAndImplicationTopology | 索引页 01_concept_definition_atlas.md 包含元数据页 05_inter_layer_topology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:IntraLayerModelMap | 索引页 01_concept_definition_atlas.md 包含元数据页 06_intra_layer_model_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:LearningGuide | 索引页 01_concept_definition_atlas.md 包含元数据页 07_learning_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:LearningMvpPath | 索引页 01_concept_definition_atlas.md 包含元数据页 08_learning_mvp_path.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:Navigation | 索引页 01_concept_definition_atlas.md 包含元数据页 09_navigation.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:ProblemGraph | 索引页 01_concept_definition_atlas.md 包含元数据页 10_problem_graph.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:QuickReference | 索引页 01_concept_definition_atlas.md 包含元数据页 11_quick_reference.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:SelfAssessment | 索引页 01_concept_definition_atlas.md 包含元数据页 12_self_assessment.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:FoundationsGapClosureIndex | 索引页 01_concept_definition_atlas.md 包含元数据页 13_foundations_gap_closure_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:RustMinimumViableLearningPath | 索引页 01_concept_definition_atlas.md 包含元数据页 14_learning_mvp_path_en.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:KnowledgeGraphOntologyV20 | 索引页 01_concept_definition_atlas.md 包含元数据页 kg_ontology_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:hasPart | ex:TopLevelOntologyAlignmentForRustKnowledgeGraph | 索引页 01_concept_definition_atlas.md 包含元数据页 kg_tlo_alignment.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:BloomTaxonomy | 索引页 02_attribute_relationship_atlas.md 包含元数据页 bloom_taxonomy.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:BoundaryExtensionTree | 索引页 02_attribute_relationship_atlas.md 包含元数据页 boundary_extension_tree.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:CognitiveDimensionMatrix | 索引页 02_attribute_relationship_atlas.md 包含元数据页 cognitive_dimension_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:CompetencyGraph | 索引页 02_attribute_relationship_atlas.md 包含元数据页 competency_graph.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:ConceptDefinitionDecisionForest | 索引页 02_attribute_relationship_atlas.md 包含元数据页 concept_definition_decision_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:DecidabilitySpectrum | 索引页 02_attribute_relationship_atlas.md 包含元数据页 decidability_spectrum.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:ExpressivenessMultiview | 索引页 02_attribute_relationship_atlas.md 包含元数据页 expressiveness_multiview.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:FaultTreeAnalysisCollection | 索引页 02_attribute_relationship_atlas.md 包含元数据页 fault_tree_analysis_collection.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:KnowledgeMindmap | 索引页 02_attribute_relationship_atlas.md 包含元数据页 knowledge_mindmap.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:Methodology | 索引页 02_attribute_relationship_atlas.md 包含元数据页 methodology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:ParadigmTransitionMatrix | 索引页 02_attribute_relationship_atlas.md 包含元数据页 paradigm_transition_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:PatternSemanticSpaceIndex | 索引页 02_attribute_relationship_atlas.md 包含元数据页 pattern_semantic_space_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:AlgorithmsPatternsSemanticBridge | 索引页 02_attribute_relationship_atlas.md 包含元数据页 semantic_bridge_algorithms_patterns.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:SemanticExpressiveness | 索引页 02_attribute_relationship_atlas.md 包含元数据页 semantic_expressiveness.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:SemanticSpace | 索引页 02_attribute_relationship_atlas.md 包含元数据页 semantic_space.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:TheoremInferenceForest | 索引页 02_attribute_relationship_atlas.md 包含元数据页 theorem_inference_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:GlobalTheoremChainRegistry | 索引页 02_attribute_relationship_atlas.md 包含元数据页 theorem_registry.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:Todos | 索引页 02_attribute_relationship_atlas.md 包含元数据页 todos.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:TerminologyGlossary | 索引页 02_attribute_relationship_atlas.md 包含元数据页 01_terminology_glossary.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:BilingualConceptTemplateV2 | 索引页 02_attribute_relationship_atlas.md 包含元数据页 02_bilingual_template_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:BilingualConceptTemplate | 索引页 02_attribute_relationship_atlas.md 包含元数据页 03_bilingual_template.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:AuthoritySourceMap | 索引页 02_attribute_relationship_atlas.md 包含元数据页 01_authority_source_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:RustBelt | 索引页 02_attribute_relationship_atlas.md 包含元数据页 02_rustbelt_predicate_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:Sources | 索引页 02_attribute_relationship_atlas.md 包含元数据页 03_sources.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:TopicAuthorityAlignmentMap | 索引页 02_attribute_relationship_atlas.md 包含元数据页 04_topic_authority_alignment_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:InternationalAuthorityIndex | 索引页 02_attribute_relationship_atlas.md 包含元数据页 05_international_authority_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:ConceptAuditGuide | 索引页 02_attribute_relationship_atlas.md 包含元数据页 01_concept_audit_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:AspMarkingGuide | 索引页 02_attribute_relationship_atlas.md 包含元数据页 02_asp_marking_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:AuditChecklist | 索引页 02_attribute_relationship_atlas.md 包含元数据页 03_audit_checklist.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:ConceptConsistencyAuditChecklist | 索引页 02_attribute_relationship_atlas.md 包含元数据页 04_concept_consistency_audit_checklist.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:TemplateDeduplicationGuide | 索引页 02_attribute_relationship_atlas.md 包含元数据页 05_template_deduplication_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:GradingSystem | 索引页 02_attribute_relationship_atlas.md 包含元数据页 06_grading_system.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:QualityDashboardV2 | 索引页 02_attribute_relationship_atlas.md 包含元数据页 07_quality_dashboard_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:CrossReferenceMatrix | 索引页 02_attribute_relationship_atlas.md 包含元数据页 01_cross_reference_matrix.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:CareerLandscape | 索引页 02_attribute_relationship_atlas.md 包含元数据页 02_career_landscape.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:ConceptIndex | 索引页 02_attribute_relationship_atlas.md 包含元数据页 03_concept_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:InterLayerMap | 索引页 02_attribute_relationship_atlas.md 包含元数据页 04_inter_layer_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:CrossLayerDependencyAndImplicationTopology | 索引页 02_attribute_relationship_atlas.md 包含元数据页 05_inter_layer_topology.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:IntraLayerModelMap | 索引页 02_attribute_relationship_atlas.md 包含元数据页 06_intra_layer_model_map.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:LearningGuide | 索引页 02_attribute_relationship_atlas.md 包含元数据页 07_learning_guide.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:LearningMvpPath | 索引页 02_attribute_relationship_atlas.md 包含元数据页 08_learning_mvp_path.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:Navigation | 索引页 02_attribute_relationship_atlas.md 包含元数据页 09_navigation.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:ProblemGraph | 索引页 02_attribute_relationship_atlas.md 包含元数据页 10_problem_graph.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:QuickReference | 索引页 02_attribute_relationship_atlas.md 包含元数据页 11_quick_reference.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:SelfAssessment | 索引页 02_attribute_relationship_atlas.md 包含元数据页 12_self_assessment.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:FoundationsGapClosureIndex | 索引页 02_attribute_relationship_atlas.md 包含元数据页 13_foundations_gap_closure_index.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:RustMinimumViableLearningPath | 索引页 02_attribute_relationship_atlas.md 包含元数据页 14_learning_mvp_path_en.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:KnowledgeGraphOntologyV20 | 索引页 02_attribute_relationship_atlas.md 包含元数据页 kg_ontology_v2.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:hasPart | ex:TopLevelOntologyAlignmentForRustKnowledgeGraph | 索引页 02_attribute_relationship_atlas.md 包含元数据页 kg_tlo_alignment.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:hasPart | ex:BoundaryExtensionTree | 索引页 03_scenario_decision_tree_atlas.md 包含元数据页 boundary_extension_tree.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:hasPart | ex:ConceptDefinitionDecisionForest | 索引页 03_scenario_decision_tree_atlas.md 包含元数据页 concept_definition_decision_forest.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:hasPart | ex:DecidabilitySpectrum | 索引页 03_scenario_decision_tree_atlas.md 包含元数据页 decidability_spectrum.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:hasPart | ex:ExpressivenessMultiview | 索引页 03_scenario_decision_tree_atlas.md 包含元数据页 expressiveness_multiview.md |
| R6-index-meta-hasPart | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:hasPart | ex:FaultTreeAnalysisCollection | 索引页 03_scenario_decision_tree_atlas.md 包含元数据页 fault_tree_analysis_collection.md |
| ... | ... | ... | ... | ... | 共 405 条，详见 JSON |

## 机器可读

- JSON: `reports/KG_RELATION_REFINEMENT_PHASE2_2026-07-15.json`
