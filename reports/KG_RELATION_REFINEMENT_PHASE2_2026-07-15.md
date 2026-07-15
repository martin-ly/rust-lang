# KG 关系精化第二阶段报告

**日期**: 2026-07-15  **模式**: 已写回
**改动数**: 108
**relatedTo**: 1563 → 1458 (-105)

## 谓词分布

- `ex:hasPart`: 3146 → 3176 (+30)
- `ex:relatedTo`: 1563 → 1458 (-105)
- `ex:dependsOn`: 1295 → 1295 (+0)
- `ex:entails`: 1015 → 1015 (+0)
- `ex:refines`: 81 → 156 (+75)
- `ex:instanceOf`: 13 → 13 (+0)
- `ex:mutexWith`: 10 → 10 (+0)
- `ex:appliesTo`: 3 → 6 (+3)
- `ex:counterExample`: 5 → 5 (+0)

## 改动摘要（前 200 条）

| 规则 | 动作 | 主语 | 谓词 | 宾语 |
|:---|:---|:---|:---|:---|
| R6-meta-hasPart | retyped relatedTo | ex:ConceptIndex | ex:hasPart | ex:InternationalAuthorityIndex |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:AttributeRelationshipAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:ScenarioDecisionTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:ExampleAndCounterexampleAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:LogicalReasoningAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:InterLayerMappingAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:IntraLayerMappingAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:ConceptSourceAlignmentAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ConceptDefinitionAtlas | ex:refines | ex:ReasoningJudgmentTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:ConceptDefinitionAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:ScenarioDecisionTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:ExampleAndCounterexampleAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:LogicalReasoningAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:InterLayerMappingAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:IntraLayerMappingAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:ConceptSourceAlignmentAtlas |
| R6-atlas-refines | retyped relatedTo | ex:AttributeRelationshipAtlas | ex:refines | ex:ReasoningJudgmentTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:refines | ex:ConceptDefinitionAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:refines | ex:AttributeRelationshipAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:refines | ex:ReasoningJudgmentTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:refines | ex:InterLayerMappingAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ScenarioDecisionTreeAtlas | ex:refines | ex:LogicalReasoningAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ExampleAndCounterexampleAtlas | ex:refines | ex:ScenarioDecisionTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ExampleAndCounterexampleAtlas | ex:refines | ex:ReasoningJudgmentTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ExampleAndCounterexampleAtlas | ex:refines | ex:LogicalReasoningAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ExampleAndCounterexampleAtlas | ex:refines | ex:ConceptDefinitionAtlas |
| R6-atlas-refines | retyped relatedTo | ex:LogicalReasoningAtlas | ex:refines | ex:ConceptDefinitionAtlas |
| R6-atlas-refines | retyped relatedTo | ex:LogicalReasoningAtlas | ex:refines | ex:ScenarioDecisionTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:LogicalReasoningAtlas | ex:refines | ex:InterLayerMappingAtlas |
| R6-atlas-refines | retyped relatedTo | ex:LogicalReasoningAtlas | ex:refines | ex:ReasoningJudgmentTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ReasoningJudgmentTreeAtlas | ex:refines | ex:ScenarioDecisionTreeAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ReasoningJudgmentTreeAtlas | ex:refines | ex:ExampleAndCounterexampleAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ReasoningJudgmentTreeAtlas | ex:refines | ex:LogicalReasoningAtlas |
| R6-atlas-refines | retyped relatedTo | ex:ReasoningJudgmentTreeAtlas | ex:refines | ex:ConceptDefinitionAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:ConceptDefinitionAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:AttributeRelationshipAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:ScenarioDecisionTreeAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:ExampleAndCounterexampleAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:LogicalReasoningAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:InterLayerMappingAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:IntraLayerMappingAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:ConceptSourceAlignmentAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:KnowledgeTopologyAtlas | ex:hasPart | ex:ReasoningJudgmentTreeAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:ConceptMetaLayer | ex:hasPart | ex:PatternSemanticSpaceIndex |
| R6-meta-hasPart | retyped relatedTo | ex:ConceptMetaLayer | ex:hasPart | ex:ConceptIndex |
| R6-meta-hasPart | retyped relatedTo | ex:ConceptMetaLayer | ex:hasPart | ex:FoundationsGapClosureIndex |
| R6-meta-hasPart | retyped relatedTo | ex:RustConceptKnowledgeSystem | ex:hasPart | ex:InternationalAuthorityIndex |
| R6-meta-hasPart | retyped relatedTo | ex:AuthoritySourceIndex | ex:hasPart | ex:InternationalAuthorityIndex |
| R6-meta-hasPart | retyped relatedTo | ex:AuthoritySourceIndex | ex:hasPart | ex:RfcIndex |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:ConceptIndex |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:Navigation |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:PatternSemanticSpaceIndex |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:FoundationsGapClosureIndex |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:InternationalAuthorityIndex |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:ConceptDefinitionAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:AttributeRelationshipAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:ScenarioDecisionTreeAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:ExampleAndCounterexampleAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:LogicalReasoningAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:InterLayerMappingAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:IntraLayerMappingAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:ConceptSourceAlignmentAtlas |
| R6-meta-hasPart | retyped relatedTo | ex:TableOfContents | ex:hasPart | ex:ReasoningJudgmentTreeAtlas |
| R7-sibling-refines | retyped relatedTo | ex:LifetimesAdvanced | ex:refines | ex:Borrowing |
| R7-sibling-refines | retyped relatedTo | ex:MoveSemantics | ex:refines | ex:Lifetimes |
| R7-sibling-refines | retyped relatedTo | ex:ControlFlow | ex:refines | ex:StatementsAndExpressions |
| R7-sibling-refines | retyped relatedTo | ex:StatementsAndExpressions | ex:refines | ex:ControlFlow |
| R7-sibling-refines | retyped relatedTo | ex:Modules | ex:refines | ex:UseDeclarations |
| R7-sibling-refines | retyped relatedTo | ex:Traits_00traits | ex:refines | ex:DerivableTraits |
| R7-sibling-refines | retyped relatedTo | ex:Generics | ex:refines | ex:TypeLevelProgramming |
| R7-sibling-refines | retyped relatedTo | ex:InteriorMutability | ex:refines | ex:SmartPointers |
| R7-sibling-refines | retyped relatedTo | ex:CowAndBorrowed | ex:refines | ex:MemoryManagement |
| R7-sibling-refines | retyped relatedTo | ex:SmartPointers | ex:refines | ex:InteriorMutability |
| R7-sibling-refines | retyped relatedTo | ex:ErrorHandling_03errorhandl_1 | ex:refines | ex:ExceptionSafetyCVsRust |
| R7-sibling-refines | retyped relatedTo | ex:Modules_05modulesand | ex:refines | ex:IdiomaticRustAPINamingConventions |
| R7-sibling-refines | retyped relatedTo | ex:IdiomaticRustAPINamingConventions | ex:refines | ex:Modules_05modulesand |
| R7-sibling-refines | retyped relatedTo | ex:DslAndEmbedding | ex:refines | ex:Metaprogramming |
| R7-sibling-refines | retyped relatedTo | ex:Concurrency_00concurrenc_1 | ex:refines | ex:Concurrency_00concurrenc |
| R7-sibling-refines | retyped relatedTo | ex:Concurrency_00concurrenc_2 | ex:refines | ex:LockingPrimitives |
| R7-sibling-refines | retyped relatedTo | ex:Concurrency_01async | ex:refines | ex:AsyncCancellationSafety |
| R7-sibling-refines | retyped relatedTo | ex:AsyncCancellationSafety | ex:refines | ex:Concurrency_01async |
| R7-sibling-refines | retyped relatedTo | ex:StreamAlgebraAndBackpressure | ex:refines | ex:PinProjectionCounterexamples |
| R7-sibling-refines | retyped relatedTo | ex:ExecutorFairnessAndScheduling | ex:refines | ex:WakerContractDeepDive |
| R7-sibling-refines | retyped relatedTo | ex:PinProjectionCounterexamples | ex:refines | ex:StreamAlgebraAndBackpressure |
| R7-sibling-refines | retyped relatedTo | ex:UnsafeBoundaryPanorama | ex:refines | ex:UnsafeRust |
| R7-sibling-refines | retyped relatedTo | ex:ProceduralMacros | ex:refines | ex:MacroDebuggingAndDiagnostics |
| R7-sibling-refines | retyped relatedTo | ex:AdvancedProcessManagementInRust | ex:refines | ex:CrossPlatformProcessManagementInRust |
| R7-sibling-refines | retyped relatedTo | ex:AsyncProcessManagementInRust | ex:refines | ex:ProcessModelAndLifecycleInRust |
| R7-sibling-refines | retyped relatedTo | ex:CrossPlatformProcessManagementInRust | ex:refines | ex:AdvancedProcessManagementInRust |
| R7-sibling-refines | retyped relatedTo | ex:ProcessSecurityAndSandboxingInRust | ex:refines | ex:InterProcessCommunicationMechanismsInRust |
| R7-sibling-refines | retyped relatedTo | ex:AxiomaticSemantics | ex:refines | ex:FormalMethods_03operationa_1 |
| R7-sibling-refines | retyped relatedTo | ex:FormalMethodsMergedRedirect | ex:refines | ex:ModernVerificationTools |
| R7-sibling-refines | retyped relatedTo | ex:KaniRustBoundedModelChecker | ex:refines | ex:AutoVerusAndVerusAutomatedVerificationEcosystem |
| R7-sibling-refines | retyped relatedTo | ex:Destructors | ex:refines | ex:SpecialTypesAndTraits |
| R7-sibling-refines | retyped relatedTo | ex:RustVsC | ex:refines | ex:RustVsGo |
| R7-sibling-refines | retyped relatedTo | ex:RustVsGo | ex:refines | ex:RustVsC |
| R7-sibling-refines | retyped relatedTo | ex:CargoRegistriesAndPublishing | ex:refines | ex:CargoDependencyResolution |
| R7-sibling-refines | retyped relatedTo | ex:SystemDesignPrinciples | ex:refines | ex:DesignPatterns |
| R7-sibling-refines | retyped relatedTo | ex:MicroservicePatterns | ex:refines | ex:SystemDesignPrinciples |
| R7-sibling-refines | retyped relatedTo | ex:CqrsEventSourcing | ex:refines | ex:MicroservicePatterns |
| R7-sibling-refines | retyped relatedTo | ex:DesignPatterns_03designpatt | ex:refines | ex:EventDrivenArchitecture |
| R7-sibling-refines | retyped relatedTo | ex:DataEngineering | ex:refines | ex:StreamProcessingEcosystem |
| R7-sibling-refines | retyped relatedTo | ex:DistributedConsensus | ex:refines | ex:CRDTTypeZooStateBasedOpBasedAndTheMergeLattice |
| R7-sibling-refines | retyped relatedTo | ex:RustForDataScienceAndScientificComputing | ex:refines | ex:DataEngineering |
| R7-sibling-refines | retyped relatedTo | ex:RustNetworkProgrammingQuickStart | ex:refines | ex:NetworkSecurityInRust |
| R8-curated-appliesTo | added new edge | ex:ProceduralMacros | ex:appliesTo | ex:Macros |
| R8-curated-appliesTo | added new edge | ex:Futures | ex:appliesTo | ex:AsyncProgramming |
| R8-curated-appliesTo | added new edge | ex:PinAndUnpin | ex:appliesTo | ex:AsyncProgramming |