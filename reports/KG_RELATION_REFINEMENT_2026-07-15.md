# KG 关系语义精化报告

**日期**: 2026-07-15  **模式**: 已写回 kg_data_v3.json
**实体数**: 512  **关系数**: 7955 → 7132
**改动数**: 4918

## 目标

将 `ex:relatedTo` 占比从 81.0% 降到 <50%。
精化后：`ex:relatedTo` = 1559 / 7132 = **21.9%**

## 规则

| 规则 | 语义 | 说明 |
|:---|:---|:---|
| R0-dedup | 删除冗余 relatedTo | 若 (s,o) 已存在 dependsOn/entails，删除共存的 relatedTo |
| R1-metadata | dependsOn / entails | 正文链接命中源页前置/后置概念元数据 |
| R2-curated | mutexWith / counterExample / refines / appliesTo / instanceOf | 人工策展的语义对 |
| R3-directory | refines | 同目录同层相邻文件视为进阶/细分 |
| R4-layer | dependsOn / entails | 非索引内容页指向更低/更高 Bloom 层 |
| R5-index | hasPart / partOf | SUMMARY/README/atlas/navigation/mapping 等索引页与内容页的包含关系 |

## 谓词分布前后对比

### 全局 KG

| 谓词 | 前 | 后 | Δ |
|:---|---:|---:|---:|
| ex:hasPart | 0 | 3146 | +3146 |
| ex:relatedTo | 6446 | 1559 | -4887 |
| ex:dependsOn | 783 | 1299 | +516 |
| ex:entails | 726 | 1016 | +290 |
| ex:refines | 0 | 81 | +81 |
| ex:instanceOf | 0 | 13 | +13 |
| ex:mutexWith | 0 | 10 | +10 |
| ex:counterExample | 0 | 5 | +5 |
| ex:appliesTo | 0 | 3 | +3 |

## 关键指标

- `ex:relatedTo` 占比：81.0% → 21.9%
- `ex:relatedTo` 数量：6446 → 1559 (Δ -4887)
- 新增谓词：`ex:hasPart` / `ex:partOf`（用于索引-内容包含关系）

## 逐边改动摘要（前 200 条）

| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |
|:---|:---|:---|:---|:---|:---|
| R0-dedup | removed redundant relatedTo | ex:ComprehensiveRustMapping | ex:relatedTo | ex:LearningGuide | (ex:ComprehensiveRustMapping,ex:LearningGuide) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ComprehensiveRustMapping | ex:relatedTo | ex:BloomTaxonomy | (ex:ComprehensiveRustMapping,ex:BloomTaxonomy) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ComprehensiveRustMapping | ex:relatedTo | ex:ApplicationDomains | (ex:ComprehensiveRustMapping,ex:ApplicationDomains) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CCToRustEngineeringComparisonRoadmap | ex:relatedTo | ex:RustVsC | (ex:CCToRustEngineeringComparisonRoadmap,ex:RustVsC) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CCToRustEngineeringComparisonRoadmap | ex:relatedTo | ex:VariableModel | (ex:CCToRustEngineeringComparisonRoadmap,ex:VariableModel) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CCToRustEngineeringComparisonRoadmap | ex:relatedTo | ex:CAbiObjectModel | (ex:CCToRustEngineeringComparisonRoadmap,ex:CAbiObjectModel) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CCToRustEngineeringComparisonRoadmap | ex:relatedTo | ex:PatternSemanticSpaceIndex | (ex:CCToRustEngineeringComparisonRoadmap,ex:PatternSemanticSpaceIndex) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:PatternSemanticSpaceIndex | ex:relatedTo | ex:DesignPatterns | (ex:PatternSemanticSpaceIndex,ex:DesignPatterns) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:PatternSemanticSpaceIndex | ex:relatedTo | ex:AlgorithmsPatternsSemanticBridge | (ex:PatternSemanticSpaceIndex,ex:AlgorithmsPatternsSemanticBridge) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:PatternSemanticSpaceIndex | ex:relatedTo | ex:DesignPatterns_03designpatt_1 | (ex:PatternSemanticSpaceIndex,ex:DesignPatterns_03designpatt_1) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:PatternSemanticSpaceIndex | ex:relatedTo | ex:TypeSystem | (ex:PatternSemanticSpaceIndex,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GeneralPLFoundationsRoadmap | ex:relatedTo | ex:Ownership | (ex:GeneralPLFoundationsRoadmap,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:AlgorithmsPatternsSemanticBridge | ex:relatedTo | ex:AlgorithmsCompetitiveProgramming | (ex:AlgorithmsPatternsSemanticBridge,ex:AlgorithmsCompetitiveProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:TemplateDeduplicationGuide | ex:relatedTo | ex:ConceptConsistencyAuditChecklist | (ex:TemplateDeduplicationGuide,ex:ConceptConsistencyAuditChecklist) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CareerLandscape | ex:relatedTo | ex:BloomTaxonomy | (ex:CareerLandscape,ex:BloomTaxonomy) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CareerLandscape | ex:relatedTo | ex:ApplicationDomains | (ex:CareerLandscape,ex:ApplicationDomains) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:FoundationsGapClosureIndex | ex:relatedTo | ex:GeneralPLFoundationsRoadmap | (ex:FoundationsGapClosureIndex,ex:GeneralPLFoundationsRoadmap) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:FoundationsGapClosureIndex | ex:relatedTo | ex:CCToRustEngineeringComparisonRoadmap | (ex:FoundationsGapClosureIndex,ex:CCToRustEngineeringComparisonRoadmap) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:FoundationsGapClosureIndex | ex:relatedTo | ex:PatternSemanticSpaceIndex | (ex:FoundationsGapClosureIndex,ex:PatternSemanticSpaceIndex) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MetaFrameworkAndKnowledgeArchitectureQuiz | ex:relatedTo | ex:ConceptMetaLayer | (ex:MetaFrameworkAndKnowledgeArchitectureQuiz,ex:ConceptMetaLayer) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GettingStartedWithRust | ex:relatedTo | ex:Ownership | (ex:GettingStartedWithRust,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GettingStartedWithRust | ex:relatedTo | ex:Borrowing | (ex:GettingStartedWithRust,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GettingStartedWithRust | ex:relatedTo | ex:TypeSystem | (ex:GettingStartedWithRust,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GettingStartedWithRust | ex:relatedTo | ex:Modules | (ex:GettingStartedWithRust,ex:Modules) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GettingStartedWithRust | ex:relatedTo | ex:ErrorHandling | (ex:GettingStartedWithRust,ex:ErrorHandling) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GettingStartedWithRust | ex:relatedTo | ex:Testing | (ex:GettingStartedWithRust,ex:Testing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ZeroCostAbstractions | ex:relatedTo | ex:Generics | (ex:ZeroCostAbstractions,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ZeroCostAbstractions | ex:relatedTo | ex:Traits | (ex:ZeroCostAbstractions,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ZeroCostAbstractions | ex:relatedTo | ex:RustVsC | (ex:ZeroCostAbstractions,ex:RustVsC) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ZeroCostAbstractions | ex:relatedTo | ex:Toolchain | (ex:ZeroCostAbstractions,ex:Toolchain) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Closures | ex:relatedTo | ex:Traits | (ex:Closures,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Closures | ex:relatedTo | ex:Ownership | (ex:Closures,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Closures | ex:relatedTo | ex:Iterators | (ex:Closures,ex:Iterators) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Closures | ex:relatedTo | ex:AsyncProgramming | (ex:Closures,ex:AsyncProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Closures | ex:relatedTo | ex:ClosureTypes | (ex:Closures,ex:ClosureTypes) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:EffectsAndPurity | ex:relatedTo | ex:VariableModel | (ex:EffectsAndPurity,ex:VariableModel) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:EffectsAndPurity | ex:relatedTo | ex:EvaluationStrategies | (ex:EffectsAndPurity,ex:EvaluationStrategies) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:EffectsAndPurity | ex:relatedTo | ex:Ownership | (ex:EffectsAndPurity,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:EffectsAndPurity | ex:relatedTo | ex:Borrowing | (ex:EffectsAndPurity,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:EffectsAndPurity | ex:relatedTo | ex:EffectSystem | (ex:EffectsAndPurity,ex:EffectSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:EffectsAndPurity | ex:relatedTo | ex:AsyncProgramming | (ex:EffectsAndPurity,ex:AsyncProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Keywords | ex:relatedTo | ex:Modules | (ex:Keywords,ex:Modules) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Keywords | ex:relatedTo | ex:Macros | (ex:Keywords,ex:Macros) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OperatorsAndSymbols | ex:relatedTo | ex:TypeSystem | (ex:OperatorsAndSymbols,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OperatorsAndSymbols | ex:relatedTo | ex:Generics | (ex:OperatorsAndSymbols,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OperatorsAndSymbols | ex:relatedTo | ex:Macros_03procmacros | (ex:OperatorsAndSymbols,ex:Macros_03procmacros) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OwnershipBorrowingLifetimesKnowledgeMap | ex:relatedTo | ex:Ownership | (ex:OwnershipBorrowingLifetimesKnowledgeMap,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OwnershipBorrowingLifetimesKnowledgeMap | ex:relatedTo | ex:Borrowing | (ex:OwnershipBorrowingLifetimesKnowledgeMap,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OwnershipBorrowingLifetimesKnowledgeMap | ex:relatedTo | ex:Lifetimes | (ex:OwnershipBorrowingLifetimesKnowledgeMap,ex:Lifetimes) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OwnershipBorrowingLifetimesKnowledgeMap | ex:relatedTo | ex:SmartPointers | (ex:OwnershipBorrowingLifetimesKnowledgeMap,ex:SmartPointers) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:OwnershipBorrowingLifetimesKnowledgeMap | ex:relatedTo | ex:Concurrency | (ex:OwnershipBorrowingLifetimesKnowledgeMap,ex:Concurrency) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Ownership | ex:relatedTo | ex:Borrowing | (ex:Ownership,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Ownership | ex:relatedTo | ex:Lifetimes | (ex:Ownership,ex:Lifetimes) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Ownership | ex:relatedTo | ex:MemoryManagement | (ex:Ownership,ex:MemoryManagement) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Lifetimes | ex:relatedTo | ex:Ownership | (ex:Lifetimes,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Lifetimes | ex:relatedTo | ex:Borrowing | (ex:Lifetimes,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MoveSemantics | ex:relatedTo | ex:Ownership | (ex:MoveSemantics,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MoveSemantics | ex:relatedTo | ex:VariableModel | (ex:MoveSemantics,ex:VariableModel) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MoveSemantics | ex:relatedTo | ex:Borrowing | (ex:MoveSemantics,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MoveSemantics | ex:relatedTo | ex:LearningGuide | (ex:MoveSemantics,ex:LearningGuide) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MoveSemantics | ex:relatedTo | ex:RustVsC | (ex:MoveSemantics,ex:RustVsC) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MoveSemantics | ex:relatedTo | ex:ConstructionAndInitialization | (ex:MoveSemantics,ex:ConstructionAndInitialization) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:TypeSystem | ex:relatedTo | ex:Ownership | (ex:TypeSystem,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:NeverType | ex:relatedTo | ex:TypeSystem | (ex:NeverType,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:NeverType | ex:relatedTo | ex:ErrorHandling | (ex:NeverType,ex:ErrorHandling) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Numerics | ex:relatedTo | ex:TypeSystem | (ex:Numerics,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Numerics | ex:relatedTo | ex:ZeroCostAbstractions | (ex:Numerics,ex:ZeroCostAbstractions) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Numerics | ex:relatedTo | ex:Collections | (ex:Numerics,ex:Collections) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CoercionAndCasting | ex:relatedTo | ex:TypeSystem | (ex:CoercionAndCasting,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CoercionAndCasting | ex:relatedTo | ex:Traits | (ex:CoercionAndCasting,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CoercionAndCasting | ex:relatedTo | ex:Generics | (ex:CoercionAndCasting,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CoercionAndCasting | ex:relatedTo | ex:ForeignFunctionInterfaceFFI | (ex:CoercionAndCasting,ex:ForeignFunctionInterfaceFFI) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:DataAbstractionSpectrum | ex:relatedTo | ex:TypeSystem | (ex:DataAbstractionSpectrum,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:DataAbstractionSpectrum | ex:relatedTo | ex:Traits | (ex:DataAbstractionSpectrum,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:DataAbstractionSpectrum | ex:relatedTo | ex:Ownership | (ex:DataAbstractionSpectrum,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ReferenceSemantics | ex:relatedTo | ex:Ownership | (ex:ReferenceSemantics,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ReferenceSemantics | ex:relatedTo | ex:Borrowing | (ex:ReferenceSemantics,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ReferenceSemantics | ex:relatedTo | ex:TypeSystem | (ex:ReferenceSemantics,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ReferenceSemantics | ex:relatedTo | ex:MemoryManagement | (ex:ReferenceSemantics,ex:MemoryManagement) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ReferenceSemantics | ex:relatedTo | ex:Generics | (ex:ReferenceSemantics,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ValueSemanticsVsReferenceSemantics | ex:relatedTo | ex:VariableModel | (ex:ValueSemanticsVsReferenceSemantics,ex:VariableModel) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ValueSemanticsVsReferenceSemantics | ex:relatedTo | ex:MoveSemantics | (ex:ValueSemanticsVsReferenceSemantics,ex:MoveSemantics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ValueSemanticsVsReferenceSemantics | ex:relatedTo | ex:Ownership | (ex:ValueSemanticsVsReferenceSemantics,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:VariableModel | ex:relatedTo | ex:Ownership | (ex:VariableModel,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ControlFlow | ex:relatedTo | ex:Ownership | (ex:ControlFlow,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ControlFlow | ex:relatedTo | ex:TypeSystem | (ex:ControlFlow,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ControlFlow | ex:relatedTo | ex:Generics | (ex:ControlFlow,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ControlFlow | ex:relatedTo | ex:AsyncProgramming | (ex:ControlFlow,ex:AsyncProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Patterns | ex:relatedTo | ex:StatementsAndExpressions | (ex:Patterns,ex:StatementsAndExpressions) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StatementsAndExpressions | ex:relatedTo | ex:Closures | (ex:StatementsAndExpressions,ex:Closures) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StatementsAndExpressions | ex:relatedTo | ex:ErrorHandling_03errorhandl | (ex:StatementsAndExpressions,ex:ErrorHandling_03errorhandl) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StatementsAndExpressions | ex:relatedTo | ex:AsyncProgramming | (ex:StatementsAndExpressions,ex:AsyncProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Collections | ex:relatedTo | ex:Ownership | (ex:Collections,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Collections | ex:relatedTo | ex:SmartPointers | (ex:Collections,ex:SmartPointers) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CollectionsAdvanced | ex:relatedTo | ex:Collections | (ex:CollectionsAdvanced,ex:Collections) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CollectionsAdvanced | ex:relatedTo | ex:PerformanceOptimization | (ex:CollectionsAdvanced,ex:PerformanceOptimization) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CollectionsAdvanced | ex:relatedTo | ex:SmartPointers | (ex:CollectionsAdvanced,ex:SmartPointers) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndText | ex:relatedTo | ex:Ownership | (ex:StringsAndText,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndText | ex:relatedTo | ex:Borrowing | (ex:StringsAndText,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndText | ex:relatedTo | ex:Collections | (ex:StringsAndText,ex:Collections) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndText | ex:relatedTo | ex:ForeignFunctionInterfaceFFI | (ex:StringsAndText,ex:ForeignFunctionInterfaceFFI) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndText | ex:relatedTo | ex:TypeSystem | (ex:StringsAndText,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndEncoding | ex:relatedTo | ex:Ownership | (ex:StringsAndEncoding,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndEncoding | ex:relatedTo | ex:TypeSystem | (ex:StringsAndEncoding,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndEncoding | ex:relatedTo | ex:Collections | (ex:StringsAndEncoding,ex:Collections) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:StringsAndEncoding | ex:relatedTo | ex:ForeignFunctionInterfaceFFI | (ex:StringsAndEncoding,ex:ForeignFunctionInterfaceFFI) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Modules | ex:relatedTo | ex:Ownership | (ex:Modules,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Modules | ex:relatedTo | ex:TypeSystem | (ex:Modules,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Modules | ex:relatedTo | ex:CoreCrates | (ex:Modules,ex:CoreCrates) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Modules | ex:relatedTo | ex:Toolchain | (ex:Modules,ex:Toolchain) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Functions | ex:relatedTo | ex:Closures | (ex:Functions,ex:Closures) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Functions | ex:relatedTo | ex:StatementsAndExpressions | (ex:Functions,ex:StatementsAndExpressions) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Functions | ex:relatedTo | ex:Ownership | (ex:Functions,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:UseDeclarations | ex:relatedTo | ex:Modules | (ex:UseDeclarations,ex:Modules) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:UseDeclarations | ex:relatedTo | ex:Items | (ex:UseDeclarations,ex:Items) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Structs | ex:relatedTo | ex:Enumerations | (ex:Structs,ex:Enumerations) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Structs | ex:relatedTo | ex:Implementations | (ex:Structs,ex:Implementations) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Enumerations | ex:relatedTo | ex:ErrorHandling | (ex:Enumerations,ex:ErrorHandling) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Enumerations | ex:relatedTo | ex:Structs | (ex:Enumerations,ex:Structs) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Enumerations | ex:relatedTo | ex:Patterns | (ex:Enumerations,ex:Patterns) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Enumerations | ex:relatedTo | ex:TypeSystem | (ex:Enumerations,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Implementations | ex:relatedTo | ex:Traits_00traits | (ex:Implementations,ex:Traits_00traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Implementations | ex:relatedTo | ex:Structs | (ex:Implementations,ex:Structs) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Implementations | ex:relatedTo | ex:Enumerations | (ex:Implementations,ex:Enumerations) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Implementations | ex:relatedTo | ex:Traits | (ex:Implementations,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Preludes | ex:relatedTo | ex:SafeAndEffectiveUnsafeRust | (ex:Preludes,ex:SafeAndEffectiveUnsafeRust) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Preludes | ex:relatedTo | ex:Linkage | (ex:Preludes,ex:Linkage) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CratesAndSourceFiles | ex:relatedTo | ex:Items | (ex:CratesAndSourceFiles,ex:Items) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CratesAndSourceFiles | ex:relatedTo | ex:CargoWorkspaces | (ex:CratesAndSourceFiles,ex:CargoWorkspaces) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CratesAndSourceFiles | ex:relatedTo | ex:CargoManifestReference | (ex:CratesAndSourceFiles,ex:CargoManifestReference) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CratesAndSourceFiles | ex:relatedTo | ex:Linkage | (ex:CratesAndSourceFiles,ex:Linkage) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CratesAndSourceFiles | ex:relatedTo | ex:TheRustRuntime | (ex:CratesAndSourceFiles,ex:TheRustRuntime) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Items | ex:relatedTo | ex:Traits | (ex:Items,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Items | ex:relatedTo | ex:Generics | (ex:Items,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Items | ex:relatedTo | ex:SafeAndEffectiveUnsafeRust | (ex:Items,ex:SafeAndEffectiveUnsafeRust) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Items | ex:relatedTo | ex:ForeignFunctionInterfaceFFI | (ex:Items,ex:ForeignFunctionInterfaceFFI) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Items | ex:relatedTo | ex:Linkage | (ex:Items,ex:Linkage) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ErrorHandling | ex:relatedTo | ex:Ownership | (ex:ErrorHandling,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ErrorHandling | ex:relatedTo | ex:ErrorHandling_03errorhandl | (ex:ErrorHandling,ex:ErrorHandling_03errorhandl) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ErrorHandlingControlFlow | ex:relatedTo | ex:ErrorHandling_03errorhandl | (ex:ErrorHandlingControlFlow,ex:ErrorHandling_03errorhandl) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ErrorHandlingControlFlow | ex:relatedTo | ex:ErrorHandling | (ex:ErrorHandlingControlFlow,ex:ErrorHandling) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:PanicAndAbort | ex:relatedTo | ex:ErrorHandling_03errorhandl_1 | (ex:PanicAndAbort,ex:ErrorHandling_03errorhandl_1) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:PanicAndAbort | ex:relatedTo | ex:SafeAndEffectiveUnsafeRust | (ex:PanicAndAbort,ex:SafeAndEffectiveUnsafeRust) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:PanicAndAbort | ex:relatedTo | ex:ForeignFunctionInterfaceFFI | (ex:PanicAndAbort,ex:ForeignFunctionInterfaceFFI) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Macros | ex:relatedTo | ex:TypeSystem | (ex:Macros,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Macros | ex:relatedTo | ex:Modules | (ex:Macros,ex:Modules) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Macros | ex:relatedTo | ex:ProceduralMacros | (ex:Macros,ex:ProceduralMacros) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Macros | ex:relatedTo | ex:DslAndEmbedding | (ex:Macros,ex:DslAndEmbedding) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Testing | ex:relatedTo | ex:Testing_09testingand_1 | (ex:Testing,ex:Testing_09testingand_1) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:UsefulDevelopmentTools | ex:relatedTo | ex:Testing | (ex:UsefulDevelopmentTools,ex:Testing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:TypeSystem_11quizzes | ex:relatedTo | ex:TypeSystem | (ex:TypeSystem_11quizzes,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ErrorHandling_11quizzes | ex:relatedTo | ex:ErrorHandling | (ex:ErrorHandling_11quizzes,ex:ErrorHandling) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Modules_11quizzes | ex:relatedTo | ex:Modules | (ex:Modules_11quizzes,ex:Modules) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Closures_11quizzes | ex:relatedTo | ex:Closures | (ex:Closures_11quizzes,ex:Closures) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Ownership_11quizzes | ex:relatedTo | ex:Borrowing | (ex:Ownership_11quizzes,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Traits | ex:relatedTo | ex:Generics | (ex:Traits,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Traits | ex:relatedTo | ex:TypeSystem | (ex:Traits,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:DispatchMechanisms | ex:relatedTo | ex:Traits | (ex:DispatchMechanisms,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:SerdePatterns | ex:relatedTo | ex:Traits | (ex:SerdePatterns,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:SerdePatterns | ex:relatedTo | ex:Macros_03procmacros | (ex:SerdePatterns,ex:Macros_03procmacros) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:SerdePatterns | ex:relatedTo | ex:Generics | (ex:SerdePatterns,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:SerdePatterns | ex:relatedTo | ex:CoreCrates | (ex:SerdePatterns,ex:CoreCrates) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:SerdePatterns | ex:relatedTo | ex:ApplicationDomains | (ex:SerdePatterns,ex:ApplicationDomains) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Traits_00traits | ex:relatedTo | ex:Traits | (ex:Traits_00traits,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Traits_00traits | ex:relatedTo | ex:Generics | (ex:Traits_00traits,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Traits_00traits | ex:relatedTo | ex:TypeSystem | (ex:Traits_00traits,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Traits_00traits | ex:relatedTo | ex:TypeInference | (ex:Traits_00traits,ex:TypeInference) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Traits_00traits | ex:relatedTo | ex:RustBelt_02separation | (ex:Traits_00traits,ex:RustBelt_02separation) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstructionAndInitialization | ex:relatedTo | ex:Ownership | (ex:ConstructionAndInitialization,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:DerivableTraits | ex:relatedTo | ex:Traits_00traits | (ex:DerivableTraits,ex:Traits_00traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:DerivableTraits | ex:relatedTo | ex:ProceduralMacros | (ex:DerivableTraits,ex:ProceduralMacros) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GenericAssociatedTypesGATs | ex:relatedTo | ex:Traits | (ex:GenericAssociatedTypesGATs,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GenericAssociatedTypesGATs | ex:relatedTo | ex:LifetimesAdvanced | (ex:GenericAssociatedTypesGATs,ex:LifetimesAdvanced) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:GenericAssociatedTypesGATs | ex:relatedTo | ex:Generics | (ex:GenericAssociatedTypesGATs,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Generics | ex:relatedTo | ex:AsyncProgramming | (ex:Generics,ex:AsyncProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Generics | ex:relatedTo | ex:Traits | (ex:Generics,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Generics | ex:relatedTo | ex:TypeSystem | (ex:Generics,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Generics | ex:relatedTo | ex:Lifetimes | (ex:Generics,ex:Lifetimes) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsValuesAsTypeParameters | ex:relatedTo | ex:TypeLevelProgramming | (ex:ConstGenericsValuesAsTypeParameters,ex:TypeLevelProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsValuesAsTypeParameters | ex:relatedTo | ex:Generics | (ex:ConstGenericsValuesAsTypeParameters,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsValuesAsTypeParameters | ex:relatedTo | ex:ConstTraitImplPreview | (ex:ConstGenericsValuesAsTypeParameters,ex:ConstTraitImplPreview) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsValuesAsTypeParameters | ex:relatedTo | ex:Traits | (ex:ConstGenericsValuesAsTypeParameters,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsValuesAsTypeParameters | ex:relatedTo | ex:TypeSystem | (ex:ConstGenericsValuesAsTypeParameters,ex:TypeSystem) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsValuesAsTypeParameters | ex:relatedTo | ex:StatementsAndExpressions | (ex:ConstGenericsValuesAsTypeParameters,ex:StatementsAndExpressions) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:TypeLevelProgramming | ex:relatedTo | ex:Generics | (ex:TypeLevelProgramming,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:TypeLevelProgramming | ex:relatedTo | ex:Traits | (ex:TypeLevelProgramming,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:Generics_01generics | ex:relatedTo | ex:Traits | (ex:Generics_01generics,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsAndTraitObjects | ex:relatedTo | ex:Generics | (ex:ConstGenericsAndTraitObjects,ex:Generics) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsAndTraitObjects | ex:relatedTo | ex:ConstGenericsValuesAsTypeParameters | (ex:ConstGenericsAndTraitObjects,ex:ConstGenericsValuesAsTypeParameters) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsAndTraitObjects | ex:relatedTo | ex:Traits | (ex:ConstGenericsAndTraitObjects,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsAndTraitObjects | ex:relatedTo | ex:DispatchMechanisms | (ex:ConstGenericsAndTraitObjects,ex:DispatchMechanisms) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsAndTraitObjects | ex:relatedTo | ex:GenericAssociatedTypesGATs | (ex:ConstGenericsAndTraitObjects,ex:GenericAssociatedTypesGATs) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:ConstGenericsAndTraitObjects | ex:relatedTo | ex:TypeLevelProgramming | (ex:ConstGenericsAndTraitObjects,ex:TypeLevelProgramming) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MemoryManagement | ex:relatedTo | ex:Ownership | (ex:MemoryManagement,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:MemoryManagement | ex:relatedTo | ex:SafeAndEffectiveUnsafeRust | (ex:MemoryManagement,ex:SafeAndEffectiveUnsafeRust) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:InteriorMutability | ex:relatedTo | ex:Ownership | (ex:InteriorMutability,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:InteriorMutability | ex:relatedTo | ex:Concurrency | (ex:InteriorMutability,ex:Concurrency) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CowAndBorrowed | ex:relatedTo | ex:Ownership | (ex:CowAndBorrowed,ex:Ownership) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CowAndBorrowed | ex:relatedTo | ex:Borrowing | (ex:CowAndBorrowed,ex:Borrowing) 已存在 dependsOn/entails，删除冗余 relatedTo |
| R0-dedup | removed redundant relatedTo | ex:CowAndBorrowed | ex:relatedTo | ex:Traits | (ex:CowAndBorrowed,ex:Traits) 已存在 dependsOn/entails，删除冗余 relatedTo |
| ... | ... | ... | ... | ... | 共 4918 条，详见 JSON |

## 机器可读

- JSON: `reports/KG_RELATION_REFINEMENT_2026-07-15.json`
