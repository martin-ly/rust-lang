# KG 通用谓词回退报告

**日期**: 2026-07-16

- 回退关系数: 563
- 操作: 将 `ex:RelationAnnotation` 改为 `ex:relatedTo`（schema 兜底弱语义谓词）
- 原因: apply_kg_semantic_predicates.py 全部批次处理后仍有残留通用谓词，
  这些边缺乏 atlas 符号或强前置/后置信号，不宜强制指定为 dependsOn/entails/refines 等强谓词。
