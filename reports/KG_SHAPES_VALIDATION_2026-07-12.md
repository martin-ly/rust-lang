# KG SHACL 子集校验（语义质量门 P3-4）

**日期**: 2026-07-12  **实体**: 491  **关系**: 5853  **决策树**: 3  **故障树**: 2

| 规则 | 命中 | 阈值 | 判定 |
|---|:---:|:---:|:---:|
| K1 缺必填字段 | 0 | 0 | pass |
| K1b 缺 ex:bloomLevel | 0 | 记录 | 记录 |
| K2 path 文件不存在 | 0 | 0 | pass |
| K3 prefLabel 非双语 | 0 | 0 | pass |
| K4 @id 重复 | 0 | 0 | pass |
| K5 关系悬空引用 | 0 | 0 | pass |
| K6 树节点不完整 | 0 | 0 | pass |
| K7 缺 ex:layer/ex:domain | 0 | 0 | pass |

关系结构样例: `{"@id": "_:rel1", "@type": "ex:RelationAnnotation", "ex:subject": "ex:ComprehensiveRustMapping", "ex:predicate": "ex:dependsOn", "ex:object": "ex:LearningGuide", "ex:source": "prerequisite:../04_navigation/learning_guide.md", "ex:confidence": 1.0, "ex:version": "1.97.0", "ex:reviewed": false, "dcter`

## WOULD-FAIL（--strict 阻断）

- 无

## 机器可读

- JSON: `reports/KG_SHAPES_VALIDATION_2026-07-12.json`
