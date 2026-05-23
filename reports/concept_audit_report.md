# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-23T17:46
> 扫描文件数: 185
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 185 | — |
| 跨文件链接 ≥3 | 175/185 | ⚠️ |
| 死链接文件 | 0 | ✅ |
| 命名规范符合 | 185/185 | ✅ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 185/185 | ✅ |
| 平均来源标注率 | 34.0% | ✅ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 248 | — |

## 跨文件链接不足的文件

| 文件 | 链接数 | 现有链接目标 |
|:---|:---|:---|
| concept/00_meta/asp_marking_guide.md | 0 | 无 |
| concept/00_meta/cognitive_dimension_matrix.md | 0 | 无 |
| concept/00_meta/competency_graph.md | 0 | 无 |
| concept/00_meta/concept_definition_decision_forest.md | 0 | 无 |
| concept/00_meta/fault_tree_analysis_collection.md | 0 | 无 |
| concept/00_meta/kg_ontology.md | 0 | 无 |
| concept/00_meta/paradigm_transition_matrix.md | 0 | 无 |
| concept/00_meta/problem_graph.md | 0 | 无 |
| concept/00_meta/quality_dashboard_v2.md | 0 | 无 |
| concept/00_meta/rustbelt_predicate_map.md | 0 | 无 |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。
