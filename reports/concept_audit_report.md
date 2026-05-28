# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-28T20:45
> 扫描文件数: 241
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 241 | — |
| 跨文件链接 ≥3 | 241/241 | ✅ |
| 死链接文件 | 9 | ❌ |
| 命名规范符合 | 241/241 | ✅ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 241/241 | ✅ |
| 平均来源标注率 | 16.7% | ✅ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 242 | — |

## 死链接检测

| 源文件 | 链接文本 | 死链接目标 |
|:---|:---|:---|
| concept/00_meta/asp_marking_guide.md | 概念判定森林 | `concept_definition_decision_forest.md` |
| concept/00_meta/fault_tree_analysis_collection.md | 概念判定森林 | `concept_definition_decision_forest.md` |
| concept/00_meta/navigation.md | concept_definition_decision_forest | `concept_definition_decision_forest.md` |
| concept/00_meta/problem_graph.md | 概念判定森林 | `concept_definition_decision_forest.md` |
| concept/00_meta/rustbelt_predicate_map.md | 概念判定森林 | `concept_definition_decision_forest.md` |
| concept/01_foundation/10_error_handling_basics.md | Logging | `../06_ecosystem/13_logging_observability.md` |
| concept/01_foundation/10_error_handling_basics.md | Logging | `../06_ecosystem/13_logging_observability.md` |
| concept/02_intermediate/15_error_handling_deep_dive.md | Logging | `../06_ecosystem/13_logging_observability.md` |
| concept/06_ecosystem/18_distributed_systems.md | Observability | `./13_logging_observability.md` |
| concept/07_future/24_roadmap.md | Edition Guide | `23_rust_edition_guide.md` |
| concept/07_future/24_roadmap.md | Edition Guide | `23_rust_edition_guide.md` |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。
