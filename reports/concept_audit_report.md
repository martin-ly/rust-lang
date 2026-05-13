# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-14T02:18
> 扫描文件数: 45
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 45 | — |
| 跨文件链接 ≥3 | 39/45 | ⚠️ |
| 死链接文件 | 0 | ✅ |
| 命名规范符合 | 32/45 | ⚠️ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 45/45 | ✅ |
| 平均来源标注率 | 14.2% | ⚠️ |
| TODO 待完成 | 8 | ⚠️ |
| TODO 已完成 | 240 | — |

## 跨文件链接不足的文件

| 文件 | 链接数 | 现有链接目标 |
|:---|:---|:---|
| concept/00_meta/audit_checklist.md | 0 | 无 |
| concept/00_meta/inter_layer_map.md | 0 | 无 |
| concept/00_meta/methodology.md | 0 | 无 |
| concept/00_meta/semantic_expressiveness.md | 0 | 无 |
| concept/00_meta/sources.md | 0 | 无 |
| concept/00_meta/todos.md | 0 | 无 |

## 命名不规范的文件

- concept/00_meta/audit_checklist.md
- concept/00_meta/concept_index.md
- concept/00_meta/inter_layer_map.md
- concept/00_meta/learning_guide.md
- concept/00_meta/methodology.md
- concept/00_meta/quick_reference.md
- concept/00_meta/self_assessment.md
- concept/00_meta/semantic_expressiveness.md
- concept/00_meta/semantic_space.md
- concept/00_meta/sources.md
- concept/00_meta/todos.md
- concept/05_comparative/safety_boundaries.md
- concept/07_future/rust_version_tracking.md

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/00_meta/audit_checklist.md | 3 | 34 | 3.8% |
| concept/00_meta/concept_index.md | 0 | 67 | 0.0% |
| concept/00_meta/learning_guide.md | 14 | 70 | 9.9% |
| concept/00_meta/methodology.md | 5 | 46 | 5.0% |
| concept/00_meta/quick_reference.md | 0 | 115 | 0.0% |
| concept/00_meta/self_assessment.md | 16 | 406 | 2.5% |
| concept/00_meta/todos.md | 0 | 23 | 0.0% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。
