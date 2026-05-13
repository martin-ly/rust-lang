# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-13T22:18
> 扫描文件数: 41
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 41 | — |
| 跨文件链接 ≥3 | 36/41 | ⚠️ |
| 死链接文件 | 0 | ✅ |
| 命名规范符合 | 29/41 | ⚠️ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 41/41 | ✅ |
| 平均来源标注率 | 10.5% | ⚠️ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 240 | — |

## 跨文件链接不足的文件

| 文件 | 链接数 | 现有链接目标 |
|:---|:---|:---|
| concept/00_meta/audit_checklist.md | 0 | 无 |
| concept/00_meta/inter_layer_map.md | 0 | 无 |
| concept/00_meta/methodology.md | 0 | 无 |
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
- concept/00_meta/semantic_space.md
- concept/00_meta/sources.md
- concept/00_meta/todos.md
- concept/05_comparative/safety_boundaries.md
- concept/07_future/rust_version_tracking.md

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/00_meta/audit_checklist.md | 0 | 33 | 0.0% |
| concept/00_meta/concept_index.md | 0 | 62 | 0.0% |
| concept/00_meta/inter_layer_map.md | 10 | 59 | 9.9% |
| concept/00_meta/learning_guide.md | 0 | 48 | 0.0% |
| concept/00_meta/methodology.md | 5 | 46 | 5.0% |
| concept/00_meta/quick_reference.md | 0 | 115 | 0.0% |
| concept/00_meta/self_assessment.md | 0 | 399 | 0.0% |
| concept/00_meta/semantic_space.md | 23 | 179 | 7.8% |
| concept/00_meta/todos.md | 0 | 23 | 0.0% |
| concept/05_comparative/01_rust_vs_cpp.md | 32 | 472 | 4.5% |
| concept/06_ecosystem/01_toolchain.md | 15 | 184 | 4.4% |
| concept/06_ecosystem/02_patterns.md | 13 | 171 | 4.2% |
| concept/06_ecosystem/03_core_crates.md | 17 | 199 | 4.2% |
| concept/06_ecosystem/04_application_domains.md | 39 | 250 | 7.4% |
| concept/07_future/01_ai_integration.md | 10 | 147 | 4.0% |
| concept/07_future/02_formal_methods.md | 17 | 194 | 5.1% |
| concept/07_future/03_evolution.md | 7 | 147 | 2.8% |
| concept/07_future/04_effects_system.md | 6 | 57 | 5.8% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。