# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-22T04:40
> 扫描文件数: 69
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 69 | — |
| 跨文件链接 ≥3 | 69/69 | ✅ |
| 死链接文件 | 0 | ✅ |
| 命名规范符合 | 67/69 | ⚠️ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 69/69 | ✅ |
| 平均来源标注率 | 16.1% | ✅ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 261 | — |

## 命名不规范的文件

- concept/07_future/borrowsanitizer_preview.md
- concept/07_future/open_enums_preview.md

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/07_future/07_mcdc_coverage_preview.md | 9 | 40 | 6.0% |
| concept/07_future/09_parallel_frontend_preview.md | 13 | 41 | 9.5% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。
