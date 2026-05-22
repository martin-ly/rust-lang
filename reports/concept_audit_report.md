# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-22T09:28
> 扫描文件数: 109
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 109 | — |
| 跨文件链接 ≥3 | 109/109 | ✅ |
| 死链接文件 | 1 | ❌ |
| 命名规范符合 | 107/109 | ⚠️ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 109/109 | ✅ |
| 平均来源标注率 | 14.7% | ⚠️ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 261 | — |

## 死链接检测

| 源文件 | 链接文本 | 死链接目标 |
|:---|:---|:---|
| concept/06_ecosystem/18_distributed_systems.md | Network | `../04_networks/01_networks.md` |
| concept/06_ecosystem/18_distributed_systems.md | Network | `../04_networks.md` |

## 命名不规范的文件

- concept/07_future/borrowsanitizer_preview.md
- concept/07_future/open_enums_preview.md

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/01_foundation/09_strings_and_text.md | 15 | 82 | 9.3% |
| concept/02_intermediate/08_interior_mutability.md | 19 | 73 | 9.7% |
| concept/02_intermediate/09_serde_patterns.md | 17 | 79 | 9.7% |
| concept/02_intermediate/11_cow_and_borrowed.md | 15 | 72 | 9.6% |
| concept/02_intermediate/13_dsl_and_embedding.md | 8 | 79 | 5.0% |
| concept/02_intermediate/14_newtype_and_wrapper.md | 13 | 79 | 8.1% |
| concept/06_ecosystem/11_webassembly.md | 13 | 55 | 8.0% |
| concept/06_ecosystem/13_logging_observability.md | 14 | 67 | 8.6% |
| concept/06_ecosystem/15_performance_optimization.md | 15 | 78 | 9.3% |
| concept/06_ecosystem/16_testing.md | 14 | 76 | 8.0% |
| concept/06_ecosystem/18_distributed_systems.md | 13 | 82 | 7.8% |
| concept/07_future/07_mcdc_coverage_preview.md | 9 | 40 | 6.0% |
| concept/07_future/09_parallel_frontend_preview.md | 13 | 41 | 9.5% |
| concept/07_future/13_unsafe_fields_preview.md | 16 | 56 | 9.9% |
| concept/07_future/14_ferrocene_preview.md | 13 | 47 | 9.9% |
| concept/07_future/16_cranelift_backend_preview.md | 13 | 46 | 9.8% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。