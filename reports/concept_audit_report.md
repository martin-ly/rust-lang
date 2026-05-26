# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-26T12:08
> 扫描文件数: 239
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 239 | — |
| 跨文件链接 ≥3 | 232/239 | ⚠️ |
| 死链接文件 | 0 | ✅ |
| 命名规范符合 | 238/239 | ⚠️ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 239/239 | ✅ |
| 平均来源标注率 | 15.9% | ✅ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 242 | — |

## 跨文件链接不足的文件

| 文件 | 链接数 | 现有链接目标 |
|:---|:---|:---|
| concept/00_meta/03_bloom_taxonomy.md | 0 | 无 |
| concept/00_meta/05_cross_reference_matrix.md | 1 | ./README.md |
| concept/00_meta/08_concept_audit_guide.md | 0 | 无 |
| concept/03_advanced/02_async_programming.md | 2 | ./02_async.md, ./02_async_patterns.md |
| concept/03_advanced/13_async_patterns.md | 1 | ./02_async_patterns.md |
| concept/04_formal/07_separation_logic.md | 1 | ./11_separation_logic.md |
| concept/04_formal/09_operational_semantics.md | 1 | ./17_operational_semantics.md |

## 命名不规范的文件

- concept/07_future/19_rust_2024_edition_preview.md

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/00_meta/semantic_bridge_algorithms_patterns.md | 4 | 38 | 2.6% |
| concept/03_advanced/19_parallel_distributed_pattern_spectrum.md | 9 | 125 | 4.1% |
| concept/03_advanced/20_stream_processing_semantics.md | 19 | 121 | 6.3% |
| concept/05_comparative/01_rust_vs_cpp.md | 54 | 493 | 7.3% |
| concept/05_comparative/02_cpp_abi_object_model.md | 22 | 114 | 8.5% |
| concept/06_ecosystem/35_pattern_composition_algebra.md | 6 | 107 | 3.0% |
| concept/06_ecosystem/39_os_kernel.md | 12 | 60 | 7.5% |
| concept/06_ecosystem/41_workflow_theory.md | 52 | 148 | 10.0% |
| concept/06_ecosystem/48_data_engineering.md | 33 | 127 | 10.0% |
| concept/07_future/29_ebpf_rust.md | 16 | 143 | 6.1% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。
