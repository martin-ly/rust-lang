# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-26T17:17
> 扫描文件数: 245
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 245 | — |
| 跨文件链接 ≥3 | 245/245 | ✅ |
| 死链接文件 | 0 | ✅ |
| 命名规范符合 | 245/245 | ✅ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 245/245 | ✅ |
| 平均来源标注率 | 16.1% | ✅ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 242 | — |

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/00_meta/semantic_bridge_algorithms_patterns.md | 4 | 38 | 2.4% |
| concept/03_advanced/19_parallel_distributed_pattern_spectrum.md | 16 | 130 | 6.8% |
| concept/03_advanced/20_stream_processing_semantics.md | 26 | 126 | 8.2% |
| concept/05_comparative/01_rust_vs_cpp.md | 54 | 493 | 7.2% |
| concept/05_comparative/02_cpp_abi_object_model.md | 22 | 114 | 8.5% |
| concept/06_ecosystem/30_system_composability.md | 23 | 155 | 9.1% |
| concept/06_ecosystem/31_microservice_patterns.md | 25 | 118 | 9.8% |
| concept/06_ecosystem/35_pattern_composition_algebra.md | 6 | 107 | 3.0% |
| concept/07_future/29_ebpf_rust.md | 16 | 143 | 6.1% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。