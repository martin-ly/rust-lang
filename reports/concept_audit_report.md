# 概念知识体系自动化审计报告 v2.0

> 生成时间: 2026-05-24T19:13
> 扫描文件数: 225
> 版本对齐: Rust 1.95.0 stable

## 摘要

| 指标 | 数值 | 状态 |
|:---|:---|:---|
| 扫描文件数 | 225 | — |
| 跨文件链接 ≥3 | 207/225 | ⚠️ |
| 死链接文件 | 1 | ❌ |
| 命名规范符合 | 224/225 | ⚠️ |
| 代码块问题文件 | 0 | ✅ |
| 显式 Bloom 标注 | 208/225 | ✅ |
| 平均来源标注率 | 30.3% | ✅ |
| TODO 待完成 | 0 | ✅ |
| TODO 已完成 | 258 | — |

## 跨文件链接不足的文件

| 文件 | 链接数 | 现有链接目标 |
|:---|:---|:---|
| concept/00_meta/03_bloom_taxonomy.md | 0 | 无 |
| concept/00_meta/05_cross_reference_matrix.md | 1 | nonexistent_file.md |
| concept/00_meta/08_concept_audit_guide.md | 0 | 无 |
| concept/03_advanced/02_async_programming.md | 0 | 无 |
| concept/03_advanced/03_unsafe_rust.md | 0 | 无 |
| concept/03_advanced/05_macros.md | 0 | 无 |
| concept/03_advanced/08_zero_cost_abstractions.md | 0 | 无 |
| concept/07_future/11_stable_abi_preview.md | 0 | 无 |
| concept/07_future/12_inline_const_pattern_preview.md | 0 | 无 |
| concept/07_future/13_must_not_suspend_preview.md | 0 | 无 |
| concept/07_future/14_lifetime_capture_preview.md | 0 | 无 |
| concept/07_future/15_rpitit_preview.md | 0 | 无 |
| concept/07_future/16_type_alias_impl_trait_preview.md | 0 | 无 |
| concept/07_future/17_const_trait_preview.md | 0 | 无 |
| concept/07_future/19_rust_2024_edition_preview.md | 0 | 无 |
| concept/07_future/22_gen_blocks_preview.md | 0 | 无 |
| concept/07_future/24_wasm_target_evolution.md | 0 | 无 |
| concept/07_future/26_rust_in_space.md | 0 | 无 |

## 死链接检测

| 源文件 | 链接文本 | 死链接目标 |
|:---|:---|:---|
| concept/00_meta/05_cross_reference_matrix.md | 不存在的概念 | `nonexistent_file.md` |

## 命名不规范的文件

- concept/07_future/19_rust_2024_edition_preview.md

## 缺少 Bloom 层级标注的文件

| 文件 | 检测到的 Bloom 关键词 |
|:---|:---|
| concept/00_meta/05_cross_reference_matrix.md | 分析, 评价 |
| concept/00_meta/08_concept_audit_guide.md | 无 |
| concept/03_advanced/02_async_programming.md | 无 |
| concept/03_advanced/03_unsafe_rust.md | 应用 |
| concept/03_advanced/05_macros.md | 应用 |
| concept/03_advanced/08_zero_cost_abstractions.md | 应用 |
| concept/07_future/11_stable_abi_preview.md | 无 |
| concept/07_future/12_inline_const_pattern_preview.md | 应用 |
| concept/07_future/13_must_not_suspend_preview.md | 应用 |
| concept/07_future/14_lifetime_capture_preview.md | 应用 |
| concept/07_future/15_rpitit_preview.md | 无 |
| concept/07_future/16_type_alias_impl_trait_preview.md | 应用 |
| concept/07_future/17_const_trait_preview.md | 应用 |
| concept/07_future/19_rust_2024_edition_preview.md | 无 |
| concept/07_future/22_gen_blocks_preview.md | 应用 |
| concept/07_future/24_wasm_target_evolution.md | 无 |
| concept/07_future/26_rust_in_space.md | 无 |

## 来源标注率偏低的文件 (< 10%)

| 文件 | 标注数 | 估算段落数 | 标注率 |
|:---|:---|:---|:---|
| concept/03_advanced/19_parallel_distributed_pattern_spectrum.md | 17 | 129 | 7.8% |
| concept/06_ecosystem/35_pattern_composition_algebra.md | 9 | 110 | 4.3% |
| concept/06_ecosystem/39_os_kernel.md | 13 | 62 | 7.8% |

## 方法论说明

- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在
- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查
- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%
- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外

> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。
