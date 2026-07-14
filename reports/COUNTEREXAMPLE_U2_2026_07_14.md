# 反例覆盖 U2 回填报告（2026-07-14）

> 目标：反例覆盖 84.4% → ~90%（+25 页）。
> 方法：`python scripts/check_mindmap_coverage.py` 确定缺口名单；每页追加「⚠️ 反例与陷阱」节（≤40 行，只追加不改既有内容）；
> 每个 `compile_fail` 块均用 **rustc 1.97.0 (2d8144b78) `--edition 2024`** 实测确认确实失败，错误码与实测输出一致；修正版实测编译通过。

## 1. 指标前后对照（check_mindmap_coverage.py 实跑）

| 层 | 前 | 后 |
|---|---|---|
| 01_foundation | 49/55 (89.1%) | 50/55 (**90.9%**) |
| 06_ecosystem | 98/127 (77.2%) | 117/127 (**92.1%**) |
| 07_future | 55/66 (83.3%) | 60/66 (**90.9%**) |
| **全库 M2** | **363/430 (84.4%)** | **388/430 (90.2%)** |

+25 页：06 层 19 页、07 层 5 页、01 层 1 页。

## 2. 逐页清单与实测证据

实测方式：bad 块 `rustc --edition 2024 --crate-type bin --emit=metadata` 必须失败且含标注错误码；good 块必须编译通过（bin 或 lib，仅 dead-code 警告）。复测脚本：`tmp/cbfix_u2/gen_and_test.py`、`tmp/cbfix_u2/verify_appended.py`（从最终文件抽块复测，25 页全过）。

| # | 文件 | 反例主题 | 实测错误 |
|---|---|---|---|
| 1 | concept/06_ecosystem/00_toolchain/06_quiz_toolchain.md | 类型标注与字面量不匹配 | `error[E0308]: mismatched types` |
| 2 | concept/06_ecosystem/00_toolchain/08_platform_rust_integration.md | Edition 2024 extern 块必须 unsafe | `error: extern blocks must be unsafe`（无错误码，原文如实标注） |
| 3 | concept/06_ecosystem/00_toolchain/12_rustc_bootstrap.md | 引用未声明的模块/crate | `error[E0433]: cannot find module or crate` |
| 4 | concept/06_ecosystem/00_toolchain/14_development_tools.md | 引用比被引用者活得久 | `error[E0597]: does not live long enough` |
| 5 | concept/06_ecosystem/01_cargo/04_cargo_196_features.md | 借用存活期间修改容器 | `error[E0502]` |
| 6 | concept/06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md | trait 实现漏项 | `error[E0046]` |
| 7 | concept/06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md | 同名函数重复定义 | `error[E0428]` |
| 8 | concept/06_ecosystem/01_cargo/10_cargo_manifest_reference.md | 导入不存在路径 | `error[E0432]: unresolved import` |
| 9 | concept/06_ecosystem/01_cargo/12_cargo_subcommands_and_plugins.md | 非函数值当函数调用 | `error[E0618]` |
| 10 | concept/06_ecosystem/01_cargo/15_cargo_getting_started.md | 使用未声明变量 | `error[E0425]` |
| 11 | concept/06_ecosystem/01_cargo/16_cargo_workflow.md | 两个可变借用同时存活 | `error[E0499]` |
| 12 | concept/06_ecosystem/01_cargo/17_cargo_guide_practices.md | 从借用的 Vec 移出元素 | `error[E0507]` |
| 13 | concept/06_ecosystem/01_cargo/18_cargo_configuration.md | collect 缺类型标注 | `error[E0283]: type annotations needed` |
| 14 | concept/06_ecosystem/01_cargo/19_cargo_commands_reference.md | 返回临时值的引用 | `error[E0515]` |
| 15 | concept/06_ecosystem/01_cargo/21_cargo_registry_internals.md | 签名缺生命周期标注 | `error[E0106]` |
| 16 | concept/06_ecosystem/01_cargo/23_cargo_197_features.md | 常量求值溢出 | `error[E0080]` |
| 17 | concept/06_ecosystem/03_design_patterns/14_design_patterns_glossary.md | 移动后再次使用 | `error[E0382]` |
| 18 | concept/06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md | Copy 与 Drop 互斥 | `error[E0184]` |
| 19 | concept/06_ecosystem/11_domain_applications/20_wasm_javascript_interop.md | 泛型方法破坏 dyn 兼容 | `error[E0038]` |
| 20 | concept/07_future/00_version_tracking/rust_1_90_stabilized.md | 未实现 Add 却用 + | `error[E0369]` |
| 21 | concept/07_future/00_version_tracking/rust_1_93_stabilized.md | 可能未初始化绑定 | `error[E0381]` |
| 22 | concept/07_future/00_version_tracking/rust_1_96_stabilized.md | 借用存活期间赋值 | `error[E0506]` |
| 23 | concept/07_future/00_version_tracking/rust_1_98_stabilized.md | unsafe 块外解引用裸指针 | `error[E0133]` |
| 24 | concept/07_future/05_quizzes/01_quiz_version_and_preview.md | 泛型缺 Display 约束 | `error[E0277]` |
| 25 | concept/01_foundation/11_quizzes/25_quiz_error_handling.md | 非 Result 函数中用 ? | `error[E0277]: the ? operator can only be used...` |

说明：代码块 fence 采用既有惯例 ` ```rust,compile_fail,Exxxx `（与 `scripts/check_concept_code_blocks.py` 的 `ERRCODE_RE` 提取口径一致，全量实测门可校验错误码）。#2 为 Edition 2024 无错误码硬错误，fence 不带错误码，正文注明实测原文。

## 3. 验证结果（2026-07-14 实跑）

| 检查 | 结果 |
|---|---|
| `check_mindmap_coverage.py` | M2 363→388（84.4%→90.2%），见 §1 |
| 代码块抽回复测（25 页 × bad/good） | 25/25 通过（bad 必败且错误码一致；good 必过） |
| `kb_auditor.py` | 死链 0、跨层问题 0、模板化 ⟹ 0 |
| `mdbook build` | 通过（仅 search index 体积 WARN，基线既有） |
| `detect_content_overlap.py`（v1 阻断门 8） | 1 对，与基线相同（migration_197 vs 197 cheatsheet，非本次引入） |
| `detect_content_overlap_v2.py` + `triage_overlap.py`（阻断门 15） | 可处理项 MERGE=0 / DOCS_INTERNAL=0（基线保持） |

## 4. 未覆盖剩余缺口（供后续轮次）

- 06_ecosystem 剩 10 页：06_quiz_toolchain 之外的 quiz 页（13_quizzes/01–04）、glossary/faq 类（15_design_patterns_faq、18_wasm_glossary、19_wasm_faq）、索引页（11_cutting_edge_algorithms、21_safety_critical_topic_index、22_autosar_and_rust）。
- 07_future 剩 6 页：feature_domain_matrix_197、rust_1_91/92/94/95/97 等版本跟踪页。
- 01_foundation 剩 5 页：00_start、01_pl_prerequisites、知识地图页、quiz 26/29。
- 03_advanced 剩 11 页、04_formal 剩 4 页（本轮未覆盖，非短板层）。
