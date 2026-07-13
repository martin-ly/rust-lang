# 缺口与行动计划（Gap and Action Plan）

> **EN**: Gap and Action Plan
> **Summary**: 基于拓扑抽取结果识别的当前缺口：来源覆盖、表征完整性、层间/层内映射、定义一致性。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [研究者]
> **内容分级**: [元层]
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

---

## 一、当前缺口概览

| 缺口类型 | 数量 | 说明 |
|:---|:---:|:---|
| 无权威来源标注 | 1 | 概念文件未引用任何外部权威来源 |
| 来源标注薄弱（≤2） | 0 | 概念文件仅引用 1–2 个来源 |
| 无定理链 | 217 | 概念文件缺少定理链 |
| 无 A/S/P 标记 | 230 | 概念文件缺少 A/S/P 维度标记 |
| 无知识表征章节 | 23 | 概念文件无决策树/矩阵/示例等表征 |

## 二、优先修复任务

本节围绕「优先修复任务」展开，依次讨论 P0：补全权威来源（L1–L4 核心概念）、P1：增强知识表征与P2：对齐国际标准。

### P0：补全权威来源（L1–L4 核心概念）

| 概念 | 层级 | 当前来源数 | 建议行动 |
|:---|:---:|:---:|:---|

### P1：增强知识表征

| 概念 | 层级 | 缺失表征 | 建议行动 |
|:---|:---:|:---|:---|
| [Preludes](../../01_foundation/07_modules_and_items/10_preludes.md) | L1 基础概念层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Safety Tags](../../04_formal/02_separation_logic/03_safety_tags_in_formal.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [形式化方法在 Rust 中的应用](../../04_formal/04_model_checking/02_formal_methods.md) | L4 形式化理论层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [rustc 编译器诊断与 UI Tests](../../06_ecosystem/00_toolchain/11_compiler_diagnostics_and_ui_tests.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [rustc 自举](../../06_ecosystem/00_toolchain/12_rustc_bootstrap.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Cargo Registry 与包发布](../../06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Cargo 认证与构建缓存](../../06_ecosystem/01_cargo/09_cargo_authentication_and_cache.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Cargo 工作流](../../06_ecosystem/01_cargo/16_cargo_workflow.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Cargo Registry 内部机制](../../06_ecosystem/01_cargo/21_cargo_registry_internals.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Target Tier 平台支持全景：分层保证与 1.90–1.97 变迁](../../06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 游戏开发](../../06_ecosystem/11_domain_applications/06_game_development.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 算法复杂度分析](../../06_ecosystem/11_domain_applications/10_algorithm_complexity_analysis.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [安全关键 Rust 专题索引](../../06_ecosystem/11_domain_applications/21_safety_critical_topic_index.md) | L6 生态工程层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 1.97.0 特性 × 领域反查矩阵](../../07_future/00_version_tracking/feature_domain_matrix_197.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 1.95.0 稳定特性](../../07_future/00_version_tracking/rust_1_95_stabilized.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 1.96 稳定特性](../../07_future/00_version_tracking/rust_1_96_stabilized.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 1.97.0 前沿特性预览](../../07_future/00_version_tracking/rust_1_97_preview.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 1.98+ 前沿特性预览](../../07_future/00_version_tracking/rust_1_98_preview.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust 2024 Edition (1.85.0+ stable)](../../07_future/01_edition_roadmap/01_rust_edition_preview.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [Rust Edition 机制与迁移指南](../../07_future/01_edition_roadmap/03_rust_edition_guide.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [cargo-semver-checks：从社区工具到 Cargo 官方集成](../../07_future/03_preview_features/27_cargo_semver_checks_preview.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |
| [AArch64 SVE / SME：可伸缩向量扩展预览](../../07_future/03_preview_features/29_aarch64_sve_sme_preview.md) | L7 前沿趋势层 | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |

### P2：对齐国际标准

针对以下主题补充 Unicode / ISO / IEEE / IETF / ABI 标准引用：

- 字符串与编码：`concept/01_foundation/18_strings_and_encoding.md` → Unicode Standard
- 内联汇编：`concept/03_advanced/13_inline_assembly.md` → Intel/ARM 架构手册
- 网络编程：`concept/03_advanced/18_network_programming.md` → IETF RFCs
- ABI：`concept/04_formal/38_application_binary_interface.md` → Itanium C++ ABI / System V AMD64 ABI
- 交叉编译/嵌入式：`concept/06_ecosystem/17_cross_compilation.md` / `22_embedded_systems.md` → 目标平台规范

## 三、自动化建议

1. 在 `kb_auditor.py` 中增加：概念文件必须引用至少一个 L1 来源。
2. 每月运行 `extract_concept_topology.py` + `generate_knowledge_topology_atlas.py` 生成图谱集。
3. 对新增文件自动检测是否包含决策树/矩阵/示例反例中的一种表征。


---

> 本文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 生成；请勿手工编辑，更新后重新运行生成脚本。
