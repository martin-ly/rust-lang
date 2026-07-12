# 安全关键 Rust 专题索引

**EN**: Safety-Critical Rust Topic Index

> **Summary**: Navigation index linking the `content/safety_critical/` in-depth suite (ISO 26262 / IEC 61508 / DO-178C / MISRA guides, case studies, checklists) with the related `concept/` canonical pages (formal methods, Ferrocene toolchain).

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L6
> **定位**: 本文件为 `concept/` 侧的**摘要+链接型导航页**（AGENTS.md §2.1 第 3 条：content/ 专题权威页需在 concept/ 建索引入口）。专题深度内容以 [`content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md`](../../../content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md) 为权威入口；通用概念解释以 `concept/` 相关权威页为准。本页不复制任何正文。

---

## 1. 专题套件入口（content/ 权威）

| 入口 | 内容 |
|:---|:---|
| [主索引](../../../content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md) | 39 篇文档、10 大分类、按角色/阶段的使用路线 |
| [ISO 26262 实施指南](../../../content/safety_critical/10_standards/03_iso_26262_rust_implementation_guide.md) | 汽车功能安全合规路径 |
| [IEC 61508 实施指南](../../../content/safety_critical/10_standards/02_iec_61508_rust_implementation_guide.md) | 工业功能安全合规路径 |
| [DO-178C 合规路径](../../../content/safety_critical/10_standards/01_do_178c_rust_compliance_pathway.md) | 航空软件认证 |
| [MISRA C:2025 Addendum 6 指南](../../../content/safety_critical/10_standards/04_misra_c_2025_addendum_6_guide.md) | MISRA 与 Rust 映射 |
| [案例研究：Ferrocene 认证](../../../content/safety_critical/07_case_studies/01_case_study_01_ferrocene_certification.md) | TÜV 认证工具链实践 |
| [案例研究：汽车 ECU](../../../content/safety_critical/07_case_studies/03_case_study_03_automotive_ecus.md) | ISO 26262 落地案例 |

## 2. 相关 concept/ 权威页

| 页面 | 主题 |
|:---|:---|
| [航空航天认证与形式化方法](../../04_formal/04_model_checking/03_aerospace_certification_formal_methods.md) | DO-178C/DO-333 与 Rust 形式化映射（定理证明/模型检查/抽象解释） |
| [Ferrocene：已交付认证工具链](../../07_future/03_preview_features/12_ferrocene_preview.md) | TÜV SÜD 鉴定工具链（ASIL D/SIL 3/Class C）与 certified core 子集 |
| [认证工具链与认证包清单](../../04_formal/04_model_checking/10_certified_toolchains_and_packages.md) | Ferrocene/HighTec/AdaCore 生态、认证 crate 现状与边界决策树 |
| [AUTOSAR 与 Rust](22_autosar_and_rust.md) | AUTOSAR CP/AP 标准与 Rust 的关系、WG-SAF 进程 |
| [MC/DC 覆盖率预研](../../07_future/03_preview_features/02_mcdc_coverage_preview.md) | DO-178C A 级覆盖率准则 |
| [Safety Tags 预研](../../07_future/03_preview_features/03_safety_tags_preview.md) | 安全标注机制 |
| [形式化验证工具链](../../04_formal/04_model_checking/01_verification_toolchain.md) | 验证工具全景 |

## 3. 分工边界

- **概念解释**（什么是 DO-178C、形式化方法如何映射 Rust、Ferrocene 是什么）：以上 `concept/` 权威页。
- **工程实践**（合规步骤、检查表、模板、培训、ROI、案例）：`content/safety_critical/` 专题套件。
- 两侧仅通过链接互引，不保留重复正文（AGENTS.md §2 Canonical 规则）。
