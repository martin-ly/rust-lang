> **内容分级**: [专家级]

# 企业架构（Enterprise Architecture）

> **EN**: Enterprise Architecture
> **Summary**: Enterprise architecture frameworks, governance, and standards alignment — connecting business/data/application/technology architecture to Rust's engineering semantics.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L5-L6
> **权威来源**: 本目录为 `concept/` 权威层；`semantic_space.md` 的企业架构子空间。
> **定位**: 从企业级视角对齐国际权威框架（TOGAF、Zachman、FEAF、ISO/IEC/IEEE 42010），建立业务架构、数据架构、应用架构、技术架构（BDAT）四维与 Rust 软件架构、系统设计原则、安全工程的映射关系。
> **前置概念**: [Software Architecture Formalization](../../04_formal/10_architecture_semantics/01_software_architecture_formalization.md) · [System Design Principles](../03_design_patterns/03_system_design_principles.md) · [Architecture Patterns](../03_design_patterns/08_architecture_patterns.md)
> **后置概念**: [Systems Engineering Standards](../../04_formal/09_system_semantics/06_systems_engineering_standards.md) · [Model-Driven Engineering](../03_design_patterns/19_model_driven_engineering.md) · [Semantic Space](../../00_meta/00_framework/semantic_space.md)

---

## 目录定位

`04_formal/10_architecture_semantics/` 解决“软件架构形式化”，`06_ecosystem/03_design_patterns/` 解决“设计模式与系统设计原则”。本目录负责把视角再向上提升一层：**企业架构**关注组织战略、业务能力、数据资产、应用组合与技术平台之间的整体一致性。

核心问题：

1. 企业架构框架（TOGAF、Zachman、FEAF）如何定义架构的描述、治理与演进？
2. BDAT 四维（Business / Data / Application / Technology）在 Rust 工程中如何落地？
3. 架构决策记录（ADR）、架构原则、技术雷达如何成为可审计的工程资产？
4. ISO/IEC/IEEE 42010 的架构描述概念模型如何与 Rust 的 crate/workspace/module 结构对齐？

---

## 计划文件清单

| # | 文件 | 主题 | 状态 |
|---:|---|---|---|
| 01 | `01_enterprise_architecture_frameworks.md` | TOGAF 10、Zachman、FEAF、BDAT 四维 | ✅ 已创建 |
| 02 | `02_architecture_governance_and_adrs.md` | 架构治理、ADR、架构原则、技术雷达 | ✅ 已创建 |
| 03 | `03_architecture_standards_alignment.md` | ISO 42010/12207/15288/25010、SWEBOK 与 Rust 映射 | ✅ 已创建 |

---

## 国际权威来源索引

- **P0 标准**: ISO/IEC/IEEE 42010:2022 — Systems and software engineering — Architecture description
- **P0 框架**: The Open Group, *TOGAF Standard, 10th Edition*
- **P0 框架**: J. Zachman, *Zachman Framework for Enterprise Architecture*
- **P1 专著**: R. Sessions, *Simple Architectures for Complex Enterprises* (2008)
- **P1 专著**: M. Lankhorst et al., *Enterprise Architecture at Work* (2017)
- **P1 标准**: ISO/IEC/IEEE 12207:2017 — Software life cycle processes
- **P1 标准**: ISO/IEC/IEEE 15288:2023 — System life cycle processes
- **P1 标准**: ISO/IEC 25010:2023 — Systems and software Quality Requirements and Evaluation (SQuaRE)
- **P1 指南**: IEEE Computer Society, *SWEBOK v4* (Software Engineering Body of Knowledge)

---

## 与表征空间的关系

```text
semantic_space.md §6 跨语言表征空间对比 / §5 机制组合
    └── 企业架构层（本目录）
            ├── EA 框架：TOGAF / Zachman / FEAF
            ├── BDAT 四维：业务 / 数据 / 应用 / 技术
            ├── 架构治理：ADR / 架构原则 / 技术雷达
            └── 标准对齐：ISO 42010 / 12207 / 15288 / 25010 / SWEBOK
```
