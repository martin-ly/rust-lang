> **权威来源**:
>
> [Rust Reference](https://doc.rust-lang.org/reference/),
> [Rustonomicon](https://doc.rust-lang.org/nomicon/),
> [Ferrocene](https://www.ferrous-systems.com/ferrocene/),
> [Rust Safety Critical WG](https://github.com/rustfoundation/safety-critical-rust-consortium)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust 安全关键生态系统来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)
>
# Rust安全关键生态系统文档集

> **EN**: Safety Critical Index
> **Summary**: Rust安全关键生态系统文档集 Safety Critical Index.
> **Bloom 层级**: L2

## 概述
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

本文档集提供Rust在安全关键系统开发领域的全面技术资源，涵盖从理论基础到实际实施的完整知识体系。内容面向功能安全工程师、嵌入式开发者和系统架构师，支持ISO 26262、IEC 61508、DO-178C等标准的合规开发。

> 📌 **前置知识要求**: 本生态系统的文档假设读者已掌握 Rust 核心知识体系。如果你是 Rust 新手，请先学习 [knowledge/](../../knowledge) 目录下的分层文档（从 `01_fundamentals` 到 `03_advanced`）。安全关键系统开发要求对所有权、借用、并发、`unsafe` 代码和 FFI 有深入理解。

---

## 文档结构
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

```
content/safety_critical/ (原 docs/RUST_SAFETY_CRITICAL_ECOSYSTEM/ 已合并，后从 knowledge/04_expert/safety_critical/ 迁移至此)
├── 01_mind_maps/                    # 思维导图 - 宏观视角
│   ├── 01_academic_research_landscape.md
│   ├── 02_rust_ecosystem_mind_map.md
│   └── 03_rust_194_195_features_deep_dive.md
│
├── 02_matrices/                     # 多维矩阵 - 对比分析
│   ├── 01_comprehensive_language_comparison_matrix.md
│   ├── 02_rust_multi_dimensional_matrix.md
│   ├── 03_rust_ownership_memory_model_matrix.md
│   └── 04_toolchain_evaluation_matrix.md
│
├── 03_decision_trees/               # 决策树 - 选择指南
│   ├── 01_rust_decision_trees.md
│   └── 02_safety_integrity_level_selection_guide.md
│
├── 04_axiomatic_reasoning/          # 公理化推理 - 形式化基础
│   ├── 01_formal_verification_practical_guide.md
│   └── 02_rust_axiomatic_reasoning_trees.md
│
├── 05_strategic_guidance/           # 战略指导 - 高层规划
│   ├── 01_adoption_strategy_and_roi_analysis.md
│   └── 02_comprehensive_recommendations_and_opinions.md
│
├── 06_roadmaps/                     # 路线图 - 前瞻规划
│   ├── 01_education_and_training_roadmap.md
│   ├── 02_rust_2026_2030_roadmap_forecast.md
│   ├── 03_sustainable_roadmap_and_plans.md
│   └── 04_technology_watch_and_emerging_trends.md
│
├── 07_case_studies/                 # 案例研究 - 实际应用
│   ├── 01_case_study_01_ferrocene_certification.md
│   ├── 02_case_study_02_nasa_cfs_rust.md
│   ├── 03_case_study_03_automotive_ecus.md
│   ├── 04_case_study_04_medical_devices.md
│   ├── 05_case_study_05_railway_signaling.md
│   └── 06_case_study_06_autonomous_driving.md
│
├── 08_training/                     # 培训材料
│   ├── 01_assessment_and_certification.md
│   ├── 02_certification_prep_guide.md
│   ├── 03_hands_on_lab_exercises.md
│   ├── 04_interactive_learning_resources.md
│   └── 05_rust_safety_critical_training_program.md  # Level 1 已链接至 concept/
│
├── 09_reference/                    # 参考材料
│   ├── 01_api_design_guidelines.md
│   ├── 02_checklists_and_templates.md
│   ├── 03_community_and_contributing.md
│   ├── 04_comprehensive_international_alignment_completion_report.md
│   ├── 05_deployment_and_maintenance_guide.md
│   ├── 06_faq_and_troubleshooting.md
│   ├── 07_ffi_integration_guide.md
│   ├── 08_glossary_and_definitions.md
│   ├── 09_metrics_and_measurement_guide.md
│   ├── 10_performance_optimization_guide.md      # 已规范化为 stub
│   ├── 11_project_templates.md
│   ├── 12_quick_reference_card.md
│   ├── 13_rust_safety_critical_coding_guidelines.md
│   ├── 14_safety_critical_checklists.md
│   ├── 15_security_audit_guide.md
│   ├── 16_supply_chain_security_guide.md
│   ├── 17_toolchain_setup_guide.md
│   ├── 18_tools_configuration_guide.md
│   └── 19_troubleshooting_and_debugging_guide.md  # 已规范化为 stub，链接 concept/
│
├── 10_standards/                    # 标准指南
│   ├── 01_do_178c_rust_compliance_pathway.md
│   ├── 02_iec_61508_rust_implementation_guide.md
│   ├── 03_iso_26262_rust_implementation_guide.md
│   ├── 04_misra_c_2025_addendum_6_guide.md
│   └── 05_regulatory_landscape_and_approvals.md
│
├── 02_rust_safety_critical_ecosystem_master_index.md
├── 03_readme_rust_safety_critical_ecosystem.md
└── README.md (本文件)
```

---

## 文档详情
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

> **AGENTS.md 规范说明**: 以下文档中，标注 `[stub]` 的文件已按 `concept/` 单一权威来源规则转为专题入口 stub；未标注 stub 的文件保留安全关键领域特有内容（案例、标准映射、认证路径、决策树、检查表等），通用 Rust 概念解释通过页首/节首 canonical 链接指向 `concept/`。

### 01. 思维导图 (Mind Maps)
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

- [`01_academic_research_landscape.md`](01_mind_maps/01_academic_research_landscape.md) — 学术研究全景 (Tree Borrows, Miri, 形式化验证工具)
- [`02_rust_ecosystem_mind_map.md`](01_mind_maps/02_rust_ecosystem_mind_map.md) — 生态系统全景图
- [`03_rust_194_195_features_deep_dive.md`](01_mind_maps/03_rust_194_195_features_deep_dive.md) — Rust 1.94/1.95 特性在安全关键场景的应用

### 02. 多维矩阵 (Matrices)
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

- [`01_comprehensive_language_comparison_matrix.md`](02_matrices/01_comprehensive_language_comparison_matrix.md) — 语言安全特性对比
- [`02_rust_multi_dimensional_matrix.md`](02_matrices/02_rust_multi_dimensional_matrix.md) — 8个核心对比矩阵
- [`03_rust_ownership_memory_model_matrix.md`](02_matrices/03_rust_ownership_memory_model_matrix.md) — 所有权与内存模型对比
- [`04_toolchain_evaluation_matrix.md`](02_matrices/04_toolchain_evaluation_matrix.md) — 认证工具链评估

### 03. 决策树 (Decision Trees)

- [`01_rust_decision_trees.md`](03_decision_trees/01_rust_decision_trees.md) — 语言/工具链/安全等级/培训路径决策
- [`02_safety_integrity_level_selection_guide.md`](03_decision_trees/02_safety_integrity_level_selection_guide.md) — ASIL/SIL 选择指南

### 04. 公理化推理与形式化验证

- [`02_rust_axiomatic_reasoning_trees.md`](04_axiomatic_reasoning/02_rust_axiomatic_reasoning_trees.md) — 内存安全公理系统、Tree Borrows 形式语义
- [`01_formal_verification_practical_guide.md`](04_axiomatic_reasoning/01_formal_verification_practical_guide.md) — Miri/Kani/Verus 实战、CI/CD 集成

### 05. 战略指导 (Strategic Guidance)

- [`01_adoption_strategy_and_roi_analysis.md`](05_strategic_guidance/01_adoption_strategy_and_roi_analysis.md) — 采用策略与 ROI 分析
- [`02_comprehensive_recommendations_and_opinions.md`](05_strategic_guidance/02_comprehensive_recommendations_and_opinions.md) — 综合建议与观点

### 06. 路线图 (Roadmaps)

- [`01_education_and_training_roadmap.md`](06_roadmaps/01_education_and_training_roadmap.md) — 教育培训路线图
- [`02_rust_2026_2030_roadmap_forecast.md`](06_roadmaps/02_rust_2026_2030_roadmap_forecast.md) — 2026-2030 技术预测
- [`03_sustainable_roadmap_and_plans.md`](06_roadmaps/03_sustainable_roadmap_and_plans.md) — 可持续推进计划
- [`04_technology_watch_and_emerging_trends.md`](06_roadmaps/04_technology_watch_and_emerging_trends.md) — 技术观察与新兴趋势

### 07. 案例研究 (Case Studies)

6个详细案例 (约 100KB 合计):

- [`01_case_study_01_ferrocene_certification.md`](07_case_studies/01_case_study_01_ferrocene_certification.md) — Ferrocene 认证 (TÜV SÜD)
- [`02_case_study_02_nasa_cfs_rust.md`](07_case_studies/02_case_study_02_nasa_cfs_rust.md) — NASA cFS 集成
- [`03_case_study_03_automotive_ecus.md`](07_case_studies/03_case_study_03_automotive_ecus.md) — 汽车 ECU 实施
- [`04_case_study_04_medical_devices.md`](07_case_studies/04_case_study_04_medical_devices.md) — 医疗设备 (IEC 62304)
- [`05_case_study_05_railway_signaling.md`](07_case_studies/05_case_study_05_railway_signaling.md) — 铁路信号系统 (EN 50128/50129)
- [`06_case_study_06_autonomous_driving.md`](07_case_studies/06_case_study_06_autonomous_driving.md) — 自动驾驶感知系统

### 08. 培训材料 (Training)

- [`01_assessment_and_certification.md`](08_training/01_assessment_and_certification.md) — 评估与认证体系
- [`02_certification_prep_guide.md`](08_training/02_certification_prep_guide.md) — ISO 26262 / IEC 61508 / DO-178C 备考
- [`03_hands_on_lab_exercises.md`](08_training/03_hands_on_lab_exercises.md) — 动手实验练习
- [`04_interactive_learning_resources.md`](08_training/04_interactive_learning_resources.md) — 交互式学习资源
- [`05_rust_safety_critical_training_program.md`](08_training/05_rust_safety_critical_training_program.md) — 8周20模块课程；**Level 1 (Rust 基础) 已链接至 `concept/` 权威页**

### 09. 参考材料 (Reference)

- [`01_api_design_guidelines.md`](09_reference/01_api_design_guidelines.md) — 安全关键 API 设计指南
- [`02_checklists_and_templates.md`](09_reference/02_checklists_and_templates.md) — 检查清单与模板
- [`03_community_and_contributing.md`](09_reference/03_community_and_contributing.md) — 社区参与与贡献
- [`04_comprehensive_international_alignment_completion_report.md`](09_reference/04_comprehensive_international_alignment_completion_report.md) — 国际化对齐完成报告
- [`05_deployment_and_maintenance_guide.md`](09_reference/05_deployment_and_maintenance_guide.md) — 部署与维护
- [`06_faq_and_troubleshooting.md`](09_reference/06_faq_and_troubleshooting.md) — 常见问题
- [`07_ffi_integration_guide.md`](09_reference/07_ffi_integration_guide.md) — FFI 集成指南
- [`08_glossary_and_definitions.md`](09_reference/08_glossary_and_definitions.md) — 术语表
- [`09_metrics_and_measurement_guide.md`](09_reference/09_metrics_and_measurement_guide.md) — 度量与测量
- [`10_performance_optimization_guide.md`](09_reference/10_performance_optimization_guide.md) — 性能优化要点 `[stub]`
- [`11_project_templates.md`](09_reference/11_project_templates.md) — 项目模板
- [`12_quick_reference_card.md`](09_reference/12_quick_reference_card.md) — 快速参考卡片
- [`13_rust_safety_critical_coding_guidelines.md`](09_reference/13_rust_safety_critical_coding_guidelines.md) — 安全关键编码规范
- [`14_safety_critical_checklists.md`](09_reference/14_safety_critical_checklists.md) — 开发检查表
- [`15_security_audit_guide.md`](09_reference/15_security_audit_guide.md) — 安全审计
- [`16_supply_chain_security_guide.md`](09_reference/16_supply_chain_security_guide.md) — 供应链安全
- [`17_toolchain_setup_guide.md`](09_reference/17_toolchain_setup_guide.md) — 工具链配置
- [`18_tools_configuration_guide.md`](09_reference/18_tools_configuration_guide.md) — 工具配置
- [`19_troubleshooting_and_debugging_guide.md`](09_reference/19_troubleshooting_and_debugging_guide.md) — 故障排除与调试 `[stub]`（通用错误排错见 `concept/`）

### 10. 标准指南 (Standards)

- [`01_do_178c_rust_compliance_pathway.md`](10_standards/01_do_178c_rust_compliance_pathway.md) — DO-178C 合规路径
- [`02_iec_61508_rust_implementation_guide.md`](10_standards/02_iec_61508_rust_implementation_guide.md) — IEC 61508 实施指南
- [`03_iso_26262_rust_implementation_guide.md`](10_standards/03_iso_26262_rust_implementation_guide.md) — ISO 26262 实施指南
- [`04_misra_c_2025_addendum_6_guide.md`](10_standards/04_misra_c_2025_addendum_6_guide.md) — MISRA C:2025 Addendum 6
- [`05_regulatory_landscape_and_approvals.md`](10_standards/05_regulatory_landscape_and_approvals.md) — 监管环境与认证审批

---

## 总览统计

| 指标 | 数值 |
|------|------|
| **核心文档数** | 45 |
| **总内容量** | ~700KB |
| **代码示例数** | 400+ |
| **配置模板数** | 50+ |
| **检查表项数** | 400+ |
| **已规范化为 stub** | 2（性能优化、故障排除）|
| **Level 1 链接至 concept/** | 1（培训计划）|

---

## 使用指南

### 按角色使用

**功能安全工程师**:

1. 阅读思维导图了解全局
2. 查看决策树进行技术选择
3. 使用标准指南进行合规开发
4. 参考检查表确保完整性

**嵌入式开发者**:

1. 学习编码规范
2. 配置工具链
3. 使用检查表
4. 参考案例研究

**系统架构师**:

1. 查看矩阵进行对比分析
2. 阅读路线图了解趋势
3. 参考公理化推理树
4. 使用决策树辅助决策

**项目经理**:

1. 阅读路线图了解规划
2. 使用培训材料规划团队
3. 查看案例研究评估风险
4. 参考检查表管理进度

### 按开发阶段使用

| 阶段 | 推荐文档 |
|------|----------|
| 项目启动 | 思维导图、决策树、启动检查表 |
| 需求分析 | 标准指南、需求检查表 |
| 架构设计 | 公理化推理、架构检查表 |
| 编码实施 | 编码规范、工具链配置 |
| 测试验证 | 形式化验证指南、测试检查表 |
| 认证准备 | 认证备考指南、发布检查表 |

---

## 技术栈覆盖

### 编译器与工具链

- rustc (稳定版/特定版本)
- Ferrocene (预认证)
- Miri (内存安全)
- rust-analyzer (IDE)

### 静态分析

- Clippy (lint规则)
- 自定义lint规则
- cargo-deny (依赖审计)

### 形式化验证

- Kani (模型检查)
- Verus (定理证明)
- Creusot (Why3集成)
- Prusti (契约检查)

### 测试与覆盖

- cargo test (单元测试)
- Miri (UB检测)
- cargo-tarpaulin (覆盖率)
- cargo-llvm-cov (LLVM覆盖)

### 构建与CI

- Cargo (包管理)
- GitHub Actions
- 可重现构建
- SBOM生成

---

## 标准覆盖

| 标准 | 领域 | ASIL/SIL等级 | 文档 |
|------|------|--------------|------|
| **ISO 26262** | 汽车 | ASIL A-D | 实施指南 |
| **IEC 61508** | 工业 | SIL 1-4 | Rust指南 |
| **DO-178C** | 航空 | A-E | 合规路径 |
| **IEC 62304** | 医疗 | A-C | 实施指南 |
| **MISRA** | 通用 | - | Addendum 6 |

---

## 版本信息

- **文档版本**: 2.2
- **最后更新**: 2026-07-15
- **Rust版本**: 1.97.0+ (Edition 2024)
- **Ferrocene版本**: 25.11 (参考)
- **Kani版本**: 0.40
- **Miri**: 最新
- **状态**: ✅ 已按 AGENTS.md §2 完成 canonical 清理（2 个 stub + 1 个 Level 1 链接化）

---

## 贡献与反馈

本文档集持续更新，欢迎反馈:

- 技术准确性问题
- 内容完整性建议
- 实际应用案例
- 工具链更新

---

## 许可证

本文档集采用知识共享许可协议，代码示例遵循MIT/Apache-2.0双许可。

---

**开始使用**: 建议从 [思维导图](01_mind_maps/02_rust_ecosystem_mind_map.md) 开始，了解Rust安全关键生态系统的全貌

- [Rust安全关键生态系统文档集 - 主索引](02_rust_safety_critical_ecosystem_master_index.md)
- [Rust 形式化语义](../../concept/04_formal/04_model_checking/03_aerospace_certification_formal_methods.md)
- [Unsafe Rust 指南](../../concept/03_advanced/02_unsafe/01_unsafe.md)

---

**最后更新**: 2026-07-15
**状态**: ✅ 已按 AGENTS.md §2 完成 canonical 清理

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference](https://doc.rust-lang.org/reference/) | 语言规范 |
| [Rust Project Goals — Safety-Critical Rust](https://rust-lang.github.io/rust-project-goals/2026/) | 安全关键领域目标 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [Ferrocene](https://ferrocene.dev/) | Rust 安全关键工具链 |
| [Rust for Linux](https://rust-for-linux.com/) | 内核应用 |
| [seL4](https://sel4.systems/) | 形式化验证操作系统微内核 |
| [MISRA C](https://www.misra.org.uk/) | 安全关键 C 编码标准 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Safety-Critical Rust Consortium](https://github.com/rustfoundation/safety-critical-rust-consortium) | 安全关键 Rust 社区 |
| [Rust Foundation](https://foundation.rust-lang.org/) | 基金会动态 |
