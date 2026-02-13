# 文档中心 - 主索引

> **创建日期**: 2026-02-13
> **用途**: 文档总入口，按主题分类导航
> **状态**: 100% 完成（阶段 1–4 + 链接修复）

---

## 按主题快速导航

| 主题 | 入口 | 说明 |
|------|------|------|
| **学习路径** | [01_learning](#01-学习路径与导航) | 学习规划、官方资源映射 |
| **速查参考** | [02_reference](#02-参考与速查) | 20 个速查卡、边界特例、标准库 |
| **形式化理论** | [03_theory](#03-理论与形式化) | 研究笔记、证明索引 |
| **思维表征** | [04_thinking](#04-思维表征) | 思维导图、决策树、证明树、矩阵 |
| **专题指南** | [05_guides](#05-专题指南) | 异步、线程、WASM、Unsafe 等 |
| **工具链** | [06_toolchain](#06-工具链与版本) | 编译器、Cargo、版本演进 |
| **项目元文档** | [07_project](#07-项目元文档) | 知识结构、版本追踪、报告 |

---

## 按角色导航

- **初学者** → 学习路径 → 速查卡 → C01 模块
- **开发者** → 专题指南 → 速查卡 → 边界特例
- **研究者** → 形式化理论 → 思维表征 → 证明索引
- **维护者** → 项目元文档 → 版本追踪

---

## 01 学习路径与导航

| 文档 | 说明 |
|------|------|
| [LEARNING_PATH_PLANNING.md](./01_learning/LEARNING_PATH_PLANNING.md) | 学习路径规划 |
| [OFFICIAL_RESOURCES_MAPPING.md](./01_learning/OFFICIAL_RESOURCES_MAPPING.md) | 本项目 ↔ The Rust Book / Reference / RBE |

---

## 02 参考与速查

| 文档/目录 | 说明 |
|-----------|------|
| [quick_reference/](./02_reference/quick_reference/) | 20 个速查卡（含 AI/ML、类型、所有权、异步等） |
| [ALIGNMENT_GUIDE.md](./02_reference/ALIGNMENT_GUIDE.md) | 对齐知识综合（内存/格式化/unsafe/缓存行） |
| [ERROR_CODE_MAPPING.md](./02_reference/ERROR_CODE_MAPPING.md) | 编译器错误码 → 本项目文档映射 |
| [EDGE_CASES_AND_SPECIAL_CASES.md](./02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) | 空集、零长度、溢出等边界特例 |
| [STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md](./02_reference/STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md) | 标准库全面分析 |
| [CROSS_LANGUAGE_COMPARISON.md](./02_reference/CROSS_LANGUAGE_COMPARISON.md) | Rust vs C++/Go/Python |

---

## 03 理论与形式化

| 文档/目录 | 说明 |
|-----------|------|
| [research_notes/](./research_notes/) | 形式化方法、类型理论、软件设计理论（主内容） |
| [rust-formal-engineering-system/](./rust-formal-engineering-system/) | 形式化工程系统索引（映射到 research_notes） |
| [research_notes/PROOF_INDEX.md](./research_notes/PROOF_INDEX.md) | 公理-定理-证明索引 |

---

## 04 思维表征

| 文档 | 说明 |
|------|------|
| [THINKING_REPRESENTATION_METHODS.md](./04_thinking/THINKING_REPRESENTATION_METHODS.md) | 思维导图、决策树、转换树、证明树 |
| [DECISION_GRAPH_NETWORK.md](./04_thinking/DECISION_GRAPH_NETWORK.md) | 决策图网络 |
| [PROOF_GRAPH_NETWORK.md](./04_thinking/PROOF_GRAPH_NETWORK.md) | 证明图网络 |
| [MIND_MAP_COLLECTION.md](./04_thinking/MIND_MAP_COLLECTION.md) | 思维导图集合 |
| [MULTI_DIMENSIONAL_CONCEPT_MATRIX.md](./04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md) | 多维概念矩阵 |
| [APPLICATIONS_ANALYSIS_VIEW.md](./04_thinking/APPLICATIONS_ANALYSIS_VIEW.md) | 应用场景→技术选型→论证依据 |

---

## 05 专题指南

| 文档 | 说明 |
|------|------|
| [ASYNC_PROGRAMMING_USAGE_GUIDE.md](./05_guides/ASYNC_PROGRAMMING_USAGE_GUIDE.md) | 异步编程使用指南 |
| [THREADS_CONCURRENCY_USAGE_GUIDE.md](./05_guides/THREADS_CONCURRENCY_USAGE_GUIDE.md) | 线程与并发使用指南 |
| [DESIGN_PATTERNS_USAGE_GUIDE.md](./05_guides/DESIGN_PATTERNS_USAGE_GUIDE.md) | 设计模式使用指南 |
| [MACRO_SYSTEM_USAGE_GUIDE.md](./05_guides/MACRO_SYSTEM_USAGE_GUIDE.md) | 宏系统使用指南 |
| [WASM_USAGE_GUIDE.md](./05_guides/WASM_USAGE_GUIDE.md) | WASM 使用指南 |
| [UNSAFE_RUST_GUIDE.md](./05_guides/UNSAFE_RUST_GUIDE.md) | Unsafe Rust 专题 |
| [AI_RUST_ECOSYSTEM_GUIDE.md](./05_guides/AI_RUST_ECOSYSTEM_GUIDE.md) | AI+Rust 生态（Burn/Candle/LLM） |
| [CLI_APPLICATIONS_GUIDE.md](./05_guides/CLI_APPLICATIONS_GUIDE.md) | CLI 应用开发（对标 Command Line Book） |
| [EMBEDDED_RUST_GUIDE.md](./05_guides/EMBEDDED_RUST_GUIDE.md) | 嵌入式 Rust（对标 Embedded Book） |
| [TROUBLESHOOTING_GUIDE.md](./05_guides/TROUBLESHOOTING_GUIDE.md) | 故障排查指南 |
| [PERFORMANCE_TUNING_GUIDE.md](./05_guides/PERFORMANCE_TUNING_GUIDE.md) | 性能调优指南 |
| [PERFORMANCE_TESTING_REPORT.md](./05_guides/PERFORMANCE_TESTING_REPORT.md) | 性能测试报告 |
| [TESTING_COVERAGE_GUIDE.md](./05_guides/TESTING_COVERAGE_GUIDE.md) | 测试覆盖率指南 |
| [BEST_PRACTICES.md](./05_guides/BEST_PRACTICES.md) | 综合最佳实践 |
| [ADVANCED_TOPICS_DEEP_DIVE.md](./05_guides/ADVANCED_TOPICS_DEEP_DIVE.md) | 高级主题深度指南 |
| [CROSS_MODULE_INTEGRATION_EXAMPLES.md](./05_guides/CROSS_MODULE_INTEGRATION_EXAMPLES.md) | 跨模块集成示例 |
| [FINAL_DOCUMENTATION_COMPLETION_GUIDE.md](./05_guides/FINAL_DOCUMENTATION_COMPLETION_GUIDE.md) | 文档完善最终指南 |
| [workflow/](./05_guides/workflow/) | 工作流理论与模型（01_workflow_theory.md、05_workflow_models.md） |

---

## 06 工具链与版本

| 文档/目录 | 说明 |
|-----------|------|
| [06_toolchain/](./06_toolchain/) | 编译器、Cargo、rustdoc、Rust 1.89–1.93 版本演进 |

**Rust 1.92 版本文档**（已归档）:

| 文档 | 说明 |
|------|------|
| [archive/version_reports/](./archive/version_reports/) | RUST_192_* 6 个文件 |

---

## 07 项目元文档

| 文档 | 说明 |
|------|------|
| [KNOWLEDGE_STRUCTURE_FRAMEWORK.md](./07_project/KNOWLEDGE_STRUCTURE_FRAMEWORK.md) | 知识结构框架 |
| [MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md](./07_project/MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md) | 模块知识结构指南 |
| [DOCUMENTATION_CROSS_REFERENCE_GUIDE.md](./07_project/DOCUMENTATION_CROSS_REFERENCE_GUIDE.md) | 文档交叉引用指南 |
| [PROJECT_ARCHITECTURE_GUIDE.md](./07_project/PROJECT_ARCHITECTURE_GUIDE.md) | 项目架构指南 |
| [RUST_RELEASE_TRACKING_CHECKLIST.md](./07_project/RUST_RELEASE_TRACKING_CHECKLIST.md) | 新版本发布后的更新流程 |
| [TASK_INDEX.md](./07_project/TASK_INDEX.md) | 未完成任务与计划总索引 |
| [MODULE_1.93_ADAPTATION_STATUS.md](./07_project/MODULE_1.93_ADAPTATION_STATUS.md) | C01–C12 模块 1.93 适配状态 |
| [PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md](./07_project/PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md) | 项目批判性评估报告 |
| [INTERNATIONAL_BENCHMARK_CRITICAL_EVALUATION_2026_02.md](./07_project/INTERNATIONAL_BENCHMARK_CRITICAL_EVALUATION_2026_02.md) | 国际化对标与全面批判性评估 |
| [ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md](./07_project/ALIGNMENT_KNOWLEDGE_CRITICAL_EVALUATION_2026_02.md) | 对齐知识批判性评估与推进方案 |
| [DOCUMENTATION_THEME_ORGANIZATION_PLAN.md](./07_project/DOCUMENTATION_THEME_ORGANIZATION_PLAN.md) | 文档主题梳理与重组规划 |
| [archive/process_reports/](./archive/process_reports/) | 改进总结、计划实施、链接修复、Crates 计划等过程性文档 |

---

## 其他

| 文档/目录 | 说明 |
|-----------|------|
| [archive/](./archive/) | 归档文件 |
| [backup/](./backup/) | 备份文件（.rar/.zip，非日常查阅） |

---

## 相关链接

- [docs/README.md](./README.md) - 文档中心主入口
- [项目主 README](../README.md) - 项目概览
