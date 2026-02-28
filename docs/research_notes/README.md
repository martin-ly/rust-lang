# 🔬 Rust 研究笔记

> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 🚀 从这里开始

**首次使用？** 按目标选一条路径 → **[00_ORGANIZATION_AND_NAVIGATION](./00_ORGANIZATION_AND_NAVIGATION.md)**

| 目标 | 入口 |
| :--- | :--- |
| 理解形式化证明 | [FORMAL_FULL_MODEL_OVERVIEW](./FORMAL_FULL_MODEL_OVERVIEW.md) → [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md) |
| 查概念/证明 | [QUICK_FIND](./QUICK_FIND.md) |
| 选设计模式/并发模型 | [software_design_theory/00_MASTER_INDEX](./software_design_theory/00_MASTER_INDEX.md) |
| 理解三大支柱 | [AUTHORITATIVE_ALIGNMENT_GUIDE](./AUTHORITATIVE_ALIGNMENT_GUIDE.md)（原 RESEARCH_PILLARS_AND_SUSTAINABLE_PLAN 已归档） |
| 完整总结与论证脉络 | [00_COMPREHENSIVE_SUMMARY](./00_COMPREHENSIVE_SUMMARY.md) → [ARGUMENTATION_CHAIN_AND_FLOW](./ARGUMENTATION_CHAIN_AND_FLOW.md) |
| 批判性意见与改进计划 | [RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](../archive/process_reports/2026_02/RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md) |
| **结构梳理与归档约定** | **[RESEARCH_NOTES_ORGANIZATION](./RESEARCH_NOTES_ORGANIZATION.md)** — 实际目录、归档说明、入口与索引 |
| 格式统一与内容/Rust 1.93 对齐计划 | [FORMAT_AND_CONTENT_ALIGNMENT_PLAN](../archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md) |
| 层次化映射（文档树/概念↔定理/文档↔思维表征） | [HIERARCHICAL_MAPPING_AND_SUMMARY](./HIERARCHICAL_MAPPING_AND_SUMMARY.md) |
| **docs 全结构梳理**（100% 覆盖） | [DOCS_STRUCTURE_OVERVIEW](../DOCS_STRUCTURE_OVERVIEW.md) |
| **目录缺失与内容深化计划** | [00_COMPREHENSIVE_SUMMARY](./00_COMPREHENSIVE_SUMMARY.md) 或 [TOC_AND_CONTENT_DEEPENING_PLAN](../archive/process_reports/2026_02/TOC_AND_CONTENT_DEEPENING_PLAN.md) (归档) |

---

## 📊 目录结构

**详细梳理**（实际文件清单、归档约定、formal_methods 概览）：见 **[RESEARCH_NOTES_ORGANIZATION.md](./RESEARCH_NOTES_ORGANIZATION.md)**。

```text
research_notes/
├── 00_ORGANIZATION_AND_NAVIGATION.md  # 组织架构与按目标导航（首次使用入口）
├── README.md                    # 本索引文件
├── RESEARCH_NOTES_ORGANIZATION.md  # 全面梳理（结构、归档、版本、维护）
├── formal_methods/              # 形式化方法研究（六篇核心 + 思维导图/矩阵/决策树，见该目录 README）
│   ├── README.md
│   ├── 00_completeness_gaps.md  # 完备性缺口（Phase 1–6 100% 完成）
│   ├── ownership_model.md       # 所有权模型形式化
│   ├── borrow_checker_proof.md  # 借用检查器证明
│   ├── async_state_machine.md   # 异步状态机形式化
│   ├── lifetime_formalization.md # 生命周期形式化
│   ├── pin_self_referential.md  # Pin 和自引用类型形式化
│   ├── send_sync_formalization.md
│   └── …（思维导图、矩阵、决策树等见 [formal_methods/README](./formal_methods/README.md)）
├── type_theory/                 # 类型理论研究
│   ├── README.md
│   ├── 00_completeness_gaps.md  # 完备性缺口（形式化论证不充分声明）
│   ├── construction_capability.md  # 类型构造能力（Def TCON1、矩阵、决策树）
│   ├── type_system_foundations.md
│   ├── trait_system_formalization.md
│   ├── lifetime_formalization.md
│   ├── advanced_types.md
│   └── variance_theory.md
├── software_design_theory/      # 软件设计理论研究
│   ├── 01_design_patterns_formal/  # 设计模式形式化（GoF 23）
│   ├── 02_workflow_safe_complete_models/  # 23 安全 / 43 完全模型
│   ├── 03_execution_models/       # 同步/异步/并发/并行/分布式
│   ├── 04_compositional_engineering/  # 组合工程有效性
│   ├── 05_boundary_system/        # 边界体系统一分析
│   ├── 06_rust_idioms.md          # Rust 惯用模式（RAII、Newtype、类型状态）
│   └── 07_anti_patterns.md        # 反模式与边界
└── experiments/                 # 实验研究
    ├── README.md
    ├── performance_benchmarks.md
    ├── memory_analysis.md
    ├── compiler_optimizations.md
    ├── concurrency_performance.md
    └── macro_expansion_performance.md
├── practical_applications.md    # 实际应用案例研究
├── research_methodology.md      # 研究方法论
├── QUICK_REFERENCE.md           # 快速参考索引
├── RESEARCH_ROADMAP.md          # 研究路线图
├── TEMPLATE.md                  # 研究笔记模板
├── CONTRIBUTING.md              # 贡献指南
├── QUALITY_CHECKLIST.md         # 质量检查清单
├── SYSTEM_SUMMARY.md            # 系统总结
├── TOOLS_GUIDE.md              # 研究工具使用指南
├── CHANGELOG.md                # 更新日志
├── INDEX.md                    # 完整索引
├── GETTING_STARTED.md          # 快速入门指南
├── FAQ.md                      # 常见问题解答
├── MAINTENANCE_GUIDE.md        # 维护指南
├── BEST_PRACTICES.md           # 最佳实践
├── GLOSSARY.md                 # 术语表
├── RESOURCES.md                # 研究资源汇总
├── SYSTEM_INTEGRATION.md       # 系统集成指南
├── EXAMPLE.md                  # 研究笔记示例
├── PROGRESS_TRACKING.md        # 研究进展跟踪
├── TASK_CHECKLIST.md           # 研究任务清单
├── PROOF_INDEX.md              # 形式化证明文档索引 🆕
├── INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md  # 国际形式化验证对标索引 🆕
├── FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md  # 批判性分析与可持续推进计划 🆕
├── FORMAL_FULL_MODEL_OVERVIEW.md  # 形式化全模型入口（统一形式系统）🆕
├── RUSTBELT_ALIGNMENT.md  # RustBelt 逐章对标 🆕
├── EXECUTABLE_SEMANTICS_ROADMAP.md  # 可执行语义路线图 🆕
├── CORE_THEOREMS_FULL_PROOFS.md  # 核心定理完整证明（L2 级，数学风格）🆕
├── THEOREM_RUST_EXAMPLE_MAPPING.md  # 定理↔Rust 示例映射 🆕
├── AENEAS_INTEGRATION_PLAN.md  # 已归档 → [archive/deprecated/](../archive/deprecated/)
├── COQ_OF_RUST_INTEGRATION_PLAN.md  # 已归档 → [archive/deprecated/](../archive/deprecated/)
├── COQ_ISABELLE_PROOF_SCAFFOLDING.md  # 已归档 → [archive/deprecated/](../archive/deprecated/)
├── coq_skeleton/  # 已归档 → [archive/deprecated/coq_skeleton/](../archive/deprecated/coq_skeleton/)
├── CONTENT_ENHANCEMENT.md      # 内容完善指南（含层次推进、实质内容自检表）🆕
├── CLASSIFICATION.md           # 文档分类体系（按角色/层次/主题域）🆕
├── WRITING_GUIDE.md            # 研究笔记写作指南
├── STATISTICS.md               # 研究笔记系统统计报告
└── QUICK_FIND.md               # 研究笔记快速查找
```

---

## 🎯 研究目标

本目录旨在记录和推进 Rust 语言相关的深入研究，包括：

1. **形式化方法**：所有权、借用检查器、异步系统的形式化建模与证明
2. **类型理论**：Rust 类型系统的理论基础、范畴论解释、形式化验证
3. **实验研究**：性能基准测试、内存分析、编译器优化实验
4. **实际应用**：实际项目案例研究、最佳实践总结
5. **研究方法**：研究方法和工具的使用指南

---

## 📚 研究方向

### 1. 形式化方法 (formal_methods/)

**目标**: 对 Rust 核心机制进行形式化建模和证明

**研究主题**:

- ✅ 所有权模型的形式化定义
- ✅ 借用检查器的正确性证明
- ✅ 异步 Future/Poll 状态机的形式化描述
- ✅ 生命周期系统的形式化语义
- ✅ 并发安全的形式化保证
- ✅ Rust 1.93.1 新特性的形式化分析（已完成）🆕
- ✅ Rust 1.93.0 新特性的形式化分析（已完成）
- ✅ Rust 1.91.1 新特性的形式化分析（已完成）

**已完成的证明**:

- ✅ 所有权唯一性证明
- ✅ 内存安全框架证明
- ✅ 数据竞争自由证明
- ✅ 借用规则正确性证明
- ✅ 引用有效性证明
- ✅ 生命周期推断算法正确性证明
- ✅ 类型安全证明（进展性、保持性）
- ✅ 类型推导正确性证明
- ✅ 类型推导算法正确性证明

**证明文档索引**: [PROOF_INDEX.md](./PROOF_INDEX.md)

**按证明深度/层次导航**:

- [按证明深度](PROOF_INDEX.md#-按证明深度导航) — L1 证明思路 / L2 完整证明 / L3 机器可检查
- [按抽象层次](FORMAL_FULL_MODEL_OVERVIEW.md#四抽象层次对应) — 语言级 / MIR 级 / 内存级
- [形式化全模型入口](FORMAL_FULL_MODEL_OVERVIEW.md) — 统一形式系统、公理列表、定理依赖 DAG

**论证系统指南**: [FORMAL_PROOF_SYSTEM_GUIDE.md](./FORMAL_PROOF_SYSTEM_GUIDE.md) - 论证缺口分析、概念-公理-定理映射、反例与证明树索引

**全面系统化梳理总览**: [COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md](./COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md) - 全局一致性、语义归纳、概念族谱、论证缺口追踪、思维表征全索引

**全局统一系统化框架**: [UNIFIED_SYSTEMATIC_FRAMEWORK.md](./UNIFIED_SYSTEMATIC_FRAMEWORK.md) - 全景思维导图、多维矩阵、公理-定理证明全链路、决策树、反例总索引

**构造性语义与表达能力边界**: [LANGUAGE_SEMANTICS_EXPRESSIVENESS.md](./LANGUAGE_SEMANTICS_EXPRESSIVENESS.md) - 操作/指称/公理语义形式化、表达能力边界论证

**设计机制论证**: [DESIGN_MECHANISM_RATIONALE.md](./DESIGN_MECHANISM_RATIONALE.md) - Pin 堆/栈区分、所有权、借用、型变等设计理由与完整论证

**论证缺口与设计理由综合索引**: [ARGUMENTATION_GAP_INDEX.md](./ARGUMENTATION_GAP_INDEX.md) - 缺口追踪、设计理由矩阵、思维表征覆盖

**理论体系与论证体系结构**（顶层框架）: [THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md](./THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) - 四层理论架构、五层论证结构、安全与非安全全面论证

**安全与非安全全面论证**: [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md](./SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) - 边界、契约、UB 分类、安全抽象

**Rust 1.93 语言特性全面分析**: [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md](./RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) - 92 项语言特性全覆盖、设计论证

**批判性分析与推进计划**: [FORMAL_PROOF_SYSTEM_GUIDE](./FORMAL_PROOF_SYSTEM_GUIDE.md) - 形式化证明体系批判性分析、国际对标、可持续推进方案

**核心定理完整证明**: [CORE_THEOREMS_FULL_PROOFS.md](./CORE_THEOREMS_FULL_PROOFS.md) - ownership T2、borrow T1、type T3 的 L2 级完整证明（归纳基/步、辅助引理、反例否定）

**国际形式化验证对标**: [INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) - RustBelt、Aeneas、RustSEM 等对标与差距

**权威对齐指南**: [AUTHORITATIVE_ALIGNMENT_GUIDE.md](./AUTHORITATIVE_ALIGNMENT_GUIDE.md) - 研究笔记权威来源对齐、技术决策参考（原三大支柱文档已归档至 archive/process_reports/2026_02/）

**相关文档**:

- [形式化工程系统](../rust-formal-engineering-system/01_theoretical_foundations/)
- [所有权与借用](../../crates/c01_ownership_borrow_scope/docs/README.md)
- [异步语义理论](../../crates/c06_async/src/async_semantics_theory.rs)

---

### 2. 类型理论 (type_theory/)

**目标**: 深入理解 Rust 类型系统的理论基础

**研究主题**:

- ✅ Rust 类型系统的范畴论解释
- ✅ Trait 系统的形式化定义
- ✅ 型变（Variance）的数学基础
- ✅ GATs (Generic Associated Types) 的类型理论
- ✅ const 泛型的类型系统影响
- ✅ Dependent Type 与 Rust 的关系（已在高级类型特性中涵盖）
- ✅ Rust 1.93.0 类型系统改进的形式化分析（已完成）🆕
- ✅ Rust 1.92.0 类型系统改进的形式化分析（已完成）
- ✅ Rust 1.91.1 类型系统改进的形式化分析（已完成）

**相关文档**:

- [类型系统基础](../../crates/c02_type_system/docs/tier_04_advanced/)
- [类型型变参考](../../crates/c02_type_system/docs/tier_03_references/) - 类型系统参考文档
- [形式化工程系统 - 类型系统](../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/)

---

### 3. 实验研究 (experiments/)

**目标**: 通过实验验证理论假设，优化实践

**研究主题**:

- ✅ 性能基准测试方法论
- ✅ 内存使用模式分析
- ✅ 并发性能测试框架
- ✅ 编译器优化效果评估
- ✅ 宏展开性能分析
- ✅ 不同分配器策略对比（已在内存分析和并发性能中涵盖）
- ✅ Rust 1.93.0 性能改进的实验验证（已完成）🆕
- ✅ Rust 1.92.0 性能改进的实验验证（已完成）
- ✅ Rust 1.91.1 性能改进的实验验证（已完成）

**相关工具**:

- [基准测试框架](../../crates/c08_algorithms/benches/)
- [性能分析工具](../../crates/c06_async/benches/)
- [内存分析工具](../../crates/c05_threads/benches/)

---

## 🔗 相关资源

### 核心文档

- [形式化工程系统](../rust-formal-engineering-system/README.md)
- [研究议程](../rust-formal-engineering-system/09_research_agenda/04_research_methods/README.md) - 形式化工程系统研究方法
- [个人索引](../archive/temp/) - 归档目录（历史文档）

### 代码实现

- [所有权与借用实现](../../crates/c01_ownership_borrow_scope/src/)
- [类型系统实现](../../crates/c02_type_system/src/)
- [异步系统实现](../../crates/c06_async/src/)

### 学习资源

- [类型系统速查卡](../02_reference/quick_reference/type_system.md)
- [所有权速查卡](../02_reference/quick_reference/ownership_cheatsheet.md)
- [异步模式速查卡](../02_reference/quick_reference/async_patterns.md)

---

## 📝 研究笔记规范 {#-研究笔记规范}

### 文档格式

每个研究笔记应包含：

1. **元信息**
   - 创建日期和最后更新日期
   - Rust 版本
   - 状态（进行中/已完成）

2. **研究目标**
   - 明确的研究问题
   - 预期成果

3. **理论基础**
   - 相关数学/逻辑基础
   - 形式化定义

4. **方法与实践**
   - 研究方法
   - 实验设计
   - 代码示例

5. **结果与分析**
   - 研究发现
   - 结论与展望

6. **参考文献**
   - 相关论文
   - 官方文档
   - 相关代码链接

---

## 🚀 快速开始

### 新用户入门

**第一次使用？** 请先阅读 [快速入门指南](./GETTING_STARTED.md)！

### 开始新的研究主题

1. 查看 [研究路线图](./RESEARCH_ROADMAP.md) 了解研究计划
2. 选择合适的子目录（formal_methods/、type_theory/、experiments/）
3. 使用 [研究笔记模板](./TEMPLATE.md) 创建新文件
4. 按照 [研究笔记规范](#-研究笔记规范) 编写内容
5. 使用 [质量检查清单](./QUALITY_CHECKLIST.md) 检查质量
6. 更新对应目录的 README.md
7. 在本索引文件中添加链接

### 贡献研究笔记

研究笔记欢迎社区贡献！请查看：

- [贡献指南](./CONTRIBUTING.md) - 详细的贡献流程和规范
- [质量检查清单](./QUALITY_CHECKLIST.md) - 确保质量的标准
- [研究笔记模板](./TEMPLATE.md) - 快速创建新笔记
- [研究进展跟踪](./PROGRESS_TRACKING.md) - 详细的研究进展跟踪
- [研究任务清单](./TASK_CHECKLIST.md) - 具体的研究任务清单
- [研究笔记写作指南](./WRITING_GUIDE.md) - 详细的写作指导
- [研究笔记内容完善指南](./CONTENT_ENHANCEMENT.md) - 内容完善指导

**贡献要求**:

- ✅ 内容准确、有据可查
- ✅ 代码示例可运行
- ✅ 遵循文档格式规范
- ✅ 提供相关资源链接

---

## 📊 研究进展

### 已完成 ✅ (17个研究笔记，100%)

**形式化方法研究** (5个):

- [x] [所有权模型形式化](./formal_methods/ownership_model.md) - ✅ 已完成 (100%)
- [x] [借用检查器证明](./formal_methods/borrow_checker_proof.md) - ✅ 已完成 (100%)
- [x] [异步状态机形式化](./formal_methods/async_state_machine.md) - ✅ 已完成 (100%)
- [x] [生命周期形式化](./formal_methods/lifetime_formalization.md) - ✅ 已完成 (100%)
- [x] [Pin 和自引用类型形式化](./formal_methods/pin_self_referential.md) - ✅ 已完成 (100%)

**类型理论研究** (5个):

- [x] [类型系统基础](./type_theory/type_system_foundations.md) - ✅ 已完成 (100%)
- [x] [Trait 系统形式化](./type_theory/trait_system_formalization.md) - ✅ 已完成 (100%)
- [x] [生命周期形式化](./type_theory/lifetime_formalization.md) - ✅ 已完成 (100%)
- [x] [高级类型特性](./type_theory/advanced_types.md) - ✅ 已完成 (100%)
- [x] [型变理论](./type_theory/variance_theory.md) - ✅ 已完成 (100%)

**实验研究** (5个):

- [x] [性能基准测试](./experiments/performance_benchmarks.md) - ✅ 已完成 (100%)
- [x] [内存分析](./experiments/memory_analysis.md) - ✅ 已完成 (100%)
- [x] [编译器优化](./experiments/compiler_optimizations.md) - ✅ 已完成 (100%)
- [x] [并发性能研究](./experiments/concurrency_performance.md) - ✅ 已完成 (100%)
- [x] [宏展开性能分析](./experiments/macro_expansion_performance.md) - ✅ 已完成 (100%)

**综合研究** (2个):

- [x] [实际应用案例研究](./practical_applications.md) - ✅ 已完成 (100%)
- [x] [研究方法论](./research_methodology.md) - ✅ 已完成 (100%)

---

## 🆕 Rust 1.93.1 研究更新 🆕

### 最新研究内容

**更新日期**: 2026-02-26

**主要研究方向**:

1. **musl 1.2.5 DNS 解析改进研究**
   - DNS 解析器可靠性改进分析
   - 大型 DNS 记录处理机制研究
   - 递归名称服务器支持改进
   - 相关笔记: [故障排查指南](../05_guides/TROUBLESHOOTING_GUIDE.md)

2. **全局分配器线程本地存储支持研究**
   - 全局分配器使用 `thread_local!` 的机制分析
   - 重入问题避免策略研究
   - 相关笔记: [并发性能研究](./experiments/concurrency_performance.md)

3. **MaybeUninit API 增强研究**
   - 新增安全方法的类型理论分析
   - 未初始化内存的安全性形式化
   - 相关笔记: [类型系统基础](./type_theory/type_system_foundations.md)、[高级类型特性](./type_theory/advanced_types.md)

4. **`cfg` 属性在 `asm!` 行上研究**
   - 内联汇编条件编译的改进
   - 平台特定代码简化策略
   - 相关笔记: [工具链文档](../06_toolchain/05_rust_1.93_vs_1.92_comparison.md)

**详细更新**: 参见 [Rust 1.93 vs 1.92 全面对比分析](../06_toolchain/05_rust_1.93_vs_1.92_comparison.md)

---

## Rust 1.91.1 / 1.92.0 研究更新（历史）

### 历史研究内容

**更新日期**: 2025-11-15 / 2025-12-11

**主要研究方向**:

1. **异步迭代器性能研究**
   - 性能提升 15-20% 的机制分析
   - 异步迭代器链式操作优化研究
   - 相关笔记: [并发性能研究](./experiments/concurrency_performance.md)

2. **const 上下文增强研究**
   - 对非静态常量引用的形式化分析
   - const 泛型配置系统研究
   - 相关笔记: [类型系统基础](./type_theory/type_system_foundations.md)

3. **JIT 编译器优化研究**
   - 异步代码性能提升机制
   - 内联优化策略分析
   - 相关笔记: [编译器优化](./experiments/compiler_optimizations.md)

4. **内存分配优化研究**
   - 小对象分配性能提升 25-30% 分析
   - 内存碎片减少机制研究
   - 相关笔记: [内存分析](./experiments/memory_analysis.md)

**详细更新**: 参见 [Rust 1.91.1 研究更新报告](./RUST_191_RESEARCH_UPDATE_2025_11_15.md)、[Rust 1.92.0 研究更新报告](./RUST_192_RESEARCH_UPDATE_2025_12_11.md)

---

## 📚 综合研究主题

### 实际应用案例研究

**目标**: 通过分析实际应用案例，验证 Rust 理论在实际项目中的应用效果

**相关笔记**: [practical_applications.md](./practical_applications.md)

**研究内容**:

- 系统编程案例
- 网络应用案例
- 并发系统案例
- 嵌入式系统案例

---

### 研究方法论

**目标**: 建立 Rust 研究的方法论体系，为研究提供系统化的方法指导

**相关笔记**: [research_methodology.md](./research_methodology.md)

**研究内容**:

- 形式化研究方法
- 实验研究方法
- 实证研究方法
- 理论研究方法
- 研究工具使用指南

---

## 🗺️ 快速导航

- [快速查找](./QUICK_FIND.md) - 研究笔记快速查找工具（按关键词、领域、目标、优先级）
- [快速参考](./QUICK_REFERENCE.md) - 按主题快速查找研究笔记
- [研究路线图](./RESEARCH_ROADMAP.md) - 研究推进计划和优先级
- [系统总结](./SYSTEM_SUMMARY.md) - 系统概览和统计信息
- [工具使用指南](./TOOLS_GUIDE.md) - 研究工具安装和使用方法
- [更新日志](./CHANGELOG.md) - 系统变更历史记录
- [完整索引](./INDEX.md) - 所有研究笔记的详细索引
- [快速入门指南](./GETTING_STARTED.md) - 新用户入门指南
- [常见问题解答](./FAQ.md) - 常见问题解答
- [维护指南](./MAINTENANCE_GUIDE.md) - 系统维护指南
- [最佳实践](./BEST_PRACTICES.md) - 研究笔记最佳实践（含实质内容不足判断与四步修复法）
- [术语表](./GLOSSARY.md) - 专业术语解释
- [研究资源汇总](./RESOURCES.md) - 学术和工具资源
- [系统集成指南](./SYSTEM_INTEGRATION.md) - 与形式化工程系统的集成
- [研究笔记示例](./EXAMPLE.md) - 完整的研究笔记示例

---

## 🔍 搜索研究笔记

使用以下方式查找研究内容：

```bash
# 搜索关键词
grep -r "关键词" docs/research_notes/

# 查找特定主题
find docs/research_notes -name "*.md" -exec grep -l "主题" {} \;
```

---

## 📞 联系方式

### 获取帮助

- 📖 查看 [常见问题解答](./FAQ.md) 获取常见问题的答案
- 📚 阅读 [快速入门指南](./GETTING_STARTED.md) 了解如何使用系统
- 🐛 提交 Issue 报告问题
- 💬 参与讨论交流
- 📧 联系维护团队

---

**维护团队**: Rust Research Community
**最后更新**: 2026-02-26
**Rust 版本**: 1.93.1+
**状态**: ✅ **研究笔记系统 100% 完成**（17/17 研究笔记全部完成）

**全面梳理**：[RESEARCH_NOTES_ORGANIZATION](./RESEARCH_NOTES_ORGANIZATION.md) — 实际结构、归档约定、入口与索引关系
