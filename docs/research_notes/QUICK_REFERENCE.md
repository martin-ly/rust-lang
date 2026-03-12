# 研究笔记快速参考

> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成（全面检查推进计划 Phase 1–8 完成）

---

## 📊 快速导航

> 💡 **提示**: 需要更详细的查找功能？请查看 [快速查找工具](./QUICK_FIND.md)！
> 📐 **分类体系**: 按文档角色、知识层次、主题域查找 → [CLASSIFICATION.md](./CLASSIFICATION.md)
> 📋 **速查卡**: 按主题的语法速查、代码示例、反例 → [docs/quick_reference](../02_reference/quick_reference/README.md)

---

### 按研究领域查找

#### 🔬 形式化方法研究

| 主题  | 文件 | 状态  |
| :--- | :--- | :--- |
| 完备性缺口  | [00_completeness_gaps.md](./formal_methods/00_completeness_gaps.md)                | ✅ Phase 1–6 100% |
| 所有权模型形式化 | [ownership_model.md](./formal_methods/ownership_model.md)                          | ✅ 100%
| 借用检查器证明   | [borrow_checker_proof.md](./formal_methods/borrow_checker_proof.md)                | ✅ 100%           |
| 异步状态机形式化 | [async_state_machine.md](./formal_methods/async_state_machine.md)                  | ✅ 100%           |
| 生命周期形式化   | [lifetime_formalization.md](./formal_methods/lifetime_formalization.md)            | ✅ 100%           |
| Pin 和自引用类型 | [pin_self_referential.md](./formal_methods/pin_self_referential.md)                | ✅ 100%           |

#### 🔷 类型理论研究

| 主题 | 文件 | 状态 |
| :--- | :--- | :--- |
| 完备性缺口       | [00_completeness_gaps.md](./type_theory/00_completeness_gaps.md)               | ✅ 阶段 1–7 Def 占位 |
| 类型构造能力     | [construction_capability.md](./type_theory/construction_capability.md)         | ✅ Def TCON1、矩阵、决策树 |
| 类型系统基础     | [type_system_foundations.md](./type_theory/type_system_foundations.md)         | ✅ 100%               |
| Trait 系统形式化 | [trait_system_formalization.md](./type_theory/trait_system_formalization.md)   | ✅ 100%               |
| 生命周期形式化   | [lifetime_formalization.md](./type_theory/lifetime_formalization.md)           | ✅ 100%               |
| 高级类型特性     | [advanced_types.md](./type_theory/advanced_types.md)                           | ✅ 100%               |
| 型变理论         | [variance_theory.md](./type_theory/variance_theory.md)                         | ✅ 100%               |

#### 🌐 软件设计理论

| 主题  | 文件 | 状态 |
| :--- | :--- | :--- |
| 设计模式形式化   | [01_design_patterns_formal](./software_design_theory/01_design_patterns_formal/README.md)             | ✅ 23 模式  |
| 23/43 模型 | [02_workflow_safe_complete_models](./software_design_theory/02_workflow_safe_complete_models/README.md) | ✅ 100% |
| 执行模型 | [03_execution_models](./software_design_theory/03_execution_models/README.md) | ✅ 五模型 |
| 组合工程 | [04_compositional_engineering](./software_design_theory/04_compositional_engineering/README.md) | ✅ CE-T1–T3 |
| 边界体系 | [05_boundary_system](./software_design_theory/05_boundary_system/README.md) | ✅ 三维矩阵 |
| Rust 惯用模式 | [06_rust_idioms](./software_design_theory/06_rust_idioms.md) | ✅ RAII、Newtype、类型状态 |
| 反模式与边界 | [07_anti_patterns](./software_design_theory/07_anti_patterns.md) | ✅ 13 反例、规避策略 |

#### ⚡ 实验研究

| 主题 | 文件 | 状态 |
| :--- | :--- | :--- |
| 性能基准测试   | [performance_benchmarks.md](./experiments/performance_benchmarks.md)               | ✅ 100% |
| 内存分析       | [memory_analysis.md](./experiments/memory_analysis.md)                             | ✅ 100% |
| 编译器优化     | [compiler_optimizations.md](./experiments/compiler_optimizations.md)               | ✅ 100% |
| 并发性能       | [concurrency_performance.md](./experiments/concurrency_performance.md)             | ✅ 100% |
| 宏展开性能     | [macro_expansion_performance.md](./experiments/macro_expansion_performance.md)     | ✅ 100% |

#### 🌐 综合研究

| 主题 | 文件 | 状态 |
| :--- | :--- | :--- |
| 实际应用案例 | [practical_applications.md](./practical_applications.md) | ✅ 100% |
| 研究方法论 | [research_methodology.md](./research_methodology.md) | ✅ 100% |

---

## 🎯 按研究目标查找

### 我想证明某个性质

**形式化证明体系**（2026-02-14）:

- 批判性分析与推进计划 → [FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](./FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md)
- 核心定理完整证明 → [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md)（L2）
- Coq 证明骨架 → [archive/deprecated/coq_skeleton](../archive/deprecated/coq_skeleton/README.md)、[COQ_ISABELLE_PROOF_SCAFFOLDING](../archive/deprecated/README.md)（已归档）

**形式化方法研究**:

- 内存安全 → [所有权模型形式化](./formal_methods/ownership_model.md)
- 数据竞争自由 → [借用检查器证明](./formal_methods/borrow_checker_proof.md)
- 并发安全 → [异步状态机形式化](./formal_methods/async_state_machine.md)
- 引用有效性 → [生命周期形式化](./formal_methods/lifetime_formalization.md)

### 我想理解类型系统

**类型理论研究**:

- 基础概念 → [类型系统基础](./type_theory/type_system_foundations.md)
- Trait 系统 → [Trait 系统形式化](./type_theory/trait_system_formalization.md)
- 高级特性 → [高级类型特性](./type_theory/advanced_types.md)
- 型变规则 → [型变理论](./type_theory/variance_theory.md)

### 我想优化性能

**实验研究**:

- 性能测试 → [性能基准测试](./experiments/performance_benchmarks.md)
- 内存优化 → [内存分析](./experiments/memory_analysis.md)
- 编译优化 → [编译器优化](./experiments/compiler_optimizations.md)
- 并发优化 → [并发性能](./experiments/concurrency_performance.md)

### 我想学习研究方法

**研究方法论**:

- 方法选择 → [研究方法论](./research_methodology.md)
- 工具使用 → [研究方法论 - 研究工具](./research_methodology.md#-研究工具)
- 实践指南 → [研究方法论 - 实践指南](./research_methodology.md#-实践指南)

---

## 🔍 按关键词查找

### 所有权相关

- 所有权模型 → [ownership_model.md](./formal_methods/ownership_model.md)
- 借用检查器 → [borrow_checker_proof.md](./formal_methods/borrow_checker_proof.md)
- Pin 类型 → [pin_self_referential.md](./formal_methods/pin_self_referential.md)

### 类型系统相关

- 类型构造能力 → [construction_capability.md](./type_theory/construction_capability.md)
- 类型推导 → [type_system_foundations.md](./type_theory/type_system_foundations.md)
- Trait → [trait_system_formalization.md](./type_theory/trait_system_formalization.md)
- GATs → [advanced_types.md](./type_theory/advanced_types.md)
- const 泛型 → [advanced_types.md](./type_theory/advanced_types.md)
- 型变 → [variance_theory.md](./type_theory/variance_theory.md)
- 类型理论缺口 → [00_completeness_gaps.md](./type_theory/00_completeness_gaps.md)

### 异步相关

- Future/Poll → [async_state_machine.md](./formal_methods/async_state_machine.md)
- async/await → [async_state_machine.md](./formal_methods/async_state_machine.md)

### 性能相关

- 基准测试 → [performance_benchmarks.md](./experiments/performance_benchmarks.md)
- 内存分析 → [memory_analysis.md](./experiments/memory_analysis.md)
- 编译器优化 → [compiler_optimizations.md](./experiments/compiler_optimizations.md)
- 并发性能 → [concurrency_performance.md](./experiments/concurrency_performance.md)
- 宏性能 → [macro_expansion_performance.md](./experiments/macro_expansion_performance.md)

### 生命周期相关

- 生命周期语义 → [lifetime_formalization.md](./formal_methods/lifetime_formalization.md)
- 生命周期推断 → [lifetime_formalization.md](./type_theory/lifetime_formalization.md)

---

## 🛠️ 常用工具快速查找

### 形式化验证工具

- **Coq** → [研究方法论](./research_methodology.md#1-形式化研究方法)
- **Lean** → [研究方法论](./research_methodology.md#1-形式化研究方法)
- **Isabelle/HOL** → [研究方法论](./research_methodology.md#1-形式化研究方法)
- **Prusti** → [研究方法论](./research_methodology.md#验证工具)

### 性能分析工具

- **Criterion.rs** → [性能基准测试](./experiments/performance_benchmarks.md)
- **perf** → [编译器优化](./experiments/compiler_optimizations.md)
- **Valgrind** → [内存分析](./experiments/memory_analysis.md)
- **flamegraph** → [研究方法论](./research_methodology.md#分析工具)

### 内存分析工具

- **Miri** → [研究方法论](./research_methodology.md#验证工具)
- **heaptrack** → [内存分析](./experiments/memory_analysis.md)
- **dhat** → [内存分析](./experiments/memory_analysis.md)

---

## 📚 学习路径建议

### 初学者路径

1. [类型系统基础](./type_theory/type_system_foundations.md) - 理解基本概念
2. [所有权模型形式化](./formal_methods/ownership_model.md) - 理解所有权
3. [性能基准测试](./experiments/performance_benchmarks.md) - 开始实验

### 进阶路径

1. [Trait 系统形式化](./type_theory/trait_system_formalization.md) - 深入类型系统
2. [借用检查器证明](./formal_methods/borrow_checker_proof.md) - 理解借用规则
3. [高级类型特性](./type_theory/advanced_types.md) - 学习高级特性

### 专家路径

1. [型变理论](./type_theory/variance_theory.md) - 深入类型理论
2. [异步状态机形式化](./formal_methods/async_state_machine.md) - 形式化异步系统
3. [研究方法论](./research_methodology.md) - 掌握研究方法

---

## 🔗 相关资源

### 核心文档

- [主索引](./README.md) - 完整的研究笔记索引
- [速查卡快速参考](../02_reference/quick_reference/README.md) - 20 个速查卡（含 AI/ML、类型、所有权、并发、设计模式等）；与本研究笔记互为补充
- [完整索引](./INDEX.md) - 所有研究笔记的详细索引
- [软件设计理论](./software_design_theory/README.md) - 设计模式、23/43、执行模型、组合工程
- [快速入门指南](./GETTING_STARTED.md) - 新用户入门指南
- [常见问题解答](./FAQ.md) - 常见问题解答
- [维护指南](./MAINTENANCE_GUIDE.md) - 系统维护指南
- [最佳实践](./BEST_PRACTICES.md) - 研究笔记最佳实践
- [术语表](./GLOSSARY.md) - 专业术语解释
- [研究资源汇总](./RESOURCES.md) - 学术和工具资源
- [系统集成指南](./SYSTEM_INTEGRATION.md) - 与形式化工程系统的集成
- [研究笔记示例](./EXAMPLE.md) - 完整的研究笔记示例
- [形式化方法索引](./formal_methods/README.md)
- [类型理论索引](./type_theory/README.md)
- [核心特性完整链](./CORE_FEATURES_FULL_CHAIN.md) - 13 项核心特性 Def→示例→论证→证明
- [特性精简模板](./FEATURE_TEMPLATE.md) - 79 项非核心特性模板
- [版本增量更新流程](./INCREMENTAL_UPDATE_FLOW.md) - 1.94+ 发布后更新步骤
- [实验研究索引](./experiments/README.md)
- [工具使用指南](./TOOLS_GUIDE.md) - 研究工具详细指南

### 外部资源

- [形式化工程系统](../rust-formal-engineering-system/README.md)
- [Rust Book](https://doc.rust-lang.org/book/README.md)
- [Rust Reference](https://doc.rust-lang.org/reference/README.md)

---

**维护团队**: Rust Research Community
**最后更新**: 2026-02-12
**状态**: ✅ **研究笔记系统 100% 完成**（全面检查推进计划 Phase 1–8 完成）
