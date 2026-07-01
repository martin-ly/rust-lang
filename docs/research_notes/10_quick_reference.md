# 研究笔记快速参考 {#研究笔记快速参考}

> **概念族**: 综合研究
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2025-01-27
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 完成
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Standard Library](https://doc.rust-lang.org/std/) | [Rust By Example](https://doc.rust-lang.org/rust-by-example/)

---

## 📑 目录 {#目录}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>

- [研究笔记快速参考 {#研究笔记快速参考}](#研究笔记快速参考-研究笔记快速参考)
  - [📑 目录 {#目录}](#-目录-目录)
  - [📊 快速导航 {#快速导航}](#-快速导航-快速导航)
    - [按研究领域查找 {#按研究领域查找}](#按研究领域查找-按研究领域查找)
      - [🔬 形式化方法研究 {#形式化方法研究}](#-形式化方法研究-形式化方法研究)
      - [🔷 类型理论研究 {#类型理论研究}](#-类型理论研究-类型理论研究)
      - [🌐 软件设计理论 {#软件设计理论}](#-软件设计理论-软件设计理论)
      - [⚡ 实验研究 {#实验研究}](#-实验研究-实验研究)
      - [🌐 综合研究 {#综合研究}](#-综合研究-综合研究)
  - [🎯 按研究目标查找 {#按研究目标查找}](#-按研究目标查找-按研究目标查找)
    - [我想证明某个性质 {#我想证明某个性质}](#我想证明某个性质-我想证明某个性质)
    - [我想理解类型系统 {#我想理解类型系统}](#我想理解类型系统-我想理解类型系统)
    - [我想优化性能 {#我想优化性能}](#我想优化性能-我想优化性能)
    - [我想学习研究方法 {#我想学习研究方法}](#我想学习研究方法-我想学习研究方法)
  - [🔍 按关键词查找 {#按关键词查找}](#-按关键词查找-按关键词查找)
    - [所有权相关 {#所有权相关}](#所有权相关-所有权相关)
    - [类型系统相关 {#类型系统相关}](#类型系统相关-类型系统相关)
    - [异步相关 {#异步相关}](#异步相关-异步相关)
    - [性能相关 {#性能相关}](#性能相关-性能相关)
    - [生命周期相关 {#生命周期相关}](#生命周期相关-生命周期相关)
  - [🛠️ 常用工具快速查找 {#常用工具快速查找}](#️-常用工具快速查找-常用工具快速查找)
    - [形式化验证工具 {#形式化验证工具}](#形式化验证工具-形式化验证工具)
    - [性能分析工具 {#性能分析工具}](#性能分析工具-性能分析工具)
    - [内存分析工具 {#内存分析工具}](#内存分析工具-内存分析工具)
  - [📚 学习路径建议 {#学习路径建议}](#-学习路径建议-学习路径建议)
    - [初学者路径 {#初学者路径}](#初学者路径-初学者路径)
    - [进阶路径 {#进阶路径}](#进阶路径-进阶路径)
    - [专家路径 {#专家路径}](#专家路径-专家路径)
  - [🔗 相关资源 {#相关资源}](#-相关资源-相关资源)
    - [核心文档 {#核心文档}](#核心文档-核心文档)
    - [外部资源 {#外部资源}](#外部资源-外部资源)
  - [🌍 权威国际化资源链接 {#权威国际化资源链接}](#-权威国际化资源链接-权威国际化资源链接)
    - [Rust Reference 核心章节 {#rust-reference-核心章节}](#rust-reference-核心章节-rust-reference-核心章节)
    - [The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}](#the-rust-programming-language-核心章节-the-rust-programming-language-核心章节)
    - [Rust Standard Library 核心 API / 模块 {#rust-standard-library-核心-api-模块}](#rust-standard-library-核心-api--模块-rust-standard-library-核心-api-模块)
    - [Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}](#rust-by-example--rust-cookbook--cheatsrs-rust-by-example-rust-cookbook-cheatsrs)
    - [快速查找专属语言 / API 链接 {#快速查找专属语言-api-链接}](#快速查找专属语言--api-链接-快速查找专属语言-api-链接)
      - [所有权与借用 {#所有权与借用}](#所有权与借用-所有权与借用)
      - [类型系统 {#类型系统}](#类型系统-类型系统)
      - [异步与并发 {#异步与并发}](#异步与并发-异步与并发)
      - [生命周期 {#生命周期}](#生命周期-生命周期)
      - [宏与错误处理 {#宏与错误处理}](#宏与错误处理-宏与错误处理)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 📊 快速导航 {#快速导航}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**
> 💡 **提示**: 需要更详细的查找功能？请查看 [快速查找工具](10_quick_find.md)！
> 📐 **分类体系**: 按文档角色、知识层次、主题域查找 → [10_classification.md](10_classification.md)
> 📋 **速查卡**: 按主题的语法速查、代码示例、反例 → [docs/quick_reference](../02_reference/quick_reference/README.md)

---

### 按研究领域查找 {#按研究领域查找}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

#### 🔬 形式化方法研究 {#形式化方法研究}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 主题  | 文件 | 状态  |
| :--- | :--- | :--- |
| 完备性缺口  | [00_completeness_gaps.md](formal_methods/00_completeness_gaps.md)                | ✅ Phase 1–6 100% |

| 所有权模型形式化 | [10_ownership_model.md](formal_methods/10_ownership_model.md)                          | ✅ 100%

| 借用检查器证明   | [10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md)                | ✅ 100%           |
| 异步状态机形式化 | [10_async_state_machine.md](formal_methods/10_async_state_machine.md)                  | ✅ 100%           |
| 生命周期形式化   | 10_lifetime_formalization.md            | ✅ 100%           |
| Pin 和自引用类型 | [10_pin_self_referential.md](formal_methods/10_pin_self_referential.md)                | ✅ 100%           |

#### 🔷 类型理论研究 {#类型理论研究}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 主题 | 文件 | 状态 |
| :--- | :--- | :--- |
| 完备性缺口       | [00_completeness_gaps.md](formal_methods/00_completeness_gaps.md)               | ✅ 阶段 1–7 Def 占位 |
| 类型构造能力     | [10_construction_capability.md](type_theory/10_construction_capability.md)         | ✅ Def TCON1、矩阵、决策树 |
| 类型系统基础     | [10_type_system_foundations.md](type_theory/10_type_system_foundations.md)         | ✅ 100%               |
| Trait 系统形式化 | [10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md)   | ✅ 100%               |
| 生命周期形式化   | [10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md)           | ✅ 100%               |
| 高级类型特性     | [10_advanced_types.md](type_theory/10_advanced_types.md)                           | ✅ 100%               |
| 型变理论         | [10_variance_theory.md](type_theory/10_variance_theory.md)                         | ✅ 100%               |

#### 🌐 软件设计理论 {#软件设计理论}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 主题  | 文件 | 状态 |
| :--- | :--- | :--- |
| 设计模式形式化   | [01_design_patterns_formal](software_design_theory/01_design_patterns_formal/README.md)             | ✅ 23 模式  |
| 23/43 模型 | [02_workflow_safe_complete_models](software_design_theory/02_workflow_safe_complete_models/README.md) | ✅ 100% |
| 执行模型 | [03_execution_models](software_design_theory/03_execution_models/README.md) | ✅ 五模型 |
| 组合工程 | [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md) | ✅ CE-T1–T3 |
| 边界体系 | [05_boundary_system](software_design_theory/05_boundary_system/README.md) | ✅ 三维矩阵 |
| Rust 惯用模式 | [06_rust_idioms](software_design_theory/06_rust_idioms.md) | ✅ RAII、Newtype、类型状态 |
| 反模式与边界 | [07_anti_patterns](software_design_theory/07_anti_patterns.md) | ✅ 13 反例、规避策略 |

#### ⚡ 实验研究 {#实验研究}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 主题 | 文件 | 状态 |
| :--- | :--- | :--- |
| 性能基准测试   | [10_performance_benchmarks.md](experiments/10_performance_benchmarks.md)               | ✅ 100% |
| 内存分析       | [10_memory_analysis.md](experiments/10_memory_analysis.md)                             | ✅ 100% |
| 编译器优化     | [10_compiler_optimizations.md](experiments/10_compiler_optimizations.md)               | ✅ 100% |
| 并发性能       | [10_concurrency_performance.md](experiments/10_concurrency_performance.md)             | ✅ 100% |
| 宏展开性能     | [10_macro_expansion_performance.md](experiments/10_macro_expansion_performance.md)     | ✅ 100% |

#### 🌐 综合研究 {#综合研究}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 主题 | 文件 | 状态 |
| :--- | :--- | :--- |
| 实际应用案例 | [10_practical_applications.md](10_practical_applications.md) | ✅ 100% |
| 研究方法论 | [10_research_methodology.md](10_research_methodology.md) | ✅ 100% |

---

## 🎯 按研究目标查找 {#按研究目标查找}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 我想证明某个性质 {#我想证明某个性质}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**形式化证明体系**（2026-02-14）:

- 批判性分析与推进计划 → [FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](10_formal_proof_critical_analysis_and_plan_2026_02.md)
- 核心定理完整证明 → [CORE_THEOREMS_FULL_PROOFS](10_core_theorems_full_proofs.md)（L2）
- Coq 证明骨架 → [archive/deprecated/coq_skeleton](../../archive/deprecated/coq_skeleton/README.md)、[COQ_ISABELLE_PROOF_SCAFFOLDING](../../archive/deprecated/README.md)（已归档）

**形式化方法研究**:

- 内存安全 → [所有权模型形式化](formal_methods/10_ownership_model.md)
- 数据竞争自由 → [借用检查器证明](formal_methods/10_borrow_checker_proof.md)
- 并发安全 → [异步状态机形式化](formal_methods/10_async_state_machine.md)
- 引用有效性 → 生命周期形式化

### 我想理解类型系统 {#我想理解类型系统}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**类型理论研究**:

- 基础概念 → [类型系统基础](type_theory/10_type_system_foundations.md)
- Trait 系统 → [Trait 系统形式化](type_theory/10_trait_system_formalization.md)
- 高级特性 → [高级类型特性](type_theory/10_advanced_types.md)
- 型变规则 → [型变理论](type_theory/10_variance_theory.md)

### 我想优化性能 {#我想优化性能}

>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**实验研究**:

- 性能测试 → [性能基准测试](experiments/10_performance_benchmarks.md)
- 内存优化 → [内存分析](experiments/10_memory_analysis.md)
- 编译优化 → [编译器优化](experiments/10_compiler_optimizations.md)
- 并发优化 → [并发性能](experiments/10_concurrency_performance.md)

### 我想学习研究方法 {#我想学习研究方法}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

**研究方法论**:

- 方法选择 → [研究方法论](10_research_methodology.md)
- 工具使用 → [研究方法论 - 研究工具](10_research_methodology.md)
- 实践指南 → [研究方法论 - 实践指南](10_research_methodology.md)

---

## 🔍 按关键词查找 {#按关键词查找}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 所有权相关 {#所有权相关}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- 所有权模型 → [10_ownership_model.md](formal_methods/10_ownership_model.md)
- 借用检查器 → [10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md)
- Pin 类型 → [10_pin_self_referential.md](formal_methods/10_pin_self_referential.md)

### 类型系统相关 {#类型系统相关}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- 类型构造能力 → [10_construction_capability.md](type_theory/10_construction_capability.md)
- 类型推导 → [10_type_system_foundations.md](type_theory/10_type_system_foundations.md)
- Trait → [10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md)
- GATs → [10_advanced_types.md](type_theory/10_advanced_types.md)
- const 泛型 → [10_advanced_types.md](type_theory/10_advanced_types.md)
- 型变 → [10_variance_theory.md](type_theory/10_variance_theory.md)
- 类型理论缺口 → [00_completeness_gaps.md](formal_methods/00_completeness_gaps.md)

### 异步相关 {#异步相关}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- Future/Poll → [10_async_state_machine.md](formal_methods/10_async_state_machine.md)
- async/await → [10_async_state_machine.md](formal_methods/10_async_state_machine.md)

### 性能相关 {#性能相关}

>
> **[来源: [crates.io](https://crates.io/)]**

- 基准测试 → [10_performance_benchmarks.md](experiments/10_performance_benchmarks.md)
- 内存分析 → [10_memory_analysis.md](experiments/10_memory_analysis.md)
- 编译器优化 → [10_compiler_optimizations.md](experiments/10_compiler_optimizations.md)
- 并发性能 → [10_concurrency_performance.md](experiments/10_concurrency_performance.md)
- 宏性能 → [10_macro_expansion_performance.md](experiments/10_macro_expansion_performance.md)

### 生命周期相关 {#生命周期相关}

>
> **[来源: [docs.rs](https://docs.rs/)]**

- 生命周期语义 → 10_lifetime_formalization.md
- 生命周期推断 → [10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md)

---

## 🛠️ 常用工具快速查找 {#常用工具快速查找}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 形式化验证工具 {#形式化验证工具}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- **Coq** → [研究方法论](10_research_methodology.md#1-形式化研究方法)
- **Lean** → [研究方法论](10_research_methodology.md#1-形式化研究方法)
- **Isabelle/HOL** → [研究方法论](10_research_methodology.md#1-形式化研究方法)
- **Prusti** → [研究方法论](10_research_methodology.md#验证工具)

### 性能分析工具 {#性能分析工具}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- **Criterion.rs** → [性能基准测试](experiments/10_performance_benchmarks.md)
- **perf** → [编译器优化](experiments/10_compiler_optimizations.md)
- **Valgrind** → [内存分析](experiments/10_memory_analysis.md)
- **flamegraph** → [研究方法论](10_research_methodology.md#分析工具)

### 内存分析工具 {#内存分析工具}

>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- **Miri** → [研究方法论](10_research_methodology.md#验证工具)
- **heaptrack** → [内存分析](experiments/10_memory_analysis.md)
- **dhat** → [内存分析](experiments/10_memory_analysis.md)

---

## 📚 学习路径建议 {#学习路径建议}

>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 初学者路径 {#初学者路径}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

1. [类型系统基础](type_theory/10_type_system_foundations.md) - 理解基本概念
2. [所有权模型形式化](formal_methods/10_ownership_model.md) - 理解所有权
3. [性能基准测试](experiments/10_performance_benchmarks.md) - 开始实验

### 进阶路径 {#进阶路径}

>
> **[来源: [crates.io](https://crates.io/)]**

1. [Trait 系统形式化](type_theory/10_trait_system_formalization.md) - 深入类型系统
2. [借用检查器证明](formal_methods/10_borrow_checker_proof.md) - 理解借用规则
3. [高级类型特性](type_theory/10_advanced_types.md) - 学习高级特性

### 专家路径 {#专家路径}

>
> **[来源: [docs.rs](https://docs.rs/)]**

1. [型变理论](type_theory/10_variance_theory.md) - 深入类型理论
2. [异步状态机形式化](formal_methods/10_async_state_machine.md) - 形式化异步系统
3. [研究方法论](10_research_methodology.md) - 掌握研究方法

---

## 🔗 相关资源 {#相关资源}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 核心文档 {#核心文档}

>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [主索引](README.md) - 完整的研究笔记索引
- [速查卡快速参考](../02_reference/quick_reference/README.md) - 20 个速查卡（含 AI/ML、类型、所有权、并发、设计模式等）；与本研究笔记互为补充
- [完整索引](INDEX.md) - 所有研究笔记的详细索引
- [软件设计理论](software_design_theory/README.md) - 设计模式、23/43、执行模型、组合工程
- [快速入门指南](10_getting_started.md) - 新用户入门指南
- [常见问题解答](10_faq.md) - 常见问题解答
- [维护指南](10_maintenance_guide.md) - 系统维护指南
- [最佳实践](10_best_practices.md) - 研究笔记最佳实践
- [术语表](10_glossary.md) - 专业术语解释
- [研究资源汇总](10_resources.md) - 学术和工具资源
- [系统集成指南](10_system_integration.md) - 与形式化工程系统的集成
- [研究笔记示例](10_example.md) - 完整的研究笔记示例
- [形式化方法索引](formal_methods/README.md)
- [类型理论索引](type_theory/README.md)
- [核心特性完整链](10_core_features_full_chain.md) - 13 项核心特性 Def→示例→论证→证明
- [特性精简模板](10_feature_template.md) - 79 项非核心特性模板
- [版本增量更新流程](10_incremental_update_flow.md) - 1.94+ 发布后更新步骤
- [实验研究索引](experiments/README.md)
- [工具使用指南](10_tools_guide.md) - 研究工具详细指南

### 外部资源 {#外部资源}

>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [形式化工程系统](../rust-formal-engineering-system/README.md)
- Rust Book
- Rust Reference

---

**维护团队**: Rust Research Community

**最后更新**: 2026-06-29

**状态**: ✅ 完成

---

## 🌍 权威国际化资源链接 {#权威国际化资源链接}

>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)**
> **来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)**
> **来源: [cheats.rs](https://cheats.rs/)**

本节为速查内容提供官方权威来源与社区经典参考的直通链接，便于深入验证与扩展阅读。

### Rust Reference 核心章节 {#rust-reference-核心章节}

- [Reference 首页](https://doc.rust-lang.org/reference/)
- [Types](https://doc.rust-lang.org/reference/types.html)
- [Items / Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Expressions](https://doc.rust-lang.org/reference/expressions.html)
- [Statements](https://doc.rust-lang.org/reference/statements.html)
- [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html)

### The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}

- [TRPL 首页](https://doc.rust-lang.org/book/)
- [Ch. 4 - Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Ch. 10 - Generic Types, Traits, Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Ch. 13 - Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- [Ch. 15 - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Ch. 19 - Advanced Features / Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)

### Rust Standard Library 核心 API / 模块 {#rust-standard-library-核心-api-模块}

- [std 首页](https://doc.rust-lang.org/std/)
- [std::result](https://doc.rust-lang.org/std/result/)
- [std::option](https://doc.rust-lang.org/std/option/)
- [std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::fmt](https://doc.rust-lang.org/std/fmt/)
- [std::panic](https://doc.rust-lang.org/std/panic/)
- [std::marker (Send / Sync / PhantomData)](https://doc.rust-lang.org/std/marker/)

### Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}

- [Rust By Example 首页](https://doc.rust-lang.org/rust-by-example/)
- [Rust Cookbook 首页](https://rust-lang-nursery.github.io/rust-cookbook/)
- [cheats.rs 首页](https://cheats.rs/)

---

### 快速查找专属语言 / API 链接 {#快速查找专属语言-api-链接}

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

#### 所有权与借用 {#所有权与借用}

- [Reference - Memory allocation and lifetime](https://doc.rust-lang.org/reference/memory-model.html#memory-allocation-and-lifetime)
- [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [TRPL Ch. 4 - References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)
- [std::cell (Cell / RefCell)](https://doc.rust-lang.org/std/cell/)
- [std::rc::Rc](https://doc.rust-lang.org/std/rc/struct.Rc.html)
- [std::sync::Arc](https://doc.rust-lang.org/std/sync/struct.Arc.html)

#### 类型系统 {#类型系统}

- [Reference - Types](https://doc.rust-lang.org/reference/types.html)
- [Reference - Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Reference - Generics](https://doc.rust-lang.org/reference/items/generics.html)
- [TRPL Ch. 10 - Generics](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [std::marker (Send / Sync / Copy / Sized)](https://doc.rust-lang.org/std/marker/)

#### 异步与并发 {#异步与并发}

- [TRPL Ch. 17 - Async / Await](https://doc.rust-lang.org/book/ch17-00-async-await.html)
- [std::future::Future](https://doc.rust-lang.org/std/future/trait.Future.html)
- [std::pin::Pin](https://doc.rust-lang.org/std/pin/struct.Pin.html)
- [std::sync](https://doc.rust-lang.org/std/sync/)
- [std::thread](https://doc.rust-lang.org/std/thread/)

#### 生命周期 {#生命周期}

- [Reference - Lifetime Elision](https://doc.rust-lang.org/reference/lifetime-elision.html)
- [TRPL Ch. 10 - Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)
- [cheats.rs - Lifetimes](https://cheats.rs/#lifetimes)

#### 宏与错误处理 {#宏与错误处理}

- [Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [TRPL Ch. 19 - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [TRPL Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [std::result::Result](https://doc.rust-lang.org/std/result/)
- [std::option::Option](https://doc.rust-lang.org/std/option/)

## 相关概念 {#相关概念}

>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

---
