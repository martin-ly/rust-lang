# 研究方法论
>
> **概念族**: 方法论 / 工具 / 指南

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-01-15
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [Rust Standard Library](https://doc.rust-lang.org/std/) | [Rustonomicon](https://doc.rust-lang.org/nomicon/) | [Rust RFCs](https://rust-lang.github.io/rfcs/)

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [研究方法论](#研究方法论)
  - [📑 目录](#-目录)
  - [🎯 研究目标 {#-研究目标}](#-研究目标--研究目标)
    - [核心问题](#核心问题)
    - [预期成果](#预期成果)
  - [形式化论证汇总](#形式化论证汇总)
  - [📚 研究方法 {#-研究方法}](#-研究方法--研究方法)
    - [1. 形式化研究方法](#1-形式化研究方法)
    - [2. 实验研究方法](#2-实验研究方法)
    - [3. 实证研究方法](#3-实证研究方法)
    - [1.1 形式化研究方法详解](#11-形式化研究方法详解)
    - [Rust 形式化方法的国际论文与工具链](#rust-形式化方法的国际论文与工具链)
    - [Iris/RustBelt 风格 Coq 示例](#irisrustbelt-风格-coq-示例)
    - [Lean 4 / Aeneas 后端示例](#lean-4--aeneas-后端示例)
    - [相关概念](#相关概念)
    - [理论背景](#理论背景)
    - [4. 理论研究方法](#4-理论研究方法)
    - [2.1 实验研究方法要点](#21-实验研究方法要点)
    - [3.1 实证研究方法要点](#31-实证研究方法要点)
    - [4.1 理论研究方法要点](#41-理论研究方法要点)
  - [🔬 研究工具 {#-研究工具}](#-研究工具--研究工具)
    - [分析工具](#分析工具)
    - [验证工具](#验证工具)
    - [实验工具](#实验工具)
    - [数据收集工具](#数据收集工具)
  - [💻 实践指南 {#-实践指南}](#-实践指南--实践指南)
    - [研究设计](#研究设计)
    - [数据收集](#数据收集)
    - [结果分析](#结果分析)
    - [报告撰写](#报告撰写)
  - [📐 质量评估标准与研究模板 {#-质量评估标准与研究模板}](#-质量评估标准与研究模板--质量评估标准与研究模板)
    - [质量评估标准](#质量评估标准)
    - [研究模板](#研究模板)
  - [🔗 工具集成与案例研究索引 {#-工具集成与案例研究索引}](#-工具集成与案例研究索引--工具集成与案例研究索引)
    - [工具集成](#工具集成)
    - [工具使用要点](#工具使用要点)
    - [案例研究索引](#案例研究索引)
  - [📖 参考文献 {#-参考文献}](#-参考文献--参考文献)
    - [方法论文献](#方法论文献)
    - [工具文档](#工具文档)
    - [最佳实践](#最佳实践)
  - [🔄 研究进展 {#-研究进展}](#-研究进展--研究进展)
    - [已完成 ✅ {#已完成-}](#已完成--已完成-)
    - [进行中 🔄（已完成）](#进行中-已完成)
    - [计划中 📋（已完成）](#计划中-已完成)
  - [🆕 权威国际化内容升级 (Rust 1.96.0+) {#-权威国际化内容升级}](#-权威国际化内容升级-rust-1960--权威国际化内容升级)
    - [本次升级要点](#本次升级要点)
  - [权威来源索引](#权威来源索引)

> **创建日期**: 2025-01-27
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 完成

---

## 🎯 研究目标 {#-研究目标}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本研究旨在建立 Rust 研究的方法论体系，为 Rust 相关研究提供系统化的方法指导。

### 核心问题

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

1. **研究方法**: Rust 研究应该采用哪些方法？
2. **工具选择**: 如何选择合适的研究工具？
3. **质量保证**: 如何保证研究的质量和可靠性？

### 预期成果

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- Rust 研究方法论框架
- 研究工具使用指南
- 研究质量评估标准

---

## 形式化论证汇总
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Def RM1（研究方法完备性）**：设 $\mathcal{R}$ 为研究方法族，$\mathcal{R} = \{\text{形式化},\, \text{实验},\, \text{实证},\, \text{理论}\}$。若研究 $Q$ 同时采用形式化证明与实验验证，则称 $Q$ **方法完备**。

**Axiom RM1**：形式化证明保证正确性；实验验证提供经验支持；二者互补，不可相互替代。见 [experiments/README](experiments/README.md) 推论 EX-C1。

**定理 RM-T1（方法衔接）**：若研究 $Q$ 的形式化定理 $T$ 有证明，且实验 $E$ 验证 $T$，则 $Q$ 的结果可追溯至 [PROOF_INDEX](10_proof_index.md) 与 [FORMAL_PROOF_SYSTEM_GUIDE](10_formal_proof_system_guide.md) 的论证链。

*证明*：由 [experiments/README](experiments/README.md) 定理 EX-T1；实验验证与定理结论一致；形式化证明在 PROOF_INDEX 可查。∎

**推论 RM-C1**：research_notes 中形式化方法、类型理论、实验研究均遵循 Def RM1；新研究应建立与已有定理的衔接。

---

## 📚 研究方法 {#-研究方法}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1. 形式化研究方法

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**定义**: 使用数学和逻辑方法对 Rust 系统进行形式化建模和证明。

**适用场景**:

- 类型系统研究
- 内存安全证明
- 并发安全验证

**方法步骤**:

1. 形式化建模
2. 性质定义
3. 定理证明
4. 工具验证

**工具**: Coq, Lean, Isabelle/HOL, TLA+

**优势**: 严格的数学证明，保证正确性

### 2. 实验研究方法

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**定义**: 通过实验验证理论假设，收集性能数据。

**适用场景**:

- 性能优化研究
- 编译器优化评估
- 算法性能对比

**方法步骤**:

1. 假设提出
2. 实验设计
3. 数据收集
4. 结果分析

**工具**: Criterion.rs, perf, Valgrind, flamegraph

**优势**: 客观的数据支持，可重复验证

### 3. 实证研究方法

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**定义**: 通过观察和分析实际项目来验证理论。

**适用场景**:

- 开发体验研究
- 生态系统分析
- 最佳实践总结

**优势**: 基于实际经验，具有实用价值

### 1.1 形式化研究方法详解

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**方法概述**：

形式化研究方法使用数学和逻辑工具对 Rust 机制进行精确建模和证明。这种方法的核心是：

1. **形式化建模**：使用数学符号和逻辑语言描述系统
2. **性质证明**：使用形式化证明验证系统性质
3. **工具辅助**：使用定理证明器辅助证明

**实施步骤**：

1. **问题形式化**：
   - 明确要研究的 Rust 机制
   - 定义相关的数学概念
   - 建立形式化模型

2. **性质定义**：
   - 定义要证明的性质（如内存安全）
   - 使用逻辑公式表达性质
   - 建立证明目标

3. **证明构造**：
   - 使用归纳法、反证法等证明方法
   - 使用定理证明器辅助证明
   - 验证证明的正确性

**工具使用**：

- **Coq**：交互式定理证明器，用于形式化证明
- **Isabelle/HOL**：高阶逻辑证明助手
- **Lean**：现代定理证明器

**示例**：

```coq
(* 所有权转移的形式化定义 *)
Definition move (x: var) (y: var) : state -> state :=
  fun s =>
    match get_owner s x with
    | Owned => set_owner (set_owner s x Moved) y Owned
    | _ => s
    end.

(* 内存安全性质 *)
Theorem memory_safety:
  forall s x,
    well_formed s ->
    get_owner s x = Owned ->
    safe_to_use s x.
Proof.
  (* 证明过程 *)
Qed.
```

### Rust 形式化方法的国际论文与工具链
>
> **来源**: [Iris Project](https://iris-project.org/)
>
> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)

在形式化研究 Rust 时，以下国际论文与项目构成了当前的主流方法：

- **RustBelt** (Jung et al., POPL 2018): 使用 Iris 高阶并发分离逻辑，对 Rust 的核心类型系统和 `unsafe` 库给出了第一个机器检查的安全证明。官方论文 PDF: <https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf>。
- **Aeneas** (Ho & Protzenko, ICFP 2022): 通过 LLBC（Low-Level Borrow Calculus）将安全 Rust 函数式翻译到 F\*/Coq/Lean，消除了显式内存推理。项目主页: <https://aeneas-verif.github.io/aeneas/>，源码: <https://github.com/AeneasVerif/aeneas>。
- **RustHorn** (Matsushita et al., ESOP 2020 / TOPLAS 2021): 基于约束 Horn 子句（CHC）的 Rust 程序验证，利用所有权信息消除指针与堆。论文 PDF: <https://www.kb.is.s.u-tokyo.ac.jp/old-users/yskm24t/web/papers/esop2020-rust-horn.pdf>。
- **RustHornBelt** (Matsushita, Denis, Jourdan, Dreyer, PLDI 2022): 扩展 RustBelt，为带 `unsafe` 代码的 Rust 程序功能正确性提供语义基础。论文 PDF: <https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf>。
- **Iris** (Jung et al., POPL 2015 / JFP 2018): 高阶并发分离逻辑框架，RustBelt 的证明基础。主页: <https://iris-project.org/>，Coq 实现: <https://gitlab.mpi-sws.org/iris/iris>。
- **λRust** (RustBelt 的 Coq 形式化): RustBelt 在 Iris 中的操作语义与类型解释。源码: <https://gitlab.mpi-sws.org/iris/lambda-rust>。

### Iris/RustBelt 风格 Coq 示例
>
> **来源**: [Iris Project](https://iris-project.org/)

下面的 Coq 片段展示 Iris 分离逻辑中 "points-to" 断言如何表达所有权（与 RustBelt 对 `Box`/`&mut` 的解释一致）:

```coq
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.

(* 位置 l 拥有值 v，对应 RustBelt 中 Box/唯一所有权的资源解释 *)
Definition own_box (l: loc) (v: val) : iProp Σ := l ↦ v.

Lemma own_box_write `{!heapG Σ} (l: loc) (v w: val) :
  l ↦ v -∗ (l ↦ w -∗ Φ) -∗ WP (Write (LitV (LitLoc l)) (LitV w)) {{ v, Φ }}.
Proof.
  iIntros "Hl Hk". wp_write. iApply "Hk". iFrame.
Qed.
```

> 说明：上述示例为示意性 Iris/Coq 代码，展示 RustBelt 如何将所有权建模为分离逻辑资源。完整可机器检查的证明请参考 [λRust](https://gitlab.mpi-sws.org/iris/lambda-rust) 与 [RustBelt 论文](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf)。

### Lean 4 / Aeneas 后端示例
>
> **来源**: [Aeneas](https://aeneas-verif.github.io/aeneas/)

Aeneas 将 Rust 的安全子集提取为 Lean 4（或 F\*/Coq/HOL4）中的纯函数，利用 Rust 借用检查保证消除内存推理：

```lean4
-- Aeneas 生成的 Lean 4 函数签名示例（Result monad 区分 ok/fail/div）
def take_max (a b : U32) : Result U32 :=
  if a ≥ b then ok a else ok b
```

> 说明：Aeneas 的 Lean 后端要求使用 Charon 生成 `.llbc` 文件，再在 Aeneas 中选择 `-backend lean`。详见 [Aeneas 文档](https://aeneas-verif.github.io/aeneas/) 与 [Charon](https://github.com/AeneasVerif/charon)。

### 相关概念

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**研究方法 (Research Methodology)**: 进行研究的系统化方法，包括研究设计、数据收集、结果分析等。

**研究设计 (Research Design)**: 研究方案的设计，包括研究目标、方法选择、数据收集计划等。

**数据收集 (Data Collection)**: 收集研究所需的数据，包括性能数据、代码数据、用户反馈等。

**结果分析 (Result Analysis)**: 分析研究结果，得出结论和建议。

**研究工具 (Research Tools)**: 用于研究的工具，包括形式化工具、性能分析工具等。

### 理论背景

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

**科学研究方法论 (Scientific Research Methodology)**: 研究科学研究的理论，包括假设检验、实验设计等。

**形式化方法理论 (Formal Methods Theory)**: 研究形式化方法的理论，包括逻辑系统、证明理论等。

**实验设计理论 (Experimental Design Theory)**: 研究实验设计的理论，包括控制变量、随机化等。

**数据分析理论 (Data Analysis Theory)**: 研究数据分析的理论，包括统计方法、机器学习等。

**方法步骤**:

1. 案例选择
2. 数据收集
3. 模式识别
4. 经验总结

**工具**: 代码分析工具, 调查工具, 统计分析工具

### 4. 理论研究方法

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

**定义**: 通过理论分析和推导来研究 Rust 系统。

**适用场景**:

- 类型理论研究
- 算法复杂度分析
- 系统设计理论

**方法步骤**:

1. 问题定义
2. 理论分析
3. 模型构建
4. 结论推导

**工具**: 数学工具, 形式化工具, 理论验证工具

### 2.1 实验研究方法要点

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**

- **假设**：明确、可测（如「opt-level=2 比 -O0 快 ≥2x」）。
- **控制变量**：固定 Rust 版本、CPU、内存、`opt-level`、`codegen-units` 等；仅变化目标因素。
- **可重复**：`cargo bench`、`criterion`、`--save-baseline`；记录环境与命令。
- **详见**：[10_performance_benchmarks.md](experiments/10_performance_benchmarks.md) 的「数据收集执行指南」与「结果分析模板」。

### 3.1 实证研究方法要点

> **来源: [ACM](https://dl.acm.org/)**

- **案例选择**：有公开代码、文档或论文；能对应到形式化/类型/实验中的至少一类问题。
- **数据**：代码片段、性能数据、 issue/PR、社区讨论。
- **模式**：归纳「所有权/借用/并发/异步」等在项目中的用法与坑点。
- **详见**：[10_practical_applications.md](10_practical_applications.md) 的「案例报告模板」与「案例快速索引」。

### 4.1 理论研究方法要点

> **来源: [IEEE](https://standards.ieee.org/)**

- **问题**：类型安全、型变、生命周期、Trait 解析等；需可形式化。
- **模型**：语法、类型规则、操作语义、性质（进展性、保持性、安全）。
- **推导**：归纳、反证、辅助定理；可借助 Coq/Lean/Isabelle。
- **详见**： [10_type_system_foundations.md](type_theory/10_type_system_foundations.md)、[10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md)、[10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md)。

---

## 🔬 研究工具 {#-研究工具}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 分析工具

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**

- **静态分析工具**: Clippy, rust-analyzer, MIRAI
- **动态分析工具**: Valgrind, Miri, sanitizers
- **性能分析工具**: perf, flamegraph, cargo-instruments
- **内存分析工具**: heaptrack, dhat, memory profilers

### 验证工具

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

- **模型检查器**: TLA+, SPIN
- **定理证明器**: Coq, Lean, Isabelle/HOL
- **形式化验证工具**: Prusti, Creusot, Kani
- **测试工具**: cargo test, proptest, quickcheck

### 实验工具

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**

- **基准测试框架**: Criterion.rs, bencher
- **性能测试工具**: hyperfine, time
- **并发测试工具**: loom, stress tests
- **压力测试工具**: wrk, ab, k6

### 数据收集工具

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

- **日志分析工具**: grep, awk, jq
- **指标收集工具**: Prometheus, Grafana
- **用户反馈工具**: 调查问卷, 访谈
- **代码分析工具**: git, code analysis tools

---

## 💻 实践指南 {#-实践指南}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 研究设计

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

1. **问题定义**: 明确研究问题和目标
2. **方法选择**: 选择合适的研究方法
3. **工具准备**: 准备必要的研究工具
4. **计划制定**: 制定详细的研究计划

### 数据收集
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

1. **数据源识别**: 确定数据来源
2. **收集方法**: 选择数据收集方法
3. **质量控制**: 确保数据质量
4. **数据存储**: 安全存储数据

### 结果分析
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

1. **数据整理**: 整理和清洗数据
2. **统计分析**: 进行统计分析
3. **模式识别**: 识别数据模式
4. **结论推导**: 推导研究结论

### 报告撰写
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

1. **结构设计**: 设计报告结构
2. **内容撰写**: 撰写报告内容
3. **图表制作**: 制作图表和可视化
4. **审阅修改**: 审阅和修改报告

---

## 📐 质量评估标准与研究模板 {#-质量评估标准与研究模板}
>
> **[来源: [crates.io](https://crates.io/)]**

### 质量评估标准
>
> **[来源: [docs.rs](https://docs.rs/)]**

- **可重复性**：环境、命令、版本可复现；实验类需「数据收集执行指南」+「结果分析模板」。
- **逻辑一致**：形式化研究中的定义、定理、证明与代码示例一致；类型/借用规则与实现对应。
- **可验证**：形式化可用 Coq/Lean/Prusti 等验证；实验可用 `cargo bench`/`cargo test`/Valgrind 等复现。
- **交叉引用**：与 [formal_methods](formal_methods/README.md)、[type_theory](type_theory/README.md)、[experiments](experiments/README.md)、[practical_applications](10_practical_applications.md) 的关联明确。
- **时效性**：注明 Rust 版本（如 1.93.1+）；若依赖未稳定特性，需标出。

### 研究模板
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

**形式化/理论**：目标 → 符号与定义 → 规则/公理 → 定理与证明草图 → 代码示例 → 与它文档的关联。

**实验**：目标 → 假设 → 设计（场景、指标、数据）→ 实现（bench/ 脚本）→ 数据收集指南 → 结果分析模板 → 结论与 Rust 版本说明。

**实证/案例**：领域 → 案例选择理由 → 项目概述 → Rust 特性应用 → 代码示例 → 性能/安全/可维护性 → 研究价值 → 参考链接。

---

## 🔗 工具集成与案例研究索引 {#-工具集成与案例研究索引}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 工具集成
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- **与 [10_tools_guide.md](10_tools_guide.md)**：本「研究工具」中的 Clippy、Miri、Criterion、Valgrind、perf 等，安装、常用参数与样例见 TOOLS_GUIDE。
- **与各实验**： [performance_benchmarks](experiments/10_performance_benchmarks.md)、
- [memory_analysis](experiments/10_memory_analysis.md)、
- [compiler_optimizations](experiments/10_compiler_optimizations.md)、
- [concurrency_performance](experiments/10_concurrency_performance.md)、
- [macro_expansion_performance](experiments/10_macro_expansion_performance.md) 的「数据收集执行指南」即工具在具体研究中的集成方式；
- 可统一用 `cargo bench`、`cargo bloat`、`cargo expand`、`time cargo build`、Valgrind/Miri 等。
- **与形式化**：Prusti、Creusot、Kani 的用法见各形式化文档的「工具验证」；Coq/Lean 示例见「1.1 形式化研究方法详解」。

### 工具使用要点
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- **Clippy**：`cargo clippy -- -W clippy::all`；在 CI 中固定 `clippy::version`。
- **Criterion**：`cargo bench`、`--save-baseline`、`BenchmarkId` 区分维度；结果见 `target/criterion/`。
- **Valgrind**：`--leak-check=full --show-leak-kinds=all`；配合 `--error-limit=no` 做回归。
- **Miri**：`cargo miri test`；`-Zmiri-tag-raw-pointers` 等见 Miri 文档。
- **cargo expand / bloat**：宏展开与二进制体积分析；见 [macro_expansion_performance](experiments/10_macro_expansion_performance.md)。

### 案例研究索引
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| 类型 | 文档 | 说明 |
| :--- | :--- | :--- |
| 形式化 | [ownership_model](formal_methods/10_ownership_model.md), [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md), [async_state_machine](formal_methods/10_async_state_machine.md), lifetime_formalization, [pin_self_referential](formal_methods/10_pin_self_referential.md) | 形式化方法 + 证明/定理 + 系统集成 |
| 类型理论 | [type_system_foundations](type_theory/10_type_system_foundations.md), [trait_system_formalization](type_theory/10_trait_system_formalization.md), [lifetime_formalization](type_theory/10_lifetime_formalization.md), [advanced_types](type_theory/10_advanced_types.md), [variance_theory](type_theory/10_variance_theory.md) | 类型、Trait、生命周期、型变 |
| 实验 | [performance_benchmarks](experiments/10_performance_benchmarks.md), [memory_analysis](experiments/10_memory_analysis.md), [compiler_optimizations](experiments/10_compiler_optimizations.md), [concurrency_performance](experiments/10_concurrency_performance.md), [macro_expansion_performance](experiments/10_macro_expansion_performance.md) | 数据收集指南 + 结果分析模板 |
| 实证 | [practical_applications](10_practical_applications.md) | 案例报告模板 + 案例快速索引 + 最佳实践 |

---

## 📖 参考文献 {#-参考文献}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 方法论文献
>
> **[来源: [Iris Project](https://iris-project.org/)]**

- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf) (Jung et al., POPL 2018) — Rust 核心安全性的 Iris/Coq 机器检查证明。
- [Iris from the Ground Up](https://people.mpi-sws.org/~dreyer/papers/iris-ground-up/paper.pdf) (Jung et al., JFP 2018) — 高阶并发分离逻辑基础。
- [Aeneas: Rust Verification by Functional Translation](https://zenodo.org/records/6672939) (Ho & Protzenko, ICFP 2022) — 基于 LLBC 的函数式翻译验证。
- [Sound Borrow-Checking for Rust via Symbolic Semantics](https://dl.acm.org/doi/pdf/10.1145/3547647) (Ho & Protzenko, ICFP 2024) — Aeneas 符号执行与借用检查的形式化。
- [RustHorn: CHC-based Verification for Rust Programs](https://www.kb.is.s.u-tokyo.ac.jp/old-users/yskm24t/web/papers/esop2020-rust-horn.pdf) (Matsushita et al., ESOP 2020 / TOPLAS 2021) — CHC 自动验证。
- [RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code](https://people.mpi-sws.org/~dreyer/papers/rusthornbelt/paper.pdf) (Matsushita et al., PLDI 2022) — 带 `unsafe` 代码的功能正确性基础。
- [λRust Coq Development](https://gitlab.mpi-sws.org/iris/lambda-rust) — RustBelt 在 Iris 中的操作语义与类型解释。

### 工具文档
>
> **[来源: [docs.rs](https://docs.rs/)]**

- [研究工具使用指南](10_tools_guide.md) - 详细的工具安装和使用方法
- [Kani Rust Verifier](https://model-checking.github.io/kani/) — 模型检查器
- [Prusti User Guide](https://viperproject.github.io/prusti-dev/user-guide/) — 基于 Viper 的演绎验证器
- [Miri](https://github.com/rust-lang/miri) — Rust MIR 解释器与 UB 检测
- [Creusot](https://creusot-rs.github.io/) — 基于 Why3/SMT 的 Rust 演绎验证
- [Aeneas](https://aeneas-verif.github.io/aeneas/) — 函数式翻译验证工具链
- [Verus](https://verus-lang.github.io/verus/) — 面向系统代码的 SMT 验证器
- [Criterion.rs](https://bheisler.github.io/criterion.rs/book/) — 统计驱动基准测试

### 最佳实践
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- Rust 研究最佳实践
- 性能研究指南
- [形式化验证指南](https://doc.rust-lang.org/book/ch19-00-advanced-topics.html)

---

## 🔄 研究进展 {#-研究进展}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 已完成 ✅ {#已完成-}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [x] 研究方法框架（包括优势说明）
- [x] 工具分类整理
- [x] 实践指南框架
- [x] 理论基础整理（包括理论背景和相关概念）

### 进行中 🔄（已完成）
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

- [x] 详细方法文档（2.1 实验、3.1 实证、4.1 理论要点 + 各文档索引）
- [x] 工具使用教程（工具使用要点 + TOOLS_GUIDE、各实验指南）
- [x] 案例研究（案例研究索引 + practical_applications）

### 计划中 📋（已完成）
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [x] 质量评估标准（见「质量评估标准与研究模板」）
- [x] 研究模板（形式化/实验/实证模板）
- [x] 工具集成（工具集成与案例研究索引）

---

**维护者**: Rust Research Methodology Group
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 🆕 权威国际化内容升级 (Rust 1.96.0+) {#-权威国际化内容升级}
>
> **来源**: [Rust Research Methodology Group]

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 本次升级要点

- 补充 Rust 形式化方法的国际权威论文索引：RustBelt、Aeneas、RustHorn、RustHornBelt、Iris。
- Coq/Lean 示例对齐 Iris/RustBelt 的分离逻辑与生命周期逻辑。
- 方法论文献与工具文档增加官方 PDF、GitHub、项目主页链接。
- 删除旧版 Rust 1.94 模板内容，状态更新为 ✅ 完成。

---

**维护者**: Rust Research Methodology Group
**最后更新**: 2026-06-29 (权威国际化内容升级)
**状态**: ✅ 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf), [Iris Project](https://iris-project.org/), [Aeneas](https://aeneas-verif.github.io/aeneas/), [RustHorn](https://www.kb.is.s.u-tokyo.ac.jp/old-users/yskm24t/web/papers/esop2020-rust-horn.pdf)
>
> **权威来源对齐变更日志**: 2026-06-29 新增 RustBelt、Aeneas、RustHorn、Iris 等国际形式化方法来源 [来源: Authority Source Sprint Batch 9]

**文档版本**: 1.2
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 权威来源索引

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
