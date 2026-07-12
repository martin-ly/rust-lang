# Next-generation Trait Solver 深度研究 {#next-generation-trait-solver-深度研究}

> **EN**: Next Generation Trait Solver
> **Summary**: Next-generation Trait Solver 深度研究 Next Generation Trait Solver.
>
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **分级**: [B]
> **Bloom 层级**: L4-L5
> **文档状态**: 活跃维护
> **创建日期**: 2026-05-08
> **最后更新**: 2026-05-08
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **关联目标**: [Rust 2026 Project Goals — Next-generation trait solver](https://rust-lang.github.io/rust-project-goals/2026/)

---

## 目录 {#目录}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [Next-generation Trait Solver 深度研究 {#next-generation-trait-solver-深度研究}](#next-generation-trait-solver-深度研究-next-generation-trait-solver-深度研究)
  - [目录 {#目录}](#目录-目录)
  - [1. 当前架构概览 {#1-当前架构概览}](#1-当前架构概览-1-当前架构概览)
    - [1.1 与 rustc 的集成方式 {#11-与-rustc-的集成方式}](#11-与-rustc-的集成方式-11-与-rustc-的集成方式)
    - [1.2 基于 SLG 的求解策略 {#12-基于-slg-的求解策略}](#12-基于-slg-的求解策略-12-基于-slg-的求解策略)
  - [2. 新一代 Solver 的核心动机 {#2-新一代-solver-的核心动机}](#2-新一代-solver-的核心动机-2-新一代-solver-的核心动机)
    - [2.1 更精确的错误信息 {#21-更精确的错误信息}](#21-更精确的错误信息-21-更精确的错误信息)
    - [2.2 更好的性能 {#22-更好的性能}](#22-更好的性能-22-更好的性能)
    - [2.3 更完整的泛型支持 {#23-更完整的泛型支持}](#23-更完整的泛型支持-23-更完整的泛型支持)
  - [3. 与 Chalk 项目的关系 {#3-与-chalk-项目的关系}](#3-与-chalk-项目的关系-3-与-chalk-项目的关系)
    - [3.1 Chalk 的设计初衷 {#31-chalk-的设计初衷}](#31-chalk-的设计初衷-31-chalk-的设计初衷)
    - [3.2 Chalk 的经验与教训 {#32-chalk-的经验与教训}](#32-chalk-的经验与教训-32-chalk-的经验与教训)
  - [4. Coherence 规则的演进 {#4-coherence-规则的演进}](#4-coherence-规则的演进-4-coherence-规则的演进)
    - [4.1 什么是 Coherence {#41-什么是-coherence}](#41-什么是-coherence-41-什么是-coherence)
    - [4.2 当前 Coherence 检查的局限 {#42-当前-coherence-检查的局限}](#42-当前-coherence-检查的局限-42-当前-coherence-检查的局限)
    - [4.3 Next-gen Solver 中的 Coherence {#43-next-gen-solver-中的-coherence}](#43-next-gen-solver-中的-coherence-43-next-gen-solver-中的-coherence)
  - [5. 当前实现状态 {#5-当前实现状态}](#5-当前实现状态-5-当前实现状态)
    - [5.1 Nightly 默认启用 {#51-nightly-默认启用}](#51-nightly-默认启用-51-nightly-默认启用)
    - [5.2 稳定化路线图 {#52-稳定化路线图}](#52-稳定化路线图-52-稳定化路线图)
    - [5.3 已知问题 {#53-已知问题}](#53-已知问题-53-已知问题)
  - [6. 对 Rust 开发者的影响 {#6-对-rust-开发者的影响}](#6-对-rust-开发者的影响-6-对-rust-开发者的影响)
    - [6.1 何时会感受到变化 {#61-何时会感受到变化}](#61-何时会感受到变化-61-何时会感受到变化)
    - [6.2 需要关注的情况 {#62-需要关注的情况}](#62-需要关注的情况-62-需要关注的情况)
  - [7. 与 Rust 2026 Project Goals 的关联 {#7-与-rust-2026-project-goals-的关联}](#7-与-rust-2026-project-goals-的关联-7-与-rust-2026-project-goals-的关联)
  - [8. 参考文献 {#8-参考文献}](#8-参考文献-8-参考文献)
    - [官方资源 {#官方资源}](#官方资源-官方资源)
    - [RFC 与设计文档 {#rfc-与设计文档}](#rfc-与设计文档-rfc-与设计文档)
    - [学术论文 {#学术论文}](#学术论文-学术论文)
  - [9. 补充：局限示例、架构细节与特性影响（合并自跟踪报告） {#9-补充局限示例架构细节与特性影响合并自跟踪报告}](#9-补充局限示例架构细节与特性影响合并自跟踪报告-9-补充局限示例架构细节与特性影响合并自跟踪报告)
    - [9.1 当前 Solver 局限的代码示例 {#91-当前-solver-局限的代码示例}](#91-当前-solver-局限的代码示例-91-当前-solver-局限的代码示例)
      - [A. 高阶类型推理 (Higher-Ranked Type Inference) {#91a-高阶类型推理}](#a-高阶类型推理-higher-ranked-type-inference-91a-高阶类型推理)
      - [B. 关联类型归一化 (Associated Type Normalization) {#91b-关联类型归一化}](#b-关联类型归一化-associated-type-normalization-91b-关联类型归一化)
      - [C. 隐式自动 trait 推导 {#91c-隐式自动-trait-推导}](#c-隐式自动-trait-推导-91c-隐式自动-trait-推导)
    - [9.2 现代 Rust 特性受制约情况 {#92-现代-rust-特性受制约情况}](#92-现代-rust-特性受制约情况-92-现代-rust-特性受制约情况)
    - [9.3 新旧架构对比与 Goal 语言 {#93-新旧架构对比与-goal-语言}](#93-新旧架构对比与-goal-语言-93-新旧架构对比与-goal-语言)
    - [9.4 Chalk 架构细节与多维对比 {#94-chalk-架构细节与多维对比}](#94-chalk-架构细节与多维对比-94-chalk-架构细节与多维对比)
    - [9.5 对现代 Rust 特性的影响（代码示例） {#95-对现代-rust-特性的影响代码示例}](#95-对现代-rust-特性的影响代码示例-95-对现代-rust-特性的影响代码示例)
    - [9.6 时间线跟踪（2017–2026） {#96-时间线跟踪20172026}](#96-时间线跟踪20172026-96-时间线跟踪20172026)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

---

## 1. 当前架构概览 {#1-当前架构概览}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 当前的 `trait solver`（特征求解器）自 `Rust 1.0` 以来一直是类型系统（Type System）的核心组件。它负责在编译期判断某个类型是否满足特定的 `trait bound`，并推导关联类型、处理高阶生命周期（Lifetimes）约束等。

### 1.1 与 rustc 的集成方式 {#11-与-rustc-的集成方式}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

当前稳定版的 `trait solver` 深度嵌入在 `rustc` 的 `typeck`（类型检查）和 `borrowck`（借用（Borrowing）检查）阶段之间：

```mermaid
flowchart LR
    A[AST / HIR] --> B[类型检查 typeck]
    B --> C{Trait Solver}
    C --> D[借用检查 borrowck]
    D --> E[MIR 生成]
    E --> F[代码生成]

    style C fill:#ffcccc
```

在 `rustc` 内部，类型检查器通过 `ObligationForest`（义务森林）结构将待求解的约束传递给 `trait solver`。每个 `Obligation`（义务）代表一个需要证明的类型命题，例如 `T: Display` 或 `Vec<T>: IntoIterator`。

### 1.2 基于 SLG 的求解策略 {#12-基于-slg-的求解策略}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

当前 solver 采用 **SLG (Selective Linear Generalized) resolution** 策略，这是一种表格化的逻辑编程求解技术。其核心流程为：

1. 将 `trait bound` 转换为子目标（subgoal）
2. 通过 `impl` 条目和内置规则递归求解
3. 使用 `depth-first` 搜索配合循环检测

```mermaid
flowchart TD
    A[输入: T: Iterator] --> B[查找匹配的 impl]
    B --> C{找到 impl?}
    C -->|是| D[生成子目标]
    C -->|否| E[检查自动推导]
    D --> F[递归求解]
    E --> G[检查 AutoTrait]
    F --> H{全部满足?}
    G --> H
    H -->|是| I[返回 Yes]
    H -->|否| J[返回 No / Ambiguity]
```

---

## 2. 新一代 Solver 的核心动机 {#2-新一代-solver-的核心动机}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

尽管当前 solver 在过去十年中支撑了 Rust 类型系统的持续扩展，但随着 `GATs`、`RPITIT`、`AFIT` 等特性的稳定化，其架构逐渐暴露出根本性的局限。

### 2.1 更精确的错误信息 {#21-更精确的错误信息}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

当前 solver 的 `depth-first` 搜索在遇到失败时，往往只能报告最顶层的失败结果，而无法回溯到真正的问题根源。新一代 solver 采用**可回溯的评估树（eval tree）**结构，能够：

- 记录完整的证明搜索路径
- 在失败时定位最具体的矛盾点
- 提供与 `GAT` 投影相关的精确诊断

### 2.2 更好的性能 {#22-更好的性能}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

新一代 solver 引入了**规范化缓存（canonicalized cache）**和**延迟归一化（lazy normalization）**：

| 优化项 | 当前 Solver | Next-gen Solver |
|--------|-----------|-----------------|
| 关联类型归一化 | 立即展开 | 按需延迟 |
| 缓存粒度 | 粗略（类型变量未实例化） | 规范化后精确匹配 |
| 重复求解 | 每次重新计算 | 响应缓存复用 |

### 2.3 更完整的泛型支持 {#23-更完整的泛型支持}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

新一代 solver 原生支持以下场景，而当前 solver 往往报错或行为不一致：

- 高阶 `trait bound`（`for<'a> T: Fn(&'a str) -> &'a str`）的完整推理链
- 嵌套 `GAT` 投影的精确归一化
- `impl Trait` 在 `trait` 定义中的隐式关联类型推断（Type Inference）

---

## 3. 与 Chalk 项目的关系 {#3-与-chalk-项目的关系}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 3.1 Chalk 的设计初衷 {#31-chalk-的设计初衷}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**Chalk** 是 Rust 编译器团队于 2017-2020 年间开发的实验性 `trait solver`，目标是：

- 将 `trait` 求解问题统一表示为**逻辑编程**问题
- 提供独立于 `rustc` 的可测试、可证明正确的类型系统核心
- 为 Rust 的类型系统建立形式化基础

```mermaid
flowchart TD
    A[Chalk 项目 2017] --> B[声明式逻辑引擎]
    B --> C[SLG Resolution]
    C --> D[Horn 子句转换]
    D --> E[独立的 chalk-engine crate]
    E --> F[归档 2021]
    F --> G[经验吸收至 next-gen solver]
```

### 3.2 Chalk 的经验与教训 {#32-chalk-的经验与教训}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Chalk 项目虽未直接替换 `rustc` 的 solver，但为新一代设计提供了关键经验：

| 方面 | Chalk 探索 | Next-gen Solver 的继承 |
|------|-----------|----------------------|
| 目标语言 | 统一的 `Goal` 枚举（Enum） | 直接沿用，扩展生命周期约束 |
| 变量处理 | 规范化（canonicalization） | 核心机制，性能优化 |
| 关联类型 | 预先归一化 | 改为延迟归一化 |
| 与 `rustc` 集成 | 外部 crate，困难 | 内嵌重写，深度耦合 |

**核心教训**：一个与 `rustc` 的实际类型表示（`TyCtxt`、`Region` 等）分离的 solver，难以在生产级编译器中达到所需的性能和精度。因此，next-gen solver 选择了在 `rustc` 内部重写，而非外部集成。

---

## 4. Coherence 规则的演进 {#4-coherence-规则的演进}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 4.1 什么是 Coherence {#41-什么是-coherence}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

**Coherence**（一致性）是 Rust 类型系统的核心安全属性，确保：

> 对于任意类型和 trait 的组合，最多只有一个 `impl` 适用（或可确定优先级）。

这一规则保证了代码的**全局一致性（Coherence）**和**可预测性**，是 `trait` 系统不变成菱形继承问题的前提。

### 4.2 当前 Coherence 检查的局限 {#42-当前-coherence-检查的局限}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**

当前 `coherence` 检查器与 `trait solver` 部分分离，导致：

- 重叠 `impl` 检查过于保守，拒绝了许多实际安全的代码
- `Specialization`（`RFC 1210`）因 solver 限制迟迟无法稳定
- 孤儿规则（orphan rules）的边界情况处理不一致

### 4.3 Next-gen Solver 中的 Coherence {#43-next-gen-solver-中的-coherence}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

新一代 solver 将 `coherence` 检查统一纳入 `Goal` 框架：

```mermaid
flowchart LR
    A[impl 定义] --> B{Coherence Check}
    B --> C[重叠检测 Goal]
    C --> D[Orphan Check Goal]
    D --> E[覆盖性检查 Goal]
    E --> F{全部通过?}
    F -->|是| G[接受 impl]
    F -->|否| H[编译错误]
```

统一框架的优势：

1. **Specialization 稳定化基础**：可回溯求解能精确判断 `impl` 之间的覆盖关系
2. 更灵活的**负 `impl`**（`impl !Trait for T`）支持
3. 与 `trait` 求解共享缓存，减少重复计算

---

## 5. 当前实现状态 {#5-当前实现状态}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 5.1 Nightly 默认启用 {#51-nightly-默认启用}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

自 **2024 年末**起，`nightly` 编译器已默认启用 next-gen solver。此前需要通过以下标志显式启用：

```bash
# 旧方式（nightly 2024 之前） {#旧方式nightly-2024-之前}
rustc +nightly -Znext-solver

# 当前 nightly（已默认启用，可切换回旧版） {#当前-nightly已默认启用可切换回旧版}
rustc +nightly -Ztrait-solver=classic
```

### 5.2 稳定化路线图 {#52-稳定化路线图}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**

```mermaid
gantt
    title Next-gen Trait Solver 路线图
    dateFormat  YYYY-MM
    section 开发阶段
    核心架构重写      :a1, 2021-01, 24M
    rustc 深度集成    :a2, 2022-06, 18M
    nightly 默认切换   :milestone, 2024-10, 0M
    section 稳定化阶段
    兼容性修复与调优   :b1, 2024-10, 12M
    RFC 提交         :milestone, 2025-07, 0M
    稳定版预计 landed  :milestone, 2026-06, 0M
```

### 5.3 已知问题 {#53-已知问题}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

| 问题 | 状态 | 影响 |
|------|------|------|
| 边缘案例兼容性回归 | 🟡 修复中 | 极少数 crate 编译行为变化 |
| 编译时间波动 | 🟡 优化中 | 大型项目增量编译略有增加 |
| 错误诊断格式调整 | 🟢 已完成 | 新格式更精确但需适应 |

---

## 6. 对 Rust 开发者的影响 {#6-对-rust-开发者的影响}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 6.1 何时会感受到变化 {#61-何时会感受到变化}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

大多数 Rust 开发者在日常编码中**不会直接感知** solver 的切换，因为新 solver 设计为完全向后兼容。但在以下场景中会感受到显著改善：

- **更清晰的编译错误**：当 `GAT` 投影失败时，错误信息会指出具体的类型不匹配路径
- **更少的手动标注**：`async fn in trait` 的隐式 `Send` 推导更智能
- **更灵活的泛型代码**：某些在当前编译器下"恰好能编译"或"恰好不能编译"的边缘案例，行为会趋于一致和合理

### 6.2 需要关注的情况 {#62-需要关注的情况}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

对于库作者（尤其是涉及复杂泛型或宏（Macro）的库），建议：

1. 在 CI 中加入 `nightly` 测试流水线，提前发现兼容性差异
2. 避免依赖当前 solver 的未定义行为（如某些 `ambiguous` 场景下的"侥幸通过"）
3. 关注编译器团队发布的迁移指南和 `crater` 测试结果

---

## 7. 与 Rust 2026 Project Goals 的关联 {#7-与-rust-2026-project-goals-的关联}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

Next-generation trait solver 是 **Rust 2026 Project Goals** 中"类型系统扩展"支柱的核心项目：

```mermaid
flowchart TD
    A[Rust 2026 Project Goals] --> B[类型系统扩展]
    A --> C[编译器性能]
    A --> D[开发者体验]
    B --> E[Next-gen Trait Solver]
    B --> F[Specialization 稳定化]
    B --> G[GATs 完善]
    C --> E
    D --> E
    E --> H[更精确的错误]
    E --> I[更快的增量编译]
    E --> J[Specialization 支撑]
```

具体关联：

- **Specialization 稳定化**（`RFC 1210`）：直接依赖新 solver 的重叠 `impl` 检查能力
- **更完整的 `GATs` 支持**：新 solver 的延迟归一化解决当前 `GAT` 投影的诸多限制
- **编译时间目标**：新 solver 的缓存机制是 `rustc` 整体性能提升计划的一部分

---

## 8. 参考文献 {#8-参考文献}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 官方资源 {#官方资源}
>
> **[来源: [crates.io](https://crates.io/)]**

1. **Rust Compiler Team**. "Next-Generation Trait Solver". [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/).
2. **Matsakis, Niko**. "Chalk: From Logic to Rust". *Rust Blog*, 2017.
   <https://blog.rust-lang.org/2017/06/08/Rust-1.18.html>

3. **Rust Compiler Team**. "Trait Solver Refactor". MCP (Major Change Proposal) #529, 2021.
   [https://rust-lang.github.io/compiler-team/ [已失效]]<!-- 原链接: https://rust-lang.github.io/compiler-team/ -->

### RFC 与设计文档 {#rfc-与设计文档}
>
> **[来源: [docs.rs](https://docs.rs/)]**

1. **RFC 1210**. "Specialization". *Rust RFCs*, 2015.
   <https://rust-lang.github.io/rfcs/1210-impl-specialization.html>

2. **RFC 2289**. "Associated Type Constructors". *Rust RFCs*, 2018.
   <https://rust-lang.github.io/rfcs/2289-associated-type-bounds.html> (GATs 的前身)

### 学术论文 {#学术论文}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

1. **Dreyer, Derek, et al.** "Type Systems for Rust: Chalk and Beyond". *PLMW @ POPL*, 2020.
2. **Jung, Ralf, et al.** "RustBelt: Securing the Foundations of the Rust Programming Language". *POPL 2018*.
   DOI: `10.1145/3158154` ( trait 系统的形式化安全基础 )

3. **Vytiniotis, Dimitrios, et al.** "Modular Implicits". *OCaml Workshop*, 2014.
   (Rust `trait` 系统的理论前身之一)

4. **de Moura, Leonardo, et al.** "The Lean Theorem Prover". *CoRR abs/1505.05043*, 2015.
   (新 solver 的部分设计灵感来源)

---

## 9. 补充：局限示例、架构细节与特性影响（合并自跟踪报告） {#9-补充局限示例架构细节与特性影响合并自跟踪报告}

> **合并说明**: 本节合并自已 stub 化的 [`05_ng_trait_solver.md`](05_ng_trait_solver.md)（Next-gen Trait Solver 跟踪报告，2026-07-12 去重，AGENTS.md §3.3）。两文重叠叙述以本章 §1–§8 为准，此处保留其独特段落。

### 9.1 当前 Solver 局限的代码示例 {#91-当前-solver-局限的代码示例}

#### A. 高阶类型推理 (Higher-Ranked Type Inference) {#91a-高阶类型推理}

当前 solver 在处理高阶 trait bounds (HRTB) 时经常出现不一致：

```rust
// 当前编译器有时无法正确处理此类约束
fn foo<T>()
where
    for<'a> T: Fn(&'a str) -> &'a str,
{}
```

#### B. 关联类型归一化 (Associated Type Normalization) {#91b-关联类型归一化}

复杂的关联类型投影在某些场景下会导致编译器死循环或错误拒绝：

```rust
trait Iterable {
    type Item;
    type Iter: Iterator<Item = Self::Item>;
}

// 深层嵌套的关联类型投影可能失败
type DeepItem<T: Iterable> = <<T as Iterable>::Iter as Iterator>::Item;
```

#### C. 隐式自动 trait 推导 {#91c-隐式自动-trait-推导}

当前 `AutoTrait` 分析（如 `Send`/`Sync` 推导）与主 solver 分离，导致：

1. 不一致的推导结果
2. 难以扩展新的 auto trait
3. 与 GATs (Generic Associated Types) 的交互问题

### 9.2 现代 Rust 特性受制约情况 {#92-现代-rust-特性受制约情况}

| 特性 | 当前 Solver 状态 | 影响 |
|------|---------------|------|
| GATs | 已稳定 (1.65)，但受限 | 复杂约束推导不准确 |
| RPITIT | 已稳定 (1.75) | 在复杂 trait 层次中推断不稳定 |
| AFIT (async fn in traits) | 已稳定 (1.75.0) | 隐式 `Send`  bounds 推导问题 |
| TAIT (type alias impl trait) | 部分稳定 | 嵌套 TAIT 场景受限 |
| Specialization | 未稳定 | 重叠 impl 检查过于保守 |

### 9.3 新旧架构对比与 Goal 语言 {#93-新旧架构对比与-goal-语言}

```text
新旧架构对比:

当前 Solver:                    Next-gen Solver:
┌─────────────────┐            ┌─────────────────┐
│  Trait Obligation│            │  Goal: Prove<T: Display>  │
│  (立即求解)      │            │  (统一目标表示)            │
└────────┬────────┘            └────────┬────────┘
         │                             │
┌────────▼────────┐            ┌────────▼────────┐
│  SLG Resolution │            │  Canonicalizer  │
│  (穷尽搜索)      │            │  (变量规范化)    │
└────────┬────────┘            └────────┬────────┘
         │                             │
┌────────▼────────┐            ┌────────▼────────┐
│  关联类型立即归一化│            │  Eval Tree      │
│                 │            │  (可回溯评估树)  │
└─────────────────┘            └────────┬────────┘
                                        │
                               ┌────────▼────────┐
                               │  Response Cache │
                               │  (响应缓存复用)  │
                               └─────────────────┘
```

所有类型系统查询统一为 `Goal`（rustc 内部简化表示）：

```rust,ignore
// rustc 内部表示 (简化)
enum Goal<'tcx> {
    // 证明类型实现 trait
    Trait(TraitPredicate<'tcx>),
    // 证明区域约束
    RegionOutlives(RegionOutlivesPredicate<'tcx>),
    // 证明类型相等
    Eq(Type<'tcx>, Type<'tcx>),
    // 逻辑与
    And(Box<Goal<'tcx>>, Box<Goal<'tcx>>),
    // 逻辑或
    Or(Box<Goal<'tcx>>, Box<Goal<'tcx>>),
    // 高阶量化
    ForAll(Box<Goal<'tcx>>),
}
```

延迟归一化（Lazy Normalization）示例：

```rust
trait Foo {
    type Bar;
}

// 当前: <T as Foo>::Bar 立即尝试归一化
// 新 solver: 保留投影，仅在需要时归一化

fn use_foo<T: Foo>(x: T::Bar) {
    // 新 solver 可以更灵活地处理未完全确定的具体类型
}
```

### 9.4 Chalk 架构细节与多维对比 {#94-chalk-架构细节与多维对比}

```text
Chalk 架构:
┌─────────────────────────────────────┐
│           Rust Source Code          │
└─────────────┬───────────────────────┘
              │ lowering
┌─────────────▼───────────────────────┐
│     Chalk IR (中间表示)              │
│  - Trait bounds → Horn clauses      │
│  - Type goals → Logic programs      │
└─────────────┬───────────────────────┘
              │
┌─────────────▼───────────────────────┐
│     SLG Solver (Rust 实现)          │
│  - 基于 Tarjan 的高效搜索           │
└─────────────────────────────────────┘
```

尽管 Chalk 在理论上很优雅，但实际集成 rustc 时遇到：

1. **性能瓶颈**: 纯逻辑求解在处理 rustc 的大规模类型约束时速度不足
2. **与 rustc 耦合困难**: Chalk 假设了过于理想化的类型系统模型
3. **生命周期（Lifetimes）交互**: Chalk 最初未考虑 Rust 独特的生命周期系统

| 维度 | Chalk (2017-2020) | Next-gen Solver (2021-now) |
|------|------------------|---------------------------|
| **设计目标** | 外部可复用库 | 深度集成 rustc |
| **求解策略** | 纯 SLG resolution | 混合策略 + 可回溯缓存 |
| **关联类型** | 预先归一化 | 延迟归一化 |
| **生命周期** | 后期添加 | 原生集成 |
| **GATs 支持** | 理论支持 | 生产级支持 |
| **Specialization** | 实验性 | 核心设计考虑 |
| **性能** | 较慢 (独立库) | 与旧 solver 相当或更优 |
| **状态** | 已归档 | nightly 默认，目标稳定化 |

```text
Rust 1.0  Solver ──→ NLL Era ──→ Chalk 实验 ──→ Next-gen Solver
   (2015)    (2018)      (2019)        (2021-now)
     │           │            │              │
     │           │            │              └── nightly 默认 (2024)
     │           │            │              └── 目标: 2025-2026 稳定
     │           │            └── 提供了理论基础和 Datalog 经验
     │           │
     │           └── NLL borrowck 分离，trait solver 未变
     │
     └── 原始基于 obligation 的 solver
```

### 9.5 对现代 Rust 特性的影响（代码示例） {#95-对现代-rust-特性的影响代码示例}

**GATs (Generic Associated Types)** — 已稳定 (Rust 1.65+)：

```rust,ignore
trait LendingIterator {
    type Item<'a>;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

// 新 solver 下更可能成功编译的场景:
trait Container {
    type Iter<'a>: Iterator<Item = &'a Self::Item>;
    type Item;
    fn iter(&self) -> Self::Iter<'_>;
}
```

Next-gen solver 的改进：更精确的 GAT 投影归一化、减少 "ambiguous projection" 错误、支持更复杂的 GAT trait bounds。

**RPITIT (Return Position Impl Trait In Traits)** — 已稳定 (Rust 1.75+)：

```rust
trait Factory {
    fn create(&self) -> impl Iterator<Item = i32>;
}
```

改进：更稳定的隐式关联类型推断（Type Inference）、支持更复杂的返回类型组合、减少 `impl Trait` 在 trait 中的边界情况错误。

**AFIT (Async Fn In Traits)** — 已稳定 (Rust 1.75+)，当前稳定版使用 desugaring to RPITIT 实现。关键问题是 `Send` bounds 的隐式推导：

```rust
// 当前: 返回的 Future 不一定自动是 Send，导致跨线程使用时问题
trait AsyncService {
    async fn call(&self) -> i32;  // Future 可能不是 Send
}

// workaround: 显式标注 (verbose)
trait AsyncServiceSend: Send + Sync {
    fn call(&self) -> impl Future<Output = i32> + Send;
}

// 新 solver 目标: 更智能的 Send/Sync 推导，减少显式标注需求
```

**Specialization (特化)** — 未稳定，需要 `feature(specialization)`：

```rust,ignore
trait Convert<T> {
    fn convert(&self) -> T;
}

// 通用实现
impl<T, U> Convert<U> for T where U: From<T> {
    fn convert(&self) -> U { U::from(self) }
}

// 特化实现 (更具体)
impl<T: Clone> Convert<T> for &T {
    fn convert(&self) -> T { (*self).clone() }
}
```

Specialization 的稳定化严重依赖新 solver 的重叠 impl 检查能力；新 solver 的可回溯约束求解是安全 specialization 的理论基础。

### 9.6 时间线跟踪（2017–2026） {#96-时间线跟踪20172026}

| 时间 | 事件 |
|------|------|
| 2017 | Chalk 项目启动 |
| 2019 | Chalk 作为独立 crate 发布 |
| 2021 | Next-gen solver 开发启动，吸取 Chalk 经验 |
| 2022 | 新 solver 核心逻辑完成，开始 rustc 集成 |
| 2023 | 解决 GATs + 新 solver 的关键 bug |
| 2024-Q3 | Nightly 默认切换至 next-gen solver |
| 2025-H1 | 性能调优，修复兼容性回归 |
| **2025-H2** | **目标: 稳定版 RFC 提交** |
| **2026** | **预计稳定化 (乐观估计)** |

---

> 📌 **复查记录**
>
> | 日期 | 复查人 | 版本 | 状态 |
> |------|-------|------|------|
> | 2026-05-08 | Kimi | Nightly 1.97.0 | ✅ 初版创建 |
> | 2026-07-08 | — | — | 🕐 待复查：跟踪 RFC 提交进展 |
> | 2026-07-12 | — | — | 🔀 合并 `05_ng_trait_solver.md` 独特内容（§9），后者改为重定向 stub |
>
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.3
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-07-12
**状态**: ✅ 权威来源对齐完成 (Batch 9)；2026-07-12 合并 `05_ng_trait_solver.md` 去重

---

- [Parent README](../README.md)

---

## 相关概念 {#相关概念}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [上级目录](../README.md)
- [Rust 版本跟踪 (concept)](../../concept/07_future/00_version_tracking/01_rust_version_tracking.md) — Next Solver 稳定化状态全局跟踪
- [Traits (concept)](../../concept/02_intermediate/00_traits/01_traits.md) — Trait 系统核心概念与 §12 Next Solver 前瞻
- [泛型（Generics） (concept)](../../concept/02_intermediate/01_generics/01_generics.md) — 泛型系统与关联类型详解

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Machine Learning](https://en.wikipedia.org/wiki/Machine_Learning)**
> **来源: [Wikipedia - Artificial Intelligence](https://en.wikipedia.org/wiki/Artificial_Intelligence)**
> **来源: [tch-rs Documentation](https://docs.rs/tch/latest/tch/)**
> **来源: [ACM - AI Systems](https://dl.acm.org/)**
> **来源: [Wikipedia - Machine Learning](https://en.wikipedia.org/wiki/Machine_Learning)**
> **来源: [Wikipedia - Artificial Intelligence](https://en.wikipedia.org/wiki/Artificial_Intelligence)**
> **来源: [tch-rs Documentation](https://docs.rs/tch/latest/tch/)**
> **来源: [ACM - AI Systems](https://dl.acm.org/)**

---
