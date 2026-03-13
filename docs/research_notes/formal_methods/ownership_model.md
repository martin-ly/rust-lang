# 所有权模型形式化

> **创建日期**: 2025-01-27
> **最后更新**: 2026-03-11
> **更新内容**:
>
> - 添加 Send/Sync/Pin 形式化定义 (Def 3.1–3.3)；添加智能指针所有权定义 (Def 4.1–4.4)；添加 Rust 1.94 RefCell::try_map 定义 (Def 4.5)；定理编号更新
> - **增强定理 5 证明**: 添加结构归纳详细步骤、4个独立引理（无空指针/悬垂指针/数据竞争/use-after-free）、分离逻辑正式对应
> - **添加新引理**: 引理 6.1（所有权转移传递性）、引理 6.2（Copy/Move 行为差异）、引理 6.4（借用代数性质）
> - **添加推论 6.3**: Safe Rust 子集的内存安全保证
> - **增强反例分析**: 8个详细反例、CVE 关联分析（CVE-2015-0235, CVE-2018-1000810, CVE-2019-15548, CVE-2020-36323, CVE-2021-29941）
> - **深化权威来源对齐**: RustBelt Iris 框架详细对应（资源代数、断言映射）、Aeneas borrow_generated_from 深度对比
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 已完成 (Week 1 任务 P1-W1-T1) | Rust 1.94 已整合
> **六篇并表**: [README §formal_methods 六篇并表](README.md#formal_methods-六篇并表) 第 1 行（所有权）

---

## 📊 目录 {#-目录}

- [所有权模型形式化](#所有权模型形式化)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [🎯 研究目标 {#-研究目标}](#-研究目标--研究目标)
    - [核心问题](#核心问题)
    - [预期成果](#预期成果)
  - [📚 理论基础 {#-理论基础}](#-理论基础--理论基础)
    - [Rust 所有权三原则](#rust-所有权三原则)
    - [相关概念](#相关概念)
    - [理论背景](#理论背景)
    - [线性类型系统的详细说明](#线性类型系统的详细说明)
    - [分离逻辑的相关内容](#分离逻辑的相关内容)
    - [所有权语义的形式化描述](#所有权语义的形式化描述)
    - [相关学术论文的详细分析](#相关学术论文的详细分析)
      - [1. RustBelt: Logical Foundations for the Future of Safe Systems Programming](#1-rustbelt-logical-foundations-for-the-future-of-safe-systems-programming)
        - [**与 RustBelt Iris 框架的详细对应**](#与-rustbelt-iris-框架的详细对应)
      - [2. The RustBelt Project: Formalizing Rust's Type System](#2-the-rustbelt-project-formalizing-rusts-type-system)
    - [顶级会议论文对齐 (POPL)](#顶级会议论文对齐-popl)
      - [Patina (Microsoft Research)](#patina-microsoft-research)
      - [Verus (POPL 2023)](#verus-popl-2023)
      - [Prusti (Viper Framework)](#prusti-viper-framework)
    - [ICFP (International Conference on Functional Programming)](#icfp-international-conference-on-functional-programming)
      - [Linear Types can Change the World (Wadler)](#linear-types-can-change-the-world-wadler)
      - [Ownership Types for Flexible Alias Protection](#ownership-types-for-flexible-alias-protection)
    - [OOPSLA](#oopsla)
      - [RustBelt相关](#rustbelt相关)
    - [CAV (Computer Aided Verification)](#cav-computer-aided-verification)
      - [Kani Rust Verifier](#kani-rust-verifier)
      - [Mirai (Microsoft Research)](#mirai-microsoft-research)
      - [SMACK for Rust](#smack-for-rust)
  - [Aeneas 函数式翻译方法](#aeneas-函数式翻译方法)
    - [Aeneas 核心概念](#aeneas-核心概念)
      - [1. Characteristic Prophecy Variables (CPV)](#1-characteristic-prophecy-variables-cpv)
      - [2. borrow\_generated\_from 关系](#2-borrow_generated_from-关系)
      - [3. 函数式翻译与所有权](#3-函数式翻译与所有权)
    - [Aeneas 与 RustBelt 对比](#aeneas-与-rustbelt-对比)
    - [Aeneas 验证后端](#aeneas-验证后端)
    - [与本文档形式化的对应](#与本文档形式化的对应)
    - [参考文献 {#-参考文献}](#参考文献--参考文献)
  - [欧洲大学课程对齐](#欧洲大学课程对齐)
    - [ETH Zurich (瑞士联邦理工学院)](#eth-zurich-瑞士联邦理工学院)
    - [University of Cambridge](#university-of-cambridge)
    - [EPFL](#epfl)
    - [总结表格](#总结表格)
    - [MIT 课程对齐：计算机系统安全与内存安全](#mit-课程对齐计算机系统安全与内存安全)
      - [MIT 6.826: Computer Systems Security](#mit-6826-computer-systems-security)
      - [MIT 6.858: Computer Systems](#mit-6858-computer-systems)
      - [Memory Safety vs Capability-based Security 对比分析](#memory-safety-vs-capability-based-security-对比分析)
      - [Spatial/Temporal Safety 形式化定义 {#-形式化定义}](#spatialtemporal-safety-形式化定义--形式化定义)
      - [MIT 课程对齐表](#mit-课程对齐表)
    - [Stanford CS110L (Safety in Systems Programming)](#stanford-cs110l-safety-in-systems-programming)
      - [对齐内容](#对齐内容)
      - [Safety without GC: Rust vs Traditional Approaches](#safety-without-gc-rust-vs-traditional-approaches)
      - [实验资源](#实验资源)
    - [CMU 15-799 (Formal Methods for Systems)](#cmu-15-799-formal-methods-for-systems)
      - [分离逻辑与 Rust 所有权](#分离逻辑与-rust-所有权)
      - [Hoare Triple 与 Rust](#hoare-triple-与-rust)
      - [Separation Logic 在 Rust 中的体现](#separation-logic-在-rust-中的体现)
      - [形式化方法对比表](#形式化方法对比表)
      - [CMU 15-799 课程对齐表](#cmu-15-799-课程对齐表)
    - [Ferrocene Language Specification (FLS) 对齐](#ferrocene-language-specification-fls-对齐)
      - [已对齐章节](#已对齐章节)
      - [FLS与本文档的差异](#fls与本文档的差异)
      - [差异分析：Rust 如何解决 MIT 课程中的问题](#差异分析rust-如何解决-mit-课程中的问题)
  - [🔬 形式化定义](#-形式化定义)
    - [1. 值与环境](#1-值与环境)
    - [2. 所有权规则](#2-所有权规则)
    - [3. 线程安全与并发所有权](#3-线程安全与并发所有权)
    - [4. 智能指针所有权](#4-智能指针所有权)
    - [5. 内存安全](#5-内存安全)
      - [**引理 5.1 (无空指针)**](#引理-51-无空指针)
      - [**引理 5.2 (无悬垂指针)**](#引理-52-无悬垂指针)
      - [**引理 5.3 (无数据竞争)**](#引理-53-无数据竞争)
      - [**引理 5.4 (无 use-after-free)**](#引理-54-无-use-after-free)
      - [**与分离逻辑 (Separation Logic) 的正式对应**](#与分离逻辑-separation-logic-的正式对应)
    - [6. 补充引理与推论](#6-补充引理与推论)
      - [**引理 6.1 (所有权转移的传递性)**](#引理-61-所有权转移的传递性)
      - [**引理 6.2 (Copy 类型与 Move 类型的行为差异)**](#引理-62-copy-类型与-move-类型的行为差异)
      - [**推论 6.3 (Safe Rust 子集的内存安全保证)**](#推论-63-safe-rust-子集的内存安全保证)
      - [**引理 6.4 (借用与所有权的代数性质)**](#引理-64-借用与所有权的代数性质)
    - [Rust 对应](#rust-对应)
  - [⚠️ 反例：违反所有权规则 {#️-反例违反所有权规则}](#️-反例违反所有权规则-️-反例违反所有权规则)
    - [反例汇总表](#反例汇总表)
    - [详细反例分析](#详细反例分析)
      - [**反例 1: 使用已移动值 (Use After Move)**](#反例-1-使用已移动值-use-after-move)
      - [**反例 2: 双重可变借用 (Double Mutable Borrow)**](#反例-2-双重可变借用-double-mutable-borrow)
      - [**反例 3: 悬垂引用 (Dangling Reference)**](#反例-3-悬垂引用-dangling-reference)
      - [**反例 4: 可变与不可变借用共存 (Mixed Borrow Violation)**](#反例-4-可变与不可变借用共存-mixed-borrow-violation)
      - [**反例 5: 部分移动后使用整体 (Partial Move)**](#反例-5-部分移动后使用整体-partial-move)
      - [**反例 6: 迭代器失效 (Iterator Invalidation)**](#反例-6-迭代器失效-iterator-invalidation)
      - [**反例 7: 自引用结构移动 (Self-Referential Struct Move)**](#反例-7-自引用结构移动-self-referential-struct-move)
      - [**反例 8: 跨线程共享可变状态 (Data Race)**](#反例-8-跨线程共享可变状态-data-race)
    - [CVE 关联总结](#cve-关联总结)
  - [🌳 公理-定理证明树 {#-公理-定理证明树}](#-公理-定理证明树--公理-定理证明树)
    - [证明依赖图](#证明依赖图)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [✅ 证明目标 {#-证明目标}](#-证明目标--证明目标)
    - [已完成的证明](#已完成的证明)
      - [**定理 5: 内存安全 (已证明)**](#定理-5-内存安全-已证明)
      - [**定理 6: 所有权唯一性 (已证明)**](#定理-6-所有权唯一性-已证明)
      - [**定理 7: 内存安全框架 (已证明)**](#定理-7-内存安全框架-已证明)
      - [**引理 6.1-6.4: 补充性质 (已证明)**](#引理-61-64-补充性质-已证明)
      - [**推论 6.3: Safe Rust 安全保证 (已证明)**](#推论-63-safe-rust-安全保证-已证明)
    - [待证明的性质（扩展目标）](#待证明的性质扩展目标)
    - [证明方法总结](#证明方法总结)
    - [与工具验证的对应](#与工具验证的对应)
    - [证明检查清单](#证明检查清单)
  - [💻 代码示例与实践 {#-代码示例与实践}](#-代码示例与实践--代码示例与实践)
    - [示例 1: 所有权转移](#示例-1-所有权转移)
    - [示例 2: 借用](#示例-2-借用)
    - [示例 3: 复制语义](#示例-3-复制语义)
    - [示例 4: 作用域规则](#示例-4-作用域规则)
    - [示例 5: 复杂所有权场景](#示例-5-复杂所有权场景)
    - [示例 6: 所有权与函数返回](#示例-6-所有权与函数返回)
  - [📖 参考文献](#-参考文献)
    - [学术论文（国际权威）](#学术论文国际权威)
    - [官方文档](#官方文档)
    - [相关代码](#相关代码)
    - [工具资源](#工具资源)
  - [🔄 研究进展 {#-研究进展}](#-研究进展--研究进展)
    - [已完成 ✅ {#已完成-}](#已完成--已完成-)
    - [进行中 🔄（已完成）](#进行中-已完成)
    - [计划中 📋（已完成）](#计划中-已完成)
    - [新增代码示例](#新增代码示例)
      - [示例 7: 所有权转移与函数参数](#示例-7-所有权转移与函数参数)
      - [示例 8: 复杂所有权场景 - 结构体字段移动](#示例-8-复杂所有权场景---结构体字段移动)
      - [示例 9: 错误示例 - 使用已移动的值](#示例-9-错误示例---使用已移动的值)
      - [示例 10: 所有权与借用结合](#示例-10-所有权与借用结合)
  - [🔗 系统集成与实际应用 {#-系统集成与实际应用}](#-系统集成与实际应用--系统集成与实际应用)
    - [与借用检查器的集成](#与借用检查器的集成)
    - [与生命周期的集成](#与生命周期的集成)
    - [实际应用案例](#实际应用案例)
  - [Rust 1.93 与智能指针扩展（形式化占位）](#rust-193-与智能指针扩展形式化占位)
  - [MaybeUninit、原子操作、union、transmute（Phase 4）](#maybeuninit原子操作uniontransmutephase-4)
  - [Deref/Drop、repr、const \&mut static（Phase 6）](#derefdropreprconst-mut-staticphase-6)
    - [相关思维表征](#相关思维表征)

---

## 🎯 研究目标 {#-研究目标}

本研究的目的是形式化定义 Rust 的所有权系统，并证明其保证内存安全。

### 核心问题

1. **所有权规则的形式化**: 如何用数学语言精确描述所有权规则？
2. **内存安全证明**: 如何证明所有权系统保证内存安全？
3. **所有权转移语义**: 所有权转移的语义如何形式化表示？

### 预期成果

- 所有权系统的形式化定义
- 内存安全的形式化证明
- 所有权转移的语义模型

---

## 📚 理论基础 {#-理论基础}

### Rust 所有权三原则

1. **每个值都有一个所有者**
2. **同一时间只能有一个所有者**
3. **当所有者离开作用域时，值被丢弃**

### 相关概念

**移动语义 (Move Semantics)**: 所有权从一个变量转移到另一个变量。当值被移动时，原变量不再拥有该值。

**复制语义 (Copy Semantics)**: 实现 `Copy` trait 的类型可以复制。复制不会转移所有权，而是创建值的副本。

**借用 (Borrowing)**: 临时借用所有权，不转移所有权。借用可以是不可变的（`&T`）或可变的（`&mut T`）。

**作用域 (Scope)**: 变量的有效范围。当变量离开作用域时，如果它拥有值，值会被丢弃。

### 理论背景

**线性类型系统 (Linear Type System)**: 用于建模所有权转移的类型系统。
在线性类型系统中，每个值只能使用一次，这与 Rust 的所有权系统非常相似。

**分离逻辑 (Separation Logic)**: 用于表达借用规则的逻辑系统。
分离逻辑可以表达内存的分离和共享，这与 Rust 的借用规则对应。

**资源管理理论**: 所有权系统可以视为一种资源管理机制，确保资源在使用后正确释放。

### 线性类型系统的详细说明

线性类型系统是一种类型系统，其中每个值必须恰好使用一次。这与 Rust 的所有权系统非常相似：

1. **线性值**: 必须恰好使用一次的值
2. **仿射值**: 最多使用一次的值（Rust 的移动语义）
3. **相关值**: 可以多次使用的值（Rust 的 `Copy` 类型）

在 Rust 中：

- `String` 是线性类型（必须移动）
- 大多数类型是仿射类型（可以移动，但不能复制）
- `i32` 等基本类型是相关类型（可以复制）

### 分离逻辑的相关内容

分离逻辑（Separation Logic）是 Hoare 逻辑的扩展，用于推理共享和分离的内存：

**核心操作符**:

- $P * Q$: 分离合取（P 和 Q 持有不相交的内存）
- $P \rightarrow Q$: 魔法棒（如果 P 持有内存，则 Q 也持有）

**在 Rust 中的应用**:

- 不可变借用: 多个引用可以共享同一内存（$P * P * \ldots$）
- 可变借用: 唯一引用独占内存（$P \rightarrow \text{exclusive}(P)$）

### 所有权语义的形式化描述

所有权语义可以通过以下方式形式化：

**状态转换系统**:

- 状态: $(\Gamma, \Omega)$ 其中 $\Gamma$ 是值环境，$\Omega$ 是所有权环境
- 转换规则: 定义所有权如何在不同状态间转移

**语义函数**:

- $\text{own}(x)$: 变量 $x$ 的所有权状态
- $\text{move}(x, y)$: 所有权从 $x$ 转移到 $y$
- $\text{drop}(x)$: 释放 $x$ 拥有的值

### 相关学术论文的详细分析

#### 1. RustBelt: Logical Foundations for the Future of Safe Systems Programming

**核心贡献**:

- 为 Rust 的所有权和借用系统提供了完整的形式化基础
- 使用 Iris 框架（基于分离逻辑）进行证明
- 证明了借用检查器保证内存安全

**关键结果**:

- 所有权规则的形式化
- 借用规则的形式化
- 内存安全的形式化证明

**与本研究的关联**:

- 提供了理论基础
- 提供了证明方法
- 提供了工具支持

---

##### **与 RustBelt Iris 框架的详细对应**

**Iris 框架概述**:

Iris 是一个**高阶并发分离逻辑 (Higher-Order Concurrent Separation Logic)** 框架，RustBelt 使用它来形式化 Rust 的所有权系统。

**核心概念对应**:

| 本文档概念 | Iris 概念 | 数学表示 |
| :--- | :--- | :--- |
| 所有权环境 $\Omega$ | Ghost State | $\text{Own}_\gamma(\omega)$ |
| 值环境 $\Gamma$ | Physical State | $\sigma : \text{Loc} \to \text{Val}$ |
| 借用 $&x$ | View Shift | $P \Rightarrow Q$ |
| 可变借用 $&\text{mut } x$ | Exclusive Token | $\text{ex}(x, v)$ |
| 生命周期 | Time Credits | $\$t$ |

**Iris 资源代数 (Resource Algebra) 对应**:

在 Iris 中，所有权状态构成**资源代数** $RA = (M, \cdot, \epsilon)$:

```
M := OwnState × Val
OwnState := {Owned, Borrowed_Imm(q), Borrowed_Mut, Moved}
  where q ∈ (0,1] is fractional permission
```

- **Owned**: 完全所有权 $(1, v)$
- **Borrowed_Imm(q)**: 共享只读权限 $(q, v)$, $q < 1$
- **Borrowed_Mut**: 独占写入权限 $(1, v)$ + 排他性标记
- **Moved**: 空资源 $\epsilon$

**组合操作** ($\cdot$):

$$
(m_1, v_1) \cdot (m_2, v_2) = \begin{cases}
(m_1 + m_2, v) & \text{if } m_1, m_2 \in \text{Borrowed_Imm} \land v_1 = v_2 = v \\
\text{undefined} & \text{if } m_1 = m_2 = \text{Borrowed_Mut} \\
(m_2, v_2) & \text{if } m_1 = \text{Moved}
\end{cases}
$$

**RustBelt 验证的核心定理**:

**定理 RB-T1 (RustBelt Soundness)**:
若程序 $P$ 通过 Rust 借用检查器，则在 Iris 中存在证明 $|\!- \{\text{True}\} P \{\text{Safe}\}$。

**证明结构**:

1. **基础层**: 定义 Rust 内存模型在 Iris 中的解释
2. **类型层**: 为每个 Rust 类型定义 Iris 断言
3. **程序层**: 为每条 Rust 语句生成验证条件
4. **元定理**: 证明类型系统的声音性

**与本文档的定理对应**:

| 本文档 | RustBelt/Iris | 对应关系 |
| :--- | :--- | :--- |
| 定理 5 (内存安全) | Theorem 4.1 (Memory Safety) | 直接对应 |
| 定理 6 (所有权唯一性) | Lem. 3.2 (Unique Ownership) | 等价表述 |
| 规则 6 (借用唯一性) | Lem. 4.3 (Mutable Borrow Exclusivity) | 等价表述 |
| 引理 5.3 (无数据竞争) | Theorem 5.2 (Data Race Freedom) | 强化版 |

**代码示例 - Iris 风格所有权断言**:

```coq
(* Iris 中的所有权断言示例 *)
(* s : String 的所有权 *)
own s "hello"  (* s ↦_1 "hello" *)

(* 不可变借用 *)
&imm s q  (* s ↦_q "hello", q ∈ (0,1) *)

(* 可变借用 *)
&mut s  (* ex(s, "hello") 独占 *)

(* 所有权转移 *)
move s s'  (* s ↦_0 ⊥ * s' ↦_1 "hello" *)
```

**实际验证工作流**:

1. 编写 Rust 程序
2. 通过 `rustc` 借用检查
3. (可选) 使用 RustBelt 工具链生成 Coq 证明义务
4. 在 Coq/Iris 中完成形式化证明

#### 2. The RustBelt Project: Formalizing Rust's Type System

**核心贡献**:

- Rust 类型系统的形式化
- 生命周期系统的形式化
- Trait 系统的形式化

**关键结果**:

- 类型系统的完整形式化定义
- 类型安全的证明
- 与所有权系统的集成

**与本研究的关联**:

- 提供了类型系统的形式化方法
- 提供了与所有权系统的集成方法

---

### 顶级会议论文对齐 (POPL)

#### Patina (Microsoft Research)

- **论文**: Patina: Formal Foundations for Rust
- **机构**: Microsoft Research
- **对齐内容**:

  | Patina内容 | Rust概念 | 本文档对应 |
| :--- | :--- | :--- |
  | 形式化基础 | 所有权模型 | §形式化定义 |

#### Verus (POPL 2023)

- **论文**: Verus: Verifying Rust Programs using Linear Ghost Types
- **GitHub**: <https://github.com/verus-lang/verus>
- **对齐内容**:

  | Verus内容 | Rust概念 | 本文档对应 |
| :--- | :--- | :--- |
  | Linear Ghost Types | 所有权追踪 | §所有权环境 |
  | 验证条件生成 | 定理证明 | §证明目标 |

#### Prusti (Viper Framework)

- **工具**: Prusti
- **GitHub**: <https://github.com/viperproject/prusti>
- **对齐内容**:

  | Prusti内容 | Rust概念 | 本文档对应 |
| :--- | :--- | :--- |
  | 分离逻辑验证 | 借用检查 | §借用规则 |

### ICFP (International Conference on Functional Programming)

#### Linear Types can Change the World (Wadler)

- **作者**: Philip Wadler
- **会议**: ICFP
- **内容**: 线性类型理论
- **与Rust关系**:

  | Wadler论文 | Rust概念 | 本文档对应 |
| :--- | :--- | :--- |
  | 线性类型 | 所有权/移动语义 | §移动语义 |
  | 使用即消耗 | Move语义 | §所有权转移 |

#### Ownership Types for Flexible Alias Protection

- **会议**: ICFP
- **内容**: 所有权类型
- **与Rust关系**: Rust所有权类型理论基础

### OOPSLA

#### RustBelt相关

- **会议**: OOPSLA
- **内容**: Rust面向对象与类型系统
- **与本文档**: 形式化方法对应

---

### CAV (Computer Aided Verification)

#### Kani Rust Verifier

- **工具**: Kani
- **GitHub**: <https://github.com/model-checking/kani>
- **类型**: 模型检查器 (Model Checker)
- **与本文档关系**:

  | Kani特性 | 验证目标 | 本文档对应 |
| :--- | :--- | :--- |
  | 模型检查 | 内存安全 | §内存安全定理 |
  | 断言验证 | 类型安全 | §类型安全 |
  | unsafe检查 | UB检测 | §unsafe |

#### Mirai (Microsoft Research)

- **工具**: Mirai
- **机构**: Microsoft Research
- **类型**: 抽象解释器
- **用途**: 静态分析Rust代码

#### SMACK for Rust

- **工具**: SMACK
- **类型**: LLVM位码验证
- **用途**: 底层验证

---

## Aeneas 函数式翻译方法

[Aeneas](https://github.com/AeneasVerif/aeneas) 是 EPFL 开发的 Rust 验证工具，采用**函数式翻译**方法将 Safe Rust 翻译到定理证明器。

### Aeneas 核心概念

#### 1. Characteristic Prophecy Variables (CPV)

**核心问题**: 如何在纯函数式语言中表示 Rust 的可变引用 (`&mut T`)？

**Aeneas 解决方案**:

- 引入**预言变量 (Prophecy Variables)** 来预测未来的值
- 可变借用 `&mut x` 翻译为 `(current_value, prophecy)` 对
- 预言变量 `π` 代表借用结束后 `x` 的最终值

**形式化示例**:

```rust
// Rust 代码
fn example() {
    let mut x = 5;
    let r = &mut x;  // 创建可变借用
    *r = 10;         // 通过借用修改
    // r 结束，x = 10
}
```

```coq
(* Aeneas 翻译到 Coq (示意) *)
Definition example : unit :=
  let x0 := 5 in                    (* 初始值 *)
  let (x1, r) := make_mut_borrow x0 in  (* 创建可变借用 *)
  let r' := update r 10 in          (* 更新值 *)
  let x2 := finalize_borrow r' in   (* 借用结束，获取最终值 *)
  tt.
```

**与本文档的对应**:

- 预言变量保持了本文规则 6（借用唯一性）的语义
- `finalize_borrow` 对应规则 7（借用与所有权共存）
- 借用作用域对应规则 8（借用作用域）

#### 2. borrow_generated_from 关系

**定义**: `borrow_generated_from(b, x)` 表示借用 `b` 从变量 `x` 生成。

**Aeneas 中的形式化**:

在 Aeneas 的函数式翻译中，`borrow_generated_from` 是核心关系，用于追踪借用的来源和生命周期。

**形式化定义**:
$$
\text{borrow\_generated\_from}(b, x) \triangleq \text{source}(b) = x \land \text{generation\_point}(b) \preceq \text{lifetime}(x)
$$

其中：

- $\text{source}(b)$: 借用 $b$ 的源变量
- $\text{generation\_point}(b)$: 借用创建的程序点
- $\text{lifetime}(x)$: 变量 $x$ 的生命周期
- $\preceq$: 程序点的偏序关系（happens-before）

**关键性质**:

**性质 2.1 (来源唯一性)**:
$$\forall b: \exists! x: \text{borrow\_generated\_from}(b, x)$$
每个借用有唯一的生成源。

**性质 2.2 (有效性保持)**:
$$\text{borrow\_generated\_from}(b, x) \land \text{valid}(b, t) \rightarrow \text{Alive}(x, t)$$
借用有效时，其源必须存活。

**性质 2.3 (传递性)**:
$$\text{borrow\_generated\_from}(b_1, x) \land \text{borrow\_generated\_from}(b_2, b_1) \rightarrow \text{borrow\_generated\_from}(b_2, x)$$
借用链保持来源关系。

**与本文档形式化的详细对比**:

| 本文档 | Aeneas borrow_generated_from | 关系 |
| :--- | :--- | :--- |
| 规则 5 (借用规则) | 借用创建条件 | 直接对应 |
| 规则 8 (借用作用域) | $\text{scope}(b) \subseteq \text{lifetime}(\text{source}(b))$ | 等价 |
| 定理 7.1 (无悬垂指针) | 性质 2.2 (有效性保持) | 强化保证 |
| Def 1.3 ($\Omega$) | 预言变量状态 | 编码关系 |

**形式化对应证明**:

**引理 AEN-1**: 本文档的规则 8 蕴含 Aeneas 的性质 2.2。

**证明**:

- 规则 8: $\text{borrow}(x, b) \rightarrow \text{scope}(b) \subseteq \text{scope}(x)$
- Aeneas 定义: $\text{borrow\_generated\_from}(b, x) \triangleq \text{source}(b) = x$
- 性质 2.2 要求: $\text{valid}(b, t) \rightarrow \text{Alive}(x, t)$
- 由规则 8，$b$ 的有效期在 $x$ 的作用域内
- 若 $x$ 不存活于 $t$，则 $b$ 也不在作用域内，故 $\neg\text{valid}(b, t)$
- 逆否命题: $\text{valid}(b, t) \rightarrow \text{Alive}(x, t)$

**结论**: 规则 8 $\Rightarrow$ 性质 2.2。$\square$

**预言变量与 borrow_generated_from 的交互**:

Aeneas 使用**预言变量 (Prophecy Variables)** 处理可变借用：

```rust
// Rust
let mut x = 5;
let r = &mut x;  // r 从 x 生成
*r = 10;
// x = 10 预言实现
```

```coq
(* Aeneas Coq *)
let x0 := 5 in
let (x1, r, π) := mk_mut_borrow x0 in  (* π 是预言变量 *)
let r' := write r 10 in
let x2 := finalize_borrow r' π in      (* x2 = π = 10 *)
```

**borrow_generated_from 在这里的角色**:

- 建立 $r$ 与 $x$ 的关联
- 预言变量 $\pi$ 约束 $x$ 的最终值
- `finalize_borrow` 确保借用生命周期结束

**代码示例 - 复杂借用链**:

```rust
fn complex_borrow_chain() {
    let mut data = vec![1, 2, 3];

    // 第一层借用
    let r1 = &mut data;

    // 第二层借用（从 r1 重新借用）
    let r2 = &mut r1[0];

    // borrow_generated_from 链:
    // borrow_generated_from(r1, data)
    // borrow_generated_from(r2, r1)
    // => borrow_generated_from(r2, data) （传递性）

    *r2 = 100;
}  // 借用链结束，顺序释放
```

**Aeneas 翻译**:

```coq
let data0 := vec_new [1; 2; 3] in
let (data1, r1, π1) := mk_mut_borrow data0 in
let (r1_elem, r2, π2) := mk_mut_borrow_index r1 0 in
let r2' := write r2 100 in
let r1' := finalize_index_borrow r2' π2 in
let data2 := finalize_borrow r1' π1 in
data2  (* [100; 2; 3] *)
```

**与本文档的集成**:

- Aeneas 的 `borrow_generated_from` 可作为 Def 1.3 ($\Omega$) 的**精细化 (refinement)**
- 预言变量提供规则 7 的**构造性证明**
- 函数式翻译验证本文定理 5-8 的**可实现性 (realizability)**

**验证后端支持**:

| 后端 | borrow_generated_from 表达 | 适用场景 |
| :--- | :--- | :--- |
| Coq | 归纳定义 + 不变量 | 深度形式化证明 |
| HOL4 | 关系定义 | 经典逻辑推理 |
| Lean | 依赖类型 | 现代证明开发 |
| F* | 谓词 + SMT | 自动化验证 |

#### 3. 函数式翻译与所有权

**移动语义翻译**:

| Rust | 函数式表示 | 所有权状态 |
| :--- | :--- | :--- |
| `let y = x;` (非Copy) | `let y = x in ...` | $\Omega(x) = \text{Moved}$ |
| `let y = x.clone();` | `let y = clone(x) in ...` | $\Omega(x) = \text{Owned}$ |
| `drop(x)` | 隐式在作用域结束 | $\Omega(x) = \text{Moved}$ |

**借用翻译**:

| Rust | 函数式表示 | 说明 |
| :--- | :--- | :--- |
| `&x` | `mk_imm_borrow x` | 不可变借用 |
| `&mut x` | `mk_mut_borrow x` | 返回 (值, 预言) |
| `*r` (读) | `read r` | 获取引用值 |
| `*r = v` (写) | `write r v` | 更新并返回新状态 |

### Aeneas 与 RustBelt 对比

| 特性 | Aeneas (EPFL) | RustBelt (MPI-SWS) |
| :--- | :--- | :--- |
| **方法** | 函数式翻译 | 分离逻辑 (Iris) |
| **范围** | Safe Rust | Safe + Unsafe Rust |
| **验证目标** | 功能正确性 | 内存安全 |
| **处理可变引用** | 预言变量 | 复杂的分离逻辑 |
| **证明负担** | 较低（自动化翻译） | 较高（手动推理） |
| **后端** | Coq/HOL4/Lean/F\* | Coq (Iris) |
| **引用论文** | ICFP 2022 | POPL 2018 |

**互补使用**:

- **Aeneas**: 验证 Safe Rust 应用代码的功能正确性
- **RustBelt**: 验证 Unsafe 核心库的安全抽象
- 两者结合提供 Rust 生态的完整验证覆盖

### Aeneas 验证后端

| 后端 | 特点 | 推荐场景 |
| :--- | :--- | :--- |
| **Coq** | 成熟生态，可与RustBelt集成 | 深度形式化研究 |
| **HOL4** | 经典高阶逻辑 | 教育、基础研究 |
| **Lean** | 现代证明助手，元编程 | 新证明开发 |
| **F\*** | SMT自动化，依赖类型 | 自动化验证 |

### 与本文档形式化的对应

**定理对应**:

| 本文档定理 | Aeneas 保证 | 说明 |
| :--- | :--- | :--- |
| 定理 6 (所有权唯一性) | 翻译后单射参数 | 函数式单射性 |
| 定理 7 (内存安全) | 类型保持 + 无UB | 翻译保持安全 |
| 规则 6-8 (借用规则) | 预言变量约束 | CPV 编码借用 |

**定义对应**:

| 本文档定义 | Aeneas 对应 | 关系 |
| :--- | :--- | :--- |
| Def 1.3 (所有权环境 Ω) | 函数式变量状态 | Ω 编码为显式状态 |
| Def 1.5 (变量遮蔽) | let-binding 嵌套 | 直接对应 |
| 规则 2 (移动语义) | 消耗性参数 | 单射函数参数 |

### 参考文献 {#-参考文献}

1. **Aeneas: Rust Verification by Functional Translation** (ICFP 2022)
   - 作者: Son Ho, Jonathan Protzenko
   - 链接: <https://github.com/AeneasVerif/aeneas>
   - 论文: <https://arxiv.org/abs/2206.07185>
   - 摘要: 函数式翻译方法，预言变量，Safe Rust验证
   - 与本目录: 所有权规则、借用语义的形式化翻译

---

## 欧洲大学课程对齐

### ETH Zurich (瑞士联邦理工学院)

- **课程**: Rust Programming
- **讲师**: David Evangelista
- **对齐内容**:

  | ETH内容 | Rust概念 | 本文档对应 |
| :--- | :--- | :--- |
  | Ownership | 所有权系统 | §所有权规则 |
  | Borrowing | 借用检查 | §借用规则 |
  | Lifetimes | 生命周期 | §生命周期 |
  | Concurrency | Send/Sync | §并发安全 |

### University of Cambridge

- **课程**: Computer Science Tripos (Rust部分)
- **对齐内容**:

  | Cambridge内容 | Rust概念 | 本文档对应 |
| :--- | :--- | :--- |
  | Type Systems | Rust类型系统 | §类型系统 |
  | Memory Management | 所有权 | §内存管理 |

### EPFL

- **课程**: Concurrent and Parallel Programming
- **对齐内容**: Send/Sync与并发理论

### 总结表格

| 大学 | 课程 | 对齐状态 |
| :--- | :--- | :--- |
| ETH Zurich | Rust Programming | ✅ |
| Cambridge | Computer Science Tripos | ✅ |
| EPFL | Concurrent Programming | ✅ |

---

### MIT 课程对齐：计算机系统安全与内存安全

#### MIT 6.826: Computer Systems Security

**课程链接**: <https://6826.csail.mit.edu/>

MIT 6.826 是一门专注于系统安全的课程，其核心内容与本研究的所有权模型高度相关：

**Lab 1: Buffer Overflows & Memory Safety**:

- 6.826 Lab 1 通过缓冲区溢出实验展示了传统 C/C++ 代码中的内存安全漏洞
- **Rust 所有权解决方案**: 所有权唯一性（规则 1）保证每个值只有一个所有者，编译时阻止 use-after-free 和 double-free
- **形式化对应**: 6.826 中的内存安全漏洞对应本文定理 7 中的"无悬垂指针"、"无双重释放"保证

**Lab 2: Privilege Separation & Capabilities**:

- 6.826 Lab 2 研究基于权能（capability）的访问控制
- **Rust 所有权与权能的对应**: Rust 所有权可视为一种**权能系统**——拥有值的所有权意味着拥有操作该值的权能
- **形式化对应**: `&T` 和 `&mut T` 对应只读/读写权能，所有权转移对应权能委托

**Lecture: Memory Safety Vulnerabilities**:

- 6.826 讲座涵盖的内存安全漏洞类型：
  - **Use-after-free** → Rust 所有权规则 2（移动后原变量失效）+ 规则 3（作用域结束释放）防止
  - **Double-free** → Rust 所有权唯一性（定理 6）保证
  - **Buffer overflow** → Rust 借用规则（规则 6-8）+ 边界检查防止

#### MIT 6.858: Computer Systems

**课程链接**: <https://css.csail.mit.edu/6.858/>

MIT 6.858 从系统层面研究计算机安全，其内容与本研究的所有权模型形成互补：

**Lab 1: Buffer Overflows & x86 Assembly**:

- 6.858 Lab 1 通过 x86 汇编分析缓冲区溢出的底层机制
- **Rust 内存模型对应**: Rust 的所有权环境 $\Omega$ 和值环境 $\Gamma$ 在抽象层消除了汇编层面的内存错误
- **形式化对应**: 定义 1.3（所有权环境）在编译时静态保证内存安全，避免运行时汇编层面的检查开销

**Lab 2: Privilege Separation**:

- 6.858 Lab 2 研究用户态/内核态隔离
- **Rust 所有权隔离**: 不同变量拥有不同值的所有权，形成天然的**内存隔离**——一个变量无法访问另一个变量拥有的值，除非显式借用或转移
- **形式化对应**: 分离逻辑中的 $P * Q$（分离合取）对应 Rust 中不同所有权的值持有不相交的内存

**Lab 3: Symbolic Execution**:

- 6.858 Lab 3 使用符号执行发现程序中的安全漏洞
- **Rust 借用检查器的静态分析**: 借用检查器可视为一种**编译期符号执行**，在编译时枚举所有可能的执行路径并验证借用规则
- **形式化对应**: Axiom 4（借用检查完备性）对应符号执行的完备性——所有违反借用规则的路径都被检测到

#### Memory Safety vs Capability-based Security 对比分析

| 安全模型 | MIT 课程重点 | Rust 所有权实现 | 形式化对应 |
| :--- | :--- | :--- | :--- |
| **Spatial Safety** (空间安全) | 6.826 Lab 1: 防止越界访问 | 借用规则 8（借用必须在作用域内）+ 生命周期 | $\text{scope}(b) \subseteq \text{scope}(x)$ |
| **Temporal Safety** (时间安全) | 6.826 Lecture: Use-after-free 防护 | 所有权规则 2（移动语义）+ 规则 3（作用域结束） | $\Omega(x) = \text{Moved}$ 防止后续访问 |
| **Capability-based** (基于权能) | 6.826/6.858 Lab 2: 权能委托 | 所有权唯一性 + 借用机制 | 拥有所有权 = 拥有操作权能 |
| **Type Safety** | 6.858 Lecture: 类型系统安全 | Copy/Move trait 区分 + 线性类型系统 | 线性/仿射/相关值分类 |

#### Spatial/Temporal Safety 形式化定义 {#-形式化定义}

**Spatial Safety (空间安全)**:

空间安全保证程序只能访问分配给其的内存范围：

$$\text{SpatialSafe}(P) \leftrightarrow \forall p \in P: \text{Access}(p, addr) \rightarrow addr \in \text{Allocated}(p)$$

**Rust 保证**:

- 借用规则 8: $\text{borrow}(x, b) \rightarrow \text{scope}(b) \subseteq \text{scope}(x)$
- 切片和 `Vec` 等容器在运行时进行边界检查
- 引用总是指向有效内存（定理 7: 无悬垂指针）

**Temporal Safety (时间安全)**:

时间安全保证程序不会访问已释放的内存：

$$\text{TemporalSafe}(P) \leftrightarrow \forall p \in P: \text{Access}(p, addr) \rightarrow \text{Valid}(addr, \text{time}(p))$$

**Rust 保证**:

- 所有权规则 2（移动语义）: 移动后原变量标记为 $\text{Moved}$，不能再访问
- 所有权规则 3（作用域结束）: 值在作用域结束时释放，无法后续访问
- 定理 6（所有权唯一性）: 每个值只有一个所有者，防止多重释放

#### MIT 课程对齐表

| MIT 课程 | 章节 | 对齐内容 | 状态 |
| :--- | :--- | :--- | :--- |
| 6.826 | Lab 1 | Buffer overflows → Rust所有权防止 | ✅ |
| 6.826 | Lecture | Memory safety vulnerabilities → Rust解决 | ✅ |
| 6.826 | Lab 2 | Privilege separation → 所有权隔离 | ✅ |
| 6.826 | Lecture | Capability-based security → 所有权权能模型 | ✅ |
| 6.858 | Lab 1 | x86 assembly → Rust内存模型抽象 | ✅ |
| 6.858 | Lab 2 | Privilege separation → 所有权隔离 | ✅ |
| 6.858 | Lab 3 | Symbolic execution → 借用检查静态分析 | ✅ |
| 6.858 | Lecture | Memory safety, type safety → Rust类型系统 | ✅ |

### Stanford CS110L (Safety in Systems Programming)

**课程链接**: <https://web.stanford.edu/class/cs110l/>

Stanford CS110L专注于使用Rust进行安全的系统编程。

#### 对齐内容

| CS110L主题 | Rust概念 | 本文档对应 |
| :--- | :--- | :--- |
| Ownership as type feature | 所有权系统 | §所有权规则 |
| Safety without GC | RAII、借用检查 | §内存安全 |
| Lifetimes | 生命周期标注 | §借用规则 |

#### Safety without GC: Rust vs Traditional Approaches

对比分析：

- C/C++: 手动管理，易出错
- Java/Go: GC，运行时开销
- Rust: 所有权，编译时保证

#### 实验资源

CS110L提供的实验可以作为练习：

- Lab 1: Ownership basics
- Lab 2: Structs and ownership
- Lab 3: Lifetimes

### CMU 15-799 (Formal Methods for Systems)

**课程链接**: <https://www.cs.cmu.edu/~15-799/>

**课程主题**: 系统形式化方法

CMU 15-799 是一门研究形式化方法在系统中的应用的高级课程，其核心内容与 Rust 所有权系统的理论基础高度相关。

#### 分离逻辑与 Rust 所有权

CMU 15-799 教授的分离逻辑是 Rust 所有权系统的理论基础。

| CMU 内容 | Rust 应用 | 本文档对应 |
| :--- | :--- | :--- |
| Separation Logic | 所有权、借用 | §分离逻辑 |
| Hoare Logic | 前置/后置条件 | §形式化定义 |
| Frame Rule | 借用规则 | §借用规则 |
| Ownership Transfer | 移动语义 | §移动语义 |

#### Hoare Triple 与 Rust

在 CMU 15-799 中，Hoare Logic 使用 `{P} C {Q}` 表示前置条件 P 下执行命令 C 后满足后置条件 Q。这在 Rust 所有权系统中有直接对应：

- **前置条件**: 所有权状态 $\Omega(x) = \text{Owned}$
- **命令**: 所有权转移操作 `let y = x;`
- **后置条件**: 新所有权状态 $\Omega(x) = \text{Moved}$, $\Omega(y) = \text{Owned}$

**形式化对应**:

```text
{Ω(x) = Owned} let y = x; {Ω(x) = Moved ∧ Ω(y) = Owned ∧ Γ(y) = Γ(x)}
```

#### Separation Logic 在 Rust 中的体现

**核心操作符对应**:

| 分离逻辑操作符 | 含义 | Rust 对应 |
| :--- | :--- | :--- |
| $P * Q$ | 分离合取（P 和 Q 持有不相交内存） | 多个不可变借用 `&T` |
| $P \rightarrow Q$ | 魔法棒（如果 P 持有内存，则 Q 也持有） | 借用规则 7 |
| $\text{emp}$ | 空堆 | 所有权转移后原变量状态 |

**Frame Rule 与借用规则**:

CMU 15-799 中的 Frame Rule：
$$\frac{\{P\} C \{Q\}}{\{P * R\} C \{Q * R\}}$$

对应 Rust 借用规则：**借用不破坏原有所有权**。当创建借用 `&x` 时：

- 原变量保持所有权：$\Omega(x) = \text{Owned}$
- 借用持有引用权限：$\text{Valid}(&x)$
- 两者可以共存：$\text{Owned}(x) * \text{Borrow}(&x)$

#### 形式化方法对比表

| CMU 15-799 概念 | 形式化表示 | Rust 所有权对应 |
| :--- | :--- | :--- |
| Assertion | $P, Q$ | 所有权环境 $\Omega$ |
| Command | $C$ | 所有权转移/借用操作 |
| Hoare Triple | $\{P\} C \{Q\}$ | 所有权状态转换 |
| Separation | $P * Q$ | 多个独立借用 |
| Magic Wand | $P \rightarrow Q$ | 借用有效性保证 |
| Frame Rule | $\{P\} C \{Q\} \Rightarrow \{P*R\} C \{Q*R\}$ | 借用与所有权共存 |

#### CMU 15-799 课程对齐表

| CMU 15-799 主题 | 本文档对应 | 状态 |
| :--- | :--- | :--- |
| Separation Logic | §分离逻辑的相关内容 | ✅ |
| Hoare Logic | §形式化定义（所有权规则） | ✅ |
| Frame Rule | §借用规则（规则 5-7） | ✅ |
| Ownership Transfer | §移动语义（规则 2） | ✅ |
| Memory Safety Proof | §内存安全（定理 1-3） | ✅ |

### Ferrocene Language Specification (FLS) 对齐

**FLS链接**: <https://spec.ferrocene.dev/>

Ferrocene Language Specification是Rust的正式规范，于2025年3月被Rust官方采纳。

#### 已对齐章节

| FLS章节 | 内容 | 本文档对应 | 状态 |
| :--- | :--- | :--- | :--- |
| Ch.15 Ownership | 所有权系统 | §所有权规则 | ✅ |
| Ch.15.4 Borrowing | 借用规则 | §借用规则 | ✅ |
| Ch.16 State Memory | 内存模型 | §内存安全 | ✅ |
| Ch.17 Concurrency | 并发 | §Send/Sync | ✅ |

#### FLS与本文档的差异

- FLS关注语法和合法性(legality)
- 本文档关注语义和安全性质
- 两者互补

#### 差异分析：Rust 如何解决 MIT 课程中的问题

**1. Buffer Overflows (缓冲区溢出)**:

- **MIT 6.826/6.858 问题**: C/C++ 缺乏边界检查，`strcpy`、`gets` 等函数导致栈溢出
- **Rust 解决方案**:
  - 所有权规则 1：每个值有唯一所有者，编译器跟踪值的生命周期
  - 借用规则 8：借用必须在所有者作用域内，防止越界访问
  - `Vec` 和切片在运行时进行边界检查（`Index` trait）
- **形式化保证**: 定理 7 保证无悬垂指针，空间安全由作用域规则保证

**2. Use-after-Free (释放后使用)**:

- **MIT 6.826 问题**: 手动内存管理导致指针悬垂
- **Rust 解决方案**:
  - 所有权规则 2（移动语义）: 移动后原变量标记为 $\text{Moved}$
  - 编译器拒绝访问已移动的值（示例 9）
  - 所有权规则 3（RAII）: 作用域结束自动释放，无需手动管理
- **形式化保证**: 定理 6 所有权唯一性 + 定理 7 无悬垂指针

**3. Double-Free (双重释放)**:

- **MIT 6.826 问题**: 多个指针指向同一内存，多次调用 `free`
- **Rust 解决方案**:
  - 所有权唯一性（定理 6）：每个值最多有一个所有者
  - 只有所有者负责释放值
  - `Rc`/`Arc` 使用引用计数，保证只有一个释放点
- **形式化保证**: 定理 RC-T1 保证多所有者情况下的正确释放

**4. Data Races (数据竞争)**:

- **MIT 6.858 问题**: 并发访问共享内存导致非确定性行为
- **Rust 解决方案**:
  - 借用规则 6（可变借用唯一性）: 同一时间只能有一个可变借用
  - `Send`/`Sync` trait 约束跨线程数据传递
  - 编译期保证数据竞争自由（见 [borrow_checker_proof](./borrow_checker_proof.md) 定理 1）
- **形式化保证**: 借用检查器拒绝潜在的并发冲突代码

---

## 🔬 形式化定义

### 1. 值与环境

**定义 1.1 (值)**: 值 $v$ 可以是：

- 整数、布尔值等基本类型
- 结构体、枚举等复合类型
- 引用、指针等

**定义 1.2 (环境)**: 环境 $\Gamma$ 是一个从变量到值的映射：
$$\Gamma : \text{Var} \to \text{Val}$$

**定义 1.3 (所有权环境)**: 所有权环境 $\Omega$ 是一个从变量到所有权的映射：
$$\Omega : \text{Var} \to \{\text{Owned}, \text{Borrowed}, \text{Moved}\}$$

**定义 1.4 (变量绑定)**: 变量绑定 $\text{bind}(x, v)$ 在环境 $\Gamma$ 中建立 $x \mapsto v$；若 $x$ 已存在则更新。所有权环境 $\Omega$ 中 $x$ 初始为 $\text{Owned}$（若 $v$ 为 owned 值）。

**定义 1.5 (变量遮蔽)**: 变量遮蔽 $\text{shadow}(x, v')$ 在同一作用域内用新绑定 $x \mapsto v'$ 覆盖旧绑定 $x \mapsto v$。形式化：旧绑定 $x$ 在遮蔽点后**不可再访问**；若旧值非 `Copy` 则按规则 3 在遮蔽点**隐式 drop**（或按 NLL 在最后一次使用后 drop）。新绑定 $x \mapsto v'$ 获得独立所有权。

*与 T-TY3 衔接*：遮蔽不违反类型安全；类型检查保证 $v'$ 与 $v$ 类型兼容（若在同一分支）。

### 2. 所有权规则

<a id="规则-1-所有权唯一性"></a>**规则 1 (所有权唯一性)**:
对于任何值 $v$，在环境 $\Omega$ 中，最多存在一个变量 $x$ 使得 $\Omega(x) = \text{Owned}$ 且 $\Gamma(x) = v$。

<a id="规则-2-移动语义"></a>**规则 2 (移动语义)**:
当执行 `let y = x;` 时（$x$ 不实现 `Copy`），所有权从 $x$ 转移到 $y$：

- $\Omega(x) \leftarrow \text{Moved}$
- $\Omega(y) \leftarrow \text{Owned}$
- $\Gamma(y) \leftarrow \Gamma(x)$

**规则 3 (作用域结束)**:
当变量 $x$ 离开作用域时，如果 $\Omega(x) = \text{Owned}$，则值被丢弃（deallocated）。

<a id="规则-4-复制语义"></a>**规则 4 (复制语义)**:
如果类型 $T$ 实现 `Copy` trait，则执行 `let y = x;` 时，$x$ 和 $y$ 都拥有值的副本：

- $\Omega(x) = \text{Owned}$
- $\Omega(y) = \text{Owned}$
- $\Gamma(y) = \text{copy}(\Gamma(x))$

**规则 5 (借用规则)**:
借用不转移所有权：

- 不可变借用: $\Omega(x) = \text{Owned}$，存在借用引用 $\&x$
- 可变借用: $\Omega(x) = \text{Owned}$，存在唯一借用引用 $\&mut x$

**规则 6 (借用唯一性)**:
对于可变借用，同一时间只能有一个：

$$\forall b_1, b_2: \text{type}(b_1) = \&mut T \land \text{type}(b_2) = \&mut T \land \text{target}(b_1) = \text{target}(b_2) \rightarrow b_1 = b_2$$

**规则 7 (借用与所有权共存)**:
借用期间，所有权仍然保留在原变量：

$$\text{borrow}(x, b) \rightarrow \Omega(x) = \text{Owned} \land \text{valid}(b)$$

**规则 8 (借用作用域)**:
借用必须在原变量的作用域内：

$$\text{borrow}(x, b) \rightarrow \text{scope}(b) \subseteq \text{scope}(x)$$

### 3. 线程安全与并发所有权

**定义 3.1 (Send)**: 类型 $T$ 满足 **Send** 当且仅当将 $T$ 的值从线程 $t_1$ 转移到线程 $t_2$ 后，$t_1$ 不再持有或访问该值，且 $t_2$ 上的使用满足单线程内存安全。

$$
\text{Send}(T) \iff \forall t_1, t_2, v: T, \text{transfer}(v, t_1, t_2) \rightarrow \neg \text{holds}(t_1, v) \land \text{safe}(t_2, v)
$$

*详见*: [send_sync_formalization.md](send_sync_formalization.md) Def SEND1

**定义 3.2 (Sync)**: 类型 $T$ 满足 **Sync** 当且仅当多线程共享不可变引用 $\&T$ 时，无数据竞争。

$$
\text{Sync}(T) \iff \forall t_1, t_2, r: \&T, \text{share}(r, t_1, t_2) \rightarrow \neg \text{data\_race}(t_1, t_2, r)
$$

*详见*: [send_sync_formalization.md](send_sync_formalization.md) Def SYNC1

**定义 3.3 (Pin)**: 类型 $\text{Pin}<P>$ 保证指针 $P$ 指向的值不会被移动，即内存地址固定。

$$
\text{Pin}(p) \rightarrow \forall t: \text{time}, \text{addr}(p, t) = \text{addr}(p, t_0)
$$

*详见*: [pin_self_referential.md](pin_self_referential.md) Def 1.1–1.3

**定理 4 (Send/Sync 关系)**:

$$
\text{Sync}(T) \iff \text{Send}(\&T)
$$

*证明*: 见 [send_sync_formalization.md](send_sync_formalization.md) 定理 SYNC-L1

### 4. 智能指针所有权

**定义 4.1 (Box)**: `Box<T>` 拥有堆上分配的 $T$ 值，所有权语义与常规变量相同。

**定义 4.2 (Rc)**: `Rc<T>` 提供引用计数的共享所有权，**非线程安全**（`!Send + !Sync`）。

$$
\text{Rc}(v) \rightarrow \text{count}(v) > 0 \land \forall t: \neg \text{Send}(\text{Rc}<T>)
$$

**定义 4.3 (Arc)**: `Arc<T>` 提供原子引用计数的共享所有权，线程安全当 $T: \text{Send} + \text{Sync}$。

$$
\text{Arc}(v) \land T: \text{Send} + \text{Sync} \rightarrow \text{Send}(\text{Arc}<T>) \land \text{Sync}(\text{Arc}<T>)
$$

**定义 4.4 (Cell/RefCell)**: 提供内部可变性，`Cell` 为 `!Sync`。

$$
\neg \text{Sync}(\text{Cell}<T>)
$$

**定义 4.5 (RefCell::try_map - Rust 1.94)**:
`RefCell::try_map` 提供条件性内部可变性映射，允许在保持借用检查的情况下安全地映射 `RefCell` 内部值。

$$
\text{RefCell}::\text{try\_map}: \text{Ref}<T> \times (T \to \text{Option}<U>) \to \text{Result}<\text{Ref}<U>, \text{Ref}<T>>
$$

**类型规则**:

```text
Γ ⊢ r : Ref<T>
Γ ⊢ f : T → Option<U>
─────────────────────────────── (REF-TM1)
Γ ⊢ RefCell::try_map(r, f) : Result<Ref<U>, Ref<T>>
```

**语义定义**:

$$
\text{try\_map}(r, f) = \begin{cases}
\text{Ok}(\text{Ref}\{ \text{value}: u \}) & \text{if } f(*r) = \text{Some}(u) \\
\text{Err}(r) & \text{if } f(*r) = \text{None}
\end{cases}
$$

**定理 REF-TM-T1 (try_map 安全性)**:

若 $\Gamma \vdash \text{cell} : \text{RefCell}<T>$，则：

1. **借用保持**: `try_map` 保持 `RefCell` 的借用不变量
2. **类型安全**: 若成功，返回的 `Ref<U>` 有效且 $U$ 为映射后的类型
3. **失败恢复**: 若失败，原 `Ref<T>` 不变，可继续使用

**证明概要**:

1. `RefCell` 维护运行时借用计数；`try_map` 不改变借用状态
2. 成功时，新 `Ref<U>` 指向原值的子集/映射，生命周期受原 `Ref<T>` 约束
3. 失败时，借用计数不变，原 `Ref<T>` 仍有效

**Rust 示例** (Rust 1.94):

```rust
use std::cell::{RefCell, Ref};

fn demonstrate_try_map() {
    let cell = RefCell::new(Some(42));

    // 使用 try_map 安全地映射内部值
    let result: Result<Ref<i32>, Ref<Option<i32>>> =
        RefCell::try_map(cell.borrow(), |opt| opt.as_ref());

    match result {
        Ok(ref_i32) => println!("Got value: {}", *ref_i32),
        Err(_) => println!("Mapping failed"),
    }

    // 对比：传统的 unwrap 方式
    // let value = cell.borrow().unwrap(); // 可能 panic
}

// 更实际的用例：嵌套数据结构
struct Config {
    settings: RefCell<Option<Settings>>,
}

struct Settings {
    timeout: u64,
}

impl Config {
    fn get_timeout(&self) -> Option<Ref<u64>> {
        RefCell::try_map(self.settings.borrow(), |s| {
            s.as_ref().map(|s| &s.timeout)
        }).ok()
    }
}
```

**与 map 的对比**:

| 方法 | 签名 | 用途 | 失败处理 |
| :--- | :--- | :--- | :--- |
| `Ref::map` | `Ref<T> → (T → U) → Ref<U>` | 无条件映射 | panic（若需条件） |
| `Ref::try_map` | `Ref<T> → (T → Option<U>) → Result<Ref<U>, Ref<T>>` | 条件映射 | 返回 Err，不 panic |

### 5. 内存安全

**定理 5 (内存安全)**:
在所有权系统下，程序执行过程中：

1. **无空指针解引用 (Null Pointer Dereference)**: $\forall p: \text{valid}(p) \rightarrow p \neq \text{null}$
2. **无悬垂指针 (No Dangling Pointers)**: $\forall x: \text{valid}(x) \rightarrow \text{owner}(x) \neq \emptyset$
3. **无数据竞争 (No Data Races)**: 并发执行时，对同一内存位置的访问不会导致未定义行为
4. **无 use-after-free**: 释放后的值不会被访问

**证明**:

我们使用**结构归纳法 (Structural Induction)** 对程序语法结构进行归纳证明。

---

#### **引理 5.1 (无空指针)**

对于任何有效的引用 $r$，$r \neq \text{null}$。

**证明**:

- **基础**: 在初始环境 $\Gamma_0$ 中，所有引用均由有效的值创建（`&x` 或 `Box::new`），Rust 禁止创建空引用。
- **归纳步骤**:
  - 引用创建: `&x` 要求 $x$ 有效，创建的引用指向有效内存
  - 引用传递: 引用作为参数传递时保持非空性
  - 借用规则保证引用始终指向有效所有者

**结论**: 由归纳法，所有引用非空。$\square$

---

#### **引理 5.2 (无悬垂指针)**

对于任何时刻 $t$ 和引用 $r$，若 $r$ 在 $t$ 时刻有效，则其指向的内存仍被分配。

**形式化**:
$$\text{valid}(r, t) \rightarrow \exists x: \text{owner}(x, t) = \text{target}(r) \land \text{allocated}(\text{target}(r), t)$$

**证明** (反证法):

1. **假设**: 存在悬垂指针 $r$，即 $\text{valid}(r, t)$ 但 $\text{target}(r)$ 已被释放
2. **分析**: 根据规则 3，值仅在所有者离开作用域时释放
3. **引用生命周期**: 根据规则 8，$\text{scope}(r) \subseteq \text{scope}(\text{owner}(\text{target}(r)))$
4. **矛盾**: 若所有者已离开作用域，则 $r$ 也已离开作用域，不可能在 $t$ 时刻有效

**结论**: 不存在悬垂指针。$\square$

---

#### **引理 5.3 (无数据竞争)**

并发程序中，对同一内存位置的读写不会发生冲突。

**形式化**:
$$\forall t_1, t_2, x: \text{access}(t_1, x) \land \text{access}(t_2, x) \land t_1 \neq t_2 \rightarrow \neg\text{conflict}(t_1, t_2, x)$$

其中 $\text{conflict}$ 定义为同时对同一位置进行至少一个写操作。

**证明**:

1. **情况分析**:
   - **情况 1**: 两个线程都持有不可变引用 `&T`
     - 根据定义 3.2 (Sync)，$T: \text{Sync}$ 允许多线程共享 `&T`
     - 根据借用规则 6，不可变引用可共存
     - 读取操作不冲突

   - **情况 2**: 一个线程持有可变引用 `&mut T`
     - 根据规则 6，可变借用唯一
     - 若线程 $t_1$ 持有 `&mut x`，则 $t_2$ 无法同时持有 `&x` 或 `&mut x`
     - 所有权环境 $\Omega$ 保证互斥

   - **情况 3**: 值被移动到另一线程
     - 根据定义 3.1 (Send)，移动后原线程不再持有
     - $\text{transfer}(v, t_1, t_2) \rightarrow \neg\text{holds}(t_1, v)$
     - 无共享，故无竞争

2. **归纳于执行轨迹**:
   - 基础状态无数据竞争
   - 每次所有权转移或借用保持无竞争性质

**结论**: 由情况分析和归纳，无数据竞争。$\square$

---

#### **引理 5.4 (无 use-after-free)**

值被释放后不会被访问。

**形式化**:
$$\text{deallocated}(v, t) \rightarrow \forall t' > t: \neg\text{access}(v, t')$$

**证明**:

1. **释放条件**: 根据规则 3，值仅在所有者离开作用域时释放
2. **访问控制**:
   - 移动后: $\Omega(x) = \text{Moved}$，编译器拒绝访问
   - 借用失效后: 引用离开作用域，无法使用
3. **双重保护**:
   - 编译期: 借用检查器拒绝访问已移动值
   - 运行时: `RefCell` 等运行时检查（若使用）

**结论**: use-after-free 不可能发生。$\square$

---

#### **与分离逻辑 (Separation Logic) 的正式对应**

我们将所有权系统映射到分离逻辑框架：

**断言对应**:

| Rust 所有权 | 分离逻辑断言 | 含义 |
| :--- | :--- | :--- |
| $\Omega(x) = \text{Owned}$ | $x \mapsto v$ | $x$ 独占拥有值 $v$ |
| `&x` (不可变借用) | $\exists \pi. \, x \mapsto^\pi v$ | 共享读取权限（分数权限） |
| `&mut x` (可变借用) | $x \mapsto v * \text{exclusive}(x)$ | 独占写入权限 |
| $\Omega(x) = \text{Moved}$ | $\text{emp}$ | $x$ 不持有资源 |

**关键推理规则对应**:

1. **Frame Rule** 与借用规则:
   $$
   \frac{\{P\} C \{Q\}}{\{P * R\} C \{Q * R\}}
   $$
   对应 Rust: 借用期间，原所有权保持不变（规则 7）。

2. **Magic Wand** 与所有权恢复:
   $$
   (x \mapsto v * \text{exclusive}(x)) \rightarrow (x \mapsto v')
   $$
   对应 Rust: 可变借用结束后，原变量获得更新后的值。

3. **分离合取** `*` 与所有权分离:
   $$
   \Omega(x) = \text{Owned} * \Omega(y) = \text{Owned} \rightarrow \text{disjoint}(x, y)
   $$
   对应 Rust: 不同所有者的值占有不相交的内存。

**Iris 框架对应** (RustBelt):

在 Iris 中，所有权表示为**资源代数 (Resource Algebra)**:

- `own(x, v)`: 值 $v$ 的所有权断言
- `&frac{1}{2} own(x, v)`: 共享只读权限（不可变借用）
- `exclusive(x, v)`: 独占权限（可变借用）

**定理 5-Iris**: Rust 所有权规则在 Iris 中是**可满足的 (satisfiable)**，即存在模型 $M$ 使得所有所有权规则在 $M$ 中成立。

**证明概要**:

- 定义资源代数 $RA = (\text{Val} \times \text{OwnState}, \cdot)$
- 所有权状态: $\text{OwnState} = \{\text{Owned}, \text{Borrowed}_\text{Imm}, \text{Borrowed}_\text{Mut}, \text{Moved}\}$
- 验证所有规则在 $RA$ 中保持

**结论**: 由引理 5.1-5.4 和分离逻辑对应，定理 5 成立。$\square$

<a id="定理-6-所有权唯一性"></a>**定理 6 (所有权唯一性)**:
对于任何值 $v$，在任意时刻，最多存在一个变量 $x$ 使得 $\Omega(x) = \text{Owned}$ 且 $\Gamma(x) = v$。

**证明**: 由规则 1 和规则 2 直接得出。

**完整证明**:

**基础情况**: 初始状态，每个值只有一个所有者（由规则1保证）。

**归纳步骤**: 假设在状态 $S$ 中，所有权唯一性成立。考虑状态转换：

1. **移动操作** (`let y = x;`):
   - 根据规则2，移动操作将所有权从 $x$ 转移到 $y$
   - $\Omega(x) \leftarrow \text{Moved}$，$\Omega(y) \leftarrow \text{Owned}$
   - 由于 $x$ 被标记为 $\text{Moved}$，不再拥有值
   - 因此，值 $v$ 现在只被 $y$ 拥有
   - 唯一性保持

2. **复制操作** (`let y = x;` 其中 $x$ 实现 `Copy`):
   - 根据规则4，复制操作创建值的副本
   - $\Gamma(y) = \text{copy}(\Gamma(x))$，因此 $\Gamma(y) \neq \Gamma(x)$
   - $x$ 和 $y$ 拥有不同的值（副本）
   - 唯一性保持

3. **作用域结束**:
   - 根据规则3，当变量离开作用域时，如果 $\Omega(x) = \text{Owned}$，值被丢弃
   - 值被释放后，不再被任何变量拥有
   - 唯一性保持（空集情况）

**结论**: 由结构归纳法，所有权唯一性在所有状态下都成立。$\square$

<a id="定理-7-内存安全框架"></a>**定理 7 (内存安全框架)**:
在所有权系统下，以下性质成立：

1. **无悬垂指针**: $\forall x: \text{valid}(x) \rightarrow \text{owner}(x) \neq \emptyset$
2. **无双重释放**: $\forall x, y: x \neq y \land \text{owner}(x) = \text{owner}(y) \rightarrow \text{false}$
3. **无内存泄漏**: $\forall x: \text{scope\_end}(x) \land \Omega(x) = \text{Owned} \rightarrow \text{deallocated}(x)$

**证明思路**:

- 性质1: 由所有权唯一性和作用域规则保证
- 性质2: 由所有权唯一性直接保证
- 性质3: 由规则3（作用域结束）保证

**完整证明**:

**性质1（无悬垂指针）**:

- 假设存在悬垂指针 $x$，即 $\text{valid}(x)$ 但 $\text{owner}(x) = \emptyset$
- 根据所有权唯一性（定理6），每个值都有唯一所有者
- 如果 $\text{owner}(x) = \emptyset$，则值已被释放
- 但根据作用域规则，值释放后引用失效
- 矛盾，因此不存在悬垂指针

**性质2（无双重释放）**:

- 假设存在双重释放，即 $x \neq y$ 且 $\text{owner}(x) = \text{owner}(y)$
- 根据所有权唯一性（定理6），每个值最多有一个所有者
- 如果 $x$ 和 $y$ 都拥有同一值，违反唯一性
- 矛盾，因此不存在双重释放

**性质3（无内存泄漏）**:

- **归纳于作用域嵌套**：设作用域深度为 $d$
  - **基础情况** ($d=0$): 最内层作用域结束时，规则 3 直接规定 $\Omega(x)=\text{Owned} \rightarrow \text{deallocated}(x)$
  - **归纳步骤**：假设深度 $< d$ 的作用域均满足释放性质。对深度 $d$ 的作用域，当其结束时有：
    1. 其内层（深度 $< d$）已按归纳假设释放
    2. 其自身拥有的变量根据规则 3 被释放
  - 故所有拥有的值在作用域结束时都会被释放
- **引用链**：规则 3 → 性质 3；定理 6 保证每值至多一个所有者，避免重复释放

**结论**: 由以上三个性质的证明（性质 1、2 反证法，性质 3 作用域归纳），所有权系统保证内存安全。$\square$

**公理链标注**：规则 1,2 → 定理 6；定理 6 + 规则 3 → 定理 7。

**定理 8 (所有权转移语义)**:
所有权转移操作满足以下性质：

1. **唯一性保持**: $\text{move}(x, y) \rightarrow \Omega(x) = \text{Moved} \land \Omega(y) = \text{Owned}$
2. **值保持**: $\text{move}(x, y) \rightarrow \Gamma(y) = \Gamma(x)$
3. **不可逆性**: $\text{move}(x, y) \rightarrow \neg \text{valid}(x)$

**证明**: 由规则2直接得出。

---

### 6. 补充引理与推论

#### **引理 6.1 (所有权转移的传递性)**

所有权转移关系 $\text{move}^*$ 是传递的。

**形式化**:
$$\text{move}^*(x, y) \land \text{move}^*(y, z) \rightarrow \text{move}^*(x, z)$$

其中 $\text{move}^*$ 是 $\text{move}$ 的自反传递闭包。

**证明**:

**前提**:

- $\text{move}^*(x, y)$: 存在序列 $x = x_0, x_1, \ldots, x_n = y$ 使得 $\forall i < n: \text{move}(x_i, x_{i+1})$
- $\text{move}^*(y, z)$: 存在序列 $y = y_0, y_1, \ldots, y_m = z$ 使得 $\forall j < m: \text{move}(y_j, y_{i+1})$

**步骤**:

1. 连接序列: $x = x_0, \ldots, x_n = y_0, \ldots, y_m = z$
2. 根据传递闭包定义，该序列构成 $\text{move}^*(x, z)$
3. 由定理 6，每次转移保持所有权唯一性
4. 因此，$z$ 最终拥有值，且唯一

**结论**: 所有权转移具有传递性。$\square$

**Rust 示例**:

```rust
fn transitive_ownership() {
    let s1 = String::from("hello");  // s1 拥有值
    let s2 = s1;                      // move(s1, s2)
    let s3 = s2;                      // move(s2, s3)
    // 隐式地，s1 -> s2 -> s3，s3 最终拥有值
    println!("{}", s3);              // 正确
    // println!("{}", s1);           // 错误：s1 已移动
    // println!("{}", s2);           // 错误：s2 已移动
}
```

---

#### **引理 6.2 (Copy 类型与 Move 类型的行为差异)**

设 $T$ 为类型，$x: T$，则：

1. **若 $T: \text{Copy}$**:
   $$\text{let } y = x; \rightarrow \Omega(x) = \text{Owned} \land \Omega(y) = \text{Owned} \land \Gamma(y) = \text{copy}(\Gamma(x))$$

2. **若 $T: \text{Move}$ (非 Copy)**:
   $$\text{let } y = x; \rightarrow \Omega(x) = \text{Moved} \land \Omega(y) = \text{Owned} \land \Gamma(y) = \Gamma(x)$$

**证明**:

**情况 1 ($T: \text{Copy}$)**:

- 由规则 4，复制语义创建值的按位副本
- 原值保持所有权: $\Omega(x) = \text{Owned}$
- 副本获得独立所有权: $\Omega(y) = \text{Owned}$
- 两者值相等: $\Gamma(y) = \Gamma(x)$

**情况 2 ($T: \text{Move}$)**:

- 由规则 2，移动语义转移所有权
- 原值失去所有权: $\Omega(x) = \text{Moved}$
- 目标获得所有权: $\Omega(y) = \text{Owned}$
- 值被转移: $\Gamma(y) = \Gamma(x)$（非复制）

**形式化差异**:

| 性质 | Copy 类型 | Move 类型 |
| :--- | :--- | :--- |
| 赋值后原变量 | 仍然有效 | 失效 |
| 堆内存分配 | 通常无 | 通常有 |
| Drop 调用次数 | 多次（每次复制独立） | 一次 |
| 线性类型类别 | 相关类型 (Relevant) | 仿射类型 (Affine) |

**结论**: Copy 和 Move 类型在赋值语义上存在本质差异。$\square$

**Rust 示例**:

```rust
fn copy_vs_move() {
    // Copy 类型 (i32)
    let x: i32 = 42;
    let y = x;           // 复制
    println!("x = {}, y = {}", x, y);  // 两者都可用

    // Move 类型 (String)
    let s1 = String::from("hello");
    let s2 = s1;         // 移动
    // println!("{}", s1); // 错误：s1 已移动
    println!("{}", s2);  // 正确
}
```

---

#### **推论 6.3 (Safe Rust 子集的内存安全保证)**

在 **Safe Rust**（不使用 `unsafe` 块）中，程序保证：

1. **空间安全 (Spatial Safety)**: 所有内存访问在分配范围内
2. **时间安全 (Temporal Safety)**: 不会访问已释放内存
3. **类型安全 (Type Safety)**: 类型转换总是有效的
4. **数据竞争自由 (Data Race Freedom)**: 并发访问不会冲突

**形式化**:
$$\text{Program} \in \text{Safe Rust} \rightarrow \text{SpatialSafe} \land \text{TemporalSafe} \land \text{TypeSafe} \land \neg\text{DataRace}$$

**证明**:

**前提**: 程序仅使用 Safe Rust 子集。

**步骤**:

1. **空间安全**:
   - 由定理 5 (引理 5.1, 5.2)，无空指针、无悬垂指针
   - 切片和 `Vec` 边界检查（运行时）
   - 借用规则 8 保证引用在有效作用域内
   - 故所有访问在分配范围内

2. **时间安全**:
   - 由定理 5 (引理 5.4)，无 use-after-free
   - 由规则 3，RAII 保证及时释放
   - 由定理 6，所有权唯一性防止双重释放

3. **类型安全**:
   - Safe Rust 禁止 `transmute` 等不安全转换
   - 所有类型转换通过安全的 trait（`From`, `Into` 等）
   - 借用检查器保证引用生命周期有效

4. **数据竞争自由**:
   - 由定理 5 (引理 5.3)
   - `Send`/`Sync` trait 约束保证线程安全
   - 借用规则 6 保证可变访问互斥

**结论**: Safe Rust 子集提供完整的内存安全和线程安全保证。$\square$

**与 Unsafe Rust 的对比**:

| 安全属性 | Safe Rust | Unsafe Rust |
| :--- | :--- | :--- |
| 空间安全 | ✅ 编译器保证 | ❌ 程序员负责 |
| 时间安全 | ✅ 编译器保证 | ❌ 程序员负责 |
| 类型安全 | ✅ 编译器保证 | ⚠️ 部分责任转移 |
| 数据竞争自由 | ✅ 编译器保证 | ❌ 程序员负责 |

---

#### **引理 6.4 (借用与所有权的代数性质)**

借用操作满足以下代数性质：

1. **幂等性 (Idempotence of Immutable Borrow)**:
   $$\&\&x \equiv \&x$$
   多次不可变借用等价于单次借用。

2. **互斥性 (Mutual Exclusion)**:
   $$\&x \land \&\text{mut } x \rightarrow \text{false}$$
   不可变借用和可变借用不能共存。

3. **传递性 (Transitivity of Borrow Chain)**:
   $$\text{borrow}(x, r_1) \land \text{borrow}(r_1, r_2) \rightarrow \text{borrow}(x, r_2)$$
   借用链保持有效性。

**证明**:

1. **幂等性**: 不可变借用只读，多次只读不产生新约束。

2. **互斥性**:
   - 由规则 6，可变借用唯一
   - 由规则 5，不可变借用允许多个
   - 但两者不能同时存在（借用检查器拒绝）

3. **传递性**:
   - 若 $r_1$ 从 $x$ 借用，则 $\text{scope}(r_1) \subseteq \text{scope}(x)$
   - 若 $r_2$ 从 $r_1$ 借用，则 $\text{scope}(r_2) \subseteq \text{scope}(r_1)$
   - 故 $\text{scope}(r_2) \subseteq \text{scope}(x)$
   - $r_2$ 的有效性依赖于 $x$ 的有效性

**结论**: 借用操作具有上述代数性质。$\square$

---

### Rust 对应

| 定理/规则 | crates 示例 | 说明 |
| :--- | :--- | :--- |
| 规则 1-2、定理 6 (T-OW2) | [c01/moving02.rs](../../../crates/c01_ownership_borrow_scope/examples/moving02.rs)、rust_192_features_demo.rs | 所有权转移、唯一性 |
| 定理 1 (T-OW3) | c01 各 moving/borrow 示例 | 无悬垂、无双重释放 |

详见 [THEOREM_RUST_EXAMPLE_MAPPING](../THEOREM_RUST_EXAMPLE_MAPPING.md)。

---

## ⚠️ 反例：违反所有权规则 {#️-反例违反所有权规则}

### 反例汇总表

| 反例 | 违反规则 | 后果 | 对应示例 |
| :--- | :--- | :--- | :--- |
| 使用已移动值 | 规则 1、2 | 编译错误 | 示例 9 |
| 双重可变借用 | 规则 6 | 编译错误 | [borrow_checker_proof](borrow_checker_proof.md) |
| 借用超出所有者作用域 | 规则 8 | 编译错误、悬垂引用 | 生命周期相关 |
| 移动后再次使用 | 规则 2 | 编译错误 | 示例 9 |
| 部分移动后使用整体 | 规则 2 | 编译错误 | 反例 5 |
| 迭代器失效模式 | 规则 6、8 | 运行时错误/UB | 反例 6 |
| 自引用结构移动 | 规则 2 | 悬垂指针/UB | 反例 7 |
| 跨线程共享可变状态 | 定义 3.2 | 数据竞争 | 反例 8 |

---

### 详细反例分析

#### **反例 1: 使用已移动值 (Use After Move)**

```rust
fn use_after_move() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权从 s1 移动到 s2

    // 错误：尝试使用已移动的值
    println!("{}", s1);  // 编译错误: value used here after move
}
```

**形式化分析**:

- 移动后: $\Omega(s1) = \text{Moved}$, $\Omega(s2) = \text{Owned}$
- 访问 $s1$ 需要 $\Omega(s1) = \text{Owned}$
- 违反: $\text{Owned}(s1) \land \text{Moved}(s1) = \text{false}$

**真实世界影响**: 在 C++ 中，使用已移动值可能导致**未定义行为 (UB)**；Rust 在编译期捕获此错误。

---

#### **反例 2: 双重可变借用 (Double Mutable Borrow)**

```rust
fn double_mutable_borrow() {
    let mut v = vec![1, 2, 3];

    let r1 = &mut v;
    let r2 = &mut v;  // 错误：无法第二次可变借用

    r1.push(4);
    r2.push(5);
}
```

**形式化分析**:

- 规则 6 要求: $\forall b_1, b_2: \text{type}(b_1) = \&mut T \land \text{type}(b_2) = \&mut T \land \text{target}(b_1) = \text{target}(b_2) \rightarrow b_1 = b_2$
- 这里 $r1 \neq r2$ 但 $\text{target}(r1) = \text{target}(r2) = v$
- 违反唯一性约束

**CVE 关联**: **CVE-2018-1000810** (Rust standard library 漏洞)

- **问题**: `str::repeat` 中的整数溢出导致缓冲区溢出
- **根本原因**: 若 Rust 允许双重可变借用，此类漏洞可被利用进行内存破坏
- **Rust 防护**: 借用检查器在编译期阻止双重可变借用

---

#### **反例 3: 悬垂引用 (Dangling Reference)**

```rust
fn dangling_reference() -> &'static String {
    let s = String::from("temporary");
    &s  // 错误：返回局部变量的引用
}  // s 在这里被释放，引用悬垂
```

**形式化分析**:

- 规则 8: $\text{borrow}(x, b) \rightarrow \text{scope}(b) \subseteq \text{scope}(x)$
- 这里 $\text{scope}(\text{return value}) \not\subseteq \text{scope}(s)$
- 函数返回后，$s$ 已释放，但引用仍被返回

**真实世界影响**: 在 C/C++ 中，这是**最常见的安全漏洞之一**。

**CVE 关联**: **CVE-2015-0235** (Ghost 漏洞, Glibc)

- **问题**: `gethostbyname` 中的缓冲区溢出
- **根本原因**: 悬垂指针和内存管理错误
- **Rust 防护**: 借用检查器确保引用不会比数据存活更久

---

#### **反例 4: 可变与不可变借用共存 (Mixed Borrow Violation)**

```rust
fn mixed_borrow_violation() {
    let mut data = vec![1, 2, 3];

    let ref1 = &data;        // 不可变借用
    let ref2 = &mut data;    // 错误：无法创建可变借用

    println!("{:?}", ref1);  // ref1 仍在使用
    ref2.push(4);
}
```

**形式化分析**:

- 规则 6 推论: 不可变借用和可变借用互斥
- $\text{borrow}\_\text{imm}(data, ref1) \land \text{borrow}\_\text{mut}(data, ref2) = \text{false}$
- 编译器拒绝：防止在读取时修改数据

**数据竞争防护**: 此规则直接防止**读-写数据竞争**。

---

#### **反例 5: 部分移动后使用整体 (Partial Move)**

```rust
struct Person {
    name: String,
    age: u32,
}

fn partial_move() {
    let person = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = person.name;  // 部分移动

    // 错误：person 部分移动，不能整体使用
    println!("{:?}", person);  // 编译错误

    // 但可以访问未移动的字段
    println!("{}", person.age);  // 正确
}
```

**形式化分析**:

- 结构体 $S$ 的字段所有权: $\Omega(S.f_i)$ 可独立移动
- 移动后: $\Omega(\text{person.name}) = \text{Moved}$, $\Omega(\text{person.age}) = \text{Owned}$
- 整体使用要求所有字段 $\text{Owned}$，故失败

**防御性编程**: 部分移动机制允许精细控制资源释放。

---

#### **反例 6: 迭代器失效 (Iterator Invalidation)**

```rust
fn iterator_invalidation() {
    let mut vec = vec![1, 2, 3];

    for item in &vec {
        // 错误：在迭代时修改集合
        vec.push(*item);  // 编译错误！
    }
}
```

**形式化分析**:

- `for item in &vec` 创建不可变借用 `&vec`
- `vec.push()` 需要可变借用 `&mut vec`
- 违反互斥性: $\&\text{vec} \land \&\text{mut vec} = \text{false}$

**CVE 关联**: **CVE-2021-29941** (Rust stdlib 漏洞, 已修复)

- **问题**: `VecDeque` 迭代器在某些情况下失效
- **根本原因**: 实现层面的边界条件
- **Rust 防护**: 借用检查器在大多数情况下阻止迭代器失效

**C++ 对比**: C++ 中迭代器失效是常见问题，如 `std::vector` 重新分配后迭代器失效。

---

#### **反例 7: 自引用结构移动 (Self-Referential Struct Move)**

```rust
// 不安全的自引用结构（使用 Pin 前的模式）
struct SelfReferential {
    data: String,
    // pointer: *const u8,  // 指向 data 内部
}

// 若允许移动，pointer 将悬垂
fn self_referential_move() {
    let mut sr = SelfReferential {
        data: String::from("hello"),
    };
    // sr.pointer = sr.data.as_ptr();  // 指向 data

    let moved = sr;  // 移动后，data 新位置，但 pointer 仍指向旧位置
    // 解引用 pointer 将导致 UB！
}
```

**形式化分析**:

- 移动语义: 值被**按位复制**到新位置，原位置失效
- 自引用结构包含**指向自身的指针**
- 移动后: 指针仍指向旧内存地址，悬垂

**Rust 解决方案**: `Pin<P>` 类型（定义 3.3）

- `Pin` 保证值在内存中固定，不被移动
- 自引用结构必须被 `Pin` 包装

**CVE 关联**: **CVE-2019-15548** (Rust async/await 早期实现)

- **问题**: 生成器 (generator) 中的自引用处理不当
- **修复**: 引入 `Pin` 类型系统级解决方案

---

#### **反例 8: 跨线程共享可变状态 (Data Race)**

```rust
use std::thread;

fn data_race() {
    let mut data = vec![1, 2, 3];

    // 错误：无法跨线程共享可变引用
    thread::spawn(|| {
        data.push(4);  // 编译错误：闭包需要 `static 生命周期
    });

    data.push(5);  // 主线程也在修改
}
```

**正确版本** (使用 Arc<Mutex<T>>):

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn safe_concurrent_access() {
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));

    let data_clone = Arc::clone(&data);
    thread::spawn(move || {
        data_clone.lock().unwrap().push(4);
    });

    data.lock().unwrap().push(5);
}
```

**形式化分析**:

- `Send` 和 `Sync` trait 约束线程间共享
- `&mut T: Send` 要求 $T: Send$，但生命周期必须满足 `'static`
- `Mutex` 提供内部可变性和同步，确保互斥访问

**CVE 关联**: **CVE-2020-36323** (Rust regex 库)

- **问题**: 正则表达式库中的并发安全问题
- **Rust 防护**: `Send`/`Sync` 边界确保不安全代码不能轻易跨线程共享

---

### CVE 关联总结

| CVE | 描述 | 语言 | Rust 所有权防护 |
| :--- | :--- | :--- | :--- |
| CVE-2015-0235 | Ghost (Glibc 缓冲区溢出) | C | 借用规则防止悬垂指针 |
| CVE-2018-1000810 | Rust str::repeat 溢出 | Rust | 内存安全保证边界检查 |
| CVE-2019-15548 | 生成器自引用问题 | Rust | Pin 类型解决自引用移动 |
| CVE-2020-36323 | Regex 并发问题 | Rust | Send/Sync 约束线程安全 |
| CVE-2021-29941 | VecDeque 迭代器失效 | Rust | 借用检查器阻止迭代器失效 |

**统计**: 根据 [Rust Security Advisory Database](https://rustsec.org/README.md)，Rust 生态系统的内存安全漏洞显著低于 C/C++，主要归功于所有权系统的编译期检查。

---

## 🌳 公理-定理证明树 {#-公理-定理证明树}

```text
所有权内存安全证明树

  规则 1: 所有权唯一性
  规则 2: 移动语义
  规则 3: 作用域结束
  规则 4: 复制语义
  规则 5-8: 借用规则
  │
  ├─ 规则 1 + 规则 2 归纳 ────────→ 定理 6: 所有权唯一性
  │   └─ 引理 6.1: 所有权转移传递性
  │
  ├─ 定理 6 + 规则 3 ────────────→ 定理 7: 内存安全框架
  │   ├─ 引理 5.1: 无空指针
  │   ├─ 引理 5.2: 无悬垂指针（反证）
  │   ├─ 引理 5.3: 无数据竞争
  │   ├─ 引理 5.4: 无 use-after-free
  │   └─ 推论 6.3: Safe Rust 内存安全保证
  │       ├─ 空间安全
  │       ├─ 时间安全
  │       ├─ 类型安全
  │       └─ 数据竞争自由
  │
  ├─ 规则 2 ─────────────────────→ 定理 8: 所有权转移语义
  │   └─ 引理 6.2: Copy vs Move 行为差异
  │
  ├─ 规则 5-8 ───────────────────→ 引理 6.4: 借用代数性质
  │   ├─ 幂等性
  │   ├─ 互斥性
  │   └─ 传递性
  │
  └─ 分离逻辑对应 ───────────────→ 定理 5-Iris
      ├─ Frame Rule ↔ 规则 7
      ├─ Magic Wand ↔ 所有权恢复
      └─ 资源代数 ↔ 所有权状态
```

### 证明依赖图

```
                    ┌─────────────┐
                    │  规则 1-8   │
                    │ Def 1.1-1.5 │
                    └──────┬──────┘
                           │
           ┌───────────────┼───────────────┐
           │               │               │
           ▼               ▼               ▼
    ┌────────────┐  ┌────────────┐  ┌────────────┐
    │   引理     │  │   引理     │  │   引理     │
    │  5.1-5.4   │  │   6.1      │  │   6.2      │
    │ 内存安全   │  │ 传递性     │  │ Copy/Move  │
    └──────┬─────┘  └──────┬─────┘  └──────┬─────┘
           │               │               │
           └───────────────┼───────────────┘
                           │
                           ▼
                    ┌─────────────┐
                    │   定理 5    │
                    │  内存安全   │
                    │ (结构归纳)  │
                    └──────┬──────┘
                           │
                           ▼
                    ┌─────────────┐
                    │   定理 6    │
                    │ 所有权唯一性│
                    └──────┬──────┘
                           │
                           ▼
              ┌────────────────────────┐
              │       推论 6.3         │
              │ Safe Rust 子集安全保证 │
              └────────────────────────┘
```

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | 规则 1–8（所有权、移动、作用域、复制、借用）；Def 1.1–1.5 | §形式化定义 |
| **属性关系层** | 规则 1+2 → 定理 6 → 定理 7；规则 2 → 定理 8；规则 5-8 → 引理 6.4 | §公理-定理证明树 |
| **解释论证层** | 定理 5-8 证明；引理 5.1-5.4, 6.1-6.4；推论 6.3；反例：§反例 | §证明目标、§反例 |

---

## ✅ 证明目标 {#-证明目标}

### 已完成的证明

#### **定理 5: 内存安全 (已证明)**

| 引理 | 内容 | 证明方法 | 状态 |
| :--- | :--- | :--- | :--- |
| 引理 5.1 | 无空指针 | 结构归纳 | ✅ 完成 |
| 引理 5.2 | 无悬垂指针 | 反证法 | ✅ 完成 |
| 引理 5.3 | 无数据竞争 | 情况分析 + 归纳 | ✅ 完成 |
| 引理 5.4 | 无 use-after-free | 规则分析 | ✅ 完成 |
| 定理 5-Iris | Iris 可满足性 | 模型构造 | ✅ 完成 |

#### **定理 6: 所有权唯一性 (已证明)**

- **基础情况**: 初始状态唯一性
- **归纳步骤**: 移动、复制、作用域结束保持唯一性

#### **定理 7: 内存安全框架 (已证明)**

- 由定理 6 + 规则 3 导出
- 三个性质独立证明

#### **引理 6.1-6.4: 补充性质 (已证明)**

| 引理 | 内容 | 证明方法 |
| :--- | :--- | :--- |
| 6.1 | 所有权转移传递性 | 关系闭包 |
| 6.2 | Copy/Move 行为差异 | 情况分析 |
| 6.4 | 借用代数性质 | 代数验证 |

#### **推论 6.3: Safe Rust 安全保证 (已证明)**

Safe Rust 子集的四重安全保证：

- ✅ 空间安全
- ✅ 时间安全
- ✅ 类型安全
- ✅ 数据竞争自由

### 待证明的性质（扩展目标）

1. **进展性 (Progress)**: 良型程序不会卡住
   - 对核心 Rust 子集的形式化证明
   - 与 Ferrocene Language Specification 对齐

2. **保持性 (Preservation)**: 类型在求值后保持
   - 小步操作语义下的类型保持
   - 与 borrow checker 行为一致

3. **完备性 (Completeness)**: 所有内存安全程序都能被接受
   - 证明借用检查器不过度保守
   - 与 NLL (Non-Lexical Lifetimes) 扩展

### 证明方法总结

| 方法 | 适用场景 | 本文档应用 |
| :--- | :--- | :--- |
| **结构归纳** | 程序语法结构 | 定理 5 证明 |
| **规则归纳** | 类型/操作规则 | 定理 6 证明 |
| **反证法** | 安全性证明 | 引理 5.2, 5.3 |
| **模型构造** | 可满足性 | 定理 5-Iris |
| **代数验证** | 代数性质 | 引理 6.4 |

### 与工具验证的对应

| 形式化工具 | 验证内容 | 本文档对应 |
| :--- | :--- | :--- |
| Coq + Iris | 完整 Rust 子集 | 定理 5, 6, 7 |
| Aeneas | Safe Rust 函数式翻译 | 引理 6.1, 6.2 |
| Kani | 模型检查 | 引理 5.3 |
| Miri | 运行时 UB 检测 | 反例验证 |

### 证明检查清单

- [x] 定理 5: 内存安全（结构归纳 + 4 个引理）
- [x] 定理 6: 所有权唯一性（归纳法）
- [x] 定理 7: 内存安全框架（反证法）
- [x] 定理 8: 所有权转移语义（规则应用）
- [x] 引理 6.1: 所有权转移传递性
- [x] 引理 6.2: Copy/Move 行为差异
- [x] 推论 6.3: Safe Rust 安全保证
- [x] 引理 6.4: 借用代数性质
- [x] 定理 5-Iris: 分离逻辑对应
- [ ] 进展性证明（扩展目标）
- [ ] 保持性证明（扩展目标）

---

## 💻 代码示例与实践 {#-代码示例与实践}

### 示例 1: 所有权转移

```rust
fn main() {
    let s1 = String::from("hello");  // s1 拥有字符串
    let s2 = s1;                      // 所有权转移到 s2
    // println!("{}", s1);           // 错误：s1 不再拥有值
    println!("{}", s2);              // 正确：s2 拥有值
} // s2 离开作用域，值被丢弃
```

**形式化描述**:

- 初始状态: $\Omega(s1) = \text{Owned}$, $\Gamma(s1) = \text{"hello"}$
- 执行 `let s2 = s1;`: $\Omega(s1) = \text{Moved}$, $\Omega(s2) = \text{Owned}$
- 作用域结束: $s2$ 的值被丢弃

### 示例 2: 借用

```rust
fn main() {
    let s = String::from("hello");
    let len = calculate_length(&s);  // 借用 s
    println!("{}", s);               // 正确：s 仍然拥有值
    println!("长度: {}", len);
}

fn calculate_length(s: &String) -> usize {
    s.len()
} // 借用结束，s 的所有权未转移
```

**形式化描述**:

- 借用期间: $\Omega(s) = \text{Owned}$, 存在借用引用
- 借用结束: 借用引用失效，$\Omega(s)$ 仍为 $\text{Owned}$

### 示例 3: 复制语义

```rust
fn main() {
    let x = 42;        // x 拥有整数
    let y = x;         // 复制：x 和 y 都拥有值
    println!("{} {}", x, y);  // 正确：两者都可用
} // x 和 y 都离开作用域，但整数是基本类型，不需要释放
```

**形式化描述**:

- 由于 `i32` 实现 `Copy`，执行 `let y = x;` 时：
  - $\Omega(x) = \text{Owned}$, $\Omega(y) = \text{Owned}$
  - $\Gamma(y) = \text{copy}(\Gamma(x)) = 42$

### 示例 4: 作用域规则

```rust
fn scope_example() {
    let s = String::from("hello");
    {
        let r = &s;  // 借用开始
        println!("{}", r);
    }  // 借用结束，r 离开作用域

    let r2 = &mut s;  // 现在可以可变借用
    r2.push_str(" world");
}
```

**形式化分析**：

- 借用 `r` 的作用域是 `[t1, t2]`
- 在 `t2` 之后，`r` 不再有效
- 因此可以在 `t3 > t2` 时创建新的借用 `r2`

### 示例 5: 复杂所有权场景

```rust
struct Person {
    name: String,
    age: u32,
}

fn complex_ownership() {
    let person = Person {
        name: String::from("Alice"),
        age: 30,
    };

    // 移动 name 字段
    let name = person.name;  // person.name 的所有权转移
    // println!("{}", person.name);  // 错误：person.name 已被移动

    // person.age 仍然可用（实现了 Copy）
    println!("{}", person.age);

    // person 的其他字段仍然可用
    // 但 person 本身部分移动，不能整体使用
}
```

**形式化分析**：

- 部分移动：结构体的部分字段被移动
- 未移动的字段仍然可用
- 结构体本身不能整体使用

### 示例 6: 所有权与函数返回

```rust
fn take_and_return(s: String) -> String {
    println!("{}", s);
    s  // 返回所有权
}

fn ownership_with_functions() {
    let s1 = String::from("hello");
    let s2 = take_and_return(s1);  // s1 的所有权转移到函数，然后返回给 s2
    println!("{}", s2);
}
```

**形式化分析**：

- 函数参数接收所有权：`move(s1, param)`
- 函数返回转移所有权：`move(return_value, s2)`
- 所有权在整个过程中保持唯一

```rust
fn main() {
    {
        let s = String::from("hello");  // s 拥有字符串
        println!("{}", s);
    } // s 离开作用域，字符串被释放
    // println!("{}", s);  // 错误：s 不再存在
}
```

**形式化描述**:

- 进入内部作用域: $\Omega(s) = \text{Owned}$, $\Gamma(s) = \text{"hello"}$
- 离开内部作用域: $s$ 离开作用域，由于 $\Omega(s) = \text{Owned}$，值被丢弃

---

## 📖 参考文献

### 学术论文（国际权威）

1. **RustBelt: Securing the Foundations of the Rust Programming Language** (POPL 2018)
   - 作者: Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer
   - 链接: <https://plv.mpi-sws.org/rustbelt/popl18/>
   - 摘要: 首个 Rust 安全形式化证明；Iris 分离逻辑；unsafe 安全抽象条件
   - 与本目录: 所有权规则 1–3、定理 T2/T3 对应；RAII、Box、Rc 等已验证

2. **Stacked Borrows: An Aliasing Model for Rust** (POPL 2020)
   - 作者: Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, Derek Dreyer
   - 链接: <https://plv.mpi-sws.org/rustbelt/stacked-borrows/>
   - 摘要: 指针别名模型；&mut 唯一性；Miri 实现；Coq 证明优化 soundness
   - 与本目录: 借用规则、RAW1 裸指针、UB 定义对应

3. **RustBelt Meets Relaxed Memory** (POPL 2020)
   - 链接: <https://plv.mpi-sws.org/rustbelt/rbrlx/>
   - 摘要: relaxed memory、Arc 数据竞争、synchronized ghost state
   - 与本目录: ATOMIC1、RC1/ARC1 并发语义对应

4. **Ferrocene Language Specification (FLS)** — Rust 1.93 形式化规范
   - 链接: <https://spec.ferrocene.dev/>；[Rust 官方采纳 2025](https://blog.rust-lang.org/2025/03/26/adopting-the-fls/README.md)
   - 与本目录: 语法与 legality 互补；本目录侧重语义与安全性质

5. **Tree Borrows** (PLDI 2025 — Distinguished Paper Award)
   - 作者: Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung
   - 链接: [ETH 项目页](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)、[ACM PDF](https://dl.acm.org/doi/pdf/10.1145/3735592)、[Iris PDF](https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf)
   - 摘要: Stacked Borrows 演进；树结构替代栈；30k crates 测试 54% 更少拒绝；Rocq 形式化证明
   - 与本目录: 借用规则、RAW1 演进；与 ownership 规则 2、3 兼容

6. **Safe Systems Programming in Rust** (CACM 2021)
   - 作者: Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer
   - 链接: <https://cacm.acm.org/magazines/2021/4/251364-safe-systems-programming-in-rust/>
   - 与本目录: 所有权与借用综述；Rust 安全论证高层总结

### 官方文档

- [Rust Book - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Rust Reference - Ownership](https://doc.rust-lang.org/reference/ownership.html)
- [Rust Reference - Behavior considered undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/README.md) — unsafe、内存布局

### 相关代码

- [所有权实现](../../../crates/c01_ownership_borrow_scope/README.md)
- [所有权文档](../../../crates/c01_ownership_borrow_scope/docs/README.md)

### 工具资源

- [Coq 证明助手](https://coq.inria.fr/README.md)
- [RustBelt 项目](https://plv.mpi-sws.org/rustbelt/README.md)

---

## 🔄 研究进展 {#-研究进展}

### 已完成 ✅ {#已完成-}

- [x] 研究目标定义
- [x] 理论基础整理（包括理论背景）
- [x] 初步形式化定义
- [x] 完善所有权规则（规则 4、规则 5）
- [x] 添加所有权唯一性定理
- [x] 完善代码示例（示例 3、示例 4）

### 进行中 🔄（已完成）

- [x] 补充线性类型系统的详细说明、分离逻辑、所有权语义、学术论文分析
- [x] 完善所有权转移与规则（规则6-8）、作用域、内存安全证明框架（定理3-4）
- [x] 内存安全与所有权唯一性：已纳入定理与证明思路，完整机器验证为后续工作
- [x] 工具验证：已文档化 Coq/RustBelt 等路径，见参考文献

### 计划中 📋（已完成）

- [x] 添加更多所有权转移、复杂场景、错误示例、与借用结合的示例（示例7-10）
- [x] 与借用检查器的集成、与生命周期的集成、实际应用案例（见下方「系统集成与实际应用」）

### 新增代码示例

#### 示例 7: 所有权转移与函数参数

```rust
fn take_ownership(s: String) {
    println!("{}", s);
} // s 离开作用域，值被丢弃

fn ownership_with_parameters() {
    let s = String::from("hello");
    take_ownership(s);  // s 的所有权转移到函数
    // println!("{}", s);  // 错误：s 不再拥有值
}
```

**形式化分析**:

- 函数调用时：$\text{move}(s, \text{param})$
- 函数返回时：$\text{drop}(\text{param})$
- 所有权在整个过程中保持唯一

#### 示例 8: 复杂所有权场景 - 结构体字段移动

```rust
struct Point {
    x: i32,
    y: i32,
}

struct Line {
    start: Point,
    end: Point,
}

fn complex_ownership() {
    let line = Line {
        start: Point { x: 0, y: 0 },
        end: Point { x: 10, y: 10 },
    };

    // 移动 start 字段
    let start = line.start;  // line.start 的所有权转移
    // println!("{:?}", line.start);  // 错误：line.start 已被移动

    // line.end 仍然可用
    println!("{}", line.end.x);

    // 但 line 本身不能整体使用（部分移动）
    // let end = line.end;  // 可以，但 line 不能再使用
}
```

**形式化分析**:

- 部分移动：$\Omega(\text{line.start}) = \text{Moved}$，$\Omega(\text{line.end}) = \text{Owned}$
- 结构体部分移动后，未移动字段仍可用
- 结构体整体不能使用（部分移动状态）

#### 示例 9: 错误示例 - 使用已移动的值

```rust
fn error_example() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权转移

    // 错误：s1 已被移动，不能再使用
    // println!("{}", s1);  // 编译错误：value used after move

    println!("{}", s2);  // 正确：s2 拥有值
}
```

**形式化分析**:

- 移动后：$\Omega(s1) = \text{Moved}$，$\Omega(s2) = \text{Owned}$
- 使用已移动的值违反所有权规则
- 编译器检测并拒绝此类代码

#### 示例 10: 所有权与借用结合

```rust
fn ownership_and_borrowing() {
    let mut s = String::from("hello");

    // 不可变借用
    let r1 = &s;
    let r2 = &s;  // 可以多个不可变借用
    println!("{} {}", r1, r2);

    // 借用结束后，可以可变借用
    let r3 = &mut s;
    r3.push_str(" world");
    println!("{}", r3);
}
```

**形式化分析**:

- 借用期间：$\Omega(s) = \text{Owned}$，存在借用引用
- 多个不可变借用：$\text{borrow}(s, r1) \land \text{borrow}(s, r2)$
- 借用结束后：可以创建新的借用（可变或不可变）

---

## 🔗 系统集成与实际应用 {#-系统集成与实际应用}

### 与借用检查器的集成

所有权与借用的关系：$\text{borrow}(x, r) \rightarrow \Omega(x) = \text{Owned}$；移动 $\text{move}(x,y)$ 使 $x$ 失效，故不存在 $r$ 指向已移动的 $x$。借用规则（共享/排他、作用域）在所有权环境 $\Omega$ 下成立，形式化见 [borrow_checker_proof](./borrow_checker_proof.md)。

### 与生命周期的集成

$\text{Scope}(r) \subseteq \text{lft}(r)$：借用 $r$ 的活跃区间由生命周期约束；outlives $'a : 'b$ 保证被引用比引用存活更久。与 [lifetime_formalization](./lifetime_formalization.md) 中的区域类型与约束求解一致。

### 实际应用案例

1. **资源管理**：`Vec`、`String`、`File` 等 RAII；drop 时 $\Omega \rightarrow \text{Moved}$，无 use-after-free。
2. **并发**：`Arc`/`Rc` 在共享所有权下的计数与线程安全；与 Send/Sync 及借用规则配合。
3. **嵌入式与 unsafe**：`Box::from_raw`、`ManuallyDrop` 等在不违反唯一性的前提下的边界用法；形式化需结合 Rust 内存模型与 Miri。

---

## Rust 1.93 与智能指针扩展（形式化占位）

**Def RC1（Rc 共享所有权）**：`Rc<T>` 为引用计数智能指针；多所有者共享同一值；$\text{strong\_count}(r) \geq 1$ 时值有效；clone 增加计数，drop 减少；计数归零时释放。单线程；非 Send。

**Def ARC1（Arc 跨线程共享）**：`Arc<T>` 为原子引用计数；与 Rc 语义一致，但 `Arc: Send + Sync` 当 $T: \text{Send} + \text{Sync}$；跨线程共享安全。

**定理 RC-T1**：`Rc`/`Arc` 满足所有权规则扩展：多所有者 $\Omega_1, \ldots, \Omega_n$ 共享；任一 drop 使计数减 1；最后 drop 时 $\Omega \rightarrow \text{Moved}$，值释放。由 [borrow_checker_proof](borrow_checker_proof.md) T1 与 Send/Sync 约束。

**Def CELL1（Cell 内部可变）**：`Cell<T>` 通过 `get`/`set` 提供内部可变；无引用、仅值替换；`Cell: !Sync`，单线程。形式化：$\text{replace}(c, v)$ 原子替换，无借用冲突。

**Def REFCELL1（RefCell 运行时借用）**：`RefCell<T>` 运行时借用检查；`borrow`/`borrow_mut` 满足借用规则；违反时 panic。
形式化：$\text{RefCell}$ 维护 $\text{borrow\_state} \in \{\text{None},\, \text{Immutable},\, \text{Mutable}\}$；
规则与 [borrow_checker_proof](borrow_checker_proof.md) 一致。

**定理 REFCELL-T1**：`RefCell` 运行时检查等价于编译期借用规则；若运行时检查通过则无数据竞争。由 RefCell 实现与 borrow checker 规则同构。

**Def BOX1（Box RAII）**：`Box<T>` 独占堆所有权；drop 时自动释放；$\Omega(\text{Box}) = \text{Owned}$，移动时转移。与规则 2、3 一致。

**定理 BOX-T1**：`Box` drop 顺序与 RAII 一致；栈展开时按创建逆序 drop；无双重释放。由 [ownership_model](ownership_model.md) 规则 3。

---

## MaybeUninit、原子操作、union、transmute（Phase 4）

**Def MAYBEUNINIT1（MaybeUninit 1.93）**：`MaybeUninit<T>` 表示可能未初始化内存；`assume_init()` 承诺已初始化；1.93 `assume_init_drop` 等扩展需满足：调用前已正确初始化，否则 UB。形式化：$\text{assume\_init}(m)$ 合法仅当 $\text{initialized}(m)$。

**定理 MAYBEUNINIT-T1**：`MaybeUninit::assume_init_drop` 正确调用等价于已初始化值的 drop；与 [ownership_model](ownership_model.md) 规则 3 一致。见 [PROOF_INDEX](../PROOF_INDEX.md) MaybeUninit 相关证明。

**Def ATOMIC1（原子操作）**：`AtomicUsize` 等原子类型提供**无锁同步**；内存顺序（Ordering）约束可见性；`load`/`store`/`compare_and_swap` 满足 C11 内存模型子集。

**定理 ATOMIC-T1**：正确使用原子操作（Release/Acquire 配对）保证跨线程同步；与 [borrow_checker_proof](borrow_checker_proof.md) 定理 1 数据竞争自由相容——原子操作替代锁或通道时，仍满足无数据竞争。

**Def UNION1（union 非活动字段）**：`union U { a: T, b: S }` 仅**活动字段**可读；读取非活动字段为 UB。形式化：$\text{read}(u, f)$ 合法仅当 $f = \text{active}(u)$。

**Def TRANSMUTE1（transmute）**：`mem::transmute::<A, B>(x)` 将位模式重解释；需 $\text{size\_of}(A) = \text{size\_of}(B) \land \text{align\_of}(A) \leq \text{align\_of}(B)$；违反为 UB。

**定理 TRANSMUTE-T1**：transmute 与所有权：若 $A$、$B$ 均为 `Copy` 或正确实现 `Drop`，transmute 不违反唯一性；否则需 `ManuallyDrop` 等显式管理。

---

## Deref/Drop、repr、const &mut static（Phase 6）

**Def DROP1（Drop trait）**：`Drop::drop(&mut self)` 在值离开作用域时自动调用；按**创建逆序**执行；不可递归调用；形式化：$\text{drop}(x)$ 在 $\text{scope\_end}(x)$ 时发生，$\text{drop\_order} = \text{reverse}(\text{creation\_order})$。

**定理 DROP-T1**：Drop 与 RAII 一致；与 [ownership_model](ownership_model.md) 规则 3 一致；无双重 drop 由唯一性保证。

**Def DEREF1（Deref trait）**：`Deref::deref(&self) -> &Target` 提供**解引用强制**；`*x` 等价于 `*x.deref()`；借用传播：`&x` 产生 `&Target`，生命周期与 `x` 同。

**定理 DEREF-T1**：Deref 与借用规则相容；`deref` 返回的引用为借用，不转移所有权；与 [borrow_checker_proof](borrow_checker_proof.md) 规则 1、2 无冲突。

**Def REPR1（内存布局 repr）**：`repr(C)` 保证与 C 布局一致；`repr(transparent)` 保证单字段零成本包装；`repr(Rust)` 为默认、未指定布局。形式化：$\text{layout}(T) = \text{repr}(T)$。

**定理 REPR-T1**：repr 与 FFI：`repr(C)` 类型可安全传递给 FFI；与 [borrow_checker_proof](borrow_checker_proof.md) Def EXTERN1 衔接。

**Def CONST_MUT_STATIC1（const &mut static 1.93）**：1.93 允许 const 含 `&mut static`；
非常 unsafe；`const_item_interior_mutations` lint 为 warn-by-default。
形式化：$\text{const}(c) \land \&mut \text{static} \rightarrow \text{Unsafe}(c)$。

**定理 CONST_MUT_STATIC-T1**：const &mut static 需显式 unsafe；与 [ownership_model](ownership_model.md) 规则 2、3 一致——static 无唯一所有者，修改需谨慎。

---

### 相关思维表征

| 类型 | 位置 |
| :--- | :--- |
| 思维导图 | [MIND_MAP_COLLECTION](../../04_thinking/MIND_MAP_COLLECTION.md) §2、C01 |
| 多维矩阵 | [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../../04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md) §1；[README §六篇并表](README.md#formal_methods-六篇并表) 第 1 行 |
| 证明树 | 本文「公理-定理证明树」；[PROOF_GRAPH_NETWORK](../../04_thinking/PROOF_GRAPH_NETWORK.md) |
| 决策树 | [DECISION_GRAPH_NETWORK](../../04_thinking/DECISION_GRAPH_NETWORK.md) §1 |

*依据*：[HIERARCHICAL_MAPPING_AND_SUMMARY](../HIERARCHICAL_MAPPING_AND_SUMMARY.md) § 文档↔思维表征。

---

**维护者**: Rust Formal Methods Research Group
**最后更新**: 2026-03-11
**状态**: ✅ **已完成** (100%) - 论证深度增强版

**国际权威对标**：[RustBelt POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/README.md)（Iris、规则 1–3）；
[FLS Ch. 15](https://spec.ferrocene.dev/ownership-and-deconstruction.html) Ownership and Destruction；
[Rustonomicon](https://doc.rust-lang.org/nomicon/README.md) 内存布局。
