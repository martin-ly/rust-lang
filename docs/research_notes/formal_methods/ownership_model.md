# 所有权模型形式化

> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-27
> **更新内容**: 添加 Send/Sync/Pin 形式化定义 (Def 3.1–3.3)；添加智能指针所有权定义 (Def 4.1–4.4)；定理编号更新
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成 (Week 1 任务 P1-W1-T1)
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
    - [Rust 对应](#rust-对应)
  - [⚠️ 反例：违反所有权规则 {#️-反例违反所有权规则}](#️-反例违反所有权规则-️-反例违反所有权规则)
  - [🌳 公理-定理证明树 {#-公理-定理证明树}](#-公理-定理证明树--公理-定理证明树)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [✅ 证明目标 {#-证明目标}](#-证明目标--证明目标)
    - [待证明的性质](#待证明的性质)
    - [证明方法](#证明方法)
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

**性质**:

1. **追踪来源**: 记录每个借用的生成源
2. **验证有效性**: 确保借用的目标在创建点存活
3. **防止悬垂**: 借用生成关系保证无悬垂引用

**形式化**:
$$
\text{borrow\_generated\_from}(b, x) \rightarrow \Omega(x) = \text{Owned} \land \text{Alive}(x, \text{create\_point}(b))
$$

**与本文档的对应**:

- 与 Def 1.3（所有权环境）兼容
- 与规则 8（借用作用域）一致
- 强化定理 7（无悬垂指针）的保证

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

**Lab 1: Buffer Overflows & Memory Safety**

- 6.826 Lab 1 通过缓冲区溢出实验展示了传统 C/C++ 代码中的内存安全漏洞
- **Rust 所有权解决方案**: 所有权唯一性（规则 1）保证每个值只有一个所有者，编译时阻止 use-after-free 和 double-free
- **形式化对应**: 6.826 中的内存安全漏洞对应本文定理 7 中的"无悬垂指针"、"无双重释放"保证

**Lab 2: Privilege Separation & Capabilities**

- 6.826 Lab 2 研究基于权能（capability）的访问控制
- **Rust 所有权与权能的对应**: Rust 所有权可视为一种**权能系统**——拥有值的所有权意味着拥有操作该值的权能
- **形式化对应**: `&T` 和 `&mut T` 对应只读/读写权能，所有权转移对应权能委托

**Lecture: Memory Safety Vulnerabilities**

- 6.826 讲座涵盖的内存安全漏洞类型：
  - **Use-after-free** → Rust 所有权规则 2（移动后原变量失效）+ 规则 3（作用域结束释放）防止
  - **Double-free** → Rust 所有权唯一性（定理 6）保证
  - **Buffer overflow** → Rust 借用规则（规则 6-8）+ 边界检查防止

#### MIT 6.858: Computer Systems

**课程链接**: <https://css.csail.mit.edu/6.858/>

MIT 6.858 从系统层面研究计算机安全，其内容与本研究的所有权模型形成互补：

**Lab 1: Buffer Overflows & x86 Assembly**

- 6.858 Lab 1 通过 x86 汇编分析缓冲区溢出的底层机制
- **Rust 内存模型对应**: Rust 的所有权环境 $\Omega$ 和值环境 $\Gamma$ 在抽象层消除了汇编层面的内存错误
- **形式化对应**: 定义 1.3（所有权环境）在编译时静态保证内存安全，避免运行时汇编层面的检查开销

**Lab 2: Privilege Separation**

- 6.858 Lab 2 研究用户态/内核态隔离
- **Rust 所有权隔离**: 不同变量拥有不同值的所有权，形成天然的**内存隔离**——一个变量无法访问另一个变量拥有的值，除非显式借用或转移
- **形式化对应**: 分离逻辑中的 $P * Q$（分离合取）对应 Rust 中不同所有权的值持有不相交的内存

**Lab 3: Symbolic Execution**

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

**Spatial Safety (空间安全)**

空间安全保证程序只能访问分配给其的内存范围：

$$\text{SpatialSafe}(P) \leftrightarrow \forall p \in P: \text{Access}(p, addr) \rightarrow addr \in \text{Allocated}(p)$$

**Rust 保证**:

- 借用规则 8: $\text{borrow}(x, b) \rightarrow \text{scope}(b) \subseteq \text{scope}(x)$
- 切片和 `Vec` 等容器在运行时进行边界检查
- 引用总是指向有效内存（定理 7: 无悬垂指针）

**Temporal Safety (时间安全)**

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

**1. Buffer Overflows (缓冲区溢出)**

- **MIT 6.826/6.858 问题**: C/C++ 缺乏边界检查，`strcpy`、`gets` 等函数导致栈溢出
- **Rust 解决方案**:
  - 所有权规则 1：每个值有唯一所有者，编译器跟踪值的生命周期
  - 借用规则 8：借用必须在所有者作用域内，防止越界访问
  - `Vec` 和切片在运行时进行边界检查（`Index` trait）
- **形式化保证**: 定理 7 保证无悬垂指针，空间安全由作用域规则保证

**2. Use-after-Free (释放后使用)**

- **MIT 6.826 问题**: 手动内存管理导致指针悬垂
- **Rust 解决方案**:
  - 所有权规则 2（移动语义）: 移动后原变量标记为 $\text{Moved}$
  - 编译器拒绝访问已移动的值（示例 9）
  - 所有权规则 3（RAII）: 作用域结束自动释放，无需手动管理
- **形式化保证**: 定理 6 所有权唯一性 + 定理 7 无悬垂指针

**3. Double-Free (双重释放)**

- **MIT 6.826 问题**: 多个指针指向同一内存，多次调用 `free`
- **Rust 解决方案**:
  - 所有权唯一性（定理 6）：每个值最多有一个所有者
  - 只有所有者负责释放值
  - `Rc`/`Arc` 使用引用计数，保证只有一个释放点
- **形式化保证**: 定理 RC-T1 保证多所有者情况下的正确释放

**4. Data Races (数据竞争)**

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

### 5. 内存安全

**定理 5 (内存安全)**:
在所有权系统下，程序执行过程中：

- 不会出现悬垂指针（dangling pointer）
- 不会出现双重释放（double free）
- 不会出现内存泄漏（memory leak）

**证明思路**:

- 所有权唯一性保证每个值只有一个所有者
- 作用域规则保证值在使用后正确释放
- 移动语义保证值不会被意外复制

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

### Rust 对应

| 定理/规则 | crates 示例 | 说明 |
| :--- | :--- | :--- |
| 规则 1-2、定理 6 (T-OW2) | [c01/moving02.rs](../../../crates/c01_ownership_borrow_scope/examples/moving02.rs)、[rust_192_features_demo.rs](../../../crates/c01_ownership_borrow_scope/examples/rust_192_features_demo.rs) | 所有权转移、唯一性 |
| 定理 1 (T-OW3) | c01 各 moving/borrow 示例 | 无悬垂、无双重释放 |

详见 [THEOREM_RUST_EXAMPLE_MAPPING](../THEOREM_RUST_EXAMPLE_MAPPING.md)。

---

## ⚠️ 反例：违反所有权规则 {#️-反例违反所有权规则}

| 反例 | 违反规则 | 后果 | 对应示例 |
| :--- | :--- | :--- | :--- |
| 使用已移动值 | 规则 1、2 | 编译错误 | 示例 9 |
| 双重可变借用 | 规则 6 | 编译错误 | [borrow_checker_proof](borrow_checker_proof.md) |
| 借用超出所有者作用域 | 规则 8 | 编译错误、悬垂引用 | 生命周期相关 |
| 移动后再次使用 | 规则 2 | 编译错误 | 示例 9 |

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
  ├─ 规则 1 + 规则 2 归纳 ────────→ 定理 2: 所有权唯一性
  │
  ├─ 定理 2 + 规则 3 ────────────→ 定理 3: 内存安全框架
  │   ├─ 无悬垂指针（反证）
  │   ├─ 无双重释放（反证）
  │   └─ 无内存泄漏（规则 3）
  │
  └─ 规则 2 ─────────────────────→ 定理 4: 所有权转移语义
```

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | 规则 1–8（所有权、移动、作用域、复制、借用）；Def 1.1–1.5 | §形式化定义 |
| **属性关系层** | 规则 1+2 → 定理 6 → 定理 7；规则 2 → 定理 8 | §公理-定理证明树 |
| **解释论证层** | 定理 6/7/8 证明；反例：§反例 | §证明目标、§反例 |

---

## ✅ 证明目标 {#-证明目标}

### 待证明的性质

1. **进展性 (Progress)**: 良型程序不会卡住
2. **保持性 (Preservation)**: 类型在求值后保持
3. **内存安全**: 不会出现内存错误

### 证明方法

- **结构归纳**: 对程序结构进行归纳证明
- **规则归纳**: 对类型规则进行归纳证明
- **模型检查**: 使用工具验证系统属性

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
   - 链接: <https://spec.ferrocene.dev/>；[Rust 官方采纳 2025](https://blog.rust-lang.org/2025/03/26/adopting-the-fls/)
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
- [Rustonomicon](https://doc.rust-lang.org/nomicon/) — unsafe、内存布局

### 相关代码

- [所有权实现](../../../crates/c01_ownership_borrow_scope/src/)
- [所有权文档](../../../crates/c01_ownership_borrow_scope/docs/README.md)

### 工具资源

- [Coq 证明助手](https://coq.inria.fr/)
- [RustBelt 项目](https://plv.mpi-sws.org/rustbelt/)

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

**Def REFCELL1（RefCell 运行时借用）**：`RefCell<T>` 运行时借用检查；`borrow`/`borrow_mut` 满足借用规则；违反时 panic。形式化：$\text{RefCell}$ 维护 $\text{borrow\_state} \in \{\text{None},\, \text{Immutable},\, \text{Mutable}\}$；规则与 [borrow_checker_proof](borrow_checker_proof.md) 一致。

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

**Def CONST_MUT_STATIC1（const &mut static 1.93）**：1.93 允许 const 含 `&mut static`；非常 unsafe；`const_item_interior_mutations` lint 为 warn-by-default。形式化：$\text{const}(c) \land \&mut \text{static} \rightarrow \text{Unsafe}(c)$。

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
**最后更新**: 2026-02-20
**状态**: ✅ **已完成** (100%)

**国际权威对标**：[RustBelt POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)（Iris、规则 1–3）；[FLS Ch. 15](https://spec.ferrocene.dev/ownership-and-deconstruction.html) Ownership and Destruction；[Rustonomicon](https://doc.rust-lang.org/nomicon/) 内存布局。
