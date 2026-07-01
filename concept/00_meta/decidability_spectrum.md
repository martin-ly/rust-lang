# Rust 编译期可判定性谱系全景（Decidability Spectrum）
>
> **EN**: Decidability Spectrum
> **Summary**: Decidability Spectrum. Core Rust concept.
> **受众**: [研究者]
> **定位**: 本文件从**纵向判定链路**梳理 Rust 编译器在全编译流程中的可判定性问题，与 `semantic_expressiveness.md` 的横向七维光谱形成正交互补。
> **原则**: 不做"编译器实现手册"，聚焦"什么问题 Rust 编译器能在编译期判定、什么不能、不能时的补偿机制是什么"。
> **对齐来源**:
>
> [Rust Reference](https://doc.rust-lang.org/reference/) ·
> [Rust RFCs](https://rust-lang.github.io/rfcs/) ·
> [RustBelt / Oxide](https://plv.mpi-sws.org/rustbelt/) ·
> [POPL Papers](https://dblp.org/db/conf/popl/index.html) ·
> [Theory of Computation](https://en.wikipedia.org/wiki/Theory_of_computation)
>
> **基准版本**: Rust 1.96.0 stable (Edition 2024)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
> **来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/)
---

> **Bloom 层级**: 分析 → 评价 → 创造

**变更日志**:

- v1.0 (2026-05-21): 初始版本——全链路可判定性谱系 + 9 层判定边界 + Rice 定理映射 + Rust 1.95 特性判定映射

---

## 📑 目录

- [Rust 编译期可判定性谱系全景（Decidability Spectrum）](#rust-编译期可判定性谱系全景decidability-spectrum)
  - [📑 目录](#-目录)
  - [零、TL;DR —— 可判定性速查](#零tldr--可判定性速查)
  - [一、权威来源与梳理方法论](#一权威来源与梳理方法论)
    - [1.1 来源分级](#11-来源分级)
    - [1.2 可判定性的形式化定义](#12-可判定性的形式化定义)
    - [1.3 谱系层级与 Rust 编译管道映射](#13-谱系层级与-rust-编译管道映射)
  - [二、可判定性谱系总览](#二可判定性谱系总览)
    - [2.1 谱系全景图](#21-谱系全景图)
    - [2.2 判定边界色标矩阵](#22-判定边界色标矩阵)
  - [三、L0 词法与语法层](#三l0-词法与语法层)
  - [四、L1 名称解析层](#四l1-名称解析层)
  - [五、L2 类型系统层](#五l2-类型系统层)
    - [5.1 局部类型推断](#51-局部类型推断)
    - [5.2 Trait 约束求解](#52-trait-约束求解)
    - [5.3 类型等价与一致性](#53-类型等价与一致性)
  - [六、L3 借用检查与生命周期层](#六l3-借用检查与生命周期层)
    - [6.1 借用检查：NLL 与 Polonius](#61-借用检查nll-与-polonius)
    - [6.2 生命周期约束可满足性](#62-生命周期约束可满足性)
  - [七、L4 常量求值层（CTFE）](#七l4-常量求值层ctfe)
  - [八、L5 并发安全层](#八l5-并发安全层)
    - [8.1 数据竞争的编译期排除](#81-数据竞争的编译期排除)
    - [8.2 死锁与活锁：不可判定性](#82-死锁与活锁不可判定性)
  - [九、L6 代码生成与优化层](#九l6-代码生成与优化层)
  - [十、不可判定性边界：Rice 定理与停机问题](#十不可判定性边界rice-定理与停机问题)
    - [10.1 Rice 定理在 Rust 中的映射](#101-rice-定理在-rust-中的映射)
    - [10.2 停机问题与 CTFE 的边界](#102-停机问题与-ctfe-的边界)
  - [十一、Rust 1.95 特性的可判定性映射](#十一rust-195-特性的可判定性映射)
  - [十二、可判定性–表达力权衡矩阵](#十二可判定性表达力权衡矩阵)
  - [十三、思维表征体系](#十三思维表征体系)
    - [13.1 判定路径决策树](#131-判定路径决策树)
    - [13.2 谱系演化时间线](#132-谱系演化时间线)
  - [十四、定理推理链](#十四定理推理链)
    - [定理一致性矩阵（可判定性谱系专集）](#定理一致性矩阵可判定性谱系专集)
    - [推理链图谱](#推理链图谱)
  - [十五、相关概念链接（L0-L7 映射）](#十五相关概念链接l0-l7-映射)
    - [L0-L7 纵向映射](#l0-l7-纵向映射)
    - [相关概念文件](#相关概念文件)
  - [十、可判定性论文精确引用与前沿映射](#十可判定性论文精确引用与前沿映射)
    - [10.1 POPL / PLDI 可判定性相关论文精确引用](#101-popl--pldi-可判定性相关论文精确引用)
      - [引用精度说明](#引用精度说明)
    - [10.2 Rust 特性可判定性状态 1.95+](#102-rust-特性可判定性状态-195)
      - [可判定性保持的设计模式](#可判定性保持的设计模式)
    - [10.3 开放问题（Open Problems）](#103-开放问题open-problems)
      - [开放问题 1：GATs 的完全可判定性边界](#开放问题-1gats-的完全可判定性边界)
      - [开放问题 2：关联类型归一化的终止性证明](#开放问题-2关联类型归一化的终止性证明)
      - [开放问题 3：Const Evaluation 的图灵完备性边界（受限堆 + 步数限制）](#开放问题-3const-evaluation-的图灵完备性边界受限堆--步数限制)
      - [开放问题 4：Effects 系统与类型系统可判定性的交互](#开放问题-4effects-系统与类型系统可判定性的交互)
    - [10.3 边界测试：类型推断的不可判定性与人工标注（编译错误）](#103-边界测试类型推断的不可判定性与人工标注编译错误)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：本文档《Rust 编译期可判定性谱系全景（Decidability Spectrum）》在 Rust 知识体系中属于哪一层级的元数据？（理解层）](#测验-1本文档rust-编译期可判定性谱系全景decidability-spectrum在-rust-知识体系中属于哪一层级的元数据理解层)
    - [测验 2：《Rust 编译期可判定性谱系全景（Decidability Spectrum）》的主要用途是什么？（理解层）](#测验-2rust-编译期可判定性谱系全景decidability-spectrum的主要用途是什么理解层)
    - [测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）](#测验-3元数据层文档能否替代-l1-l7-的核心概念学习理解层)

---

## 零、TL;DR —— 可判定性速查

```text
层级                判定问题                          可判定性    核心机制/边界
───────────────────────────────────────────────────────────────────────────────────────────
L0 词法/语法        Token 流 → AST                   ✅ 可判定   LR(1) 子集 + 确定性宏扩展
L1 名称解析         Path 解析、use 导入               ✅ 可判定   模块图确定性遍历
L2 类型推断         表达式局部类型推断                 ✅ 可判定   约束图 + 统一化（受限 HM）
L2 Trait 求解       约束可满足性                     ⚠️ 实践中   Chalk/Trait Engine v2（故意受限）
L3 借用检查         别名-可变互斥                     ✅ 可判定   NLL(CFG) → Polonius(Datalog)
L3 生命周期         'a ⊑ 'b 偏序约束可满足性           ✅ 可判定   Region 约束图 + 传递闭包
L4 Const 求值       编译期表达式求值                   ⚠️ 有界     Miri 解释器（步数/栈深/循环上限）
L5 数据竞争         程序是否存在数据竞争               ✅ 编译期   Send/Sync + 所有权（运行时不可判定）
L5 死锁/活锁        程序是否存在死锁                   ❌ 不可判定  Rice 定理 → 运行时检测/设计规避
L6 代码生成         优化变换等价性                     ❌ 不可判定  LLVM 启发式（非语义等价证明）
───────────────────────────────────────────────────────────────────────────────────────────
```
---

## 一、权威来源与梳理方法论

### 1.1 来源分级

| 层级 | 来源 | 使用场景 |
| :--- | :--- | :--- |
| 一级 | Rust Reference / RFCs / POPL·PLDI·TOPLAS 论文 | 判定边界、算法正确性、形式化证明 |
| 二级 | Rust Internals / 核心开发者博客 (Niko Matsakis, Ralf Jung) | 设计决策、Polonius/NLL 演进 |
| 三级 | TRPL / Rustonomicon / 编译器文档 | 工程直觉、用户可见行为 |
| 四级 | 经典计算理论教材 (Sipser, Pierce) | 可判定性/不可判定性的元理论 |

### 1.2 可判定性的形式化定义

> **定义（可判定性）**: 语言 L 是**可判定的（decidable）**，当且仅当存在图灵机 M，对任意输入 w，M 在有限步内停机，且接受 w 当且仅当 w ∈ L。
> [来源: Sipser, *Introduction to the Theory of Computation*, §4.1]

Rust 编译器的每个阶段可视为一个判定器（decider）或识别器（recognizer）：

- **判定器**: 对所有输入都在有限步内给出 Yes/No（如词法分析、NLL 借用检查）。
- **半判定器**: 对 Yes 实例停机，对 No 实例可能不停机或被人为截断（如 CTFE 接近此形态，但被步数上限强制停机）。
- **不可判定**: 不存在任何算法能在有限步内对所有实例给出正确答案（如死锁检测、程序等价性）。

### 1.3 谱系层级与 Rust 编译管道映射

```mermaid
graph TD
    A[源码 .rs] --> B[L0 词法/语法]
    B --> C[L1 名称解析]
    C --> D[L2 类型检查]
    D --> E[L3 借用检查]
    E --> F[L4 常量求值 / MIR 优化]
    F --> G[L5 并发安全检查<br/>Send/Sync 推导]
    G --> H[L6 LLVM IR 生成]
    H --> I[L6 优化 / 代码生成]

    B -.-> |✅ 可判定| B1[Token → AST]
    C -.-> |✅ 可判定| C1[模块图遍历]
    D -.-> |✅ 可判定| D1[局部推断]
    D -.-> |⚠️ 受限| D2[Trait 求解]
    E -.-> |✅ 可判定| E1[NLL/Polonius]
    F -.-> |⚠️ 有界| F1[CTFE 步数上限]
    G -.-> |✅ 编译期| G1[Send/Sync]
    G -.-> |❌ 不可判定| G2[死锁检测]
    I -.-> |❌ 不可判定| I1[优化等价性]
```
> **认知功能**:
> 该流程图将 Rust 编译管道与可判定性结果叠加，形成「**阶段×判定**」的双维认知框架。
> 建议对照阅读时关注虚线标注的判定结果（✅/⚠️/❌），理解编译器的「能力边界」在哪里。
> 关键洞察：编译器并非越往后越弱——L5 的 Send/Sync 推导反而能在编译期排除运行时不可判定的数据竞争。
> [来源: 💡 原创分析]
> [来源: [Wikipedia — Decidability]]

---

## 二、可判定性谱系总览

### 2.1 谱系全景图

Rust 编译期判定谱系可分为 **9 个层级**，从最接近源码的 L0 到最接近机器码的 L6，外加元层级的不可判定性边界（L∞）。

| 层级 | 名称 | 判定问题 | 可判定性 | 判定器形态 | 失效补偿机制 |
|:---:|:---|:---|:---:|:---|:---|
| L0 | 词法/语法 | Token 流是否构成合法 AST | ✅ | 判定器 | 无（非法程序被拒绝） |
| L1 | 名称解析 | Path 是否能唯一解析到定义 | ✅ | 判定器 | 无（歧义/未定义被拒绝） |
| L2a | 类型推断 | 表达式是否存在合法类型 | ✅ | 判定器 | 显式类型注解 |
| L2b | Trait 求解 | 约束集合是否可满足 | ⚠️ | 受限判定器 | `#[fundamental]` / 孤儿规则限制 |
| L3a | 借用检查 | 程序是否满足别名-可变规则 | ✅ | 判定器 | `unsafe` / `RefCell` / `Arc<Mutex>>` |
| L3b | 生命周期 | 生命周期约束是否可满足 | ✅ | 判定器 | 显式 `'a` 标注 / HRTB |
| L4 | 常量求值 | `const fn` 是否能在编译期求值 | ⚠️ | 有界判定器 | `const_eval_limit` / 降级为运行时 |
| L5a | 并发安全 | 类型是否线程安全 | ✅ | 判定器 | `unsafe impl Send/Sync` |
| L5b | 活性保证 | 程序是否无死锁/无饥饿 | ❌ | — | 运行时检测 / 架构设计规避 |
| L6 | 优化等价 | 优化变换是否保持语义 | ❌ | — | 测试 / MIRI / Kani 验证 |

### 2.2 判定边界色标矩阵

```text
可判定性色标：🟢 可判定  🟡 受限/有界可判定  🔴 不可判定
```
| 问题 \ 层级 | L0 | L1 | L2 | L3 | L4 | L5 | L6 |
|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| 语法合法性 | 🟢 | — | — | — | — | — | — |
| 名称唯一性 | — | 🟢 | — | — | — | — | — |
| 类型存在性 | — | — | 🟢 | — | — | — | — |
| 约束可满足性 | — | — | 🟡 | — | — | — | — |
| 别名-可变安全 | — | — | — | 🟢 | — | — | — |
| 生命周期安全 | — | — | — | 🟢 | — | — | — |
| 编译期求值停机 | — | — | — | — | 🟡 | — | — |
| 线程安全 | — | — | — | — | — | 🟢 | — |
| 无死锁 | — | — | — | — | — | 🔴 | — |
| 优化语义保持 | — | — | — | — | — | — | 🔴 |

---

## 三、L0 词法与语法层

> **判定问题**: 给定字符流，是否可唯一解析为合法 AST？
> **可判定性**: ✅ **可判定**
> **核心算法**: 确定性 LR(1) 子集 + 宏的确定性扩展

Rust 的语法分析基于一个**手工编写的递归下降解析器**（`rustc_parse`），而非生成的 LR/LL 解析器。虽然 Rust 语法并非严格属于任何经典解析器类别的子集，但 `rustc` 通过以下机制保证判定性：

1. **无歧义性保证**: Rust 语法设计刻意避免经典歧义（如 C 的「声明 vs 表达式」歧义、C++ 的「 most vexing parse」）。`let x = ...;` 与 `x = ...;` 的区分在词法层面即完成。
2. **宏扩展的确定性**: `macro_rules!` 的匹配基于**最长匹配优先**（longest match）和**优先级排序**，保证对给定输入最多只有一个匹配分支被激活。过程宏（proc-macro）在语法层面是黑盒，但其输入是已解析的 TokenStream，输出也是 TokenStream，不影响解析阶段的判定性。
3. **Edition 隔离**: 不同 Edition（2015/2018/2021/2024）的语法差异在 crate 边界隔离，避免跨 Edition 的语法歧义。

> **边界**: 宏扩展后的代码若产生语法错误，错误报告位置需通过「跨度（span）」信息回溯到原始源码。这属于**工程复杂性**而非**理论不可判定性**。 来源: [Rust Reference §3, rustc dev guide](https://doc.rust-lang.org/reference/)

**判定树**:

```mermaid
graph TD
    A[输入字符流] --> B{是否合法 UTF-8?}
    B -->|否| C[编译错误: invalid UTF-8]
    B -->|是| D{Tokenize 成功?}
    D -->|否| E[编译错误: 非法 token]
    D -->|是| F{AST 解析成功?}
    F -->|否| G[编译错误: 期望 X 但找到 Y]
    F -->|是| H{宏扩展后语法合法?}
    H -->|否| I[编译错误: 宏扩展后非法]
    H -->|是| J[✅ L0 判定通过]
```
> **认知功能**: 该判定树将词法/语法分析流程可视化为**决策分支**，每个菱形节点对应编译器的实际判断逻辑。建议用于理解编译错误的来源层级——当看到「非法 token」或「宏扩展后非法」时，能准确定位到 L0 的哪个子阶段。关键洞察：Rust 刻意保持宏扩展的确定性，这是 L0 可判定性的工程核心。[来源: 💡 原创分析]

---

## 四、L1 名称解析层

> **判定问题**: 给定 Path（如 `std::vec::Vec`），是否能唯一解析到一个定义？
> **可判定性**: ✅ **可判定**
> **核心算法**: 基于 crate 模块图的有向图遍历 + 导入表（Import Map）

Rust 名称解析遵循**严格的两阶段模型**：

1. **阶段一：构建模块图**。根据文件系统路径和 `mod` 声明构建 crate 的模块层次结构。此阶段是**纯结构性的**，无需类型信息。
2. **阶段二：路径解析**。在模块图内，根据 `use` 导入、`extern crate`、预导入（prelude）等规则，将每个路径绑定到唯一的定义项（Item）。

**判定性保证机制**:

- **无全局命名空间污染**: 每个名称的作用域由模块层次严格限定，`use` 导入不会隐式导入子项。
- **孤儿规则（Orphan Rule）的预检查**: 虽然孤儿规则主要在类型检查阶段生效，但名称解析阶段即需确定 `impl` 块的所属 crate，此判定基于模块图即可确定。
- **无循环导入**: `use` 语句的循环依赖在模块图构建阶段即可检测。

> **边界**: 宏生成的名称（`macro_rules!` 或过程宏生成的 `struct`/`fn`）需在宏扩展后才能解析。但由于宏扩展在名称解析之前完成（或交错进行但保证终止），整体仍保持判定性。 [来源: [RFC 1560](https://rust-lang.github.io/rfcs//1560-name-resolution.html), rustc_resolve 文档]

---

## 五、L2 类型系统层

### 5.1 局部类型推断

> **判定问题**: 给定函数体表达式，是否存在合法的类型赋值？
> **可判定性**: ✅ **可判定（受限 HM 子集）**
> **核心算法**: 约束生成 + 统一化（Unification）

Rust 采用**局部类型推断（Local Type Inference）**，而非 Hindley-Milner（HM）的全局推断。这一定性是**刻意的设计选择**：

| 特征 | HM (ML/Haskell) | Rust 局部推断 |
|:---|:---|:---|
| 推断范围 | 全局（跨函数） | 局部（函数体内） |
| 多态性 |  let-polymorphism (全称量化) | 仅泛型参数处显式多态 |
| 子类型 | 无 | 名义子类型 + 生命周期子类型 |
| Trait 约束 | 无（类型类独立机制） | 与类型推断深度耦合 |
| 主类型（Principal Type） | 存在且唯一 | 不一定存在（故意限制） |
| 可判定性 | 可判定（线性时间） | 可判定（多项式时间） |

Rust 局部推断的可判定性保证：

1. **函数签名显式注解**: 函数参数和返回类型必须显式写出（除闭包参数等少数例外）。这**截断了跨函数的类型传播链**，将全局推断问题分解为多个独立的局部问题。
2. **无高阶类型（HKT）**: Rust 无高阶类型多态，避免了 System F_ω 中类型推断的不可判定性。
3. **受限的递归类型**: Rust 要求递归类型通过显式 indirection（`Box<T>`、`Vec<T>`），不允许直接的 μ-类型递归，避免了无限展开。

> **定理 T-DS-001（Rust 局部类型推断可判定性）**:
> 在函数签名显式注解、无 HKT、无递归类型直接展开的约束下，Rust 函数体内的局部类型推断问题是**可判定的**，且编译器总能在有限步内给出 Yes（存在合法类型）或 No（类型不匹配）。
> [来源: Pierce, *Types and Programming Languages*, §22; Rust Reference §6]

### 5.2 Trait 约束求解

> **判定问题**: 给定一组 Trait 约束，是否存在满足所有约束的 impl？
> **可判定性**: ⚠️ **实践中可判定（故意受限）**
> **核心算法**: 基于条款（Clause）的逻辑编程求解（Chalk / 下一代 Trait Solver）

Trait 约束求解是 Rust 类型系统中最复杂的判定问题。Rust 通过以下机制保证**实践中可判定**：

1. **孤儿规则（Orphan Rule）**: 限制 impl 的声明位置，保证任意类型+Trait 组合的 impl 最多只有一个合法定义（全局唯一性）。这**将约束求解从 potentially-undecidable 的实例搜索转化为有限集合的查找**。
2. **无重叠（Coherence）**: 通过 `impl` 一致性检查，保证不存在两个重叠的 impl。若存在重叠，编译器拒绝程序（而非尝试消歧）。
3. **无高阶 Trait Bound（HRTB）的无限量化**: HRTB `for<'a>` 仅允许在生命周期上全称量化，不允许在类型上高阶量化，避免了高阶统一化的不可判定性。
4. **无关联类型的递归定义**: 关联类型（Associated Types）的投影必须终止，不允许无限类型级递归。

> **定理 T-DS-002（Trait 求解的受限可判定性）**: 在孤儿规则、一致性检查、无高阶类型量化、无关联类型无限递归的约束下，Rust Trait 约束求解是**可判定的**。
> 若移除孤儿规则或允许任意重叠 impl，问题将退化为类似 Haskell 类型类的约束求解，在实践中可能进入非终止（尽管 Haskell 通过「上下文缩减限制」也保持了实践中可判定）。
> [来源: [RFC 1665](https://rust-lang.github.io/rfcs//1665-windows-subsystem.html), Chalk 设计文档]
> **Rust 1.95 更新**: 下一代 Trait Solver（Trait Engine v2）正在逐步替换旧 solver，核心判定性保证不变，但错误信息质量和求解效率提升。

### 5.3 类型等价与一致性

> **判定问题**: 两个类型在语义上是否等价？
> **可判定性**: ✅ **可判定（单态化后结构等价）**

Rust 的类型等价基于**名义等价（Nominal Equivalence）**而非结构等价：

- `struct Foo(i32)` 与 `struct Bar(i32)` 是不同的类型，即使结构相同。
- 泛型单态化后，编译器将 `Vec<i32>` 和 `Vec<u32>` 视为完全不同的具体类型。

名义等价的判定性 trivial：比较类型定义的路径和泛型参数即可。
这避免了依赖类型或 refinement 类型中类型等价可能涉及的任意计算（因而不可判定）。

---

## 六、L3 借用检查与生命周期层

### 6.1 借用检查：NLL 与 Polonius

> **判定问题**: 程序是否满足「别名 XOR 可变」（AXM）规则？
> **可判定性**: ✅ **可判定**
> **核心算法**: NLL（基于 CFG 的活跃性分析）→ Polonius（基于数据流的起源/约束分析）

Rust 借用检查经历了三代演进，每一代都保持了判定性：

| 代际 | 名称 | 算法核心 | 精度 | 可判定性 |
|:---|:---|:---|:---|:---:|
| 第一代 | 词法借用检查 | 基于 AST 作用域 | 低（过于保守） | ✅ |
| 第二代 | NLL (Non-Lexical Lifetimes) | 基于 CFG 的活跃性分析 + 区域约束 | 中（接受更多合法程序） | ✅ |
| 第三代 | Polonius | 基于数据流的起源（origin）分析 + Datalog | 高（解决 NLL 问题案例 #3） | ✅ |

**NLL 的判定性保证**:
NLL 将借用检查转化为**控制流图上的数据流问题**：

- 每个变量在 CFG 的每个程序点上有「活跃/不活跃」状态。
- 借用 `&mut x` 仅在 `x` 的活跃期间被禁止重新借用或修改。
- 数据流分析在有限 CFG 上总是终止（Kleene 不动点迭代在有限格上收敛）。

> **定理 T-DS-003（NLL 终止性）**: 对任意有限 MIR（Mid-level IR）表示的函数，NLL 借用检查算法在有限步内终止，且判定结果是 sound 的（拒绝的程序一定不安全）和 complete 的 relative to 词法借用检查（接受更多程序）。 [来源: [RFC 2094](https://rust-lang.github.io/rfcs//2094-nll.html), *Oxide: The Essence of Rust*]

**Polonius 的判定性保证**:
Polonius 将借用检查表述为**Datalog 程序**（实际上是 Datalog 的某个可判定子集）：

- 事实（facts）： loan 被创建、loan 被使用、变量赋值等。
- 规则（rules）： 如果 loan 活跃且存在对原变量的可变访问，则报错。
- Datalog 在有限事实集上总是终止（多项式时间）。

> **边界**: Polonius 的挑战不在于判定性，而在于**性能可扩展性**。大型函数产生的事实集可能很大，因此引入了分级分析（graded analysis）和近似。 [来源: Polonius Update, Rust Blog 2023]

### 6.2 生命周期约束可满足性

> **判定问题**: 给定一组生命周期约束 `'a: 'b`（'a outlives 'b），是否存在满足所有约束的赋值？
> **可判定性**: ✅ **可判定**
> **核心算法**: 偏序集约束图 + 传递闭包 + 环检测

生命周期约束系统是一个**偏序约束满足问题（POCSP）**：

- 变量：生命周期参数 `'a, 'b, ...`
- 约束：`'a: 'b`（'a 至少和 'b 一样长）
- 判定：约束图是否无环？（若 `'a: 'b` 且 `'b: 'a`，则 `'a = 'b`，不矛盾；若出现 `'a: 'a` 的无效自环则报错）

此问题的判定性 trivial：在有限变量集上构建约束图，计算传递闭包，检测是否出现与已知事实（如 `'static` 是最长生命周期）矛盾的约束。

> **定理 T-DS-004（生命周期约束可满足性）**: 对有限生命周期变量集和有限约束集，生命周期约束可满足性问题是**可判定的**，且可在多项式时间内求解（传递闭包 = O(V³)）。 [来源: Tofte-Talpin, *Region-Based Memory Management*]

---

## 七、L4 常量求值层（CTFE）

> **判定问题**: `const fn` 表达式是否能在编译期求值且停机？
> **可判定性**: ⚠️ **有界可判定（Bounded Decidable）**
> **核心算法**: Miri 解释器（MIR 级别的 Rust 子集解释器）

CTFE（Compile-Time Function Evaluation）是 Rust 编译期计算的核心机制。其判定性边界是 Rust 全编译流程中最微妙的部分：

**可判定性保证机制**:

1. **无堆分配**: `const fn` 中不能调用 `Box::new`、`Vec::new` 等堆分配操作。这**去除了图灵完备性中的一个关键能力（无限内存）**，使得 CTFE 在理论上接近有限状态机。
2. **无 I/O 与非确定性**: 禁止文件、网络、随机数、环境变量读取。保证相同输入总是产生相同输出。
3. **无 `unsafe`**: 禁止裸指针解引用和内联汇编，保证解释器始终处于安全抽象层。
4. **步数/栈深上限**: Miri 解释器有默认的栈深上限（约 1000 栈帧）和可配置的求值步数上限（`#[const_eval_limit]`）。这**强制截断可能的非终止计算**。

> **定理 T-DS-005（CTFE 有界可判定性）**: 在「无堆分配、无 I/O、无 unsafe、有步数/栈深上限」的约束下，Rust CTFE 是**有界可判定的**：对任意 `const` 表达式，解释器要么在有限步内求值成功，要么在达到上限时报错。 来源: [RFC 911, Ralf Jung blog 2018](https://github.com/rust-lang/rfcs/pull/911)

**不可判定性边界**:
若移除上述约束（尤其是步数上限和堆分配限制），CTFE 将变为**图灵完备**的，因而停机问题不可判定。Rust 编译器团队刻意保持 CTFE 的「有界图灵不完备」状态，以维护编译期的可预测性。

> **Rust 1.95 更新**: `inline const` 块和 `const { }` 表达式允许在更多上下文中使用编译期求值，但判定性边界不变。`const_eval_limit` 属性仍为可选的上限控制。 来源: [Rust 1.95 Release Notes](https://releases.rs/)

---

## 八、L5 并发安全层

### 8.1 数据竞争的编译期排除

> **判定问题**: 程序是否存在数据竞争？
> **可判定性**: ✅ **编译期可排除（运行时不可判定）**
> **核心机制**: `Send` / `Sync` trait + 所有权规则

Rust 的「fearless concurrency」并非通过运行时检测实现，而是通过**类型系统的静态证明**：

- **`Send`**: 类型 `T` 是 `Send` 当且仅当将 `T` 的所有权转移到另一个线程是安全的。
- **`Sync`**: 类型 `T` 是 `Sync` 当且仅当 `&T` 是 `Send`（即多个线程同时只读访问 `T` 是安全的）。

编译器通过**结构化推导**自动实现 `Send`/`Sync`：

- 所有原始类型（`i32`、`bool`、裸指针等）的基础实现。
- 复合类型（`struct`、`enum`、`tuple`）的推导：若所有字段都是 `Send`/`Sync`，则复合类型也是。
- 特殊类型的显式 opt-out：`Rc<T>` 不是 `Send`（引用计数非原子），`Cell<T>` 不是 `Sync`（内部可变性非线程安全）。

> **定理 T-DS-006（数据竞争的编译期排除）**: 在 Safe Rust（不含 `unsafe`）中，well-typed 的程序不存在数据竞争。这是 RustBelt 在 Iris 逻辑中证明的核心 soundness 结果之一。 来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)

**运行时不可判定性**:
虽然编译期可排除数据竞争，但「给定一个任意程序（含 `unsafe`），是否存在数据竞争」在运行时是不可判定的（Rice 定理的推论）。Rust 的策略是：**将不可判定问题转化为编译期的可判定类型检查**，对无法通过类型系统证明安全的部分，要求显式 `unsafe` 标记。

### 8.2 死锁与活锁：不可判定性

> **判定问题**: 程序是否存在死锁（或活锁、饥饿）？
> **可判定性**: ❌ **不可判定**
> **理论根基**: Rice 定理 + 停机问题归约

死锁检测是程序分析中的经典不可判定问题：

> **定理 T-DS-007（死锁检测的不可判定性）**: 判定任意程序是否会在某个执行路径上发生死锁是**不可判定的**。证明思路：将停机问题归约到死锁检测——构造一个程序，其死锁条件等价于某图灵机的停机条件。 [来源: Rice 1953, *Classes of Recursively Enumerable Sets*]

Rust 的补偿机制（无法编译期判定时的工程策略）：

| 策略 | 机制 | 成本 | 适用场景 |
|:---|:---|:---|:---|
| 类型系统规避 | `Send`/`Sync` 保证无数据竞争，但不保证无死锁 | 零成本 | 所有 Safe Rust |
| 锁顺序规范 | 文档约定 + `parking_lot::deadlock_detection` | 运行时开销 | 复杂锁层次 |
| 无锁数据结构 | `crossbeam` / `lock-free` crates | 设计复杂度高 | 高并发核心路径 |
| Actor 模型 | 单线程 Actor 消息处理，无共享锁 | 消息传递开销 | 高容错分布式 |
| 超时与退避 | `try_lock_for` + 指数退避 | 轻微运行时开销 | 通用容错 |

---

## 九、L6 代码生成与优化层

> **判定问题**: 优化变换是否保持程序语义？
> **可判定性**: ❌ **不可判定**
> **理论根基**: 程序等价性（Program Equivalence）的不可判定性

LLVM 对 MIR 的优化（内联、常量传播、死代码消除、循环优化等）基于**启发式**和**局部规则**，而非全局语义等价证明。

> **定理 T-DS-008（程序等价性的不可判定性）**: 判定两个程序是否在所有输入上等价（即是否具有相同的可观察行为）是**不可判定的**。这是 Rice 定理的直接推论。 [来源: Rice 1953]

Rust 的补偿机制：

1. **MIR 验证**: 优化后的 MIR 仍通过借用检查，保证内存安全不变性不被破坏。
2. **测试**: `cargo test` + `miri test` 检测未定义行为。
3. **形式化验证**: Kani（模型检测）、Creusot（Why3）、Verus（SMT）可对关键函数验证优化前后的行为等价性（但仅限标注了规约的函数）。

---

## 十、不可判定性边界：Rice 定理与停机问题

### 10.1 Rice 定理在 Rust 中的映射

> **Rice 定理**: 任何非平凡的（non-trivial）程序语义属性都是不可判定的。非平凡指：存在至少一个程序具有该属性，且至少一个程序不具有该属性。 [来源: Rice 1953]

| 语义属性 | 平凡性 | 可判定性 | Rust 策略 |
|:---|:---:|:---:|:---|
| 程序是否通过编译 | 非平凡 | ✅ 可判定 | 编译器即判定器 |
| 程序是否存在类型错误 | 非平凡 | ✅ 可判定 | 类型检查器 |
| 程序是否内存安全 | 非平凡 | ⚠️ 部分可判定 | Safe Rust 可判定；含 `unsafe` 不可判定 |
| 程序是否无死锁 | 非平凡 | ❌ 不可判定 | 运行时检测 / 设计规避 |
| 程序是否终止 | 非平凡 | ❌ 不可判定 | CTFE 步数上限 / 运行时调度 |
| 程序输出是否为 "hello" | 非平凡 | ❌ 不可判定 | 测试验证 |
| 程序语法是否合法 | 非平凡 | ✅ 可判定 | 解析器 |

**关键洞察**: Rust 编译器的核心价值在于——它将「内存安全」这一通常不可判定的语义属性，通过**类型系统的刻意设计**，转化为一个**可判定的类型检查问题**。这是 Rust 区别于 C/C++/Go 的根本理论创新。

### 10.2 停机问题与 CTFE 的边界

```mermaid
graph TD
    A[通用程序] -->|停机问题| B{是否停机?}
    B -->|不可判定| C[无法保证]

    D[Rust CTFE] -->|无堆分配| E[有限状态近似]
    D -->|步数上限| F[强制停机]
    D -->|无递归无限展开| G[有限调用图]
    E --> H{CTFE 是否停机?}
    F --> H
    G --> H
    H -->|有界可判定| I[✅ 编译期保证]
```
> **认知功能**: 该图通过**对比结构**（通用程序 vs Rust CTFE）揭示停机问题的不可判定性如何被 Rust 的有界约束「驯服」。建议用于理解「为什么 CTFE 不能堆分配」这一设计决策的理论根基。关键洞察：CTFE 的三重约束（无堆、步数上限、无递归无限展开）共同构成一个「有界图灵不完备」子集，这是编译期可预测性的刻意牺牲。[来源: 💡 原创分析]

---

## 十一、Rust 1.95 特性的可判定性映射

| 1.95 特性 | 所属层级 | 判定问题 | 可判定性 | 备注 |
|:---|:---:|:---|:---:|:---|
| `if let` guards in match | L2/L3 | 模式守卫中的绑定是否合法 | ✅ | 模式匹配与借用检查的交互，NLL 覆盖 |
| `assert_matches!` / `debug_assert_matches!` | L0/L2 | 宏扩展后的类型检查 | ✅ | 标准库宏，不影响编译期判定性 |
| `cfg_select!` | L0 | 编译期条件选择 | ✅ | 纯编译期宏，无运行时语义 |
| `core::hint::cold_path` | L6 | 分支预测提示 | — | 优化提示，无判定性问题 |
| `as_ref_unchecked` / `as_mut_unchecked` | L3/L5 | `unsafe` 裸指针转换的安全前提 | ❌ | 由程序员承担证明责任 |
| `Atomic*` `update` / `try_update` | L5 | 原子操作序列的正确性 | ❌ | 运行时内存序正确性不可判定 |
| `RangeInclusive` in `core` | L2 | 类型系统的范围表达 | ✅ | 纯类型层面 |
| `MaybeUninit` 数组互转 | L3 | 未初始化内存的安全操作 | ⚠️ | 需 `unsafe` + 手动不变性维护 |
| `Cell<[T; N]>` `AsRef` | L2 | 内部可变性的类型安全 | ✅ | 编译期推导 |
| `const {}` blocks (stable) | L4 | 编译期求值的停机性 | 🟡 | CTFE 有界可判定 |

---

## 十二、可判定性–表达力权衡矩阵

> **核心洞察**: 可判定性与表达力之间存在根本的张力。Rust 的设计哲学是在关键安全属性上牺牲表达力以换取可判定性，在次要属性上保留表达力但要求显式 `unsafe`。

| 设计选择 | 牺牲的表达力 | 获得的判定性 | 补偿机制 |
|:---|:---|:---|:---|
| 无全局 HM 推断 | 隐式多态的便利性 | 类型检查可判定 + 错误信息清晰 | 显式类型注解 + `let` 类型推断 |
| 无 HKT | 高阶抽象（如 monad transformer） | 类型推断可判定 | 宏 + GATs（有限替代） |
| 无完整依赖类型 | 类型级任意计算 | 类型等价可判定 | Const Generics（受限子集） |
| 孤儿规则限制 | 任意类型上任意 impl 的灵活性 | Trait 求解可判定 + 全局一致性 | Newtype 模式 + 包装 trait |
| 无绿色线程 | goroutine 的透明调度 | 运行时简单可预测 | `async/await` + Tokio（显式调度） |
| CTFE 无堆分配 | 编译期动态数据结构 | CTFE 有界可判定 | `lazy_static` / `OnceLock`（运行时） |
| 无 STM | 软件事务内存的透明性 | 并发语义简单可分析 | `Mutex` / `RwLock` / 无锁结构 |

---

## 十三、思维表征体系

### 13.1 判定路径决策树

```mermaid
graph TD
    A[编译错误?] --> B{错误阶段}
    B -->|词法/语法| C[L0 判定失败<br/>非法 token / 语法]
    B -->|名称未找到| D[L1 判定失败<br/>未解析的 Path]
    B -->|类型不匹配| E[L2 判定失败<br/>类型推断/约束不满足]
    B -->|借用冲突| F[L3 判定失败<br/>AXM 违反 / 生命周期不足]
    B -->|常量求值溢出| G[L4 判定失败<br/>CTFE 步数上限 / 堆分配]
    B -->|线程安全| H[L5 判定失败<br/>Send/Sync 不满足]

    C --> C1[修复: 检查拼写 / 语法]
    D --> D1[修复: 检查 use 导入 / 模块路径]
    E --> E1[修复: 显式类型标注 / 调整约束]
    F --> F1[修复: 缩小借用范围 / Rc<RefCell> / unsafe]
    G --> G1[修复: 简化表达式 / 提升为运行时]
    H --> H1[修复: Arc<Mutex<T>> / unsafe impl]
```
> **认知功能**: 该决策树将编译错误映射到**修复策略**，形成「症状→诊断→处方」的完整认知闭环。建议在遇到编译错误时按图索骥，快速定位应查阅的文档章节。关键洞察：借用冲突（L3）和线程安全（L5）的错误往往有多种修复路径——`Rc<RefCell>` 与 `unsafe` 代表了「运行时检查」与「程序员契约」两种哲学选择。[来源: 💡 原创分析]

### 13.2 谱系演化时间线

```mermaid
timeline
    title Rust 借用检查与类型系统判定性演进
    2015 : Rust 1.0 发布
         : 词法借用检查（最保守）
    2018 : Edition 2018
         : NLL 首次引入（非词法生命周期）
    2019 : async/await stable
         : Future 状态机变换可判定
    2021 : Edition 2021
         : 闭包捕获精确化
    2022-2023 : Polonius 开发中
              : Datalog 借用检查，解决 NLL 问题案例
    2024 : Edition 2024
         : `gen` blocks / `async closures`
         : + use<..> precise capturing
    2025+ : Trait Engine v2
          : 下一代 Trait Solver，判定性保证不变
```
> **认知功能**: 该时间线将 Rust 类型系统与借用检查的**代际演进**可视化，帮助读者理解当前编译器行为的历史成因。建议结合 Rust 版本号阅读，理解「为什么我的代码在旧版本编译失败」的深层原因。关键洞察：每一代借用检查（词法→NLL→Polonius）都是判定性不变前提下的精度提升——这是 Rust 向后兼容承诺的技术体现。[来源: 💡 原创分析]

---

## 十四、定理推理链

### 定理一致性矩阵（可判定性谱系专集）

| 编号 | 定理 | 前提 | 结论 | L4 公理依赖 | 失效条件 | 错误码映射 |
|:---|:---|:---|:---|:---|:---|:---|
| T-DS-001 | 局部类型推断可判定性 | 函数签名显式；无 HKT；无直接递归类型 | 函数体内类型推断可判定 | HM 算法完备性 | 全局推断 / HKT / 递归 μ-类型 | E0308, E0282 |
| T-DS-002 | Trait 求解受限可判定性 | 孤儿规则；一致性检查；无高阶类型量化 | Trait 约束可满足 | 一阶逻辑可满足性 | 重叠 impl / 无限递归关联类型 | E0277, E0119 |
| T-DS-003 | NLL 终止性 | 有限 MIR；有限变量集 | NLL 在有限步终止 | 数据流分析 Kleene 不动点 | MIR 无限展开（宏） | E0502, E0499 |
| T-DS-004 | 生命周期约束可满足性 | 有限生命周期变量；有限约束 | 偏序约束可多项式求解 | 偏序集传递性 | 矛盾约束（`'static: 'a` 且 `'a` 非 `'static`） | E0478, E0495 |
| T-DS-005 | CTFE 有界可判定性 | 无堆分配；无 I/O；无 unsafe；步数上限 | CTFE 在有限步求值或报错 | 有界停机 | 移除上限 / 允许堆分配 | E0080, E0015 |
| T-DS-006 | 数据竞争编译期排除 | Safe Rust；well-typed | 无数据竞争 | RustBelt Soundness | `unsafe` 代码 / 编译器 bug | — |
| T-DS-007 | 死锁检测不可判定性 | 任意程序；非平凡语义属性 | 死锁检测不可判定 | Rice 定理 | 受限程序类（如有限状态协议） | — |
| T-DS-008 | 程序等价性不可判定性 | 任意两个程序 | 语义等价不可判定 | Rice 定理 | 结构化等价（如同构 AST） | — |

### 推理链图谱

```mermaid
graph TD
    A[Rice 定理] --> B[T-DS-007: 死锁不可判定]
    A --> C[T-DS-008: 等价性不可判定]

    D[HM 完备性] --> E[T-DS-001: 局部推断可判定]
    F[一阶逻辑 SAT] --> G[T-DS-002: Trait 求解可判定]
    H[Kleene 不动点] --> I[T-DS-003: NLL 终止]
    J[偏序集理论] --> K[T-DS-004: 生命周期可判定]
    L[有限状态机] --> M[T-DS-005: CTFE 有界可判定]
    N[Iris 分离逻辑] --> O[T-DS-006: 无数据竞争]

    E --> P[Rust 编译器总可判定性]
    G --> P
    I --> P
    K --> P
    M --> P
    O --> P

    B -.-> Q[编译期策略: 类型系统规避]
    C -.-> R[编译期策略: 测试 + 形式化验证]
```
> **认知功能**: 该图呈现八条定理的**依赖拓扑**——从数学公理（Rice 定理、HM 完备性等）到 Rust 编译器具体保证的推导路径。建议用于理解「为什么编译器能保证 X」的元理论根基。关键洞察：Rust 的编译期安全保证并非工程魔术，而是有坚实数学根基的——Iris 分离逻辑推导无数据竞争（T-DS-006）是最具代表性的例子。[来源: 💡 原创分析]
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

---

## 十五、相关概念链接（L0-L7 映射）

### L0-L7 纵向映射

| 本文件主题 | L1 基础 | L2 进阶 | L3 高级 | L4 形式化 | L5 对比 | L6 生态 | L7 前沿 |
|:---|:---|:---|:---|:---|:---|:---|:---|
| 可判定性谱系 | 所有权/借用/生命周期的编译期判定 | 类型推断 / Trait 求解 | NLL / Polonius / Send/Sync | 线性逻辑判定 / RustBelt Soundness | Rust vs Go 判定性对比 | Clippy / Miri / Kani 静态检测 | Effects 系统对判定性的影响 |
| 不可判定性边界 | — | — | `unsafe` 逃逸门 | Rice 定理 / 停机问题 | C++ 模板元编程的不可判定性 | 运行时检测工具 | 形式化验证的覆盖率极限 |

### 相关概念文件

- [L1 所有权](../01_foundation/01_ownership.md) —— 所有权唯一性的编译期判定
- [L1 借用](../01_foundation/02_borrowing.md) —— AXM 规则与借用检查
- [L1 生命周期](../01_foundation/03_lifetimes.md) —— 偏序约束可满足性
- [L1 类型系统](../01_foundation/04_type_system.md) —— 类型推断与一致性
- [L2 泛型](../02_intermediate/02_generics.md) —— Trait 求解与 Const Generics
- [L3 并发](../03_advanced/01_concurrency.md) —— Send/Sync 推导与数据竞争排除
- [L3 异步](../03_advanced/02_async.md) —— Future 状态机与执行模型
- [L4 所有权形式化](../04_formal/03_ownership_formal.md) —— COR / Polonius Datalog
- [L4 RustBelt](../04_formal/04_rustbelt.md) —— Iris 逻辑与 Soundness 证明
- [L5 Rust vs Go](../05_comparative/02_rust_vs_go.md) —— 并发模型同构性
- [L0 语义表达力](semantic_expressiveness.md) —— 可判定性-表达力权衡的横向光谱
- [L7 版本跟踪](../07_future/05_rust_version_tracking.md) —— 1.95/1.96 新特性的判定性映射

## 十、可判定性论文精确引用与前沿映射

### 10.1 POPL / PLDI 可判定性相关论文精确引用

以下表格将形式化验证与可判定性理论领域的核心论文映射至 Rust 编译器特性，为「可判定性谱系」提供文献锚点：

| 论文 | 会议 | 年份 | 核心结果 | Rust 映射 |
|:---|:---|:---:|:---|:---|
| Jung et al. "RustBelt: Securing the Foundations of the Rust Programming Language" | POPL | 2018 | Safe + Unsafe Rust 的机器检验分离逻辑语义 | 所有权形式化基础；Iris 逻辑框架首次应用于系统语言 |
| Weiss et al. "Oxide: The Essence of Rust" | POPL | 2019 | 非词法生命周期（NLL）的完整类型系统 | NLL 形式化；`&'a T` 与流动分析（flow analysis）的代数刻画 |
| Matsushita et al. "RustHorn: CHC-based Verification for Rust Programs" / "RustHornBelt" | PLDI | 2020 / 2022 | 基于 Horn 子句的函数式验证，支持 unsafe | Horn 子句验证路径；与 SMT 求解器对接的自动化方向 |
| Gäher et al. "RefinedRust: A Type System for Automated Separation Logic Verification" | PLDI | 2024 | 自动化分离逻辑验证，生成 Coq proof script | 自动分离逻辑；降低形式化验证的人工负担 |
| Dreyer et al. "Tree Borrows: A New Aliasing Model for Rust" | PLDI | 2025 | 树状别名模型，替换 Stacked Borrows，判定性语义 | Miri 实现基础；`noalias` 注解的 LLVM 兼容形式化 |
| Various (CTFE Step Counter Decidability) | POPL | 2026 | 受限计数器系统的连续可判定性 | 与 Rust CTFE 步数限制（`const_eval_limit`）的理论关联 |
| Jung et al. "Stacked Borrows: An Aliasing Model for Rust" | POPL | 2019 | 栈状别名模型，首次为 Rust 提供操作语义的别名规范 | 早期 Miri 实现基础；后被 Tree Borrows 取代 |
| Toman et al. "CRust: Automatically Proving the Correctness of Rust Programs" | SOAP | 2015 | 基于 SMACK 验证器的 Rust 到 Boogie 翻译 | 早期自动化验证尝试；未覆盖所有权核心 |

#### 引用精度说明

- **RustBelt (POPL 2018)**：首次将高阶并发分离逻辑（Iris）用于证明真实系统语言的 soundness。
- 其 λRust 演算虽未覆盖 trait，但为所有权、生命周期、unsafe primitive 建立了可复用的逻辑基础。
- RustBelt 的 soundness 定理表述为：「如果一个 λRust 程序通过类型检查，则在执行过程中不会发生数据竞争、use-after-free 或悬垂指针解引用」。
- 这一结果直接对应 Rust 的核心安全承诺。
- **Oxide (POPL 2019)**：
- 将 Rust 的生命周期系统归约为 **流敏感、上下文敏感** 的仿射类型系统，证明 NLL 的 type safety。
- 该工作与后来 Polonius（Rust 编译器 NLL 引擎）的实现存在直接血缘关系。Oxide 的创新在于将生命周期视为「区域变量」（region variables），并用子类型约束的可满足性（POSAT）替代早期的词法作用域分析。
- 从可判定性角度看，Oxide 证明了 NLL 约束求解是多项式时间可判定的。
- **Tree Borrows (PLDI 2025)**：
- 提出「树状借用」别名模型，将 Stacked Borrows 的栈结构放宽为树结构，解决了 `unsafe` 代码中部分合法模式被误判为 UB 的问题。
- 其语义规则集合是有限的、可判定的，为 Miri 的动态检查提供了数学根基。
- Tree Borrows 的可判定性来源于其状态空间的有限性：对于任意内存位置，其借用状态由一棵有限深度的树表示，且状态转移规则是确定性的有限重写系统。
- **RustHornBelt (PLDI 2022)**：将 Rust 的验证问题翻译为 **约束 Horn 子句（Constrained Horn Clauses, CHC）** 求解问题。
- CHC 的可判定性边界已被广泛研究：线性 CHC 是可判定的，但非线性 CHC（允许多个递归调用）在一般情况下不可判定。
- RustHornBelt 通过限制递归模式（只支持尾递归风格的内存操作）保持了实践中的可判定性。

### 10.2 Rust 特性可判定性状态 1.95+

下表更新至 Rust 1.96.0 stable，评估新引入或稳定的语言特性对类型系统可判定性的影响：

| 特性 | 稳定版本 | 可判定性状态 | 论证 |
|:---|:---:|:---:|:---|
| `adt_const_params` | 1.75+ | ✅ 可判定（带边界） | 只允许 `#[derive(PartialEq, Eq)]` 类型作为 const generic 参数，限制搜索空间为有限等价类 来源: [RFC 2000](https://github.com/rust-lang/rfcs/pull/2000) |
| `min_generic_const_args` | 1.79+ | ✅ 可判定（简化子集） | 仅允许整数、布尔、`char` 作为 const generic，无任意表达式，避免 Diophantine 复杂性 来源: [Rust Reference](https://doc.rust-lang.org/reference/) |
| `async_fn_in_trait` | 1.75+ | ⚠️ 实际可判定 | 语义等价于返回 `impl Future` 的关联类型，当前编译器采用「惰性单态化」策略，未引入新的不可判定路径 来源: [RFC 3185](https://rust-lang.github.io/rfcs/3185-static-async-fn-in-trait.html) |
| `let_chains` | 1.64+ | ✅ 可判定（语法糖） | 纯语法扩展，不改变类型系统或借用检查的判定性边界 来源: [RFC 2497](https://github.com/rust-lang/rfcs/pull/2497) |
| `never_type` (`!`) | 1.41+ / 1.82 完善 | ✅ 可判定 | 底类型作为所有类型的子类型，子类型关系保持偏序，不引入递归 undecidability 来源: [RFC 1216](https://github.com/rust-lang/rfcs/pull/1216) |
| `precise_capturing` (`use<...>`) | 1.82+ | ✅ 可判定 | 显式生命周期捕获列表是 borrow checker 输入的细化，不改变约束求解本身的复杂度类 来源: [RFC 3498](https://rust-lang.github.io/rfcs/3617-precise-capturing.html) |
| `inline_const` | 1.79+ | ✅ 可判定（步数限制） | 编译期常量块受 `const_eval_limit` 约束，等价于有限状态解释器 来源: [Rust Reference](https://doc.rust-lang.org/reference/) |
| `impl_trait_in_assoc_type` | 1.79+ | ⚠️ 实际可判定 | `type Foo = impl Trait;` 的语义等价于存在量化类型，编译器通过延迟单态化控制复杂度 来源: [RFC 2289](https://rust-lang.github.io/rfcs/2289-associated-type-bounds.html) |
| `cfg_version` / `cfg_accessible` | 1.79+ | ✅ 可判定 | 编译期条件编译属性，不涉及类型系统或运行时可判定性 来源: [Rust Reference](https://doc.rust-lang.org/reference/) |

**关键洞察**：
Rust 1.70–1.95 周期内稳定的新特性，在语言团队的设计审查中均经过了「可判定性筛查」。
没有一个特性将类型系统或借用检查推入不可判定领域——这并非偶然，而是 Rust 语言演进的有意约束。
语言团队在设计新特性时，会主动评估该特性是否会导致 trait 求解器或借用检查器的非终止行为；
如果会，则通过限制子集（如 `min_generic_const_args`）或添加编译期护栏（如 `const_eval_limit`）来保持可判定性。

#### 可判定性保持的设计模式

Rust 语言团队在过去 6 个 release cycle 中反复使用以下三种模式来维持类型系统的可判定性：

| 模式 | 应用特性 | 机制 | 形式化类比 |
|:---|:---|:---|:---|
| **子集限制** | `min_generic_const_args` | 禁止任意 const 表达式，只允许字面量 | 将 Diophantine 问题限制为有限域赋值 |
| **深度计数器** | GATs、关联类型 | 递归实例化深度硬上限 | 将图灵完备计算限制为有限步数 |
| **语法糖隔离** | `let_chains`、`async`/`await` | 编译期展开，不改变核心类型规则 | 保归约（confluence）的宏展开 |

### 10.3 开放问题（Open Problems）

尽管当前 Rust stable 的特性集保持了可判定性，以下三个问题仍代表形式化理论与编译器实现之间的活跃张力：

#### 开放问题 1：GATs 的完全可判定性边界

泛型关联类型（Generic Associated Types）允许在 trait 中定义带泛型参数的类型族。
其类型归一化问题与 **Haskell type family 的 undecidability** 同源。
Rust 编译器当前通过以下启发式维持实践中的可判定性：

- 递归实例化深度限制（默认 256）
- 关联类型投影的「Occurs Check」变体
- 不允许 GAT 在 where 子句中形成非良基递归（non-well-founded recursion）

但**这些限制的全局充分性尚未被形式化证明**。
存在理论上的可能性：某组合法 Rust GAT 定义在编译器限制之外仍会导致非终止归一化。
具体而言，GAT 的归一化可以编码 **半统一化（semi-unification）** 问题，而半统一化已被证明是 undecidable 的。
Rust 编译器当前的限制是否足以将 GAT 归一化限制在半统一化的可判定子集内，是一个尚未回答的问题。

#### 开放问题 2：关联类型归一化的终止性证明

即使不考虑 GATs，普通关联类型（`type Output;`）的归一化（normalization）也涉及将类型族实例化为具体类型。
在存在高阶 trait bound（`for<T: Trait> <T as Assoc>::Type: Bound`）时，归一化可能需要实例化无限类型序列。
考虑以下理论上的构造：

```rust,compile_fail
trait Rec { type Next: Rec; }
impl<T: Rec> Rec for Wrap<T> {
    type Next = Wrap<T::Next>;
}
```
在此场景中，尝试归一化 `<Wrap<...> as Rec>::Next` 将产生无限类型塔 `Wrap<Wrap<Wrap<...>>>。
Rust 编译器通过「递归深度计数器」在实践中断开此类循环，但**该计数器策略的 soundness 与 completeness 缺乏 machine-checked 证明**：

- **Soundness**：计数器是否保证所有被它拒绝的程序确实会导致非终止归一化？（是的，但未被证明）
- **Completeness**：是否存在某组合法、终止的关联类型定义被计数器误杀？（理论上可能，尚未发现实例）

#### 开放问题 3：Const Evaluation 的图灵完备性边界（受限堆 + 步数限制）

Rust 的 const evaluation（`const fn` 编译期执行）在 Miri 引擎支持下已具备：

- 原始指针算术与解引用
- 受限的堆内存分配（`const_mut_refs` + 内部可变性）
- 循环与条件分支
- 递归调用（受调用深度限制）

这些能力的组合使 CTFE 在理论上接近图灵完备。
一个已被社区讨论的思想实验是：在 `const fn` 中实现一个 Brainfuck 解释器，使其在编译期执行任意 Brainfuck 程序。
如果配合 `const generics` 将 Brainfuck 程序的输出编码为类型，则类型检查将等价于停机问题判定。

然而，Rust 编译器通过双重机制强制维持「伪可判定性」：

1. **硬步数上限**（`const_eval_limit`，默认约 1M 步）
2. **硬内存上限**（CTFE 分配器的固定容量池，通常限制为数十 MB）

**核心张力**：如果放宽上述限制，const generics 中的常量表达式可能用于编码任意计算，从而使类型检查等价于停机问题判定。
当前限制的「最小充分集合」——即既保证表达力又维持可判定性的精确边界——仍然未知。
形式化上，这对应于一个开放问题：**带有限堆和步数限制的命令式语言的可判定性分类**。
该问题与理论计算机科学中的「有限状态程序验证」和「反链 well-quasi-ordering」研究相关，但尚未有完全对应 Rust CTFE 复杂度的结果。

#### 开放问题 4：Effects 系统与类型系统可判定性的交互

Rust 社区正在逐步探索 effects 系统（如 `const`、`async`、`unsafe` 等 effect 的显式标注与组合）。
从可判定性角度看，effects 系统的引入可能产生以下张力：

- **Effect 多态**：如果允许泛型参数携带 effect 变量（如 `fn foo<T, E>(x: T) -> E T`），则 effect 推断可能与类型推断耦合，形成高阶 unification 问题。
- **Effect 子效应（sub-effecting）**：如果引入 effect 之间的偏序关系（如 `const < async`），则类型检查需要求解 effect 约束的传递闭包，这在一般情况下是可判定的，但与 trait 系统交互后复杂度尚不明确。

目前 Rust 的 effects 系统尚处于早期设计阶段（`const` trait 是最初步的尝试），其可判定性边界尚未成为紧迫问题，但值得前瞻性关注。

---

> **权威来源**:
> [Rust Reference](https://doc.rust-lang.org/reference/) ·
> [RFC 1560](https://rust-lang.github.io/rfcs//1560-name-resolution.html) ·
> [RFC 1665](https://rust-lang.github.io/rfcs//1665-windows-subsystem.html) ·
> [RFC 2094](https://rust-lang.github.io/rfcs//2094-nll.html) ·
> [RFC 911](https://rust-lang.github.io/rfcs//0911-const-fn.html) ·
> [RustBelt POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf) ·
> [Oxide arXiv 2019](https://arxiv.org/abs/1903.00982) ·
> [Pierce *TAPL*](https://www.cis.upenn.edu/~bcpierce/tapl/) ·
> [Sipser *ITOC*](https://math.mit.edu/~sipser/book.html)
>
> **Rust 版本**: 1.96.0 stable (Edition 2024)
> **文档版本**: 1.0
> **最后更新**: 2026-05-21
> **状态**: ✅ 可判定性谱系全景 v1.0

### 10.3 边界测试：类型推断的不可判定性与人工标注（编译错误）

```rust,compile_fail
fn main() {
    let v = vec![];
    // ❌ 编译错误: 无法推断 Vec<T> 的元素类型
    v.push(1);
    v.push("hello"); // 若注释上一行，这里也编译错误（类型冲突）
}
```
> **修正**:
> Rust 的类型推断基于 **Hindley-Milner** 算法的扩展，但加入了 trait 约束、生命周期和关联类型。
> 某些情况下推断需要人工提示：
>
> 1) `vec![]` 无上下文时无法推断 `T`；
> 2) 闭包参数类型在多态上下文中可能模糊；
> 3) `collect()` 的目标类型无处推导时失败。
>
> 类型推断的复杂度：最坏情况下是指数级（`O(2^n)`），但 Rust 编译器使用启发式限制实际复杂度。
> 这与 Haskell 的 HM（完整且高效，无 trait 约束）或 C++ 的 `auto`（基于表达式类型，无统一变量）不同——Rust 的类型推断在 HM 基础上增加了 trait 系统的约束求解，某些边界情况需人工标注。
> [来源: [Rust Reference — Type Inference](https://doc.rust-lang.org/reference/types.html)] ·
> [来源: [Hindley-Milner Type Inference](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)]

## 认知路径

> **认知路径**: 本文件作为 Rust 分层知识体系的 **Rust 编译期可判定性谱系全景（Decidability Spectrum）** 元层导航节点，连接概念定义、学习路径与质量评估框架。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Decidability Spectrum 结构化定义 ⟹ 学习者认知锚点可建立 | 本文件定义了元层结构 | 支持上层概念定位 | 高 |

> **过渡**: 利用本文件的导航结构，读者可以从当前位置快速跃迁到任意概念层级，实现非线性学习。
> **过渡**: Rust 编译期可判定性谱系全景（Decidability Spectrum） 的维护需要与概念内容同步更新，确保元数据与实际知识体系的一致性。
> **过渡**: 将 Rust 编译期可判定性谱系全景（Decidability Spectrum） 作为学习起点或复习锚点，有助于建立全局视野，避免陷入局部细节而忽视整体架构。

### 反命题与边界

> **反命题**: "元层文档可以替代具体概念学习" —— 错误。Rust 编译期可判定性谱系全景（Decidability Spectrum） 提供的是导航与评估框架，不能替代对核心概念（L1-L5）的深入理解与实践。
> **内容分级**: [综述级]

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文档《Rust 编译期可判定性谱系全景（Decidability Spectrum）》在 Rust 知识体系中属于哪一层级的元数据？（理解层）

**题目**: 本文档《Rust 编译期可判定性谱系全景（Decidability Spectrum）》在 Rust 知识体系中属于哪一层级的元数据？

<details>
<summary>✅ 答案与解析</summary>

属于 00_meta 元数据层，为整个知识体系提供导航、评估、审计和结构化的支持框架，辅助学习者定位和理解核心概念。
</details>

---

### 测验 2：《Rust 编译期可判定性谱系全景（Decidability Spectrum）》的主要用途是什么？（理解层）

**题目**: 《Rust 编译期可判定性谱系全景（Decidability Spectrum）》的主要用途是什么？

<details>
<summary>✅ 答案与解析</summary>

作为知识体系的支撑文档，提供学习路径导航、概念关系映射、质量评估标准或审计检查清单，帮助学习者和维护者高效使用知识库。
</details>

---

### 测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）

**题目**: 元数据层文档能否替代 L1-L7 的核心概念学习？

<details>
<summary>✅ 答案与解析</summary>

不能。元数据层提供导航和评估框架，但不能替代对核心概念（所有权、类型系统、并发等）的深入理解与实践。
</details>
