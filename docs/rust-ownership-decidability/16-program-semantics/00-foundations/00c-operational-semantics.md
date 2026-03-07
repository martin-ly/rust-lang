# 操作语义 (Operational Semantics)

## 目录

- [操作语义 (Operational Semantics)](#操作语义-operational-semantics)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 操作语义分类](#2-操作语义分类)
    - [2.1 两大类操作语义](#21-两大类操作语义)
    - [2.2 对比示例](#22-对比示例)
  - [3. 大步语义 (Big-Step Semantics)](#3-大步语义-big-step-semantics)
    - [3.1 基本形式](#31-基本形式)
    - [3.2 算术表达式语义](#32-算术表达式语义)
    - [3.3 变量与赋值](#33-变量与赋值)
    - [3.4 条件表达式](#34-条件表达式)
    - [3.5 循环 (While)](#35-循环-while)
  - [4. 小步语义 (Small-Step Semantics)](#4-小步语义-small-step-semantics)
    - [4.1 基本形式](#41-基本形式)
    - [4.2 求值上下文 (Evaluation Contexts)](#42-求值上下文-evaluation-contexts)
    - [4.3 算术表达式的小步语义](#43-算术表达式的小步语义)
    - [4.4 小步语义的完整求值](#44-小步语义的完整求值)
    - [4.5 小步 vs 大步的等价性](#45-小步-vs-大步的等价性)
  - [5. λ演算的操作语义](#5-λ演算的操作语义)
    - [5.1 调用按值 (Call-by-Value, CBV)](#51-调用按值-call-by-value-cbv)
    - [5.2 调用按名 (Call-by-Name, CBN)](#52-调用按名-call-by-name-cbn)
    - [5.3 调用按需 (Call-by-Need)](#53-调用按需-call-by-need)
  - [6. 状态与命令式语言](#6-状态与命令式语言)
    - [6.1 存储模型](#61-存储模型)
    - [6.2 引用操作](#62-引用操作)
  - [7. 并发操作语义](#7-并发操作语义)
    - [7.1 并行组合](#71-并行组合)
    - [7.2 原子操作](#72-原子操作)
    - [7.3 Happens-Before 关系](#73-happens-before-关系)
  - [8. 结构化操作语义 (SOS)](#8-结构化操作语义-sos)
    - [8.1 Plotkin 的 SOS](#81-plotkin-的-sos)
    - [8.2 规则分类](#82-规则分类)
    - [8.3 类型指导的语义](#83-类型指导的语义)
  - [9. 抽象机](#9-抽象机)
    - [9.1 CEK 机器](#91-cek-机器)
    - [9.2 Krivine 机器](#92-krivine-机器)
    - [9.3 抽象机与编译](#93-抽象机与编译)
  - [10. 在 Rust 中的应用](#10-在-rust-中的应用)
    - [10.1 MIR (Mid-level IR) 语义](#101-mir-mid-level-ir-语义)
    - [10.2 所有权转移的小步语义](#102-所有权转移的小步语义)
    - [10.3 借用检查的小步语义](#103-借用检查的小步语义)
  - [11. 操作语义的性质](#11-操作语义的性质)
    - [11.1 确定性](#111-确定性)
    - [11.2 合流性 (Confluence)](#112-合流性-confluence)
    - [11.3 标准化 (Standardization)](#113-标准化-standardization)
  - [12. 总结](#12-总结)
  - [参考文献](#参考文献)

## 1. 引言

操作语义通过定义程序执行时的逐步行为来描述编程语言的含义。
它回答了"程序如何运行"的问题，是最贴近实现的语义描述方式。

> **核心思想**: 操作语义将程序执行建模为状态转换系统，明确定义每一步计算的规则。

---

## 2. 操作语义分类

### 2.1 两大类操作语义

```
操作语义分类:

┌─────────────────────────────────────────────────────────────┐
│                    操作语义                                  │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  ┌──────────────────┐        ┌──────────────────┐          │
│  │  大步语义         │        │  小步语义         │          │
│  │  (Big-Step)      │        │  (Small-Step)    │          │
│  │                  │        │                  │          │
│  │  自然语义         │        │  结构化操作语义   │          │
│  │  Natural Sem.    │        │  SOS             │          │
│  │                  │        │                  │          │
│  │  e ⇓ v          │        │  e → e'         │          │
│  │  (直接到结果)     │        │  (单步转换)       │          │
│  │                  │        │                  │          │
│  │  优点:          │        │  优点:           │          │
│  │  • 简洁          │        │  • 展示中间状态   │          │
│  │  • 易读          │        │  • 适合并发       │          │
│  │                  │        │  • 分析非终止     │          │
│  └──────────────────┘        └──────────────────┘          │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 2.2 对比示例

**表达式**: `(3 + 4) * 5`

**大步语义**:

$$
\frac{3 \Downarrow 3 \quad 4 \Downarrow 4 \quad 3 + 4 = 7}{(3 + 4) \Downarrow 7} \quad
\frac{(3 + 4) \Downarrow 7 \quad 5 \Downarrow 5 \quad 7 \times 5 = 35}{(3 + 4) \times 5 \Downarrow 35}
$$

**小步语义**:

$$
(3 + 4) \times 5 \rightarrow 7 \times 5 \rightarrow 35
$$

---

## 3. 大步语义 (Big-Step Semantics)

### 3.1 基本形式

**判断形式**: $\langle e, \sigma \rangle \Downarrow \langle v, \sigma' \rangle$

含义: 在存储 $\sigma$ 下，表达式 $e$ 求值为值 $v$，产生新存储 $\sigma'$。

### 3.2 算术表达式语义

**语法**:

$$
e ::= n \mid e_1 + e_2 \mid e_1 - e_2 \mid e_1 \times e_2
$$

**语义规则**:

$$
\frac{}{ val{n} \Downarrow n} \quad (B ext{-}Num)
$$

$$
\frac{e_1 \Downarrow n_1 \quad e_2 \Downarrow n_2 \quad n = n_1 + n_2}{e_1 + e_2 \Downarrow n} \quad (B ext{-}Add)
$$

$$
\frac{e_1 \Downarrow n_1 \quad e_2 \Downarrow n_2 \quad n = n_1 - n_2}{e_1 - e_2 \Downarrow n} \quad (B ext{-}Sub)
$$

$$
\frac{e_1 \Downarrow n_1 \quad e_2 \Downarrow n_2 \quad n = n_1 \times n_2}{e_1 \times e_2 \Downarrow n} \quad (B ext{-}Mul)
$$

### 3.3 变量与赋值

**语法扩展**:

$$
e ::= ... \mid x \mid x := e \mid e_1; e_2
$$

**存储** $\sigma$: 变量名到值的映射。

**语义规则**:

$$
\frac{}{ val{x}, \sigma \Downarrow \sigma(x), \sigma} \quad (B ext{-}Var)
$$

$$
\frac{e \Downarrow v, \sigma'}{x := e, \sigma \Downarrow v, \sigma'[x \mapsto v]} \quad (B ext{-}Assign)
$$

$$
\frac{e_1 \Downarrow v_1, \sigma_1 \quad e_2 \Downarrow v_2, \sigma_2}{e_1; e_2, \sigma \Downarrow v_2, \sigma_2} \quad (B ext{-}Seq)
$$

### 3.4 条件表达式

**语法**:

$$
e ::= ... \mid \text{if } e_1 \text{ then } e_2 \text{ else } e_3
$$

**语义规则**:

$$
\frac{e_1 \Downarrow \text{true} \quad e_2 \Downarrow v}{\text{if } e_1 \text{ then } e_2 \text{ else } e_3 \Downarrow v} \quad (B ext{-}IfTrue)
$$

$$
\frac{e_1 \Downarrow \text{false} \quad e_3 \Downarrow v}{\text{if } e_1 \text{ then } e_2 \text{ else } e_3 \Downarrow v} \quad (B ext{-}IfFalse)
$$

### 3.5 循环 (While)

**语法**:

$$
e ::= ... \mid \text{while } e_1 \text{ do } e_2
$$

**语义规则**:

$$
\frac{e_1 \Downarrow \text{false}}{\text{while } e_1 \text{ do } e_2 \Downarrow \text{skip}} \quad (B ext{-}WhileFalse)
$$

$$
\frac{e_1 \Downarrow \text{true} \quad e_2 \Downarrow v_2 \quad (\text{while } e_1 \text{ do } e_2) \Downarrow v}{\text{while } e_1 \text{ do } e_2 \Downarrow v} \quad (B ext{-}WhileTrue)
$$

---

## 4. 小步语义 (Small-Step Semantics)

### 4.1 基本形式

**判断形式**: $\langle e, \sigma \rangle \rightarrow \langle e', \sigma' \rangle$

含义: 在存储 $\sigma$ 下，表达式 $e$ 单步归约为 $e'$，存储变为 $\sigma'$。

### 4.2 求值上下文 (Evaluation Contexts)

**核心思想**: 将表达式分为"上下文"和"焦点"（可归约表达式）。

**上下文定义**:

$$
E ::= [] \mid E + e \mid v + E \mid E - e \mid v - E \mid E \times e \mid v \times E \mid ...
$$

其中 $[]$ 是"洞"，表示可归约子表达式的位置。

**上下文规则**:

$$
\frac{e \rightarrow e'}{E[e] \rightarrow E[e']} \quad (Ctx)
$$

### 4.3 算术表达式的小步语义

**归约规则**:

$$
\frac{n = n_1 + n_2}{n_1 + n_2 \rightarrow n} \quad (S ext{-}Add)
$$

$$
\frac{n = n_1 - n_2}{n_1 - n_2 \rightarrow n} \quad (S ext{-}Sub)
$$

$$
\frac{n = n_1 \times n_2}{n_1 \times n_2 \rightarrow n} \quad (S ext{-}Mul)
$$

**上下文规则**:

$$
\frac{e_1 \rightarrow e_1'}{e_1 + e_2 \rightarrow e_1' + e_2} \quad (S ext{-}AddLeft)
$$

$$
\frac{e_2 \rightarrow e_2'}{v_1 + e_2 \rightarrow v_1 + e_2'} \quad (S ext{-}AddRight)
$$

### 4.4 小步语义的完整求值

**多步归约**: $\rightarrow^*$ 是 $\rightarrow$ 的自反传递闭包。

**示例**: $(1 + 2) \times (3 + 4)$ 的求值

$$
\begin{aligned}
(1 + 2) \times (3 + 4) &\rightarrow 3 \times (3 + 4) \\
&\rightarrow 3 \times 7 \\
&\rightarrow 21
\end{aligned}
$$

### 4.5 小步 vs 大步的等价性

**定理**: 小步语义和大步语义等价。

$$
\langle e, \sigma \rangle \Downarrow \langle v, \sigma' \rangle \iff
\langle e, \sigma \rangle \rightarrow^* \langle v, \sigma' \rangle \text{ 且 } v \text{ 是值}
$$

---

## 5. λ演算的操作语义

### 5.1 调用按值 (Call-by-Value, CBV)

**值**: $v ::= \lambda x.e$

**求值上下文**:

$$
E ::= [] \mid E\ e \mid v\ E
$$

**归约规则**:

$$
\frac{}{\lambda x.e) \ v \rightarrow e[v/x]} \quad (\beta_v)
$$

**上下文规则**:

$$
\frac{e_1 \rightarrow e_1'}{e_1\ e_2 \rightarrow e_1'\ e_2} \quad
\frac{e_2 \rightarrow e_2'}{v_1\ e_2 \rightarrow v_1\ e_2'}
$$

**Rust 对应**: Rust 采用 CBV

```rust
// (λx.x+1) 5 → 5+1 = 6
let f = |x: i32| x + 1;
let result = f(5);  // 先求值 5，然后应用
```

### 5.2 调用按名 (Call-by-Name, CBN)

**求值上下文**:

$$
E ::= [] \mid E\ e
$$

**归约规则**:

$$
\frac{}{\lambda x.e)\ e_2 \rightarrow e[e_2/x]} \quad (\beta_n)
$$

**上下文规则**:

$$
\frac{e_1 \rightarrow e_1'}{e_1\ e_2 \rightarrow e_1'\ e_2}
$$

**特点**: 参数不求值直接替换，延迟求值。

### 5.3 调用按需 (Call-by-Need)

**核心思想**: CBN + 记忆化（只计算一次）。

**Haskell 采用此策略**。

---

## 6. 状态与命令式语言

### 6.1 存储模型

**存储** $\sigma$: 位置到值的偏函数。

$$
\sigma : \text{Loc} \rightharpoonup \text{Val}
$$

### 6.2 引用操作

**语法**:

$$
e ::= ... \mid \text{ref } e \mid !e \mid e_1 := e_2
$$

**语义**:

$$
\frac{e \Downarrow v}{\text{ref } e, \sigma \Downarrow l, \sigma[l \mapsto v]} \quad (\text{alloc})
$$

$$
\frac{e \Downarrow l}{!e, \sigma \Downarrow \sigma(l), \sigma} \quad (\text{deref})
$$

$$
\frac{e_1 \Downarrow l \quad e_2 \Downarrow v}{e_1 := e_2 \Downarrow (), \sigma[l \mapsto v]} \quad (\text{assign})
$$

**Rust 对应**:

```rust
// ref e
let l = Box::new(5);  // 分配

// !e
let v = *l;           // 解引用

// e1 := e2
*l = 10;              // 赋值
```

---

## 7. 并发操作语义

### 7.1 并行组合

**语法**:

$$
e ::= ... \mid e_1 \parallel e_2
$$

**交错语义 (Interleaving Semantics)**:

$$
\frac{e_1 \rightarrow e_1'}{e_1 \parallel e_2 \rightarrow e_1' \parallel e_2} \quad
\frac{e_2 \rightarrow e_2'}{e_1 \parallel e_2 \rightarrow e_1 \parallel e_2'}
$$

### 7.2 原子操作

**语法**:

$$
e ::= ... \mid \text{atomic } e
$$

**语义**: `atomic e` 保证 $e$ 的执行不可中断。

### 7.3 Happens-Before 关系

**定义**: 操作 $a$ happens-before 操作 $b$（记作 $a \rightarrow_{hb} b$），如果：

1. $a$ 和 $b$ 在同一线程，且 $a$ 在程序序中先于 $b$
2. $a$ 是解锁，$b$ 是 subsequent 加锁
3. 传递性: $a \rightarrow_{hb} b$ 且 $b \rightarrow_{hb} c$ 则 $a \rightarrow_{hb} c$

**意义**: $a \rightarrow_{hb} b$ 保证 $a$ 的效果对 $b$ 可见。

---

## 8. 结构化操作语义 (SOS)

### 8.1 Plotkin 的 SOS

由 Gordon Plotkin 提出的标准形式，使用推理规则描述语义。

**规则格式**:

$$
\frac{\text{前提}_1 \quad \text{前提}_2 \quad ... \quad \text{前提}_n}{\text{结论}} \quad (\text{规则名})
$$

### 8.2 规则分类

| 规则类型 | 特征 | 示例 |
|----------|------|------|
| **公理** | 无前提 | 数值、变量查找 |
| **计算规则** | 描述计算步骤 | β-归约、算术运算 |
| **_congruence_规则** | 传播归约 | 上下文规则 |

### 8.3 类型指导的语义

结合类型系统的语义：

$$
\frac{\Gamma \vdash e : \tau \quad e \rightarrow e'}{\Gamma \vdash e' : \tau}
$$

**保持性**: 类型在归约下保持。

---

## 9. 抽象机

### 9.1 CEK 机器

**组成**:

- **C**ontrol: 当前表达式
- **E**nvironment: 环境
- **K**ontinuation: 续延（计算上下文）

**状态**: $\langle C, E, K \rangle$

**示例转换**:

$$
\langle e_1\ e_2, E, K \rangle \rightarrow \langle e_1, E, \langle [], E, e_2 \rangle :: K \rangle
$$

### 9.2 Krivine 机器

用于 CBN λ演算的抽象机。

**状态**: $\langle e, E, S \rangle$

- $e$: 当前项
- $E$: 环境
- $S$: 栈（参数列表）

### 9.3 抽象机与编译

抽象机提供了编译器的中间表示 (IR) 模型。

**Rust MIR**: 可以看作高级抽象机的一种形式。

---

## 10. 在 Rust 中的应用

### 10.1 MIR (Mid-level IR) 语义

MIR 是 Rust 编译器使用的中间表示，具有显式的控制流图。

**MIR 结构**:

```rust
// Rust 源代码
fn main() {
    let x = 5;
    let y = x + 1;
    println!("{}", y);
}

// 对应的 MIR 概念（简化）
bb0: {
    _1 = 5;           // let x = 5
    _2 = _1;          // 复制 x
    _3 = Add(_2, 1);  // x + 1
    _4 = _3;          // let y = ...
    println(_4);      // 调用 println
    return;
}
```

### 10.2 所有权转移的小步语义

**规则**:

$$
\frac{x \text{ 拥有 } v \text{ 在 } \sigma \text{ 中}}{\langle \text{move } x, \sigma \rangle \rightarrow \langle v, \sigma' \rangle}
$$

其中 $\sigma'$ 将 $x$ 标记为已移动（不可再访问）。

### 10.3 借用检查的小步语义

**借用规则**:

$$
\frac{x \text{ 有效} \quad \text{borrow\_check}(\&x, \sigma)}{\langle \&x, \sigma \rangle \rightarrow \langle \text{ref\_to}(x), \sigma \rangle}
$$

---

## 11. 操作语义的性质

### 11.1 确定性

**定义**: 若 $e \rightarrow e_1$ 且 $e \rightarrow e_2$，则 $e_1 = e_2$。

**性质**: 简单 λ演算（CBV/CBN）是确定性的。

**非确定性扩展**: 并行组合、选择算子。

### 11.2 合流性 (Confluence)

**Church-Rosser 性质**:

```
    e
   / \
  ↓   ↓
 e₁   e₂
  \   /
   ↓ ↓
    e'
```

**意义**: 不同求值顺序最终收敛到相同结果。

### 11.3 标准化 (Standardization)

**定义**: 存在"标准"求值顺序能达正规形式（若存在）。

**意义**: 为解释器实现提供理论基础。

---

## 12. 总结

| 语义类型 | 形式 | 适用场景 | Rust应用 |
|----------|------|----------|----------|
| **大步语义** | $e \Downarrow v$ | 简洁描述、类型安全证明 | 高层语义 |
| **小步语义** | $e \rightarrow e'$ | 并发、分析非终止 | 并发模型 |
| **SOS** | 推理规则 | 语言规范 | 语言定义 |
| **抽象机** | $\langle C, E, K \rangle$ | 编译器实现 | MIR |

操作语义提供了从理论到实现的桥梁，是理解和实现 Rust 语义的基础工具。

---

## 参考文献

1. Plotkin, G. D. (1981). "A Structural Approach to Operational Semantics".
2. Hennessy, M. (1990). *The Semantics of Programming Languages*.
3. Winskel, G. (1993). *The Formal Semantics of Programming Languages*.
4. Felleisen, M., & Flatt, M. (2006). *Programming Languages and Lambda Calculi*.
5. Pierce, B. C. (2002). *Types and Programming Languages*.

---

**难度级别**: 🔴 高级 (理论基础)
**前置知识**: λ演算、类型理论
**后续学习**: 指称语义、公理语义
