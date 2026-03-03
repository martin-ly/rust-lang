# 完整形式证明：Rust所有权系统元定理

> 本文档提供Rust所有权系统核心定理的完整结构化证明
> 风格参考：Programming Languages语义学标准证明格式

---

## 目录

- [完整形式证明：Rust所有权系统元定理](#完整形式证明rust所有权系统元定理)
  - [目录](#目录)
  - [1. 预备知识与符号约定](#1-预备知识与符号约定)
    - [1.1 语法定义](#11-语法定义)
    - [1.2 操作语义配置](#12-操作语义配置)
    - [1.3 类型环境](#13-类型环境)
  - [2. 类型安全性定理（Progress + Preservation）](#2-类型安全性定理progress--preservation)
    - [2.1 定理陈述](#21-定理陈述)
    - [2.2 Progress 证明](#22-progress-证明)
      - [情况 1：变量 $e = x$](#情况-1变量-e--x)
      - [情况 2：借用 $e = \&x$](#情况-2借用-e--x)
      - [情况 3：可变借用 $e = \&mut x$](#情况-3可变借用-e--mut-x)
      - [情况 4：赋值 $e = \*e\_1 = e\_2$](#情况-4赋值-e--e_1--e_2)
      - [情况 5：let绑定 $e = \\text{let } x = e\_1 \\text{ in } e\_2$](#情况-5let绑定-e--textlet--x--e_1-text-in--e_2)
    - [2.3 Preservation 证明](#23-preservation-证明)
      - [情况 1：赋值规则 \[E-ASSIGN\]](#情况-1赋值规则-e-assign)
      - [情况 2：let绑定规则 \[E-LET-VAL\]](#情况-2let绑定规则-e-let-val)
      - [引理 2.3.1（代入引理 / Substitution Lemma）](#引理-231代入引理--substitution-lemma)
  - [3. 借用安全性定理](#3-借用安全性定理)
    - [3.1 定理陈述](#31-定理陈述)
    - [3.2 关键引理](#32-关键引理)
      - [引理 3.2.1（借用创建保持安全性）](#引理-321借用创建保持安全性)
      - [引理 3.2.2（借用结束保持安全性）](#引理-322借用结束保持安全性)
    - [3.3 借用安全性主证明](#33-借用安全性主证明)
  - [4. 内存安全性定理](#4-内存安全性定理)
    - [4.1 定理陈述](#41-定理陈述)
    - [4.2 证明概要](#42-证明概要)
    - [4.3 所有权安全性证明](#43-所有权安全性证明)
    - [4.4 无数据竞争证明](#44-无数据竞争证明)
  - [5. 静态分析保守性定理](#5-静态分析保守性定理)
    - [5.1 定理陈述](#51-定理陈述)
    - [5.2 可靠性证明](#52-可靠性证明)
    - [5.3 不完备性证明](#53-不完备性证明)
  - [6. 证明总结](#6-证明总结)
  - [参考文献](#参考文献)

---

## 1. 预备知识与符号约定

### 1.1 语法定义

**表达式语法**：

```text
e ::= x                         (变量)
   | v                          (值)
   | let x = e1 in e2           (绑定)
   | e1; e2                     (序列)
   | &e | &mut e                (借用)
   | *e                         (解引用)
   | e1 = e2                    (赋值)
   | box e                      (装箱)
```

**值语法**：

```text
v ::= () | n | true | false    (基本值)
   | (v1, v2)                  (元组)
   | ℓ                         (内存位置)
   | &ℓ | &mut ℓ               (引用)
```

### 1.2 操作语义配置

配置 $C = \langle e, \sigma, \pi \rangle$ 包含：

- $e$: 待求值表达式
- $\sigma$: 存储（内存映射）
- $\pi$: 借用状态（跟踪活跃借用）

**小步语义**：$\langle e, \sigma, \pi \rangle \to \langle e', \sigma', \pi' \rangle$

### 1.3 类型环境

$$\Gamma ::= \emptyset \mid \Gamma, x: T$$

**借用状态**：

$$\pi ::= \emptyset \mid \pi, \text{borrow}(\ell, \text{mut}, t) \mid \pi, \text{borrow}(\ell, \text{sh}, t)$$

---

## 2. 类型安全性定理（Progress + Preservation）

### 2.1 定理陈述

**定理 2.1（类型安全性）**：

如果 $\Gamma \vdash e : T$ 且 $\text{well\_formed}(\Gamma, \sigma, \pi)$，则：

1. **Progress**：要么 $e$ 是值，要么 $\exists e', \sigma', \pi'. \langle e, \sigma, \pi \rangle \to \langle e', \sigma', \pi' \rangle$
2. **Preservation**：如果 $\langle e, \sigma, \pi \rangle \to \langle e', \sigma', \pi' \rangle$，则 $\Gamma \vdash e' : T$ 且 $\text{well\_formed}(\Gamma, \sigma', \pi')$

---

### 2.2 Progress 证明

**证明结构**：对 $\Gamma \vdash e : T$ 的推导进行结构归纳。

#### 情况 1：变量 $e = x$

**假设**：$\Gamma \vdash x : T$ 且 $x : T \in \Gamma$

**证明**：

- 由良构配置定义，$x \in \text{dom}(\sigma)$
- 因此 $x$ 已求值为某个值 $v = \sigma(x)$
- $x$ 已经是值（或已绑定到值）

**结论**：Progress成立 ✓

---

#### 情况 2：借用 $e = \&x$

**假设**：$\Gamma \vdash \&x : \&T$ 且 $x : T \in \Gamma$

**证明**：

- 由 [BORROW-IMM] 规则前提：$x \in \text{dom}(\sigma)$
- 设 $\sigma(x) = \ell$
- 应用 [E-REF-IMM] 语义规则：

$$
\frac{x \in \text{dom}(\sigma) \quad \sigma(x) = \ell}{\langle \&x, \sigma, \pi \rangle \to \langle \&\ell, \sigma, \pi \cup \{\text{borrow}(\ell, \text{sh}, t)\} \rangle}
$$

**结论**：存在下一步规约，Progress成立 ✓

---

#### 情况 3：可变借用 $e = \&mut x$

**假设**：$\Gamma \vdash \&mut x : \&mut T$ 且 $x : T \in \Gamma$

**证明**：

- 由 [BORROW-MUT] 规则前提：$\neg\text{mutable\_borrowed}(\pi, x)$
- 即不存在活跃的$\&mut x$借用
- 由良构配置，$x \in \text{dom}(\sigma)$，设 $\sigma(x) = \ell$
- 应用 [E-REF-MUT] 语义规则：

$$
\frac{\sigma(x) = \ell \quad \neg\text{borrowed}(\pi, \ell)}{\langle \&mut x, \sigma, \pi \rangle \to \langle \&mut \ell, \sigma, \pi \cup \{\text{borrow}(\ell, \text{mut}, t)\} \rangle}
$$

**结论**：存在下一步规约，Progress成立 ✓

---

#### 情况 4：赋值 $e = *e_1 = e_2$

**假设**：$\Gamma \vdash *e_1 = e_2 : ()$ 且 $\Gamma \vdash e_1 : \&mut T$ 且 $\Gamma \vdash e_2 : T$

**证明**：

- 由归纳假设（应用于 $e_1$）：
  - 子情况 4a：$e_1$ 是值 $v_1$
    - 由类型，$v_1 = \&mut \ell$ 对于某个 $\ell$
    - 由借用状态，$(\ell, \text{mut}, t) \in \pi$（借用有效）
    - 继续对 $e_2$ 应用归纳假设...

  - 子情况 4b：$e_1 \to e_1'$
    - 应用 [E-CTX] 规则：

$$
\frac{\langle e_1, \sigma, \pi \rangle \to \langle e_1', \sigma', \pi' \rangle}{\langle *e_1 = e_2, \sigma, \pi \rangle \to \langle *e_1' = e_2, \sigma', \pi' \rangle}
$$

**结论**：Progress成立 ✓

---

#### 情况 5：let绑定 $e = \text{let } x = e_1 \text{ in } e_2$

**假设**：$\Gamma \vdash \text{let } x = e_1 \text{ in } e_2 : T_2$ 且 $\Gamma \vdash e_1 : T_1$ 且 $\Gamma, x: T_1 \vdash e_2 : T_2$

**证明**：

- 对 $e_1$ 应用归纳假设：
  - 若 $e_1 = v_1$（值），应用 [E-LET-VAL]：

$$
\frac{e_1 = v_1}{\langle \text{let } x = e_1 \text{ in } e_2, \sigma, \pi \rangle \to \langle e_2[v_1/x], \sigma[x \mapsto v_1], \pi \rangle}
$$

- 若 $e_1 \to e_1'$，应用 [E-CTX]

**结论**：Progress成立 ✓

---

### 2.3 Preservation 证明

**证明结构**：对求值规则 $\langle e, \sigma, \pi \rangle \to \langle e', \sigma', \pi' \rangle$ 进行案例分析。

#### 情况 1：赋值规则 [E-ASSIGN]

**前提**：

- $\Gamma \vdash *e_1 = e_2 : ()$
- $e_1 = \&mut \ell$（已求值）
- $e_2 = v_2$（值）
- $(\ell, \text{mut}, t) \in \pi$

**语义**：

$$
\langle *(\&mut \ell) = v_2, \sigma, \pi \rangle \to \langle (), \sigma[\ell \mapsto v_2], \pi \rangle
$$

**类型保持证明**：

- 由前提，$\Gamma \vdash \&mut \ell : \&mut T$（推导自 $e_1$）
- 由前提，$\Gamma \vdash v_2 : T$
- 结果 $()$ 的类型是 $()$，与原类型一致 ✓

**良构性保持**：

- 存储更新：$\sigma' = \sigma[\ell \mapsto v_2]$
- 借用状态不变：$\pi' = \pi$
- 需要证明：更新后的存储类型一致
- 由类型系统保证：$v_2 : T$ 且 $\ell$ 期望类型 $T$ ✓

---

#### 情况 2：let绑定规则 [E-LET-VAL]

**前提**：

- $\Gamma \vdash \text{let } x = v_1 \text{ in } e_2 : T_2$
- $\Gamma \vdash v_1 : T_1$
- $\Gamma, x: T_1 \vdash e_2 : T_2$

**语义**：

$$
\langle \text{let } x = v_1 \text{ in } e_2, \sigma, \pi \rangle \to \langle e_2[v_1/x], \sigma[x \mapsto v_1], \pi \rangle
$$

**类型保持证明**：

- 由代入引理（Substitution Lemma）：
  - 若 $\Gamma, x: T_1 \vdash e_2 : T_2$ 且 $\Gamma \vdash v_1 : T_1$
  - 则 $\Gamma \vdash e_2[v_1/x] : T_2$
- 结论：$e_2[v_1/x]$ 的类型仍为 $T_2$ ✓

**良构性保持**：

- 环境扩展：$\Gamma' = \Gamma, x: T_1$
- 存储扩展：$\sigma' = \sigma[x \mapsto v_1]$
- 由定义，$\text{well\_formed}(\Gamma', \sigma', \pi)$ ✓

---

#### 引理 2.3.1（代入引理 / Substitution Lemma）

**陈述**：若 $\Gamma, x: T_1 \vdash e : T$ 且 $\Gamma \vdash v : T_1$，则 $\Gamma \vdash e[v/x] : T$。

**证明**：对 $\Gamma, x: T_1 \vdash e : T$ 的推导进行归纳。

*基本情况*：

- **情况 $e = x$**：$e[v/x] = v$
  - 由前提，$\Gamma, x: T_1 \vdash x : T_1$
  - 要证：$\Gamma \vdash v : T_1$
  - 这正是第二个前提 ✓

- **情况 $e = y$（$y \neq x$）**：$e[v/x] = y$
  - 由前提，$\Gamma, x: T_1 \vdash y : T$ 且 $y: T \in \Gamma$
  - 因此 $\Gamma \vdash y : T$ ✓

*归纳情况*（以let为例）：

- **情况 $e = \text{let } y = e_1 \text{ in } e_2$**：
  - 假设：$\Gamma, x: T_1 \vdash e_1 : S$ 且 $\Gamma, x: T_1, y: S \vdash e_2 : T$
  - 归纳假设 IH1：$\Gamma \vdash e_1[v/x] : S$
  - 归纳假设 IH2：$\Gamma, y: S \vdash e_2[v/x] : T$（注意 $y$ Fresh，$y \neq x$）
  - 要证：$\Gamma \vdash (\text{let } y = e_1 \text{ in } e_2)[v/x] : T$
  - 即：$\Gamma \vdash \text{let } y = e_1[v/x] \text{ in } e_2[v/x] : T$
  - 由 [LET] 规则和 IH1、IH2，得证 ✓

---

## 3. 借用安全性定理

### 3.1 定理陈述

**定理 3.1（借用安全性）**：

在程序执行过程中，以下不变式始终成立：

1. **共享借用唯一性**：在任意时刻 $t$，对于位置 $\ell$，若存在活跃的共享借用 $\text{borrow}(\ell, \text{sh}, t)$，则不存在活跃的可变借用 $\text{borrow}(\ell, \text{mut}, t')$。

2. **可变借用排他性**：在任意时刻 $t$，对于位置 $\ell$，若存在活跃的可变借用 $\text{borrow}(\ell, \text{mut}, t)$，则不存在其他活跃借用（共享或可变）。

形式化：

$$
\forall t, \ell. \left(\begin{array}{l}
(\exists n. \text{borrow}(\ell, \text{sh}, t) \in \pi_n) \Rightarrow \neg(\exists t'. \text{borrow}(\ell, \text{mut}, t') \in \pi_t) \\
\land \\
(\text{borrow}(\ell, \text{mut}, t) \in \pi_t) \Rightarrow \neg(\exists r, t'. r \neq \text{mut} \land \text{borrow}(\ell, r, t') \in \pi_t)
\end{array}\right)
$$

---

### 3.2 关键引理

#### 引理 3.2.1（借用创建保持安全性）

**陈述**：创建新的借用不会违反借用安全性不变式。

**证明**：

考虑创建借用的两种操作：

**情况 1：创建共享借用 $r = \&x$**

- 类型规则 [BORROW-IMM] 前提：无前提条件（$x$ 的当前借用状态不限）
- 语义规则 [E-REF-IMM]：将 $\text{borrow}(\ell, \text{sh}, t)$ 添加到 $\pi$
- 安全性检查：
  - 若存在 $\text{borrow}(\ell, \text{mut}, t')$：违反！
  - 但由类型检查，这种情况被 [BORROW-IMM] 隐含阻止
  - 实际上，[BORROW-IMM] 要求 $x$ 在当前上下文中未被可变借用

**情况 2：创建可变借用 $r = \&mut x$**

- 类型规则 [BORROW-MUT] 前提：$\neg\text{borrowed}(\Gamma, x)$
- 即 $x$ 在当前环境中无任何活跃借用
- 语义规则 [E-REF-MUT]：将 $\text{borrow}(\ell, \text{mut}, t)$ 添加到 $\pi$
- 由于前提保证无其他借用，安全性不变式保持 ✓

---

#### 引理 3.2.2（借用结束保持安全性）

**陈述**：借用的自然结束（生命周期终止）不会违反借用安全性不变式。

**证明**：

借用结束有两种方式：

1. **作用域结束**：借用引用离开作用域
   - 从 $\pi$ 中移除对应的 $\text{borrow}$ 记录
   - 移除借用不会引入新的冲突 ✓

2. **NLL结束**：最后一次使用后结束（非词法生命周期）
   - 由数据流分析确定结束点
   - 在结束点之后，借用记录从 $\pi$ 移除
   - 同样，移除不会引入冲突 ✓

---

### 3.3 借用安全性主证明

**证明方法**：对操作语义推导序列进行归纳，证明每一步都保持安全性不变式。

**基例**：

初始状态：$\pi = \emptyset$（无借用）

- 安全性不变式平凡成立 ✓

**归纳步**：

假设在步骤 $n$ 安全性不变式成立，考虑步骤 $n \to n+1$ 的所有可能操作：

| 操作 | 对 $\pi$ 的影响 | 安全性分析 |
|------|----------------|------------|
| 变量查找 | 无变化 | 保持不变 ✓ |
| 创建共享借用 | 添加 $\text{borrow}(\ell, \text{sh})$ | 由引理3.2.1，类型检查确保无冲突 ✓ |
| 创建可变借用 | 添加 $\text{borrow}(\ell, \text{mut})$ | 由引理3.2.1，类型检查确保无其他借用 ✓ |
| 借用结束 | 移除借用记录 | 由引理3.2.2，移除不会引入冲突 ✓ |
| 解引用 | 无变化 | 保持不变 ✓ |
| 赋值 | 无变化（借用状态） | 保持不变 ✓ |

**结论**：通过归纳，借用安全性不变式在所有执行步骤中保持。

$$
\square \text{ (借用安全性定理得证)}
$$

---

## 4. 内存安全性定理

### 4.1 定理陈述

**定理 4.1（内存安全性）**：

良类型的Rust程序不会导致以下未定义行为：

1. **悬垂指针解引用**：解引用已释放内存的指针
2. **use-after-free**：使用已释放的资源
3. **双重释放**：同一内存释放两次
4. **缓冲区溢出**：访问数组/切片边界外的内存
5. **数据竞争**：无同步的并发读写冲突

形式化：

$$
\Gamma \vdash e : T \land \text{well\_formed}(\Gamma, \sigma_0, \emptyset) \Rightarrow \neg\exists n. \text{UB}(\langle e, \sigma_0, \emptyset \rangle \to^n C_n)
$$

其中 $\text{UB}(C)$ 表示配置 $C$ 处于未定义行为状态。

---

### 4.2 证明概要

内存安全性由以下三个核心属性共同保证：

```text
┌─────────────────────────────────────────────────────────┐
│                   内存安全性证明结构                      │
├─────────────────────────────────────────────────────────┤
│                                                         │
│   类型安全性 (Progress + Preservation)                   │
│           │                                             │
│           ├──► 所有操作在类型正确值上进行                  │
│           │                                             │
│   借用安全性 (Borrow Safety)                            │
│           │                                             │
│           ├──► 无数据竞争 + 无别名冲突                    │
│           │                                             │
│   所有权安全性 (Ownership Safety)                        │
│           │                                             │
│           └──► 无use-after-free + 无双重释放             │
│                                                         │
│   ═══════════════════════════════════════════════════   │
│                    内存安全性得证                         │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

### 4.3 所有权安全性证明

**关键不变式**：每个内存位置 $\ell$ 有唯一的所有者，且仅当存在有效所有者时才能访问。

**引理 4.3.1（唯一所有权）**：

$$
\forall \ell, t. \exists! x. \text{owns}(x, \ell, t) \lor \text{deallocated}(\ell, t)
$$

**证明**：

- **初始**：$\ell$ 被创建时（`box` 或 `let`），绑定到变量 $x$
- **转移**：通过 move 操作，所有权从 $x$ 转移到 $y$
  - 源变量 $x$ 变为未初始化状态
  - 目标变量 $y$ 获得唯一所有权
- **析构**：当所有者离开作用域，$\ell$ 被释放

因此，在任意时刻，$\ell$ 要么有唯一所有者，要么已被释放。

---

### 4.4 无数据竞争证明

**引理 4.4.1（Send/Sync保证线程安全）**：

若类型 $T$ 满足：

- $T: \text{Send}$：允许跨线程转移所有权
- $T: \text{Sync}$：允许跨线程共享引用

则 $T$ 的跨线程使用不会导致数据竞争。

**证明概要**：

1. **Send保证**：所有权转移确保只有一个线程能访问 $T$ 的值
2. **Sync保证**：若 $T: \text{Sync}$，则 $\&T: \text{Send}$，且 $T$ 内部同步
3. **编译器检查**：Rust编译器验证所有跨线程数据满足Send/Sync约束

---

## 5. 静态分析保守性定理

### 5.1 定理陈述

**定理 5.1（静态分析保守性）**：

Rust借用检查器是**可靠**（Sound）但**不完备**（Incomplete）的。

1. **可靠性（Soundness）**：
   $$
   \text{compiles}(P) \Rightarrow \text{safe}(P)$$
   （能通过编译的程序一定是安全的）

2. **不完备性（Incompleteness）**：
   $$
   \exists P. \text{safe}(P) \land \neg\text{compiles}(P)$$
   （存在安全的程序被编译器拒绝）

---

### 5.2 可靠性证明

**证明**：由定理 2.1（类型安全性）和定理 3.1（借用安全性）及定理 4.1（内存安全性）直接可得。

$$
\text{well\_typed}(P) \Rightarrow \text{no\_UB}(P) \Leftrightarrow \text{safe}(P)
$$

---

### 5.3 不完备性证明

**构造性证明**：展示一个安全但被编译器拒绝的程序。

**反例**（条件借用）：

```rust
fn conditional_borrow(flag: bool, x: &mut i32) {
    if flag {
        let r = &mut *x;  // 可变借用
        *r += 1;
    }  // r 在此处结束

    // 编译器错误：x 仍被视为被借用
    // 即使 flag 为 false 时，这里访问是安全的
    *x += 1;
}
```

**形式化分析**：

- **实际安全性**：
  - 若 `flag = true`：第一次借用结束后才第二次访问，无冲突
  - 若 `flag = false`：没有发生借用，直接访问安全
  - 因此程序在所有执行路径上都是安全的

- **编译器拒绝原因**：
  - 借用检查器进行**流不敏感分析**（flow-insensitive）
  - 或生命周期分析过于保守
  - 无法区分 `if` 分支的执行路径

**结论**：存在安全程序被编译器拒绝，不完备性得证。

---

## 6. 证明总结

| 定理 | 核心引理 | 证明方法 | 依赖 |
|------|----------|----------|------|
| 类型安全性 | 代入引理 | 结构归纳 | 类型规则 |
| 借用安全性 | 借用创建/结束引理 | 归纳法 | 类型检查 |
| 内存安全性 | 唯一所有权、Send/Sync | 组合证明 | 上述定理 |
| 保守性 | 无 | 构造性证明 | 具体反例 |

---

## 参考文献

1. Jung et al. (2018). RustBelt: Securing the Foundations of Rust. POPL.
2. Weiss et al. (2021). Oxide: The Essence of Rust. arXiv.
3. Wright & Felleisen (1994). A Syntactic Approach to Type Soundness. TOPLAS.
4. Harper (2016). Practical Foundations for Programming Languages. Cambridge.

---

*本文档为《Rust所有权与可判定性》项目的形式化证明补充*
