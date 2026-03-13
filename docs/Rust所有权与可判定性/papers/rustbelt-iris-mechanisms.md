# RustBelt：Iris分离逻辑核心机制详解

> 本文档深入解析Iris框架的核心机制，包括资源代数、Hoare三元组、高阶协议等
> 基于 Jung et al. (2018) RustBelt 和 Iris 论文

---

## 目录

- [RustBelt：Iris分离逻辑核心机制详解](#rustbeltiris分离逻辑核心机制详解)
  - [目录](#目录)
  - [1. Iris 框架概述](#1-iris-框架概述)
    - [1.1 核心设计理念](#11-核心设计理念)
    - [1.2 断言语言](#12-断言语言)
  - [2. 资源代数（Resource Algebra）](#2-资源代数resource-algebra)
    - [2.1 定义](#21-定义)
    - [2.2 分数所有权（Fractional Ownership）](#22-分数所有权fractional-ownership)
    - [2.3 独占资源（Exclusive Resource）](#23-独占资源exclusive-resource)
  - [3. Hoare 三元组与最弱前置条件](#3-hoare-三元组与最弱前置条件)
    - [3.1 Hoare 三元组](#31-hoare-三元组)
    - [3.2 Iris Hoare 三元组规则](#32-iris-hoare-三元组规则)
    - [3.3 最弱前置条件（Weakest Precondition）](#33-最弱前置条件weakest-precondition)
  - [4. 高阶协议（Higher-Order Protocols）](#4-高阶协议higher-order-protocols)
    - [4.1 协议定义](#41-协议定义)
    - [4.2 协议示例：Cell](#42-协议示例cell)
    - [4.3 协议兼容性](#43-协议兼容性)
  - [5. 幽灵状态（Ghost State）](#5-幽灵状态ghost-state)
    - [5.1 幽灵变量](#51-幽灵变量)
    - [5.2 幽灵状态更新](#52-幽灵状态更新)
    - [5.3 RustBelt中的应用：RefCell](#53-rustbelt中的应用refcell)
  - [6. 不变量（Invariants）](#6-不变量invariants)
    - [6.1 不变量定义](#61-不变量定义)
    - [6.2 不变量规则](#62-不变量规则)
    - [6.3 RustBelt中的应用：静态数据](#63-rustbelt中的应用静态数据)
  - [7. 原子性验证](#7-原子性验证)
    - [7.1 原子操作规则](#71-原子操作规则)
    - [7.2 无锁数据结构验证](#72-无锁数据结构验证)
  - [8. 完整的RustBelt证明结构](#8-完整的rustbelt证明结构)
    - [8.1 证明层次](#81-证明层次)
    - [8.2 核心引理](#82-核心引理)
  - [参考文献](#参考文献)

## 1. Iris 框架概述

### 1.1 核心设计理念

Iris是一个**高阶并发分离逻辑**框架，RustBelt基于它构建了Rust的形式化验证。

**关键特性**：

| 特性 | 说明 | 在RustBelt中的应用 |
|------|------|-------------------|
| 资源代数 | 可组合的资源模型 | 所有权建模 |
| 高阶协议 | 协议作为资源 | 借用生命周期 |
| 幽灵状态 | 逻辑层面的辅助状态 | 内部可变性 |
| 原子性 | 无锁数据结构验证 | Arc, Mutex |
| 模态运算符 | 时间/知识推理 | 不变量 |

### 1.2 断言语言

Iris断言 $P, Q$ 的语法：

$$
P, Q ::= \text{True} \mid \text{False} \mid P \land Q \mid P \lor Q \mid P \Rightarrow Q \mid \forall x. P \mid \exists x. P \mid P * Q \mid P \wand Q \mid \ell \mapsto v \mid \square P \mid \Diamond P
$$

**分离逻辑运算符**：

| 符号 | 名称 | 含义 |
|------|------|------|
| $P * Q$ | 分离合取 | $P$ 和 $Q$ 拥有不相交的资源 |
| $P \wand Q$ | 魔术棒（分离蕴含） | 若加上 $P$ 的资源，则得到 $Q$ |
| $\ell \mapsto v$ | 点指向 | 位置 $\ell$ 存储值 $v$ |
| $\square P$ | 持久性（Persistently） | $P$ 不消耗资源，可无限复制 |
| $\Diamond P$ | 可能性 | 未来某个时刻 $P$ 成立 |

---

## 2. 资源代数（Resource Algebra）

### 2.1 定义

资源代数 $\mathcal{RA} = (M, \cdot, \varepsilon, V)$ 包含：

- $M$：载体集合（资源的集合）
- $\cdot: M \times M \to M$：资源组合运算（偏函数）
- $\varepsilon \in M$：单位元
- $V \subseteq M$：有效资源集合

**公理**：

1. **结合律**：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$（当两边都定义时）
2. **单位元**：$a \cdot \varepsilon = \varepsilon \cdot a = a$
3. **有效性**：$a \cdot b \in V \Rightarrow a \in V \land b \in V$

### 2.2 分数所有权（Fractional Ownership）

用于建模共享借用：

$$
\text{Frac}(\text{Val}) \triangleq (\mathbb{Q} \cap (0, 1]) \times \text{Val}
$$

**组合规则**：

$$
(q_1, v) \cdot (q_2, v) = (q_1 + q_2, v) \quad \text{if } q_1 + q_2 \leq 1
$$

**解释**：

- $(1, v)$：完全所有权（可变借用）
- $(q, v)$ 且 $q < 1$：部分所有权（共享借用）

**Iris断言**：

$$
\ell \mapsto^{q} v \triangleq \text{拥有位置 } \ell \text{ 的 } q \text{ 份额，存储值 } v
$$

### 2.3 独占资源（Exclusive Resource）

用于建模可变借用：

$$
\text{Ex}(\text{Val}) \triangleq \{\text{Ex}(v) \mid v \in \text{Val}\} \cup \{\top\}
$$

**组合规则**：

- $\text{Ex}(v) \cdot \text{Ex}(v')$ 未定义（不能组合两个独占资源）
- $\text{Ex}(v) \cdot \top = \top$（与无效资源组合无效）

---

## 3. Hoare 三元组与最弱前置条件

### 3.1 Hoare 三元组

**定义**：

$$
\{P\} \, e \, \{v. Q(v)\}
$$

含义：在预条件 $P$ 下执行表达式 $e$，若终止则返回满足 $Q(v)$ 的值 $v$。

### 3.2 Iris Hoare 三元组规则

**返回值规则**：

$$
\frac{}{\{\Phi(v)\} \, v \, \{w. w = v \land \Phi(v)\}} \quad \text{[HT-RETURN]}
$$

**绑定规则（Bind）**：

$$
\frac{\{P\} \, e \, \{v. Q(v)\} \quad \forall v. \{Q(v)\} \, K[v] \, \{w. R(w)\}}{\{P\} \, K[e] \, \{w. R(w)\}} \quad \text{[HT-BIND]}
$$

**帧规则（Frame Rule）**：

$$
\frac{\{P\} \, e \, \{v. Q(v)\}}{\{P * R\} \, e \, \{v. Q(v) * R\}} \quad \text{[HT-FRAME]}
$$

（前提：$e$ 不修改 $R$ 中的资源）

### 3.3 最弱前置条件（Weakest Precondition）

**定义**：

$$
\text{wp}(e, \Phi) \triangleq \text{最弱的 } P \text{ 使得 } \{P\} \, e \, \{v. \Phi(v)\}
$$

**性质**：

$$
\{P\} \, e \, \{v. Q(v)\} \Leftrightarrow P \vdash \text{wp}(e, Q)
$$

**递归定义**：

$$
\text{wp}(e, \Phi) \triangleq \text{match } e \text{ with}
$$

$$
\mid v \Rightarrow \Phi(v)
$$

$$
\mid e_1; e_2 \Rightarrow \text{wp}(e_1, \_ . \text{wp}(e_2, \Phi))
$$

$$
\mid \text{let } x = e_1 \text{ in } e_2 \Rightarrow \text{wp}(e_1, v. \text{wp}(e_2[v/x], \Phi))
$$

---

## 4. 高阶协议（Higher-Order Protocols）

### 4.1 协议定义

协议是描述资源如何随时间演化的规范：

$$
\text{Protocol} \triangleq \text{State} \to \text{iProp}
$$

其中 $\text{iProp}$ 是Iris命题。

### 4.2 协议示例：Cell<T>

**Cell<T>的协议**：

```rust
// Cell<T> 允许通过共享引用进行内部可变性
// 协议：Cell总是包含某个值，可以被读取或替换
```

**形式化协议**：

$$
\text{CellProt}(\gamma, \ell) \triangleq \exists v. \ell \mapsto v * \gamma \mapsto v
$$

其中：

- $\ell$：Cell的内存位置
- $\gamma$：幽灵变量，跟踪Cell的逻辑内容

**方法规范**：

$$
\{\text{CellProt}(\gamma, \ell)\} \, \text{Cell::get}(\&\ell) \, \{v. v = \gamma \land \text{CellProt}(\gamma, \ell)\}
$$

$$
\{\text{CellProt}(\gamma, \ell)\} \, \text{Cell::set}(\&\ell, v') \, \{\_. \text{CellProt}(v', \ell)\}
$$

### 4.3 协议兼容性

**定义**：两个协议兼容如果它们可以安全地组合：

$$
\text{compatible}(P_1, P_2) \triangleq \exists R. P_1 * P_2 \vdash R
$$

**示例**：

- `Rc<T>` 和 `Arc<T>` 的协议兼容（共享所有权）
- `&mut T` 和 `&mut T` 的协议不兼容（冲突）

---

## 5. 幽灵状态（Ghost State）

### 5.1 幽灵变量

幽灵状态是**逻辑层面**的辅助状态，不影响程序执行但用于验证。

**声明**：

$$
\gamma \mapsto v \triangleq \text{幽灵变量 } \gamma \text{ 存储值 } v
$$

### 5.2 幽灵状态更新

$$
\frac{\{P * \gamma \mapsto v\} \, e \, \{Q * \gamma \mapsto v'\}}{\{P\} \, e \, \{Q\}} \quad \text{(幽灵状态可更新)}
$$

### 5.3 RustBelt中的应用：RefCell

**RefCell借用计数**：

使用幽灵状态跟踪RefCell的借用状态：

$$
\text{RefCellState}(\gamma, \ell) \triangleq \ell \mapsto v * \gamma \mapsto (v, \text{borrow\_count})
$$

**borrow()规范**：

$$
\{\text{RefCellState}(\gamma, \ell) * \gamma \mapsto (v, n)\} \, \text{borrow}() \, \{r. \gamma \mapsto (v, n+1) * r \mapsto v\}
$$

---

## 6. 不变量（Invariants）

### 6.1 不变量定义

$$
\overline{P}^{\mathcal{N}} \triangleq \text{命名空间 } \mathcal{N} \text{ 中的不变量 } P
$$

**性质**：$P$ 始终成立，可以被临时"打开"以进行验证。

### 6.2 不变量规则

**创建不变量**：

$$
\frac{P \text{ 是持久的}}{\{\text{True}\} \, \text{create\_inv}(P) \, \{i. \overline{P}^{i}\}} \quad \text{[INV-CREATE]}
$$

**打开不变量**：

$$
\frac{\{P * R\} \, e \, \{v. P * Q(v)\}}{\{\overline{P}^{\mathcal{N}} * R\} \, e \, \{v. \overline{P}^{\mathcal{N}} * Q(v)\}} \quad \text{[INV-OPEN]}
$$

（前提：$e$ 不释放不变量 $P$）

### 6.3 RustBelt中的应用：静态数据

**全局不变量**：

```rust
static COUNTER: AtomicUsize = AtomicUsize::new(0);
```

**形式化**：

$$
\overline{\exists n. \&\text{COUNTER} \mapsto n}^{\text{static}}
$$

---

## 7. 原子性验证

### 7.1 原子操作规则

**比较并交换（CAS）**：

$$
\frac{}{\{\ell \mapsto v\} \, \text{CAS}(\ell, v_{\text{old}}, v_{\text{new}}) \, \{b. (b = \text{true} \land \ell \mapsto v_{\text{new}}) \lor (b = \text{false} \land \ell \mapsto v \land v \neq v_{\text{old}})\}}
$$

### 7.2 无锁数据结构验证

**Treiber Stack push操作**：

```rust
fn push(&self, value: T) {
    let new_node = Box::new(Node { value, next: self.head.load() });
    while self.head.compare_exchange(new_node.next, new_node).is_err() {
        new_node.next = self.head.load();
    }
}
```

**验证要点**：

- 使用原子操作保证线程安全
- 使用Iris的原子性规则验证
- 考虑ABA问题（若适用）

---

## 8. 完整的RustBelt证明结构

### 8.1 证明层次

```
┌─────────────────────────────────────────────────────────────┐
│                    安全定理 (Safety Theorem)                 │
│              "良类型Rust程序是内存安全的"                     │
├─────────────────────────────────────────────────────────────┤
│                    类型解释 (Type Interpretation)            │
│           [T].own(t, v) - 类型T的所有权定义                  │
├─────────────────────────────────────────────────────────────┤
│                    Iris 推理 (Iris Reasoning)                │
│           Hoare三元组、资源代数、不变量                       │
├─────────────────────────────────────────────────────────────┤
│                    λ_Rust 语义 (λ_Rust Semantics)            │
│           小步操作语义、配置定义                              │
├─────────────────────────────────────────────────────────────┤
│                    Coq 形式化 (Coq Formalization)            │
│           19,000行证明代码                                   │
└─────────────────────────────────────────────────────────────┘
```

### 8.2 核心引理

**引理（所有权保持）**：

$$
\text{well\_typed}(e) \land \{[\Gamma]\} \, e \, \{v. \tau(v)\}
$$

**引理（借用安全性）**：

$$
\text{borrowed}(\ell, \text{mut}) \Rightarrow \neg\text{aliased}(\ell)
$$

---

## 参考文献

1. Jung, R., et al. (2018). Iris from the ground up: A modular foundation for higher-order concurrent separation logic. JFP.
2. Jung, R., et al. (2018). RustBelt: Securing the Foundations of Rust. POPL.
3. Krebbers, R., et al. (2017). Tealeaves: category-theoretic reasoning for Iris in Coq.

---

*本文档为《Rust所有权与可判定性》项目的RustBelt/Iris深度解析补充*
