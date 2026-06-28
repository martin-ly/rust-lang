# 借用检查器证明导读 / Borrow Checker Proof Guide

> **Bloom 层级**: 分析 / 评价
> **论文**: RustBelt: Securing the Foundations of the Rust Programming Language (POPL 2018)
> **会议**: POPL 2018 / PLDI 2025 (Tree Borrows)
> **状态**: ✅ 稳定保证（Safe Rust 子集）
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-06-25
> **权威来源**: [RustBelt (Jung et al., POPL 2018)](https://plv.mpi-sws.org/rustbelt/popl18/), [Stacked Borrows (POPL 2020)](https://plv.mpi-sws.org/rustbelt/stacked-borrows/), [Tree Borrows (PLDI 2025)](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html), [Polonius](https://rust-lang.github.io/polonius/), [Rust Reference](https://doc.rust-lang.org/reference/)
>
> **权威来源对齐变更日志**: 2026-06-25 新增 RustBelt、Stacked/Tree Borrows、Polonius 来源标注
>
> **受众**: [专家] / [研究者]
> **内容分级**: [专家级]
> 本文内容来自已归档的 `docs/research_notes/formal_methods/10_borrow_checker_proof.md`，经提炼后迁移。

---

## 📋 目录

- [借用检查器证明导读 / Borrow Checker Proof Guide](.#借用检查器证明导读--borrow-checker-proof-guide)
  - [📋 目录](.#-目录)
  - [学习目标](.#学习目标)
  - [1. 借用检查器保证什么](.#1-借用检查器保证什么)
  - [2. 流敏感分析：区域、借用与冲突](.#2-流敏感分析区域借用与冲突)
    - [2.1 核心抽象](.#21-核心抽象)
    - [2.2 冲突规则](.#22-冲突规则)
    - [2.3 从 NLL 到 Polonius](.#23-从-nll-到-polonius)
  - [3. 正确性证明草图](.#3-正确性证明草图)
    - [3.1 公理层](.#31-公理层)
    - [3.2 定理：数据竞争自由](.#32-定理数据竞争自由)
    - [3.3 定理：引用有效性](.#33-定理引用有效性)
    - [3.4 两阶段借用](.#34-两阶段借用)
  - [4. Stacked Borrows、Tree Borrows 与 Miri](.#4-stacked-borrowstree-borrows-与-miri)
    - [4.1 借用检查器 ≠ 别名模型](.#41-借用检查器--别名模型)
    - [4.2 Stacked Borrows](.#42-stacked-borrows)
    - [4.3 Tree Borrows](.#43-tree-borrows)
    - [4.4 Miri 的角色](.#44-miri-的角色)
  - [5. MIT / CMU / RustBelt 对齐](.#5-mit--cmu--rustbelt-对齐)
    - [5.1 MIT 6.826：内存安全形式化](.#51-mit-6826内存安全形式化)
    - [5.2 MIT 6.858：符号执行与并发安全](.#52-mit-6858符号执行与并发安全)
    - [5.3 CMU 15-799：并发分离逻辑](.#53-cmu-15-799并发分离逻辑)
    - [5.4 RustBelt 的数学基础](.#54-rustbelt-的数学基础)
  - [6. 与借用检查可判定性的联系](.#6-与借用检查可判定性的联系)
  - [7. 可运行 Rust 示例](.#7-可运行-rust-示例)
    - [示例 1：不可变借用共享](.#示例-1不可变借用共享)
    - [示例 2：NLL 允许提前结束借用](.#示例-2nll-允许提前结束借用)
    - [示例 3：两阶段借用](.#示例-3两阶段借用)
    - [示例 4：并发数据竞争被编译期拒绝](.#示例-4并发数据竞争被编译期拒绝)
    - [示例 5：悬垂引用被编译期拒绝](.#示例-5悬垂引用被编译期拒绝)
  - [权威来源索引](.#权威来源索引)

---

## 学习目标

> **[来源: RustBelt (Jung et al., POPL 2018)]**

完成本节后，你应能：

1. 用形式化语言陈述借用检查器保证的三大安全性质：数据竞争自由、无悬垂引用、别名与互斥的 XOR 规则。
2. 解释流敏感分析中的区域约束、借用状态与冲突检测如何协同工作。
3. 概述数据竞争自由的证明结构：从公理到定理的归纳论证。
4. 区分 Stacked Borrows、Tree Borrows 与 Miri 在验证链中的角色。
5. 将本文的公理/定理与 `concept/04_formal/28_borrow_checking_decidability.md` 中的可判定性视角对应起来。

---

## 1. 借用检查器保证什么

> **[来源: Rust Reference — References and Borrowing](https://doc.rust-lang.org/reference/)**

Rust 借用检查器在编译期为 Safe Rust 程序建立以下不变式：

| 不变式 | 直觉 | 形式化意义 |
|:---|:---|:---|
| **别名 XOR 可变** | 同一内存要么被多个只读引用共享，要么被一个可变引用独占 | 任意程序点，重叠内存上不可同时存在 `&mut` 与 `&` |
| **无悬垂引用** | 引用的生命周期不超过被引用值的存活区域 | `Lifetime(r) ⊆ Scope(r) ∧ Alive(Target(r), p)` |
| **数据竞争自由** | 并发访问要么只读，要么通过同步原语互斥 | 不存在无同步的冲突并发写 |

这三条不变式共同构成 Safe Rust 的**内存安全边界**：所有违反都会在编译期被拒绝，无需运行时垃圾回收。

---

## 2. 流敏感分析：区域、借用与冲突

> **[来源: Polonius / RFC 2094 — NLL](https://rust-lang.github.io/rfcs/2094-nll.html)**

借用检查器不是基于词法作用域的简单扫描，而是基于控制流图（CFG）的**流敏感分析**。

### 2.1 核心抽象

- **区域（Region）** $\rho$：CFG 上的路径集合，表示生命周期 `'a` 可能延伸到的所有程序点。
- **借用状态（Loan State）**：在程序点 $p$ 处，每条内存路径 $\pi$ 处于以下状态之一：

$$
\text{State}(\pi, p) \in \{\text{Free},\ \text{Shared},\ \text{Mut}(\rho),\ \text{Reserved}\}
$$

| 状态 | 含义 |
|:---|:---|
| **Free** | 无借用，可读写 |
| **Shared** | 一个或多个 `&` 只读借用 |
| **Mut($\rho$)** | `&mut` 独占借用，在区域 $\rho$ 内有效 |
| **Reserved** | 两阶段借用的预留态，尚未激活为可变借用 |

### 2.2 冲突规则

借用检查器在每个程序点检查：

$$
\text{Conflict}(b_1, b_2) \leftrightarrow \text{Overlap}(\text{Target}(b_1), \text{Target}(b_2)) \land \neg\text{Compatible}(b_1, b_2)
$$

兼容性仅允许**两个不可变借用**共存：

$$
\text{Compatible}(b_1, b_2) \leftrightarrow T(b_1) = \text{Immutable} \land T(b_2) = \text{Immutable}
$$

这直接编码了 **aliasing XOR mutation**。

### 2.3 从 NLL 到 Polonius

- **NLL**：将生命周期从“词法作用域”松弛为“创建点 → 最后使用点”，通过数据流方程求解：

$$
\begin{aligned}
\text{OUT}[B] &= (\text{IN}[B] \setminus \text{KILL}[B]) \cup \text{GEN}[B] \\
\text{IN}[B] &= \bigcap_{P \in \text{pred}(B)} \text{OUT}[P]
\end{aligned}
$$

- **Polonius**：将借用检查表达为 Datalog 约束传播，可接受 NLL 仍拒绝的部分安全模式（如条件借用、循环内精确分析）。

---

## 3. 正确性证明草图

> **[来源: RustBelt (Jung et al., POPL 2018)]**

### 3.1 公理层

**Axiom 1（可变借用唯一性）**：

$$
\forall p, m: |\{b \mid \text{Active}(b, p) \land T(b) = \text{Mutable} \land \text{Target}(b) = m\}| \leq 1
$$

**Axiom 2（可变-不可变互斥）**：

$$
\forall p, b_1, b_2: \text{Active}(b_1, p) \land \text{Active}(b_2, p) \land T(b_1) = \text{Mutable} \land T(b_2) = \text{Immutable} \to \neg\text{Overlap}(\text{Target}(b_1), \text{Target}(b_2))
$$

**Axiom 3（借用有效性保持）**：

$$
\text{Valid}(b, p) \land \neg\text{Invalidate}(b, p, p') \to \text{Valid}(b, p')
$$

**Axiom 4（借用检查完备性）**：

$$
\text{Check}(P) = \text{Pass} \leftrightarrow \forall \pi \in \text{Paths}(P): \pi \models \text{Axiom 1} \land \text{Axiom 2} \land \text{Axiom 3}
$$

### 3.2 定理：数据竞争自由

**Theorem 1**：通过借用检查的程序是数据竞争自由的。

$$
\forall P: \text{Check}(P) = \text{Pass} \to \text{DataRaceFree}(P)
$$

**证明草图（反证法 + 结构归纳）**：

1. 假设 $P$ 通过借用检查，但存在数据竞争 $(m, t_1, t_2)$。
2. 根据数据竞争定义，两个线程并发访问同一内存，至少一个为写，且无同步。
3. 若两个都是写：每个写需要 `&mut`，违反 Axiom 1，借用检查器会拒绝。
4. 若一读一写：写需要 `&mut`，读需要 `&`，违反 Axiom 2，借用检查器会拒绝。
5. 对 AST/CFG 做结构归纳，借用创建、跨线程传递、同步操作、函数调用均保持公理。
6. 矛盾，因此通过借用检查的程序数据竞争自由。$\square$

### 3.3 定理：引用有效性

**Theorem 3**：通过借用检查的程序中，所有引用在使用点都是有效的。

$$
\forall P: \text{Check}(P) = \text{Pass} \to \forall r \in \text{Refs}(P): \forall p \in \text{Use}(r): \text{Valid}(r, p)
$$

这由生命周期约束系统与 Axiom 3 共同保证：引用只能在被引用值存活区域内使用。

### 3.4 两阶段借用

现代 Rust 支持**两阶段借用（Two-Phase Borrows）**以接受直观代码，如 `vec.push(vec.len())`：

1. 方法调用的 receiver `vec` 先进入 **Reserved** 状态；
2. 参数 `vec.len()` 以不可变借用求值；
3. 参数求值完成后，Reserved 升级为 **Mut($\rho$)**。

其安全性在于：Reserved 期间禁止任何新冲突借用，因此升级时仍满足 Axiom 1 与 Axiom 2。

---

## 4. Stacked Borrows、Tree Borrows 与 Miri

> **[来源: Stacked Borrows (POPL 2020) / Tree Borrows (PLDI 2025) / Miri](https://github.com/rust-lang/miri)**

### 4.1 借用检查器 ≠ 别名模型

- **借用检查器**：编译期静态分析，保证 Safe Rust 程序的上述不变式。
- **别名模型（Stacked/Tree Borrows）**：定义 `unsafe` Rust 中引用的精确语义，规定何时别名使用构成未定义行为（UB）。

### 4.2 Stacked Borrows

- 将引用视为内存位置上的**栈**。
- `&mut` 唯一性被严格强制执行；违反为 UB。
- 已作为 Miri 的默认别名模型多年。

### 4.3 Tree Borrows

- 将引用视为**树**结构，父子引用可共存。
- 比 Stacked Borrows 更宽容：在 30k+ crates 评估中减少约 54% 的误报。
- 已在 Miri 中可用，未来可能切换为默认。
- 提供 Rocq 形式化证明。

### 4.4 Miri 的角色

Miri 是 Rust 的**解释器级验证工具**：

- 在 MIR 层级执行程序；
- 检测未定义行为（越界、悬垂指针、别名规则违反等）；
- 使用 Stacked Borrows 或 Tree Borrows 作为别名模型；
- 对 `unsafe` 代码的契约验证尤其有价值。

借用检查器保证 Safe Rust 无需 Miri 即可安全；Miri 则把同一套规则延伸到 `unsafe` 代码的运行时语义检查。

---

## 5. MIT / CMU / RustBelt 对齐

> **[来源: MIT 6.826 / MIT 6.858 / CMU 15-799 / RustBelt]**

### 5.1 MIT 6.826：内存安全形式化

| MIT 6.826 概念 | MIT 形式化 | Rust 借用检查器对应 |
|:---|:---|:---|
| Spatial Safety | $\forall addr: \text{Access}(addr) \to addr \in \text{ValidRegion}$ | 借用有效性 Def 1.3 + 生命周期约束 |
| Temporal Safety | $\forall t: \text{Access}(addr, t) \to \text{Valid}(addr, t)$ | 所有权环境 + 借用状态追踪 |
| Use-after-free | $\exists t_1 < t_2: \text{Free}(addr, t_1) \land \text{Access}(addr, t_2)$ | 编译期拒绝悬垂引用 |
| Capability | $\text{Access}(resource) \to \text{Hold}(capability)$ | 所有权 `Owned` / 借用 `&` / `&mut` |

### 5.2 MIT 6.858：符号执行与并发安全

MIT 6.858 使用符号执行在运行时探索路径条件；Rust 借用检查器则在编译期保证**所有路径**满足借用规则，避免路径爆炸问题。

| 6.858 主题 | Rust 编译期保证 |
|:---|:---|
| Race Condition | Axiom 1 / Axiom 2 |
| TOCTOU | `&mut T` 独占性 |
| ROP / 格式化字符串 | 所有权 + 类型安全 + 边界检查 |

### 5.3 CMU 15-799：并发分离逻辑

| CMU 15-799 概念 | Rust 实现 |
|:---|:---|
| Concurrent Separation Logic | `Send` / `Sync` trait |
| Resource Invariants | `Mutex<T>` / `RwLock<T>` |
| Ghost State | `PhantomData<T>` / `unsafe` 契约 |
| Linearizability | 原子操作语义 |

### 5.4 RustBelt 的数学基础

RustBelt 在 **Iris 分离逻辑**中形式化 Rust 类型系统：

- 将类型解释为一阶逻辑断言（谓词）；
- 借用规则编码为对资源（resource）的独占或共享权限；
- 证明 Safe Rust 程序在标准内存模型下数据竞争自由；
- `unsafe` 代码通过**协议（protocols）**和**不变式（invariants）**接入同一框架。

---

## 6. 与借用检查可判定性的联系

> **[来源: concept/04_formal/28_borrow_checking_decidability.md]**

`concept/04_formal/28_borrow_checking_decidability.md` 从**可判定性**视角补充了本文的形式化模型：

| 本文视角 | 可判定性视角 |
|:---|:---|
| Axiom 1–3 保证安全性 | 借用检查是“有限状态 + 单调闭包”上的判定问题 |
| NLL 数据流方程 | 借用状态在有限格上迭代，必收敛到不动点 |
| Polonius 约束传播 | 区域约束图的可满足性检查 |
| Theorem 1 数据竞争自由 | “通过编译 → 无数据竞争”是 sound but incomplete 的静态过滤器 |

核心对应：

- 生命周期 `'a` 是 CFG 上的路径集合 $\rho$；
- 区域约束 $\rho_i \subseteq \rho_j$ 编码为有向图；
- 约束可满足 ⟺ 引用使用点位于被引用值存活区域内；
- 借用检查是 **P-完全**的：多项式时间可解，但难以高效并行化到 NC。

这一视角解释了为什么 NLL/Polonius 能比词法作用域接受更多安全程序，同时仍保持可判定的编译期分析。

---

## 7. 可运行 Rust 示例

> **[来源: The Rust Programming Language / Rust Reference]**

### 示例 1：不可变借用共享

```rust
fn shared_read() {
    let s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    println!("{} {}", r1, r2);
}
```

两个不可变借用可共存，满足兼容性规则。

### 示例 2：NLL 允许提前结束借用

```rust
fn nll_example() {
    let mut s = String::from("hello");
    let r = &s;
    println!("{}", r); // r 最后一次使用
    s.push_str(" world"); // ✅ NLL：r 已结束
    println!("{}", s);
}
```

### 示例 3：两阶段借用

```rust
fn two_phase_borrow() {
    let mut v = vec![1, 2, 3];
    v.push(v.len()); // ✅ 两阶段借用：先 &，再 &mut
    println!("{:?}", v);
}
```

### 示例 4：并发数据竞争被编译期拒绝

```rust,ignore
use std::thread;

fn would_be_data_race() {
    let mut data = vec![1, 2, 3];
    // 下述代码无法编译：不能同时 move 并借用 data
    // thread::spawn(move || {
    //     data.push(4);
    // });
    // println!("{:?}", data);
}
```

### 示例 5：悬垂引用被编译期拒绝

```rust,ignore
// 错误：返回局部变量的引用
// fn dangling() -> &String {
//     let s = String::from("hello");
//     &s
// }

fn valid<'a>(s: &'a String) -> &'a String {
    s
}
```

---

## 权威来源索引

> **[来源: Rust Reference / RustBelt / POPL / PLDI]**

- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/) — POPL 2018
- [Stacked Borrows: An Aliasing Model for Rust](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) — POPL 2020
- [Tree Borrows: An Aliasing Model for Rust](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) — PLDI 2025
- [Polonius](https://rust-lang.github.io/polonius/)
- [Miri](https://github.com/rust-lang/miri)
- [RFC 2094 — NLL](https://rust-lang.github.io/rfcs/2094-nll.html)
- [Rust Reference — References and Borrowing](https://doc.rust-lang.org/reference/)
- [Rust Reference — Undefined Behavior](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
- [Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [concept/04_formal/28_borrow_checking_decidability.md](../../../concept/04_formal/28_borrow_checking_decidability.md)
- [docs/research_notes/formal_methods/10_borrow_checker_proof.md](../../../docs/research_notes/formal_methods/10_borrow_checker_proof.md)
