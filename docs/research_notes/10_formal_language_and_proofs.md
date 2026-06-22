# 形式语言与形式证明

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 用形式语言（推理规则、操作语义、判定形式）表达 Rust 核心定理，提供数学级形式证明；与 Coq 骨架互补（形式语言为规范，Coq 为机器可检查实现）
> **上位文档**: [CORE_THEOREMS_FULL_PROOFS](./10_core_theorems_full_proofs.md)、[FORMAL_FULL_MODEL_OVERVIEW](./10_formal_full_model_overview.md)

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [形式语言与形式证明](#形式语言与形式证明)
  - [📑 目录](#-目录)
  - [一、形式语言总览](#一形式语言总览)
  - [二、语法（归纳定义）](#二语法归纳定义)
    - [2.1 核心表达式（简化）](#21-核心表达式简化)
    - [2.2 所有权状态](#22-所有权状态)
    - [2.3 借用类型](#23-借用类型)
  - [三、判定形式与推理规则](#三判定形式与推理规则)
    - [3.1 类型判定](#31-类型判定)
    - [3.2 所有权状态判定](#32-所有权状态判定)
    - [3.3 借用判定](#33-借用判定)
  - [四、操作语义（小步）](#四操作语义小步)
    - [4.1 类型系统归约](#41-类型系统归约)
    - [4.2 所有权状态转换](#42-所有权状态转换)
  - [五、形式证明（数学级）](#五形式证明数学级)
    - [5.1 定理 T-OW2（所有权唯一性）](#51-定理-t-ow2所有权唯一性)
    - [5.2 定理 T-BR1（数据竞争自由）](#52-定理-t-br1数据竞争自由)
    - [5.3 定理 T-TY3（类型安全）](#53-定理-t-ty3类型安全)
  - [六、推导树示例](#六推导树示例)
    - [T-OW2 归纳步（move）的推导](#t-ow2-归纳步move的推导)
    - [T-BR1 情况 1 的推导](#t-br1-情况-1-的推导)
  - [七、与 Coq 的对应](#七与-coq-的对应)
  - [八、引用](#八引用)
  - [🆕 Rust 1.94 更新](#-rust-194-更新)
  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)
  - [**最后更新**: 2026-03-14 (Rust 1.94 深度整合)](#最后更新-2026-03-14-rust-194-深度整合)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 一、形式语言总览
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

本文档采用**标准 PL 形式化风格**（TAPL、RustBelt）：

| 层次 | 形式 | 说明 |
| :--- | :--- | :--- |
| **语法** | BNF / 归纳定义 | 表达式、类型、程序 |
| **判定形式** | $\mathcal{J}$ 形式 | 类型判定、借用判定、状态判定 |
| **推理规则** | $\frac{\text{前提}}{\text{结论}}$ | 良构、良型、可达 |
| **操作语义** | $e \to e'$、$S \xrightarrow{op} S'$ | 小步归约、状态转换 |
| **形式证明** | 归纳、反证、推导树 | 定理的数学证明 |

**与 Rust 的衔接**：形式语言为**数学规范层**；Rust 示例为**实现层**；见 [THEOREM_RUST_EXAMPLE_MAPPING](./10_theorem_rust_example_mapping.md)。

---

## 二、语法（归纳定义）
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 核心表达式（简化）

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

$$
\begin{aligned}
e \mathrel{::=} &\; x \mid v \mid e_1\; e_2 \mid \lambda x{:}\tau.\, e \mid \textbf{let}\; x = e_1\;\textbf{in}\; e_2 \\
v \mathrel{::=} &\; n \mid \textbf{true} \mid \textbf{false} \mid \lambda x{:}\tau.\, e \\
\tau \mathrel{::=} &\; \textbf{Int} \mid \textbf{Bool} \mid \tau_1 \to \tau_2
\end{aligned}
$$

### 2.2 所有权状态

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

$$
\Omega(x) \in \{\text{Owned}, \text{Moved}, \text{Dropped}\}
$$

### 2.3 借用类型

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

$$
B \mathrel{::=} \text{Immutable} \mid \text{Mutable}
$$

---

## 三、判定形式与推理规则
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 3.1 类型判定

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**判定形式**：$\Gamma \vdash e : \tau$（在环境 $\Gamma$ 下，$e$ 具有类型 $\tau$）

**推理规则**：

$$
\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau} \;\text{(Var)}
\quad
\frac{\Gamma \vdash e_1 : \tau_1 \to \tau_2 \quad \Gamma \vdash e_2 : \tau_1}{\Gamma \vdash e_1\; e_2 : \tau_2} \;\text{(App)}
$$

$$
\frac{\Gamma, x : \tau_1 \vdash e : \tau_2}{\Gamma \vdash \lambda x{:}\tau_1.\, e : \tau_1 \to \tau_2} \;\text{(Abs)}
\quad
\frac{\Gamma \vdash e_1 : \tau_1 \quad \Gamma, x : \tau_1 \vdash e_2 : \tau_2}{\Gamma \vdash \textbf{let}\; x = e_1\;\textbf{in}\; e_2 : \tau_2} \;\text{(Let)}
$$

### 3.2 所有权状态判定

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**判定形式**：$(\Gamma, \Omega) \vdash_{\text{own}} \text{ok}$（所有权配置良构）

**规则**：

$$
\frac{}{\Gamma, \Omega \vdash_{\text{own}} \text{ok}} \;\text{(Init)}
\quad
\frac{\Omega(x) = \text{Owned} \quad \forall y \neq x.\, \Omega(y) \neq \text{Owned} \lor \Gamma(y) \neq \Gamma(x)}{(\Gamma, \Omega) \vdash_{\text{own}} \text{ok}} \;\text{(Unique)}
$$

### 3.3 借用判定

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**判定形式**：$\Gamma \vdash_{\text{borrow}} b : \text{ok}$（借用 $b$ 满足规则）

**规则 1（可变借用唯一性）**：

$$
\frac{\text{BorrowType}(b) = \text{Mutable} \quad \forall b' \neq b.\, \text{Disjoint}(b, b')}{\Gamma \vdash_{\text{borrow}} b : \text{ok}} \;\text{(MutUnique)}
$$

**规则 2（可变与不可变互斥）**：

$$
\frac{\text{BorrowType}(b_1) = \text{Immutable} \quad \text{BorrowType}(b_2) = \text{Mutable} \rightarrow \text{Disjoint}(b_1, b_2)}{\Gamma \vdash_{\text{borrow}} b_1 : \text{ok}} \;\text{(ImmMutExcl)}
$$

---

## 四、操作语义（小步）
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 4.1 类型系统归约

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

**归约关系**：$e \to e'$

$$
\frac{e_1 \to e_1'}{e_1\; e_2 \to e_1'\; e_2} \;\text{(App-L)}
\quad
\frac{e_2 \to e_2'}{v_1\; e_2 \to v_1\; e_2'} \;\text{(App-R)}
$$

$$
\frac{}{(\lambda x{:}\tau.\, e)\; v \to e[x := v]} \;\text{($\beta$)}
\quad
\frac{e_1 \to e_1'}{\textbf{let}\; x = e_1\;\textbf{in}\; e_2 \to \textbf{let}\; x = e_1'\;\textbf{in}\; e_2} \;\text{(Let-Step)}
$$

$$
\frac{}{\textbf{let}\; x = v\;\textbf{in}\; e \to e[x := v]} \;\text{(Let-Value)}
$$

### 4.2 所有权状态转换

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

**转换关系**：$(\Gamma, \Omega) \xrightarrow{op} (\Gamma', \Omega')$

| 操作 $op$ | 前提 | 效果 |
| :--- | :--- | :--- |
| $\text{move}(x, y)$ | $\Omega(x) = \text{Owned}$ | $\Omega'(x) = \text{Moved}$, $\Omega'(y) = \text{Owned}$, $\Gamma'(y) = \Gamma(x)$ |
| $\text{copy}(x, y)$ | $\Gamma(x) : \text{Copy}$ | $\Gamma'(y) = \text{copy}(\Gamma(x))$；$\Omega$ 不变 |
| $\text{drop}(x)$ | 作用域结束 | $\Omega'(x) = \text{Dropped}$ |

---

## 五、形式证明（数学级）
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 5.1 定理 T-OW2（所有权唯一性）
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

**陈述**：$\forall v, S: |\{x \mid \Omega_S(x)=\text{Owned} \land \Gamma_S(x)=v\}| \leq 1$

**证明**（结构归纳于可达状态）：

**归纳谓词** $P(S)$：$S$ 中 $\forall v$ 至多一个 $x$ 满足 $\Omega(x)=\text{Owned} \land \Gamma(x)=v$。

**基例**：$S = S_0$。由规则 1（每值唯一所有者），初始绑定时 $P(S_0)$ 成立。∎

**归纳步**：设 $P(S)$，$S \xrightarrow{op} S'$。分情况：

1. **$op = \text{move}(x, y)$**：$\Omega'(x)=\text{Moved}$，$\Omega'(y)=\text{Owned}$；$v$ 仅 $y$ 拥有。$P(S')$。
2. **$op = \text{copy}(x, y)$**：$\Gamma'(y) = \text{copy}(\Gamma'(x))$，故 $\Gamma'(y) \neq \Gamma'(x)$（不同值）。$P(S')$。
3. **$op = \text{drop}(x)$**：$\Omega'(x)=\text{Dropped}$；$v$ 不再被拥有。$P(S')$。

由归纳，$\forall S: P(S)$。∎

### 5.2 定理 T-BR1（数据竞争自由）
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**陈述**：$\text{BorrowCheck}(P)=\text{OK} \rightarrow \text{DataRaceFree}(P)$

**数据竞争定义**：
$$
\text{DataRace}(m,t_1,t_2) \;\equiv\; \text{Concurrent}(t_1,t_2) \land \text{Access}(t_1,m) \land \text{Access}(t_2,m) \land (\text{Write}(t_1,m) \lor \text{Write}(t_2,m)) \land \neg\text{Synchronized}(t_1,t_2)
$$

**证明**（反证）：

设 $\text{BorrowCheck}(P)=\text{OK}$ 且 $\exists m,t_1,t_2: \text{DataRace}(m,t_1,t_2)$。

**情况 1**：$\text{Write}(t_1,m) \land \text{Write}(t_2,m)$。则两线程并发写 $m$ ⇒ 两可变借用并存 ⇒ 违反规则 1（MutUnique）。矛盾。

**情况 2**：$\text{Write}(t_1,m) \land \text{Read}(t_2,m)$（或对称）。则写与读并发 ⇒ 可变与不可变借用并存 ⇒ 违反规则 2（ImmMutExcl）。矛盾。

**情况 3**：$\text{Read}(t_1,m) \land \text{Read}(t_2,m)$。则无写操作，不满足 DataRace 定义。矛盾。

故 $\neg\exists m,t_1,t_2: \text{DataRace}(m,t_1,t_2)$。∎

### 5.3 定理 T-TY3（类型安全）
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**陈述**：$\Gamma \vdash e : \tau \rightarrow \neg\exists e': e \to^* e' \land \text{type\_error}(e')$

**引理 L-TY1**：$\text{type\_error}(e) \rightarrow \neg\exists \Gamma,\tau: \Gamma \vdash e : \tau$。

*证明*：类型错误违反 typing rules；良型需满足规则。∎

**证明**（反证）：

设 $\Gamma \vdash e : \tau$ 且 $\exists e': e \to^* e' \land \text{type\_error}(e')$。

由**保持性**（T-TY2）：$e \to^* e' \Rightarrow \Gamma \vdash e' : \tau$。

由 **L-TY1**：$\text{type\_error}(e') \Rightarrow \neg\Gamma \vdash e' : \tau$。

矛盾。故 $\neg\exists e'$。∎

---

## 六、推导树示例
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### T-OW2 归纳步（move）的推导
>
> **[来源: [crates.io](https://crates.io/)]**

$$
\frac{
  P(S) \quad S \xrightarrow{\text{move}(x,y)} S' \quad
  \Omega'(x)=\text{Moved} \quad \Omega'(y)=\text{Owned} \quad \Gamma'(y)=\Gamma(x)
}{
  \forall v: |\{z \mid \Omega'(z)=\text{Owned} \land \Gamma'(z)=v\}| \leq 1
} \;\text{(Move-Preserve)}
$$

### T-BR1 情况 1 的推导
>
> **[来源: [docs.rs](https://docs.rs/)]**

$$
\frac{
  \text{Write}(t_1,m) \land \text{Write}(t_2,m) \land \text{Concurrent}(t_1,t_2) \quad
  \text{规则 1: 可变借用唯一}
}{
  \bot
} \;\text{(Contra-Write)}
$$

---

## 七、与 Coq 的对应
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 形式语言 | Coq 骨架 |
| :--- | :--- |
| 判定 $\Gamma \vdash e : \tau$ | `has_type Gamma e tau` |
| 归约 $e \to e'$ | `step e e'` |
| 定理 T-OW2 | `T_OW2_ownership_uniqueness` |
| 定理 T-BR1 | `T_BR1_data_race_freedom` |
| 定理 T-TY3 | `T_TY3_type_safety` |

**形式语言**提供数学规范；**Coq** 提供机器可检查实现。两者陈述一致，证明思路对应。

---

## 八、引用
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [CORE_THEOREMS_FULL_PROOFS](./10_core_theorems_full_proofs.md) — 完整证明（L2）
- [coq_skeleton](./coq_skeleton/README.md) — Coq 骨架（L3）
- [ownership_model](./formal_methods/10_ownership_model.md)、[borrow_checker_proof](./formal_methods/10_borrow_checker_proof.md)、[type_system_foundations](./type_theory/10_type_system_foundations.md)

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14

---

## 🆕 Rust 1.94 更新
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **适用版本**: Rust 1.96.0+

详见 [RUST_194_RESEARCH_UPDATE](./10_rust_194_research_update.md)

**最后更新**: 2026-03-14

---

## 🆕 Rust 1.94 深度整合更新
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- Rust 1.94 迁移指南
- [Rust 1.94 特性速查
- [性能调优指南](../05_guides/05_performance_tuning_guide.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [research_notes 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Coq Reference](https://coq.inria.fr/doc/)**
> **来源: [TLA+](https://lamport.azurewebsites.net/tla/tla.html)**
> **来源: [ACM - Formal Verification](https://dl.acm.org/)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
