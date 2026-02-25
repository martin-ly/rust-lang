# 形式语言与形式证明

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 用形式语言（推理规则、操作语义、判定形式）表达 Rust 核心定理，提供数学级形式证明；与 Coq 骨架互补（形式语言为规范，Coq 为机器可检查实现）
> **上位文档**: [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md)、[FORMAL_FULL_MODEL_OVERVIEW](./FORMAL_FULL_MODEL_OVERVIEW.md)

---

## 一、形式语言总览

本文档采用**标准 PL 形式化风格**（TAPL、RustBelt）：

| 层次 | 形式 | 说明 |
| :--- | :--- | :--- |
| **语法** | BNF / 归纳定义 | 表达式、类型、程序 |
| **判定形式** | $\mathcal{J}$ 形式 | 类型判定、借用判定、状态判定 |
| **推理规则** | $\frac{\text{前提}}{\text{结论}}$ | 良构、良型、可达 |
| **操作语义** | $e \to e'$、$S \xrightarrow{op} S'$ | 小步归约、状态转换 |
| **形式证明** | 归纳、反证、推导树 | 定理的数学证明 |

**与 Rust 的衔接**：形式语言为**数学规范层**；Rust 示例为**实现层**；见 [THEOREM_RUST_EXAMPLE_MAPPING](./THEOREM_RUST_EXAMPLE_MAPPING.md)。

---

## 二、语法（归纳定义）

### 2.1 核心表达式（简化）

$$
\begin{aligned}
e \mathrel{::=} &\; x \mid v \mid e_1\; e_2 \mid \lambda x{:}\tau.\, e \mid \textbf{let}\; x = e_1\;\textbf{in}\; e_2 \\
v \mathrel{::=} &\; n \mid \textbf{true} \mid \textbf{false} \mid \lambda x{:}\tau.\, e \\
\tau \mathrel{::=} &\; \textbf{Int} \mid \textbf{Bool} \mid \tau_1 \to \tau_2
\end{aligned}
$$

### 2.2 所有权状态

$$
\Omega(x) \in \{\text{Owned}, \text{Moved}, \text{Dropped}\}
$$

### 2.3 借用类型

$$
B \mathrel{::=} \text{Immutable} \mid \text{Mutable}
$$

---

## 三、判定形式与推理规则

### 3.1 类型判定

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

**判定形式**：$(\Gamma, \Omega) \vdash_{\text{own}} \text{ok}$（所有权配置良构）

**规则**：

$$
\frac{}{\Gamma, \Omega \vdash_{\text{own}} \text{ok}} \;\text{(Init)}
\quad
\frac{\Omega(x) = \text{Owned} \quad \forall y \neq x.\, \Omega(y) \neq \text{Owned} \lor \Gamma(y) \neq \Gamma(x)}{(\Gamma, \Omega) \vdash_{\text{own}} \text{ok}} \;\text{(Unique)}
$$

### 3.3 借用判定

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

### 4.1 类型系统归约

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

**转换关系**：$(\Gamma, \Omega) \xrightarrow{op} (\Gamma', \Omega')$

| 操作 $op$ | 前提 | 效果 |
| :--- | :--- | :--- |
| $\text{move}(x, y)$ | $\Omega(x) = \text{Owned}$ | $\Omega'(x) = \text{Moved}$, $\Omega'(y) = \text{Owned}$, $\Gamma'(y) = \Gamma(x)$ |
| $\text{copy}(x, y)$ | $\Gamma(x) : \text{Copy}$ | $\Gamma'(y) = \text{copy}(\Gamma(x))$；$\Omega$ 不变 |
| $\text{drop}(x)$ | 作用域结束 | $\Omega'(x) = \text{Dropped}$ |

---

## 五、形式证明（数学级）

### 5.1 定理 T-OW2（所有权唯一性）

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

### T-OW2 归纳步（move）的推导

$$
\frac{
  P(S) \quad S \xrightarrow{\text{move}(x,y)} S' \quad
  \Omega'(x)=\text{Moved} \quad \Omega'(y)=\text{Owned} \quad \Gamma'(y)=\Gamma(x)
}{
  \forall v: |\{z \mid \Omega'(z)=\text{Owned} \land \Gamma'(z)=v\}| \leq 1
} \;\text{(Move-Preserve)}
$$

### T-BR1 情况 1 的推导

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

- [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md) — 完整证明（L2）
- [coq_skeleton](./coq_skeleton/) — Coq 骨架（L3）
- [ownership_model](./formal_methods/ownership_model.md)、[borrow_checker_proof](./formal_methods/borrow_checker_proof.md)、[type_system_foundations](./type_theory/type_system_foundations.md)

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
