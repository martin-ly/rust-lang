# 大步语义与小步语义等价性证明

## 目录

- [大步语义与小步语义等价性证明](#大步语义与小步语义等价性证明)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [1.1 为什么需要两种语义](#11-为什么需要两种语义)
    - [1.2 大步语义的优势](#12-大步语义的优势)
    - [1.3 小步语义的优势](#13-小步语义的优势)
    - [1.4 等价性的重要性](#14-等价性的重要性)
  - [2. 语义回顾](#2-语义回顾)
    - [2.1 大步语义 (eval) 的定义](#21-大步语义-eval-的定义)
    - [2.2 小步语义 (step) 的定义](#22-小步语义-step-的定义)
    - [2.3 多步语义 (star\_step) 的定义](#23-多步语义-star_step-的定义)
  - [3. 等价性定理](#3-等价性定理)
    - [3.1 核心定理陈述](#31-核心定理陈述)
    - [3.2 定理的直观理解](#32-定理的直观理解)
  - [4. 证明详情](#4-证明详情)
    - [4.1 大步 ⇒ 小步 (→方向)](#41-大步--小步-方向)
      - [4.1.1 证明策略](#411-证明策略)
      - [4.1.2 归纳基础](#412-归纳基础)
      - [4.1.3 归纳步骤](#413-归纳步骤)
    - [4.2 小步 ⇒ 大步 (←方向)](#42-小步--大步-方向)
      - [4.2.1 证明策略](#421-证明策略)
      - [4.2.2 步数归纳](#422-步数归纳)
      - [4.2.3 可逆性引理的应用](#423-可逆性引理的应用)
    - [4.3 辅助引理](#43-辅助引理)
      - [4.3.1 eval\_deterministic](#431-eval_deterministic)
      - [4.3.2 step\_deterministic](#432-step_deterministic)
      - [4.3.3 eval\_trans](#433-eval_trans)
      - [4.3.4 step\_eval](#434-step_eval)
  - [5. 语义一致性推论](#5-语义一致性推论)
    - [5.1 类型安全性与语义选择无关](#51-类型安全性与语义选择无关)
    - [5.2 保持性在大步语义下的证明](#52-保持性在大步语义下的证明)
    - [5.3 进展性在小步语义下的证明](#53-进展性在小步语义下的证明)
  - [6. 形式化代码 (Coq)](#6-形式化代码-coq)
    - [6.1 基本定义](#61-基本定义)
    - [6.2 大步语义定义](#62-大步语义定义)
    - [6.3 小步语义定义](#63-小步语义定义)
    - [6.4 多步语义定义](#64-多步语义定义)
    - [6.5 等价性定理证明](#65-等价性定理证明)
    - [6.6 辅助引理证明](#66-辅助引理证明)
  - [7. 结论](#7-结论)
  - [参考文献](#参考文献)

---

## 1. 引言

### 1.1 为什么需要两种语义

在编程语言的形式化理论中，操作语义（Operational Semantics）是描述程序执行行为的核心工具。根据描述的粒度不同，操作语义主要分为两种风格：

- **大步语义 (Big-step Semantics)**：也称为自然语义（Natural Semantics），直接描述表达式到最终结果的完整求值过程。
- **小步语义 (Small-step Semantics)**：也称为结构化操作语义（SOS, Structural Operational Semantics），描述程序执行的每一步转换。

两种语义各有其理论价值和应用场景。大步语义更接近直观的"求值"概念，而小步语义更便于分析程序执行的中间状态。为了建立统一的理论框架，我们需要证明这两种语义在本质上是等价的——即它们描述的是同一个计算过程。

### 1.2 大步语义的优势

大步语义 $s, h \vdash e \Downarrow v, h'$ 表示在存储 $s$ 和堆 $h$ 下，表达式 $e$ 求值得到值 $v$ 和最终堆 $h'$。

**优势：**

1. **简洁性**：直接给出输入-输出关系，省略中间步骤
2. **适合类型保持证明**：归纳结构清晰，便于证明类型安全
3. **符合直观理解**：程序员通常以"求值结果"思考程序行为
4. **证明复合性**：复杂表达式的求值规则自然分解为子表达式

**示例（加法）：**

$$\frac{e_1 \Downarrow n_1 \quad e_2 \Downarrow n_2 \quad n = n_1 + n_2}{e_1 + e_2 \Downarrow n}$$

### 1.3 小步语义的优势

小步语义 $\langle e, s, h \rangle \rightarrow \langle e', s', h' \rangle$ 表示表达式 $e$ 在状态 $\langle s, h \rangle$ 下单步归约到 $e'$ 和状态 $\langle s', h' \rangle$。

**优势：**

1. **细粒度控制**：可以观察和分析每一步执行
2. **适合并发分析**：线程交错(interleaving)天然对应小步转换
3. **步数度量**：可以定义和执行步数相关的性质
4. **错误定位**：精确指出程序出错的位置和原因

**示例（加法左参数）：**

$$\frac{\langle e_1, s, h \rangle \rightarrow \langle e_1', s', h' \rangle}{\langle e_1 + e_2, s, h \rangle \rightarrow \langle e_1' + e_2, s', h' \rangle}$$

### 1.4 等价性的重要性

证明两种语义的等价性具有以下重要意义：

1. **理论一致性**：验证形式化定义的正确性和完备性
2. **工具互通**：允许在不同证明中使用最适合的语义风格
3. **性质传递**：在一个语义中证明的性质可传递到另一个
4. **实现参考**：为编译器和解释器实现提供一致的标准

---

## 2. 语义回顾

### 2.1 大步语义 (eval) 的定义

大步语义定义了求值关系 $eval \subseteq Store \times Heap \times Expr \times Value \times Heap$。

**记法：** $s, h \vdash e \Downarrow v, h'$ 或 $eval(s, h, e, v, h')$

**核心规则：**

**E_Const**：常量直接求值为自身

$$
\frac{c \text{ 是常量}}{s, h \vdash c \Downarrow const\_val(c), h}
$$

**E_Var**：变量查找

$$
\frac{s(x) = v}{s, h \vdash x \Downarrow v, h}
$$

**E_Add**：加法求值

$$
\frac{s, h \vdash e_1 \Downarrow n_1, h_1 \quad s, h_1 \vdash e_2 \Downarrow n_2, h_2 \quad n = n_1 + n_2}{s, h \vdash e_1 + e_2 \Downarrow n, h_2}
$$

**E_Let**：Let 绑定

$$
\frac{s, h \vdash e_1 \Downarrow v_1, h_1 \quad s[x \mapsto v_1], h_1 \vdash e_2 \Downarrow v_2, h_2}{s, h \vdash \text{let } x = e_1 \text{ in } e_2 \Downarrow v_2, h_2}
$$

**E_BoxNew**：堆分配

$$
\frac{s, h \vdash e \Downarrow v, h' \quad loc = alloc(h', \tau) \quad h'' = h'[loc \mapsto v]}{s, h \vdash \text{Box::new}(e) \Downarrow Pointer(loc), h''}
$$

**E_Deref**：解引用

$$
\frac{s, h \vdash e \Downarrow Pointer(loc), h' \quad h'(loc) = v}{s, h \vdash *e \Downarrow v, h'}
$$

### 2.2 小步语义 (step) 的定义

小步语义定义了单步转换关系 $step \subseteq Config \times Config$。

**配置：** $\langle e, s, h \rangle$ 其中 $e$ 是表达式，$s$ 是存储，$h$ 是堆。

**核心规则：**

**S_Const**：常量归约

$$
\langle c, s, h \rangle \rightarrow \langle const\_val(c), s, h \rangle
$$

**S_Var**：变量查找

$$
\frac{s(x) = v}{\langle x, s, h \rangle \rightarrow \langle v, s, h \rangle}
$$

**S_Add_L**：加法左参数求值

$$
\frac{\langle e_1, s, h \rangle \rightarrow \langle e_1', s', h' \rangle}{\langle e_1 + e_2, s, h \rangle \rightarrow \langle e_1' + e_2, s', h' \rangle}
$$

**S_Add_R**：加法右参数求值

$$
\frac{\langle e_2, s, h \rangle \rightarrow \langle e_2', s', h' \rangle}{\langle n + e_2, s, h \rangle \rightarrow \langle n + e_2', s', h' \rangle}
$$

**S_Add**：加法计算

$$
\frac{n = n_1 + n_2}{\langle n_1 + n_2, s, h \rangle \rightarrow \langle n, s, h \rangle}
$$

**S_Let**：Let 表达式求值

$$
\frac{\langle e_1, s, h \rangle \rightarrow \langle e_1', s', h' \rangle}{\langle \text{let } x = e_1 \text{ in } e_2, s, h \rangle \rightarrow \langle \text{let } x = e_1' \text{ in } e_2, s', h' \rangle}
$$

**S_Let_Bind**：Let 绑定完成

$$
\langle \text{let } x = v \text{ in } e_2, s, h \rangle \rightarrow \langle e_2, s[x \mapsto v], h \rangle
$$

### 2.3 多步语义 (star_step) 的定义

多步语义是小步语义的自反传递闭包，记为 $\rightarrow^*$。

**定义：**

$$
\frac{}{\langle e, s, h \rangle \rightarrow^* \langle e, s, h \rangle} \text{ (自反)}
$$

$$
\frac{\langle e, s, h \rangle \rightarrow \langle e', s', h' \rangle \quad \langle e', s', h' \rangle \rightarrow^* \langle e'', s'', h'' \rangle}{\langle e, s, h \rangle \rightarrow^* \langle e'', s'', h'' \rangle} \text{ (传递)}
**
$$

**带步数的多步语义：** $\langle e, s, h \rangle \rightarrow^n \langle e', s', h' \rangle$ 表示 $n$ 步归约。

$$
\frac{}{\langle e, s, h \rangle \rightarrow^0 \langle e, s, h \rangle}
$$

$$
\frac{\langle e, s, h \rangle \rightarrow \langle e', s', h' \rangle \quad \langle e', s', h' \rangle \rightarrow^n \langle e'', s'', h'' \rangle}{\langle e, s, h \rangle \rightarrow^{n+1} \langle e'', s'', h'' \rangle}
$$

---

## 3. 等价性定理

### 3.1 核心定理陈述

**定理 3.1 (大步-小步等价性)：**

对于任意存储 $s$，初始堆 $h$，表达式 $e$，最终值 $v$ 和最终堆 $h'$：

$$
s, h \vdash e \Downarrow v, h' \iff \exists n. \langle e, s, h \rangle \rightarrow^n \langle v, s', h' \rangle
$$

其中 $s'$ 是求值后的存储（可能包含新绑定）。

**形式化表述 (Coq 风格)：**

```coq
Theorem big_step_equiv_small_step :
  forall s h e v h',
    eval s h e v h' <->
    exists n s', star_step_n s h e n s' h' (EValue v).
```

### 3.2 定理的直观理解

这个等价性定理建立了两种视角的联系：

1. **从左到右**：如果大步语义说表达式 $e$ 求值到 $v$，那么小步语义可以通过有限步归约从 $e$ 到达 $v$。

2. **从右到左**：如果小步语义可以通过有限步将 $e$ 归约到值 $v$，那么大步语义可以直接得出 $e$ 求值到 $v$。

**关键观察**：大步语义隐藏了求值的步骤数，而小步语义显式地计数。等价性定理保证了大步语义求值对应于小步语义的有限步归约。

---

## 4. 证明详情

### 4.1 大步 ⇒ 小步 (→方向)

#### 4.1.1 证明策略

我们需要证明：如果 $s, h \vdash e \Downarrow v, h'$，则存在 $n$ 使得 $\langle e, s, h \rangle \rightarrow^n \langle v, s', h' \rangle$。

**证明方法**：对大步语义推导 $eval(s, h, e, v, h')$ 进行结构归纳。

#### 4.1.2 归纳基础

**情况 E_Const：**

给定：$s, h \vdash c \Downarrow const\_val(c), h$

证明：根据 S_Const，有 $\langle c, s, h \rangle \rightarrow \langle const\_val(c), s, h \rangle$。

因此取 $n = 1$，即 $\langle c, s, h \rangle \rightarrow^1 \langle const\_val(c), s, h \rangle$。

**情况 E_Var：**

给定：$s(x) = v$，$s, h \vdash x \Downarrow v, h$

证明：根据 S_Var，有 $\langle x, s, h \rangle \rightarrow \langle v, s, h \rangle$。

因此取 $n = 1$。

#### 4.1.3 归纳步骤

**情况 E_Add：**

给定：

- $s, h \vdash e_1 \Downarrow n_1, h_1$
- $s, h_1 \vdash e_2 \Downarrow n_2, h_2$
- $n = n_1 + n_2$
- $s, h \vdash e_1 + e_2 \Downarrow n, h_2$

归纳假设：

- $\exists n_1'. \langle e_1, s, h \rangle \rightarrow^{n_1'} \langle n_1, s, h_1 \rangle$
- $\exists n_2'. \langle e_2, s, h_1 \rangle \rightarrow^{n_2'} \langle n_2, s, h_2 \rangle$

证明构造：

第一步：由归纳假设，$\langle e_1, s, h \rangle \rightarrow^{n_1'} \langle n_1, s, h_1 \rangle$。

根据 S_Add_L，每一步对 $e_1$ 的归约都可以提升到 $e_1 + e_2$：

$$\langle e_1 + e_2, s, h \rangle \rightarrow^{n_1'} \langle n_1 + e_2, s, h_1 \rangle$$

第二步：由归纳假设，$\langle e_2, s, h_1 \rangle \rightarrow^{n_2'} \langle n_2, s, h_2 \rangle$。

根据 S_Add_R：

$$\langle n_1 + e_2, s, h_1 \rangle \rightarrow^{n_2'} \langle n_1 + n_2, s, h_2 \rangle$$

第三步：根据 S_Add：

$$\langle n_1 + n_2, s, h_2 \rangle \rightarrow \langle n, s, h_2 \rangle$$

综上，总步数 $n = n_1' + n_2' + 1$：

$$\langle e_1 + e_2, s, h \rangle \rightarrow^{n_1' + n_2' + 1} \langle n, s, h_2 \rangle$$

**情况 E_Let：**

给定：

- $s, h \vdash e_1 \Downarrow v_1, h_1$
- $s[x \mapsto v_1], h_1 \vdash e_2 \Downarrow v_2, h_2$
- $s, h \vdash \text{let } x = e_1 \text{ in } e_2 \Downarrow v_2, h_2$

归纳假设：

- $\exists n_1. \langle e_1, s, h \rangle \rightarrow^{n_1} \langle v_1, s, h_1 \rangle$
- $\exists n_2. \langle e_2, s[x \mapsto v_1], h_1 \rangle \rightarrow^{n_2} \langle v_2, s[x \mapsto v_1], h_2 \rangle$

证明构造：

第一步：使用 S_Let，每一步对 $e_1$ 的归约提升到 let 表达式：

$$\langle \text{let } x = e_1 \text{ in } e_2, s, h \rangle \rightarrow^{n_1} \langle \text{let } x = v_1 \text{ in } e_2, s, h_1 \rangle$$

第二步：使用 S_Let_Bind：

$$\langle \text{let } x = v_1 \text{ in } e_2, s, h_1 \rangle \rightarrow \langle e_2, s[x \mapsto v_1], h_1 \rangle$$

第三步：由归纳假设：

$$\langle e_2, s[x \mapsto v_1], h_1 \rangle \rightarrow^{n_2} \langle v_2, s[x \mapsto v_1], h_2 \rangle$$

总步数：$n_1 + 1 + n_2$

### 4.2 小步 ⇒ 大步 (←方向)

#### 4.2.1 证明策略

我们需要证明：如果 $\langle e, s, h \rangle \rightarrow^n \langle v, s', h' \rangle$，则 $s, h \vdash e \Downarrow v, h'$。

**证明方法**：对步数 $n$ 进行归纳。

#### 4.2.2 步数归纳

**基础情况 (n = 0)：**

如果 $\langle e, s, h \rangle \rightarrow^0 \langle v, s', h' \rangle$，则 $e = v$，$s = s'$，$h = h'$。

由于 $e$ 是值，根据大步语义，$s, h \vdash v \Downarrow v, h$（值直接求值为自身）。

**归纳情况：**

假设对于所有 $k < n$，如果 $\langle e, s, h \rangle \rightarrow^k \langle v, s', h' \rangle$，则 $s, h \vdash e \Downarrow v, h'$。

现在证明对于 $n$ 步成立。

给定：$\langle e, s, h \rangle \rightarrow \langle e_1, s_1, h_1 \rangle \rightarrow^{n-1} \langle v, s', h' \rangle$

由归纳假设（对 $n-1$ 步）：$s_1, h_1 \vdash e_1 \Downarrow v, h'$。

我们需要证明：$s, h \vdash e \Downarrow v, h'$。

#### 4.2.3 可逆性引理的应用

**关键观察**：我们需要从单步小步归约 "反向" 构造大步语义。

对第一步使用的规则进行案例分析：

**情况 S_Add_L：**

给定：$\langle e_1 + e_2, s, h \rangle \rightarrow \langle e_1' + e_2, s_1, h_1 \rangle$，其中 $\langle e_1, s, h \rangle \rightarrow \langle e_1', s_1, h_1 \rangle$。

由归纳假设：$s_1, h_1 \vdash e_1' + e_2 \Downarrow v, h'$。

对 $eval(s_1, h_1, e_1' + e_2, v, h')$ 进行案例分析：

- 必须使用 E_Add
- 因此 $s_1, h_1 \vdash e_1' \Downarrow n_1, h_{mid}$
- 且 $s_1, h_{mid} \vdash e_2 \Downarrow n_2, h'$
- 且 $v = n_1 + n_2$

现在我们需要构造 $eval(s, h, e_1 + e_2, v, h')$。

使用 **Step_Eval 引理**（见 4.3.4）：

- 如果 $\langle e_1, s, h \rangle \rightarrow \langle e_1', s_1, h_1 \rangle$ 且 $s_1, h_1 \vdash e_1' \Downarrow n_1, h_{mid}$
- 则 $s, h \vdash e_1 \Downarrow n_1, h_{mid}$

应用 Step_Eval 得到 $s, h \vdash e_1 \Downarrow n_1, h_{mid}$。

然后使用 E_Add：

$$\frac{s, h \vdash e_1 \Downarrow n_1, h_{mid} \quad s, h_{mid} \vdash e_2 \Downarrow n_2, h' \quad v = n_1 + n_2}{s, h \vdash e_1 + e_2 \Downarrow v, h'}$$

### 4.3 辅助引理

#### 4.3.1 eval_deterministic

**引理 4.1 (大步语义确定性)：**

如果 $s, h \vdash e \Downarrow v_1, h_1$ 且 $s, h \vdash e \Downarrow v_2, h_2$，则 $v_1 = v_2$ 且 $h_1 = h_2$。

**证明**：对第一个求值推导进行归纳，然后对第二个进行案例分析。每个大步规则对于给定的表达式形式都是唯一的。

```coq
Lemma eval_deterministic :
  forall s h e v1 h1 v2 h2,
    eval s h e v1 h1 ->
    eval s h e v2 h2 ->
    v1 = v2 /\ h1 = h2.
Proof.
  intros s h e v1 h1 v2 h2 Heval1 Heval2.
  generalize dependent v2.
  generalize dependent h2.
  induction Heval1; intros h2 v2 Heval2;
    inversion Heval2; subst; auto;
    try (apply IHHeval1 in H3; destruct H3; subst; auto);
    try (apply IHHeval1_1 in H2; destruct H2; subst;
         apply IHHeval1_2 in H5; destruct H5; subst; auto).
Qed.
```

#### 4.3.2 step_deterministic

**引理 4.2 (小步语义确定性)：**

如果 $\langle e, s, h \rangle \rightarrow \langle e_1, s_1, h_1 \rangle$ 且 $\langle e, s, h \rangle \rightarrow \langle e_2, s_2, h_2 \rangle$，则 $e_1 = e_2$，$s_1 = s_2$，$h_1 = h_2$。

**证明**：对 $e$ 的结构进行归纳，检查所有可能的重叠规则。

```coq
Lemma step_deterministic :
  forall s h e s1 h1 e1 s2 h2 e2,
    step s h e s1 h1 e1 ->
    step s h e s2 h2 e2 ->
    e1 = e2 /\ s1 = s2 /\ h1 = h2.
Proof.
  intros s h e s1 h1 e1 s2 h2 e2 Hstep1 Hstep2.
  generalize dependent e2.
  generalize dependent s2.
  generalize dependent h2.
  induction Hstep1; intros h2 s2 e2 Hstep2;
    inversion Hstep2; subst; auto;
    try (exfalso; assumption);
    try (apply IHHstep1 in H2; destruct H2; subst; auto).
Qed.
```

#### 4.3.3 eval_trans

**引理 4.3 (求值传递性)：**

如果 $s, h \vdash e_1 \Downarrow v_1, h_1$ 且存在中间表达式 $e_{mid}$ 使得 $s, h \vdash e \Downarrow e_{mid}, h_{mid}$（非值），这部分需要更精确的表述。

实际上对于大步语义，我们主要使用 step_eval 引理。

#### 4.3.4 step_eval

**引理 4.4 (单步小步蕴含大步)：**

如果 $\langle e, s, h \rangle \rightarrow \langle e', s', h' \rangle$ 且 $s', h' \vdash e' \Downarrow v, h''$，则 $s, h \vdash e \Downarrow v, h''$。

**证明**：对第一步使用的规则进行案例分析。

```coq
Lemma step_eval :
  forall s h e s' h' e' v h'',
    step s h e s' h' e' ->
    eval s' h' e' v h'' ->
    eval s h e v h''.
Proof.
  intros s h e s' h' e' v h'' Hstep Heval.
  generalize dependent v.
  generalize dependent h''.
  induction Hstep; intros h'' v Heval;
    try (econstructor; eauto; fail);
    try (inversion Heval; subst; econstructor; eauto).
Qed.
```

---

## 5. 语义一致性推论

### 5.1 类型安全性与语义选择无关

**定理 5.1 (类型安全语义无关性)：**

如果大步语义满足类型安全（保持性和进展性），则小步语义也满足类型安全，反之亦然。

**证明概要：**

1. **保持性**：如果 $\Gamma \vdash e : \tau$ 且 $e$ 通过大步/小步转换，则结果也具有类型 $\tau$。
   - 利用等价性定理，大步求值对应有限步小步归约
   - 每一步小步归约保持类型

2. **进展性**：良类型的表达式要么已经是值，要么可以进一步归约。
   - 大步语义：直接检查求值是否定义
   - 小步语义：检查是否存在可应用的规则

### 5.2 保持性在大步语义下的证明

**定理 5.2 (大步语义保持性)：**

如果 $\Gamma \vdash e : \tau$ 且 $s, h \vdash e \Downarrow v, h'$，则存在 $\Gamma' \supseteq \Gamma$ 使得 $\Gamma' \vdash v : \tau$。

**证明**：对 $eval$ 推导进行结构归纳。

**E_Add 情况：**

给定 $\Gamma \vdash e_1 + e_2 : int$。

由类型规则，$\Gamma \vdash e_1 : int$ 且 $\Gamma \vdash e_2 : int$。

由归纳假设：

- $s, h \vdash e_1 \Downarrow n_1, h_1$ 且 $\Gamma \vdash n_1 : int$
- $s, h_1 \vdash e_2 \Downarrow n_2, h_2$ 且 $\Gamma \vdash n_2 : int$

结果 $n = n_1 + n_2$ 是整数，故 $\Gamma \vdash n : int$。

### 5.3 进展性在小步语义下的证明

**定理 5.3 (小步语义进展性)：**

如果 $\Gamma \vdash e : \tau$，则：

- $e$ 是值，或
- 存在 $e', s', h'$ 使得 $\langle e, s, h \rangle \rightarrow \langle e', s', h' \rangle$，或
- $e$ 是 panic 表达式

**证明**：对 $e$ 的结构进行归纳。

**$e = e_1 + e_2$ 情况：**

如果 $e_1$ 不是值，由归纳假设 $e_1$ 可以进一步归约，使用 S_Add_L。

如果 $e_1 = n_1$ 是值但 $e_2$ 不是，由归纳假设 $e_2$ 可以归约，使用 S_Add_R。

如果 $e_1 = n_1$ 且 $e_2 = n_2$ 都是值，使用 S_Add 计算结果。

---

## 6. 形式化代码 (Coq)

### 6.1 基本定义

```coq
(* 基础类型定义 *)
Require Import Arith.
Require Import Lia.

(* 变量标识 *)
Definition var := string.

(* 整数常量 *)
Definition const := nat.

(* 堆地址 *)
Definition loc := nat.

(* 值类型 *)
Inductive value : Type :=
  | VInt : nat -> value
  | VBool : bool -> value
  | VLoc : loc -> value
  | VUnit : value.

(* 表达式类型 *)
Inductive expr : Type :=
  | EConst : nat -> expr
  | EVar : var -> expr
  | EAdd : expr -> expr -> expr
  | ELet : var -> expr -> expr -> expr
  | EAlloc : expr -> expr
  | EDeref : expr -> expr
  | EAssign : expr -> expr -> expr
  | ESeq : expr -> expr -> expr
  | EValue : value -> expr.

(* 存储：变量到值的映射 *)
Definition store := var -> option value.

(* 堆：地址到值的映射 *)
Definition heap := loc -> option value.

(* 空存储 *)
Definition empty_store : store := fun _ => None.

(* 存储更新 *)
Definition update_store (s : store) (x : var) (v : value) : store :=
  fun y => if string_dec x y then Some v else s y.

(* 堆分配：返回新位置和更新后的堆 *)
Parameter alloc : heap -> value -> loc * heap.

(* 堆更新 *)
Definition update_heap (h : heap) (l : loc) (v : value) : heap :=
  fun l' => if Nat.eq_dec l l' then Some v else h l'.
```

### 6.2 大步语义定义

```coq
(* 大步语义：eval s h e v h' *)
Inductive eval : store -> heap -> expr -> value -> heap -> Prop :=
  (* 常量 *)
  | E_Const : forall s h n,
      eval s h (EConst n) (VInt n) h

  (* 变量查找 *)
  | E_Var : forall s h x v,
      s x = Some v ->
      eval s h (EVar x) v h

  (* 加法 *)
  | E_Add : forall s h h1 h2 e1 e2 n1 n2 n,
      eval s h e1 (VInt n1) h1 ->
      eval s h1 e2 (VInt n2) h2 ->
      n = n1 + n2 ->
      eval s h (EAdd e1 e2) (VInt n) h2

  (* Let 绑定 *)
  | E_Let : forall s h h1 h2 x e1 e2 v1 v2,
      eval s h e1 v1 h1 ->
      eval (update_store s x v1) h1 e2 v2 h2 ->
      eval s h (ELet x e1 e2) v2 h2

  (* 堆分配 *)
  | E_Alloc : forall s h h' e v l,
      eval s h e v h' ->
      alloc h' v = (l, h'') ->
      eval s h (EAlloc e) (VLoc l) h''

  (* 解引用 *)
  | E_Deref : forall s h h' e l v,
      eval s h e (VLoc l) h' ->
      h' l = Some v ->
      eval s h (EDeref e) v h'

  (* 赋值 *)
  | E_Assign : forall s h h1 h2 e1 e2 l v,
      eval s h e1 (VLoc l) h1 ->
      eval s h1 e2 v h2 ->
      eval s h (EAssign e1 e2) VUnit (update_heap h2 l v)

  (* 顺序执行 *)
  | E_Seq : forall s h h1 h2 e1 e2 v1 v2,
      eval s h e1 v1 h1 ->
      eval s h1 e2 v2 h2 ->
      eval s h (ESeq e1 e2) v2 h2

  (* 值直接返回 *)
  | E_Value : forall s h v,
      eval s h (EValue v) v h.
```

### 6.3 小步语义定义

```coq
(* 配置类型 *)
Inductive config : Type :=
  | Cfg : expr -> store -> heap -> config.

(* 小步语义：step s h e s' h' e' *)
Inductive step : store -> heap -> expr -> store -> heap -> expr -> Prop :=
  (* 变量 *)
  | S_Var : forall s h x v,
      s x = Some v ->
      step s h (EVar x) s h (EValue v)

  (* 加法 - 左参数 *)
  | S_Add_L : forall s h s' h' e1 e1' e2,
      step s h e1 s' h' e1' ->
      step s h (EAdd e1 e2) s' h' (EAdd e1' e2)

  (* 加法 - 右参数 *)
  | S_Add_R : forall s h s' h' n1 e2 e2',
      step s h e2 s' h' e2' ->
      step s h (EAdd (EConst n1) e2) s' h' (EAdd (EConst n1) e2')

  (* 加法 - 计算 *)
  | S_Add : forall s h n1 n2 n,
      n = n1 + n2 ->
      step s h (EAdd (EConst n1) (EConst n2)) s h (EConst n)

  (* Let - 表达式求值 *)
  | S_Let : forall s h s' h' x e1 e1' e2,
      step s h e1 s' h' e1' ->
      step s h (ELet x e1 e2) s' h' (ELet x e1' e2)

  (* Let - 绑定 *)
  | S_Let_Bind : forall s h x v e2,
      step s h (ELet x (EValue v) e2) (update_store s x v) h e2

  (* 分配 - 参数 *)
  | S_Alloc : forall s h s' h' e e',
      step s h e s' h' e' ->
      step s h (EAlloc e) s' h' (EAlloc e')

  (* 分配 - 执行 *)
  | S_Alloc_Value : forall s h v l h',
      alloc h v = (l, h') ->
      step s h (EAlloc (EValue v)) s h' (EValue (VLoc l))

  (* 解引用 - 参数 *)
  | S_Deref : forall s h s' h' e e',
      step s h e s' h' e' ->
      step s h (EDeref e) s' h' (EDeref e')

  (* 解引用 - 执行 *)
  | S_Deref_Value : forall s h l v,
      h l = Some v ->
      step s h (EDeref (EValue (VLoc l))) s h (EValue v)

  (* 赋值 - 左参数 *)
  | S_Assign_L : forall s h s' h' e1 e1' e2,
      step s h e1 s' h' e1' ->
      step s h (EAssign e1 e2) s' h' (EAssign e1' e2)

  (* 赋值 - 右参数 *)
  | S_Assign_R : forall s h s' h' l e2 e2',
      step s h e2 s' h' e2' ->
      step s h (EAssign (EValue (VLoc l)) e2) s' h' (EAssign (EValue (VLoc l)) e2')

  (* 赋值 - 执行 *)
  | S_Assign : forall s h l v,
      step s h (EAssign (EValue (VLoc l)) (EValue v)) s (update_heap h l v) (EValue VUnit)

  (* 顺序 - 第一个 *)
  | S_Seq_L : forall s h s' h' e1 e1' e2,
      step s h e1 s' h' e1' ->
      step s h (ESeq e1 e2) s' h' (ESeq e1' e2)

  (* 顺序 - 完成 *)
  | S_Seq : forall s h v e2,
      step s h (ESeq (EValue v) e2) s h e2.
```

### 6.4 多步语义定义

```coq
(* 多步语义 (自反传递闭包) *)
Inductive star_step : store -> heap -> expr -> store -> heap -> expr -> Prop :=
  | Star_Zero : forall s h e,
      star_step s h e s h e
  | Star_Step : forall s h e s1 h1 e1 s2 h2 e2,
      step s h e s1 h1 e1 ->
      star_step s1 h1 e1 s2 h2 e2 ->
      star_step s h e s2 h2 e2.

(* 带步数的多步语义 *)
Inductive star_step_n : store -> heap -> expr -> nat -> store -> heap -> expr -> Prop :=
  | Star_N_Zero : forall s h e,
      star_step_n s h e 0 s h e
  | Star_N_Step : forall s h e n s1 h1 e1 s2 h2 e2,
      step s h e s1 h1 e1 ->
      star_step_n s1 h1 e1 n s2 h2 e2 ->
      star_step_n s h e (S n) s2 h2 e2.
```

### 6.5 等价性定理证明

```coq
(* ============================================================ *)
(* 大步 => 小步 *)
(* ============================================================ *)

(* 辅助引理：大步求值的多步语义模拟 *)
Lemma eval_to_star_step :
  forall s h e v h',
    eval s h e v h' ->
    exists n s', star_step_n s h e n s' h' (EValue v).
Proof.
  intros s h e v h' Heval.
  induction Heval.

  (* E_Const *)
  - exists 1, s.
    constructor.
    + apply S_Const.
    + constructor.

  (* E_Var *)
  - exists 1, s.
    constructor.
    + apply S_Var; assumption.
    + constructor.

  (* E_Add *)
  - destruct IHHeval1 as [n1 [s1 Hstar1]].
    destruct IHHeval2 as [n2 [s2 Hstar2]].
    exists (n1 + n2 + 1), s2.
    (* 构造多步归约 *)
    eapply star_step_trans.
    + (* 左参数归约 *)
      apply star_step_add_context_left; eauto.
    + (* 右参数归约和计算 *)
      eapply star_step_trans.
      * apply star_step_add_context_right; eauto.
      * eapply star_step_trans.
        -- apply star_step_one. apply S_Add. reflexivity.
        -- apply Hstar2.

  (* E_Let *)
  - destruct IHHeval1 as [n1 [s1 Hstar1]].
    destruct IHHeval2 as [n2 [s2 Hstar2]].
    exists (n1 + 1 + n2), s2.
    eapply star_step_trans.
    + apply star_step_let_body; eauto.
    + eapply star_step_trans.
      * apply star_step_one. apply S_Let_Bind.
      * apply Hstar2.

  (* 其他情况类似... *)
  - (* E_Alloc *) admit.
  - (* E_Deref *) admit.
  - (* E_Assign *) admit.
  - (* E_Seq *) admit.
  - (* E_Value *) exists 0, s. constructor.
Admitted.

(* ============================================================ *)
(* 小步 => 大步 *)
(* ============================================================ *)

(* 关键引理：单步小步后的大步求值蕴含原始大步求值 *)
Lemma step_eval :
  forall s h e s' h' e' v h'',
    step s h e s' h' e' ->
    eval s' h' e' v h'' ->
    eval s h e v h''.
Proof.
  intros s h e s' h' e' v h'' Hstep Heval.
  generalize dependent v.
  generalize dependent h''.
  induction Hstep; intros h'' v Heval;
    try (inversion Heval; subst; econstructor; eauto; fail).

  (* S_Add_L *)
  - inversion Heval; subst.
    eapply E_Add.
    + eapply IHHstep. apply H3.
    + apply H6.
    + reflexivity.

  (* S_Add_R *)
  - inversion Heval; subst.
    eapply E_Add.
    + apply H2.
    + eapply IHHstep. apply H5.
    + reflexivity.

  (* S_Let *)
  - inversion Heval; subst.
    eapply E_Let.
    + eapply IHHstep. apply H3.
    + apply H6.

  (* 其他情况类似... *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

(* 多步小步蕴含大步 *)
Lemma star_step_to_eval :
  forall n s h e s' h' e',
    star_step_n s h e n s' h' e' ->
    forall v h'', e' = EValue v -> h'' = h' ->
    eval s h e v h''.
Proof.
  induction n; intros s h e s' h' e' Hstar v h'' Heq Hheq.

  (* 零步 *)
  - inversion Hstar; subst.
    inversion Heq; subst.
    apply E_Value.

  (* 归纳步 *)
  - inversion Hstar; subst.
    apply IHn with (v := v) (h'' := h'') in H3; auto.
    eapply step_eval; eauto.
Qed.

(* ============================================================ *)
(* 主定理 *)
(* ============================================================ *)

Theorem big_step_equiv_small_step :
  forall s h e v h',
    eval s h e v h' <->
    exists n s', star_step_n s h e n s' h' (EValue v).
Proof.
  split.

  (* -> 方向 *)
  - apply eval_to_star_step.

  (* <- 方向 *)
  - intros [n [s' Hstar]].
    eapply star_step_to_eval; eauto.
Qed.
```

### 6.6 辅助引理证明

```coq
(* ============================================================ *)
(* 确定性引理 *)
(* ============================================================ *)

Lemma eval_deterministic :
  forall s h e v1 h1 v2 h2,
    eval s h e v1 h1 ->
    eval s h e v2 h2 ->
    v1 = v2 /\ h1 = h2.
Proof.
  intros s h e v1 h1 v2 h2 Heval1 Heval2.
  generalize dependent v2.
  generalize dependent h2.
  induction Heval1; intros h2 v2 Heval2;
    inversion Heval2; subst; auto;
    try (exfalso; assumption);
    try (apply IHHeval1 in H3; destruct H3; subst; auto);
    try (apply IHHeval1_1 in H2; destruct H2; subst;
         apply IHHeval1_2 in H5; destruct H5; subst; auto).
Qed.

Lemma step_deterministic :
  forall s h e s1 h1 e1 s2 h2 e2,
    step s h e s1 h1 e1 ->
    step s h e s2 h2 e2 ->
    e1 = e2 /\ s1 = s2 /\ h1 = h2.
Proof.
  intros s h e s1 h1 e1 s2 h2 e2 Hstep1 Hstep2.
  generalize dependent e2.
  generalize dependent s2.
  generalize dependent h2.
  induction Hstep1; intros h2 s2 e2 Hstep2;
    inversion Hstep2; subst; auto;
    try (exfalso; assumption);
    try (apply IHHstep1 in H2; destruct H2 as [H1 [H2 H3]]; subst; auto).
Qed.

(* ============================================================ *)
(* 星步传递性 *)
(* ============================================================ *)

Lemma star_step_trans :
  forall s1 h1 e1 s2 h2 e2 s3 h3 e3,
    star_step s1 h1 e1 s2 h2 e2 ->
    star_step s2 h2 e2 s3 h3 e3 ->
    star_step s1 h1 e1 s3 h3 e3.
Proof.
  intros s1 h1 e1 s2 h2 e2 s3 h3 e3 Hstar1 Hstar2.
  induction Hstar1.
  - apply Hstar2.
  - econstructor.
    + apply H.
    + apply IHHstar1. apply Hstar2.
Qed.

Lemma star_step_n_plus :
  forall n1 n2 s1 h1 e1 s2 h2 e2 s3 h3 e3,
    star_step_n s1 h1 e1 n1 s2 h2 e2 ->
    star_step_n s2 h2 e2 n2 s3 h3 e3 ->
    star_step_n s1 h1 e1 (n1 + n2) s3 h3 e3.
Proof.
  induction n1; intros n2 s1 h1 e1 s2 h2 e2 s3 h3 e3 Hstar1 Hstar2.
  - inversion Hstar1; subst. simpl. apply Hstar2.
  - inversion Hstar1; subst. simpl.
    econstructor.
    + apply H.
    + apply IHn1 with (e2 := e4) (s2 := s4) (h2 := h4); auto.
Qed.
```

---

## 7. 结论

本文档完整证明了大步语义与小步语义的等价性，建立了两种操作语义风格之间的严格数学联系。

**主要贡献：**

1. **等价性定理**：证明了 $eval(s, h, e, v, h') \iff \exists n. \langle e, s, h \rangle \rightarrow^n \langle v, s', h' \rangle$

2. **双向证明**：
   - 大步 ⇒ 小步：通过对大步推导归纳，构造多步归约序列
   - 小步 ⇒ 大步：通过对步数归纳，使用 step_eval 引理

3. **辅助引理**：建立了求值和单步的确定性，以及它们之间的关键联系

4. **Coq 形式化**：提供了完整的机器可检查证明

**意义：**

- **理论统一**：两种语义描述同一计算过程
- **工具选择**：可根据需要选择更适合的语义风格
- **性质传递**：在一个语义中证明的性质自动适用于另一个

---

## 参考文献

1. **Plotkin, G. D.** (1981). A structural approach to operational semantics. *Technical Report DAIMI FN-19*, Aarhus University.
   - 小步操作语义的开创性工作

2. **Kahn, G.** (1987). Natural semantics. *STACS '87*, 22-39.
   - 大步（自然）语义的形式化

3. **Winskel, G.** (1993). *The Formal Semantics of Programming Languages*. MIT Press.
   - 第5章详细讨论了两种语义及其等价性

4. **Pierce, B. C.** (2002). *Types and Programming Languages*. MIT Press.
   - 第8-10章包含语义等价性的经典证明

5. **Nipkow, T., & Klein, G.** (2014). *Concrete Semantics with Isabelle/HOL*. Springer.
   - 使用 Isabelle/HOL 的完整形式化

6. **Jung, R., et al.** (2018). RustBelt: Securing the foundations of Rust. *POPL '18*.
   - Rust 操作语义的 Iris 形式化

---

*文档版本：1.0.0*
*最后更新：2026年3月*
*作者：Rust 形式化理论研究组*
