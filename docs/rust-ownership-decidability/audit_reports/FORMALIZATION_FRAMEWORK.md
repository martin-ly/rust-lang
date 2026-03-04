# Rust所有权与可判定性 - 形式化框架规范

> 本文档定义整个系列的形式化标准和数学符号体系

---

## 1. 形式化语言层次

```text
┌─────────────────────────────────────────────────────────────────┐
│ Layer 4: Rust Source (用户代码)                                  │
│ 例: let x = String::from("hello");                               │
├─────────────────────────────────────────────────────────────────┤
│ Layer 3: MIR (Rust中级中间表示)                                  │
│ 例: _1 = String::from(const "hello") -> bb1;                     │
├─────────────────────────────────────────────────────────────────┤
│ Layer 2: λRust (RustBelt核心语言)                                │
│ 例: let x = new(String::from("hello")) in ...                    │
├─────────────────────────────────────────────────────────────────┤
│ Layer 1: Iris分离逻辑 (断言和规范)                               │
│ 例: ∃ℓ. ℓ ↦ "hello" * String.own(ℓ)                            │
├─────────────────────────────────────────────────────────────────┤
│ Layer 0: Coq/Lean (机器检验证明)                                 │
│ 例: Lemma memory_safety: forall e, typed e -> safe e.            │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. 数学符号规范

### 2.1 元变量命名约定

| 符号 | 含义 | 例子 |
|------|------|------|
| x, y, z | 程序变量 | x: String |
| α, β, γ | 类型变量 | ∀α. α → α |
| ℓ, m, n | 内存位置 | ℓ ↦ v |
| τ, σ | 类型 | τ₁ → τ₂ |
| Γ, Δ | 类型环境 | Γ ⊢ e : τ |
| Σ | 堆/存储 | Σ: Loc → Val |
| ρ | 区域/生命周期 | ρ₁ ⊆ ρ₂ |
| t, u | 线程ID | t ∈ ThreadID |
| v | 值 | v ∈ Val |
| e | 表达式 | e ∈ Expr |

### 2.2 逻辑符号

| 符号 | LaTeX | 含义 | 读法 |
|------|-------|------|------|
| ⊢ | \vdash | 推导 | "turnstile" |
| ⊨ | \vDash | 满足 | "models" |
| ∈ | \in | 属于 | "in" |
| ∀ | \forall | 全称量词 | "for all" |
| ∃ | \exists | 存在量词 | "exists" |
| → | \rightarrow | 蕴含 | "implies" |
| ∧ | \wedge | 合取 | "and" |
| ∨ | \vee | 析取 | "or" |
| ¬ | \neg | 否定 | "not" |
| ⊤ | \top | 真 | "true" |
| ⊥ | \bot | 假/矛盾 | "false" |
| ≡ | \equiv | 定义相等 | "defined as" |
| ≜ | \triangleq | 定义为 | "defined to be" |

### 2.3 分离逻辑符号

| 符号 | LaTeX | 含义 | 读法 |
|------|-------|------|------|
| * | * | 分离合取 | "star" / "separating conjunction" |
| -* | -* | 分离蕴含/Magic Wand | "magic wand" |
| ↦ | \mapsto | 指向 | "points to" |
| ▷ | \triangleright | 稍后模态 | "later" |
| □ | \Box | 持久性 | "persistently" |
| ◇ | \Diamond | 更新模态 | "update" |
| ∅ | \emptyset | 空资源 | "emp" |

### 2.4 类型理论符号

| 符号 | LaTeX | 含义 | 读法 |
|------|-------|------|------|
| → | \rightarrow | 函数类型 | "function" |
| × | \times | 乘积类型 | "product" |
| + | + | 和类型 | "sum" |
| ⊸ | \multimap | 线性函数 | "lollipop" |
| ⊗ | \otimes | 张量积 | "tensor" |
| & | \& | 加法积 | "with" |
| ⊕ | \oplus | 加法并 | "plus" |
| ! | ! | 指数模态 | "bang" |
| ∀ | \forall | 全称类型 | "forall" |
| ∃ | \exists | 存在类型 | "exists" |
| μ | \mu | 最小不动点 | "mu" |
| ν | \nu | 最大不动点 | "nu" |

---

## 3. 形式化定义模板

### 3.1 语法定义模板

```markdown
### 定义 X.X (语法)

**表达式**:
$$
e \in \text{Expr} ::= x \mid c \mid \lambda x.e \mid e_1\, e_2 \mid \text{let } x = e_1 \text{ in } e_2
$$

其中:
- $x \in \text{Var}$: 变量
- $c \in \text{Const}$: 常量
- $\lambda x.e$: 函数抽象
- $e_1\, e_2$: 函数应用
- $\text{let } x = e_1 \text{ in } e_2$: let绑定

**上下文无关语法**:
```bnf
expr ::= var
      |  const
      |  "λ" var "." expr
      |  expr expr
      |  "let" var "=" expr "in" expr
```

```

### 3.2 操作语义模板

```markdown
### 定义 X.X (操作语义)

**配置**: $(e, \Sigma)$ 其中 $e$ 是表达式，$\Sigma$ 是堆

**小步语义** $(e, \Sigma) \rightarrow (e', \Sigma')$:

| 规则 | 条件 | 转换 |
|------|------|------|
| E-Beta | - | $((\lambda x.e)\, v, \Sigma) \rightarrow (e[v/x], \Sigma)$ |
| E-Let | - | $(\text{let } x = v \text{ in } e, \Sigma) \rightarrow (e[v/x], \Sigma)$ |
| E-New | $\ell \notin \text{dom}(\Sigma)$ | $(\text{new } v, \Sigma) \rightarrow (\ell, \Sigma[\ell \mapsto v])$ |
| E-Read | $\Sigma(\ell) = v$ | $(!\ell, \Sigma) \rightarrow (v, \Sigma)$ |
| E-Write | - | $(\ell := v, \Sigma) \rightarrow ((), \Sigma[\ell \mapsto v])$ |

**求值上下文**:
$$
E ::= [] \mid E\, e \mid v\, E \mid \text{let } x = E \text{ in } e \mid \dots
$$
```

### 3.3 类型规则模板

```markdown
### 定义 X.X (类型系统)

**类型环境**:
$$
\Gamma ::= \emptyset \mid \Gamma, x: \tau \mid \Gamma, \alpha \text{ type}
$$

**类型推导** $\Gamma \vdash e : \tau$:

```

─────────────── T-Var    (x:τ) ∈ Γ
Γ ⊢ x : τ

Γ, x:τ₁ ⊢ e : τ₂
─────────────────── T-Abs
Γ ⊢ λx.e : τ₁ → τ₂

Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
────────────────────────────────── T-App
Γ ⊢ e₁ e₂ : τ₂

```

**定理 X.X (类型安全性)**:
> 如果 $\vdash e : \tau$ 且 $(e, \emptyset) \rightarrow^* (e', \Sigma')$，则要么 $e'$ 是值，要么存在 $e''$ 使得 $(e', \Sigma') \rightarrow (e'', \Sigma'')$。

**证明**: 见附录 A。∎
```

### 3.4 定理证明模板

```markdown
### 定理 X.X (定理名称)

**陈述**:
> 如果前提条件，则结论。

**证明**:

*对推导进行结构归纳*。

**基本情况**:
- 情况 1: [...]
  - 由[引理X.X]得证

**归纳情况**:
- 情况 2: [...]
  - 由归纳假设(IH)，我们有[...]
  - 结合[定义X.X]，得证

**引理 X.X (辅助引理名称)**:
> 辅助引理陈述

*证明*: [...] ∎

∎
```

---

## 4. 可判定性分析模板

### 4.1 复杂度类定义

```markdown
### 定义 X.X (复杂度类)

**P**: 确定性图灵机在多项式时间内可解的问题类
$$
\text{P} = \bigcup_{k \in \mathbb{N}} \text{TIME}(n^k)
$$

**NP**: 非确定性图灵机在多项式时间内可解的问题类
$$
\text{NP} = \bigcup_{k \in \mathbb{N}} \text{NTIME}(n^k)
$$

**PSPACE**: 多项式空间可解的问题类
$$
\text{PSPACE} = \bigcup_{k \in \mathbb{N}} \text{SPACE}(n^k)
$$

**EXPTIME**: 指数时间可解的问题类
$$
\text{EXPTIME} = \bigcup_{k \in \mathbb{N}} \text{TIME}(2^{n^k})
$$
```

### 4.2 可判定性证明模板

```markdown
      ### 定理 X.X (可判定性)

      **陈述**:
      > 问题 P 是可判定的，且复杂度为 O(f(n))。

      **证明**:

      1. **问题规约**:
         - 将 P 规约到已知可判定问题 Q
         - 规约可在 O(g(n)) 时间内完成

      2. **算法描述**:
         ```

         算法 Solve-P(input):
         1. 将 input 转换为 Q 的实例 x'
         2. 运行 Q 的算法求解 x'
         3. 返回结果

         ```

      3. **复杂度分析**:
         - 步骤1: O(g(n))
         - 步骤2: O(h(n))
         - 总复杂度: O(g(n) + h(n)) = O(f(n))

      4. **正确性证明**:
         - 完备性: 如果 P(x) 成立，则算法返回 true
         - 可靠性: 如果算法返回 true，则 P(x) 成立

      ∎
```

---

## 5. 引用格式规范

### 5.1 学术论文引用

```markdown
1. **作者, A. B., & 作者, C. D.** (年份). 论文标题. *期刊名*, 卷(期), 页码.
   - 关键贡献: 一句话总结
   - 与本文档的关联: 说明如何应用

例:
1. **Jung, R., et al.** (2018). RustBelt: Securing the Foundations of the Rust
   Programming Language. *POPL '18*.
   - 关键贡献: 首次机器检验的Rust形式化证明
   - 关联: 第2章类型语义基于本文
```

### 5.2 书籍引用

```markdown
2. **作者.** (年份). *书名* (版次). 出版社.
   - 关键章节: 章节号或页码范围
   - 关联: 说明如何使用

例:
2. **Pierce, B. C.** (2002). *Types and Programming Languages*. MIT Press.
   - 关键章节: 第9章(子类型)、第22章(多态)
   - 关联: 类型系统基础理论
```

---

## 6. 图示规范

### 6.1 推导树

```
Γ ⊢ e₁ : τ₁ → τ₂    Γ ⊢ e₂ : τ₁
────────────────────────────────── T-App
Γ ⊢ e₁ e₂ : τ₂
```

### 6.2 状态转换图

```
        new v
(∅) ───────────→ (ℓ, {ℓ ↦ v})

        !ℓ
(ℓ, {ℓ ↦ v}) ───→ (v, {ℓ ↦ v})

        ℓ := v'
(ℓ, {ℓ ↦ v}) ───→ ((), {ℓ ↦ v'})
```

### 6.3 层次架构图

```
┌─────────────────────────────────┐
│         Rust 源代码              │
├─────────────────────────────────┤
│            MIR                  │
├─────────────────────────────────┤
│          λRust                  │
├─────────────────────────────────┤
│      Iris 分离逻辑               │
├─────────────────────────────────┤
│       Coq/Lean 证明              │
└─────────────────────────────────┘
```

---

## 7. 代码块规范

### 7.1 数学代码 (伪代码)

使用 ` ``` ` 或明确的语言标识:

```haskell
-- 伪代码示例 (Haskell风格)
unify :: Type -> Type -> Maybe Substitution
unify (TVar a) t = if occurs a t then Nothing else Just (singleton a t)
unify t (TVar a) = unify (TVar a) t
unify (TCon c1 ts1) (TCon c2 ts2)
  | c1 == c2  = unifyMany ts1 ts2
  | otherwise = Nothing
```

### 7.2 Rust代码

```rust
// Rust代码示例
fn example<T: Clone>(x: T) -> (T, T) {
    let y = x.clone();
    (x, y)
}
```

### 7.3 Coq/Lean证明代码

```coq
(* Coq证明示例 *)
Lemma progress : forall e τ,
  empty ⊢ e : τ ->
  value e / exists e', e --> e'.
Proof.
  intros e τ Hty.
  induction Hty; eauto.
  - (* T_Var *) inversion H.
  - (* T_Abs *) left. constructor.
Qed.
```

```lean4
-- Lean 4证明示例
theorem progress {e τ} (h : ∅ ⊢ e : τ) :
    Value e ∨ ∃ e', e ⟶ e' := by
  induction h with
  | T_Var h => cases h
  | T_Abs => left; constructor
  | T_App h1 h2 ih1 ih2 =>
      right
      cases ih1 with
      | inl h1v =>
          cases ih2 with
          | inl h2v =>
              cases h1v with
              | V_Abs =>
                  exists _; apply Step_Beta
          | inr h2step =>
              let ⟨e2', h2'⟩ := h2step
              exists _; apply Step_App2; assumption
      | inr h1step =>
          let ⟨e1', h1'⟩ := h1step
          exists _; apply Step_App1; assumption
```

---

## 8. 质量检查清单

在发布每个文档前，检查:

- [ ] 所有数学符号使用正确的LaTeX格式
- [ ] 每个定义都有唯一的编号
- [ ] 每个定理都有完整的证明或引用证明位置
- [ ] 代码块标明语言类型
- [ ] 引用格式符合规范
- [ ] 图示使用ASCII艺术或正确的外部链接
- [ ] 术语首次出现时有定义
- [ ] 没有未定义的符号或缩写

---

*框架版本: 1.0.0*
*最后更新: 2026-03-04*
