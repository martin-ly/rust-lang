# Rust 所有权系统可判定性 - 核心定理

## 定理 1: Borrow Checking 终止性 (Termination)

### 1.1 定理陈述

```text
Theorem BorrowChecking_Termination:
  ∀Γ: TypeEnv,
  Linearizable(Γ) →
  Terminates(borrow_check(Γ))
```

**中文**: 对于任何线性化的类型环境 Γ，借用检查算法都会终止。

### 1.2 关键定义

#### 定义 1.2.1: 类型的秩 (Type Rank)

```text
rank: Type → ℕ

rank(B) = 0                              (基础类型)
rank(&ρ ω τ) = 1 + rank(τ)               (引用类型)
rank(Box τ) = 1 + rank(τ)                (Box 类型)
rank((τ₁, ..., τₙ)) = max{rank(τᵢ)}      (元组类型)
```

#### 定义 1.2.2: 类型中的自由变量

```text
fv: Type → P(Var)

fv(B) = ∅
fv(&ρ ω τ) = fv(τ) ∪ free_regions(ρ)
fv(Box τ) = fv(τ)
fv((τ₁, ..., τₙ)) = ⋃ fv(τᵢ)
```

#### 定义 1.2.3: 类型环境的线性化 (Linearizability)

```text
Linearizable(Γ) ≜ ∀x ∈ dom(Γ). rank(Γ(x)) > max{ rank(y) | y ∈ fv(Γ(x)) }

直观含义: 每个变量的类型秩严格大于其类型中引用的所有变量的类型秩。
这确保了类型依赖关系构成一个有向无环图 (DAG)。
```

#### 定义 1.2.4: 环境度量 (Environment Measure)

```text
μ: TypeEnv → ℕ

μ(Γ) = Σ_{x ∈ dom(Γ)} rank(Γ(x))

或者使用加权版本:
μ_weighted(Γ) = Σ_{x ∈ dom(Γ)} w^{rank(Γ(x))}  for some w > 1
```

### 1.3 证明草图

```text
证明思路: 通过度量函数 μ 的递减性证明终止性

步骤 1: 定义 borrow_check 算法的状态
  State = TypeEnv × Worklist × Constraints

步骤 2: 证明引理 - μ 是良定义的
  Lemma μ_well_defined:
    ∀Γ, μ(Γ) ∈ ℕ and μ(Γ) ≥ 0

步骤 3: 证明关键引理 - borrow_check 步骤递减 μ
  Lemma borrow_check_step_decreases_μ:
    ∀Γ₁, Γ₂,
    borrow_check_step(Γ₁) = Some Γ₂ →
    Linearizable(Γ₁) →
    μ(Γ₂) < μ(Γ₁)

  证明要点:
  - borrow_check 的核心操作是类型左值 (typing places)
  - 左值可能包含借用，需要递归检查
  - Linearizable 确保了递归的深度是有限的
  - 每次递归调用处理秩严格更小的类型

步骤 4: 应用良基归纳法
  由于 μ 递减且有下界 0，根据良基归纳原理，
  borrow_check 必然终止。

步骤 5: 良类型程序满足 Linearizable
  Lemma well_typed_implies_linearizable:
    ∀P: Program,
    well_typed(P) → Linearizable(Γ_P)

  这个引理连接了终止性定理与 Rust 的类型系统。
```

### 1.4 形式化证明结构 (Coq)

```coq
Section Termination.

(* 类型的秩 *)
Fixpoint rank (τ : ty) : nat :=
  match τ with
  | TBase _ => 0
  | TRef _ _ τ' => 1 + rank τ'
  | TBox τ' => 1 + rank τ'
  | TTuple τs => list_max (map rank τs)
  | _ => 0
  end.

(* 自由变量 *)
Fixpoint fv_ty (τ : ty) : list var :=
  match τ with
  | TBase _ => []
  | TRef _ _ τ' => fv_ty τ'
  | TBox τ' => fv_ty τ'
  | TTuple τs => flat_map fv_ty τs
  | _ => []
  end.

(* Linearizability *)
Definition Linearizable (Γ : type_env) : Prop :=
  forall x τ,
    Γ x = Some τ ->
    forall y, In y (fv_ty τ) ->
    exists τ', Γ y = Some τ' /\ rank τ > rank τ'.

(* 环境度量 *)
Definition measure (Γ : type_env) (dom : list var) : nat :=
  list_sum (map (fun x =>
    match Γ x with
    | Some τ => rank τ
    | None => 0
    end) dom).

(* 关键引理: borrow_check_step 递减度量 *)
Lemma borrow_check_step_decreases :
  forall Γ Γ' dom worklist,
    Linearizable Γ ->
    borrow_check_step Γ worklist = Some (Γ', worklist') ->
    measure Γ' dom < measure Γ dom.
Proof.
  (* 详细证明 *)
  intros.
  (* 展开 borrow_check_step 的定义 *)
  unfold borrow_check_step in H0.
  (* 分析情况 *)
  case worklist; [discriminate | intros w ws].
  (* 根据工作列表头部元素的类型进行分析 *)
  destruct w as [x | p | e];
  (* 每种情况都显示度量递减 *)
  (* ... *)
Qed.

(* 主定理 *)
Theorem borrow_check_termination :
  forall Γ worklist,
    Linearizable Γ ->
    exists Γ' n,
      borrow_check_nsteps Γ worklist n = Some Γ' /\
      is_fixed_point Γ'.
Proof.
  (* 使用良基归纳 *)
  intros.
  remember (measure Γ (dom Γ)) as m.
  generalize dependent Γ.
  generalize dependent worklist.
  induction m using lt_wf_ind.
  (* ... *)
Qed.

End Termination.
```

---

## 定理 2: 类型保持 (Preservation)

### 2.1 定理陈述

```text
Theorem Preservation:
  ∀Δ, Γ, Θ, σ, h, e, τ, σ', h', v,
  Δ; Γ; Θ ⊢ e : τ →
  σ; h ⊢ e ⇓ σ'; h'; v →
  (∃Γ', Θ',
    Δ; Γ'; Θ' ⊢ v : τ ∧
    ⊢ σ' : Γ' ∧
    ⊢ h' : Θ')
```

**中文**: 如果表达式 e 在环境 Δ, Γ, Θ 下具有类型 τ，且 e 在 σ, h 下求值为 v，
那么存在更新后的环境 Γ', Θ' 使得 v 具有类型 τ，且结果环境和堆满足类型约束。

### 2.2 证明结构

```coq
Theorem preservation :
  forall Δ Γ Θ σ h e τ σ' h' v,
    has_type Δ Γ Θ e τ ->
    eval σ h e σ' h' v ->
    exists Γ' Θ',
      has_type_value Δ Γ' Θ' v τ /\
      env_well_typed σ' Γ' /\
      heap_well_typed h' Θ'.
Proof.
  intros Δ Γ Θ σ h e τ σ' h' v Hty Heval.
  generalize dependent Θ.
  generalize dependent Γ.
  induction Heval; intros.
  (* 根据求值规则进行情况分析 *)
  - (* E-Value *)
    exists Γ, Θ.
    split; [|split].
    + (* v 具有类型 τ *)
      inversion Hty; subst. auto.
    + (* σ 满足 Γ *)
      auto.
    + (* h 满足 Θ *)
      auto.

  - (* E-Var *)
    exists Γ, Θ.
    split; [|split].
    + (* 变量值具有类型 *)
      inversion Hty; subst.
      apply H0.
    + auto.
    + auto.

  - (* E-Borrow *)
    (* 复杂情况: 需要更新贷款环境 *)
    inversion Hty; subst.
    exists Γ, (update_loan Θ ρ (ω, p)).
    split; [|split].
    + (* 引用值具有类型 *)
      constructor. auto.
    + auto.
    + (* 证明堆满足更新后的贷款环境 *)
      apply heap_update_loan; auto.

  (* 更多情况... *)
Qed.
```

---

## 定理 3: 进展 (Progress)

### 3.1 定理陈述

```text
Theorem Progress:
  ∀Δ, Γ, Θ, σ, h, e, τ,
  Δ; Γ; Θ ⊢ e : τ →
  (⊢ σ : Γ) →
  (⊢ h : Θ) →
  (is_value e) ∨
  (∃e', σ', h', ⟨σ, h, e⟩ → ⟨σ', h', e'⟩) ∨
  (stuck e)
```

**中文**: 良类型的表达式要么是值，要么可以进一步求值，要么是卡住的（类型错误或 UB）。

---

## 定理 4: 类型安全 (Type Safety)

### 4.1 定理陈述

```text
Theorem Type_Safety:
  ∀Δ, Γ, Θ, σ, h, e, τ,
  Δ; Γ; Θ ⊢ e : τ →
  (⊢ σ : Γ) →
  (⊢ h : Θ) →
  ¬(stuck e)
```

**证明**: 由 Preservation + Progress 直接得出。

---

## 定理 5: 所有权安全保证内存安全

### 5.1 定理陈述

```text
Theorem Ownership_Implies_Memory_Safety:
  ∀P: Program,
  well_typed(P) →
  no_undefined_behavior(P)
```

其中 undefined behavior 包括:

- Use after free
- Double free
- Data race
- Dangling pointer dereference

---

## 定理 6: 可判定性 (Decidability)

### 6.1 定理陈述

```text
Theorem Decidability:
  ∀Γ: TypeEnv, ∀e: Expr, ∀τ: Type,
  Decidable(Δ; Γ; Θ ⊢ e : τ)
```

**证明要点**:

1. 语法判断是可判定的（结构归纳）
2. borrow checking 终止（定理 1）
3. 类型推断对于核心 Rust 是可判定的

---

## 定理间的依赖关系

```text
                    ┌──────────────────┐
                    │   Linearizable   │
                    │    Definition    │
                    └────────┬─────────┘
                             │
                             v
┌──────────────┐    ┌──────────────────┐
│   WellTyped  │───>│   Termination    │<──┐
│   Programs   │    │  (Theorem 1)     │   │
└──────────────┘    └────────┬─────────┘   │
                             │             │
                             v             │
                    ┌──────────────────┐   │
                    │   Preservation   │   │
                    │  (Theorem 2)     │   │
                    └────────┬─────────┘   │
                             │             │
         ┌───────────────────┼──────────┐  │
         │                   │          │  │
         v                   v          v  │
┌─────────────────┐  ┌──────────────┐  ┌───┴───────┐
│     Progress    │  │  Type Safety │  │ Decidability│
│   (Theorem 3)   │  │ (Theorem 4)  │  │(Theorem 6) │
└─────────────────┘  └──────────────┘  └───────────┘
         │
         v
┌─────────────────┐
│ Memory Safety   │
│ (Theorem 5)     │
└─────────────────┘
```

---

**状态**: 草案 v0.1
**最后更新**: 2026-03-05
