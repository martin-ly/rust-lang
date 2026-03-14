# 证明策略详解

> **本文档目标**：详细解释每个定理的证明策略，包括关键技巧、常见陷阱和完成 admit 的指导。

---

## 一、通用证明技巧

### 1.1 结构归纳法（Structural Induction）

**适用场景**：

- 表达式是归纳定义的
- 类型是归纳定义的
- 需要对语法结构进行推理

**基本模式**：

```coq
induction e; intros.
- (* 基本情况：e 是值 *)
  simpl. auto.
- (* 归纳步骤：e 是复合表达式 *)
  apply IH. (* 应用归纳假设 *)
```

**在 Rust 形式化中的应用**：

```coq
(* 证明：所有表达式要么已经是值，要么可以求值 *)
Theorem progress :
  forall e, is_value e \/ can_eval e.
Proof.
  induction e.
  - (* EValue：已经是值 *)
    left. constructor.
  - (* EVar：可以求值 *)
    right. apply can_eval_var.
  - (* ELBorrow：取决于子表达式 *)
    destruct IHe. (* 使用归纳假设 *)
    + (* 子表达式是值 *)
      right. apply can_eval_borrow.
    + (* 子表达式可以求值 *)
      right. apply can_eval_ctx.
Qed.
```

### 1.2 良基归纳法（Well-Founded Induction）

**适用场景**：

- 需要一个"度量"来确保终止
- 递归调用在"更小"的参数上

**基本模式**：

```coq
apply (well_founded_induction_type measure).
- (* 证明 measure 是良基的 *)
- (* 证明目标 *)
  intros x IH.
  (* IH：对于所有 y < x，P(y) 成立 *)
  (* 证明 P(x) *)
```

**在终止性证明中的应用**：

```coq
Lemma linearizable_implies_wf_ty_dep :
  forall Γ, Linearizable Γ -> well_founded (ty_dep Γ).
Proof.
  intros Γ Hlin.
  apply (well_founded_induction_type
    (R := fun y z => ty_rank (te_lookup_type Γ y) < ty_rank (te_lookup_type Γ z))).
  - apply well_founded_ltof.  (* 自然数是良基的 *)
  - (* 证明目标 *)
    intros x IH.
    (* IH：对于所有秩更小的 y，性质成立 *)
    constructor. intros z Hdep.
    apply IH.
    (* 证明 ty_rank z < ty_rank x *)
    apply linearizable_rank_decreasing.
Qed.
```

### 1.3 反证法（Proof by Contradiction）

**适用场景**：

- 证明某事"不可能"发生
- 否定形式的目标

**基本模式**：

```coq
intro H. (* 假设反面成立 *)
(* 推导出矛盾 *)
contradiction.
```

**在所有权安全证明中的应用**：

```coq
Lemma no_use_after_free :
  forall e, well_typed e -> no_use_after_free e.
Proof.
  intros e Hty.
  unfold no_use_after_free.
  intros ℓ Hnone [s' [h' [v [Heval Haccess]]]].
  (* 假设 use-after-free 发生 *)
  (* 推导出矛盾 *)
  assert (heap_lookup h' ℓ = Some v') by (type_safety ...).
  assert (heap_lookup h ℓ = None) by assumption.
  (* 类型系统保证引用有效，但 Hnone 说无效 *)
  contradiction.
Qed.
```

### 1.4 构造性证明（Constructive Proof）

**适用场景**：

- 需要展示"存在"某物
- 提供具体的算法或构造

**基本模式**：

```coq
exists witness. (* 提供见证 *)
(* 证明 witness 满足条件 *)
```

**在可判定性证明中的应用**：

```coq
Theorem decidable_type_checking :
  forall e, {has_type e} + {~ has_type e}.
Proof.
  intro e.
  (* 构造类型检查算法 *)
  induction e.
  - (* 值：构造 VT_Int 或 VT_Bool 等 *)
    left. constructor.
  - (* 变量：查找环境 *)
    destruct (env_lookup x).
    + left. constructor. auto.
    + right. intro H. inversion H. contradiction.
Qed.
```

---

## 二、特定定理的证明策略

### 2.1 终止性定理的证明策略

**核心挑战**：

- 借用检查可能涉及循环（类型相互引用）
- 需要证明即使有循环，检查也会终止

**关键洞察**：

- Linearizability 确保类型依赖无环
- 类型秩提供一个递减的度量

**证明步骤**：

**步骤1：定义度量**

```coq
Definition measure (Γ : type_env) : nat :=
  te_measure Γ.  (* 环境中所有类型的秩之和 *)
```

**步骤2：证明度量递减**

```coq
Lemma measure_decreases :
  forall Γ Γ',
    Linearizable Γ ->
    borrow_check_step Γ = Some Γ' ->
    measure Γ' < measure Γ.
Proof.
  (* 每次借用检查步骤都严格减小度量 *)
  intros Γ Γ' Hlin Hstep.
  unfold measure, borrow_check_step in *.
  (* 分析借用检查的操作 *)
  destruct Hstep.
  - (* 情况1：发现冲突，需要重新排序 *)
    apply reorder_decreases_measure.
  - (* 情况2：更新类型信息 *)
    apply update_decreases_measure.
Qed.
```

**步骤3：应用良基归纳**

```coq
Theorem termination :
  forall Γ, Linearizable Γ -> exists Γ', fixed_point Γ'.
Proof.
  intros Γ Hlin.
  apply (well_founded_induction_type
    (R := fun Γ' Γ => measure Γ' < measure Γ)).
  - apply well_founded_ltof.
  - intros Γ' IH.
    (* 检查是否到达不动点 *)
    destruct (is_fixed_point_dec Γ').
    + exists Γ'. auto.
    + (* 继续借用检查 *)
      assert (measure (borrow_check_step Γ') < measure Γ').
      { apply measure_decreases; auto. }
      apply IH. auto.
Qed.
```

**常见陷阱**：

1. **度量不是良基的**：确保度量是自然数且有下界
2. **度量不减**：仔细检查每次迭代是否严格递减
3. **Linearizability 不足**：确保前提条件足够强

### 2.2 保持性定理的证明策略

**核心挑战**：

- 表达式求值后，类型必须保持
- 需要处理环境扩展和堆更新

**关键洞察**：

- 对每个求值规则，证明输出类型与输入类型一致
- 环境扩展保持良类型性

**证明结构**：

```coq
Theorem preservation :
  forall e τ, has_type Γ e τ ->
  forall v, eval e v -> has_type_value v τ.
Proof.
  intros e τ Hty v Heval.
  generalize dependent τ.
  induction Heval; intros.

  (* Case: E_Value *)
  - (* e 已经是值 *)
    inversion Hty; subst.
    constructor.

  (* Case: E_Var *)
  - (* 变量查找 *)
    inversion Hty; subst.
    apply stack_well_typed_lookup.
    auto.

  (* Case: E_Borrow *)
  - (* 借用表达式 *)
    inversion Hty; subst.
    constructor. (* RVLoc 有引用类型 *)

  (* Case: E_Let *)
  - (* Let 绑定 *)
    inversion Hty; subst.
    (* 子表达式 e₁ 有类型 τ₁ *)
    apply IHHeval1 in H3. (* 应用归纳假设 *)
    (* 扩展环境 *)
    assert (has_type (Γ, x:τ₁) e₂ τ₂).
    { apply H5. }
    apply IHHeval2 in H.
    auto.

  (* 其他 cases ... *)
Qed.
```

**关键技巧**：

**技巧1：使用 `generalize dependent`**

```coq
(* 错误：在引入 Hty 之前就归纳 *)
induction Heval.
intros τ Hty.  (* 太晚了 *)

(* 正确：先归纳，再引入 *)
generalize dependent τ.
induction Heval.
intros τ Hty.  (* 现在可以对 Hty 进行 case 分析 *)
```

**技巧2：环境扩展引理**

```coq
Lemma env_extend_preserves_typing :
  forall Γ x τ₁ e τ₂,
    has_type Γ e τ₂ ->
    has_type (Γ, x:τ₁) e τ₂.
Proof.
  (* 如果 x 不在 e 的自由变量中，类型保持不变 *)
  intros.
  apply weakening_lemma.
Qed.
```

**技巧3：堆更新引理**

```coq
Lemma heap_update_preserves_typing :
  forall h ℓ v τ,
    heap_well_typed h ->
    value_has_type v τ ->
    heap_well_typed (heap_update h ℓ v).
Proof.
  (* 更新堆中的位置保持堆的良好类型 *)
  intros.
  unfold heap_well_typed in *.
  intros ℓ' v' Hlookup.
  destruct (ℓ' =? ℓ).
  - (* 更新的位置 *)
    subst. inversion Hlookup; subst. auto.
  - (* 其他位置 *)
    apply H. auto.
Qed.
```

### 2.3 进展定理的证明策略

**核心挑战**：

- 需要证明每个良类型的表达式都可以求值
- 处理各种表达式构造

**关键洞察**：

- 对表达式结构进行归纳
- 每个构造要么已经是值，要么有求值规则

**证明模式**：

```coq
Theorem progress :
  forall e, has_type e τ -> is_value e \/ can_step e.
Proof.
  intros e Hty.
  induction Hty.

  (* Case: T_Value *)
  - (* e = EValue v *)
    left. constructor.

  (* Case: T_Var *)
  - (* e = EVar x *)
    right. (* 证明可以求值 *)
    exists (EValue v).
    apply S_Var.
    apply stack_lookup. (* 变量在栈中 *)

  (* Case: T_Seq *)
  - (* e = ESeq e₁ e₂ *)
    destruct IHHty1.
    + (* e₁ 是值 *)
      right. apply S_Seq. auto.
    + (* e₁ 可以求值 *)
      right. apply S_Ctx. auto.

  (* 其他 cases ... *)
Qed.
```

**关键技巧**：

**技巧1：使用求值上下文（Evaluation Context）**

```coq
(* 对于复合表达式，使用上下文规则 *)
right.
exists (fill_ctx C e').
apply S_Ctx.
auto.
```

**技巧2：处理卡住的情况**

```coq
(* 某些情况可能卡住，但类型系统保证不会发生 *)
- (* T_Deref：解引用 *)
  destruct IHHty.
  + (* e 是值 *)
    destruct v.
    * (* RVLoc ℓ：可以求值 *)
      right. apply S_Deref.
    * (* 其他：类型系统保证不会发生 *)
      inversion Hty; subst. contradiction.
  + (* e 可以求值 *)
    right. apply S_Ctx. auto.
```

### 2.4 可判定性定理的证明策略

**核心挑战**：

- 构造一个完整的类型检查算法
- 证明算法终止并给出正确答案

**关键洞察**：

- 类型检查是语法导向的
- 每个构造都有有限的规则

**算法结构**：

```coq
Fixpoint type_check (e : expr) : option ty :=
  match e with
  | EValue v => Some (infer_value_type v)
  | EVar x => env_lookup x
  | EBorrow p =>
      match type_check_place p with
      | Some τ => Some (TRef RStatic Shrd τ)
      | None => None
      end
  | ESeq e₁ e₂ =>
      match type_check e₁ with
      | Some _ => type_check e₂
      | None => None
      end
  | ELet x τ₁ e₁ e₂ =>
      match type_check e₁ with
      | Some τ₁' =>
          if ty_eq τ₁ τ₁'
          then type_check (subst x e₁ e₂)
          else None
      | None => None
      end
  | ...
  end.
```

**证明策略**：

```coq
Theorem type_checking_decidable :
  forall e, {has_type e} + {~ has_type e}.
Proof.
  intro e.
  (* 使用算法 *)
  destruct (type_check e) eqn:H.
  - (* 算法返回 Some τ *)
    left. apply type_check_sound. auto.
  - (* 算法返回 None *)
    right. intro Hty.
    apply type_check_complete in Hty.
    congruence.
Qed.
```

**关键引理**：

```coq
Lemma type_check_sound :
  forall e τ, type_check e = Some τ -> has_type e τ.
Proof.
  (* 证明算法正确：如果返回类型，程序确实有该类型 *)
  induction e; simpl; intros τ H; try discriminate.
  - (* EValue *)
    inversion H. constructor.
  - (* 其他 cases *)
    ...
Qed.

Lemma type_check_complete :
  forall e τ, has_type e τ -> type_check e = Some τ.
Proof.
  (* 证明算法完备：如果程序有类型，算法能找到 *)
  induction 1; simpl.
  - (* T_Value *)
    reflexivity.
  - (* 其他 cases *)
    ...
Qed.
```

---

## 三、完成 admit 的实用指南

### 3.1 常见 admit 模式

**模式1：技术性辅助引理**

```coq
(* admit：列表操作引理 *)
Lemma list_map_preserves_length :
  forall {A B} (f : A -> B) (l : list A),
    length (map f l) = length l.
Proof.
  (* 简单归纳 *)
  induction l; simpl; auto.
Qed.
```

**模式2：case 分析不完整**

```coq
(* admit：某个 case 的处理 *)
destruct x; try auto.
- (* case1 *)
  auto.
- (* case2 *)
  admit. (* 需要单独证明 *)
```

**模式3：需要外部引理**

```coq
(* admit：依赖未证明的引理 *)
apply some_unproven_lemma.
(* 需要先证明 some_unproven_lemma *)
```

### 3.2 完成 admit 的步骤

**步骤1：理解上下文**

```text
1. 查看 admit 前后的目标（Goal）
2. 理解假设（Hypotheses）
3. 确定需要什么结论
```

**步骤2：确定证明策略**

```text
- 需要归纳吗？
- 需要反证法吗？
- 可以应用现有引理吗？
```

**步骤3：尝试证明**

```coq
(* 如果证明复杂，提取为单独引理 *)
Lemma helper_lemma : ...
Proof.
  ...
Qed.

(* 在原位置应用 *)
apply helper_lemma.
```

**步骤4：验证证明**

```text
- Qed. 能过吗？
- 是否有未使用的假设？
- 是否可以简化？
```

### 3.3 具体 admit 完成示例

**示例1：环境扩展保持良好性**

```coq
(* 原 admit *)
+ admit. (* 扩展环境保持良好性 *)

(* 完成版本 *)
+ apply stack_well_typed_extend.
  * auto. (* 新值的类型正确 *)
  * auto. (* 原环境保持良好性 *)
```

**示例2：列表归纳**

```coq
(* 原 admit *)
- admit. (* 列表归纳 *)

(* 完成版本 *)
- induction es; intros.
  + (* 空列表 *)
    constructor.
  + (* 非空列表 *)
    constructor.
    * auto.
    * apply IHes. auto.
```

**示例3：语义等价性**

```coq
(* 原 admit *)
admit. (* 大步蕴含小步 *)

(* 完成版本 *)
eapply star_step_trans.
- apply eval_to_step. auto.
- apply IHHeval.
```

---

## 四、高级技巧

### 4.1 使用 Ltac 自动化

```coq
Ltac solve_progress :=
  match goal with
  | [ |- is_value _ \/ _ ] => left; constructor
  | [ |- _ \/ can_step _ ] => right; eexists; apply S_Ctx; solve_progress
  | _ => auto
  end.

Theorem progress_many :
  forall e, has_type e -> is_value e \/ can_step e.
Proof.
  induction e; intros; solve_progress.
Qed.
```

### 4.2 处理复杂的 induction

```coq
(* 多态归纳 *)
induction e using expr_induction_principle.

(* 带参数的归纳 *)
induction n as [| n' IH] eqn:Hn.

(* 互相递归的归纳 *)
apply (mutual_induction_principle
  (P := fun e => ...)
  (Q := fun v => ...)).
```

### 4.3 使用 ssreflect

```coq
From mathcomp Require Import ssreflect.

Lemma example :
  forall x y, x < y -> y < z -> x < z.
Proof.
  move=> x y Hxy Hyz.
  apply: lt_trans Hxy Hyz.
Qed.
```

---

## 五、常见错误和解决方案

### 5.1 错误：Induction 过早

```coq
(* 错误 *)
induction H.
intros x.  (* x 在归纳后引入，IH 不通用 *)

(* 正确 *)
intros x.
induction H.
```

### 5.2 错误：Hypothesis 太具体

```coq
(* 错误 *)
apply H.  (* H 的假设不匹配 *)

(* 正确 *)
apply H with (x := specific_value).
(* 或 *)
generalize dependent x.
apply H.
```

### 5.3 错误：忘记 inversion

```coq
(* 错误 *)
H : has_type (EVar x) τ
...
(* 直接使用 H，但不知道 Var 的类型规则 *)

(* 正确 *)
inversion H; subst; clear H.
(* 现在知道 te_lookup Γ x = Some τ *)
```

---

## 六、总结

证明策略的核心原则：

1. **理解结构**：分析语法和语义结构
2. **选择策略**：归纳、反证、构造
3. **建立引理**：复杂步骤提取为辅助引理
4. **验证完整**：确保所有 case 都处理
5. **自动化**：使用 Ltac 减少重复

**下一篇**：阅读 `CONCEPT_MAP.md` 了解概念间的联系。

---

## 🆕 Rust 1.94 所有权系统更新

> **适用版本**: Rust 1.94.0+

### 新特性对所有权系统的影响

| 特性 | 所有权影响 | 可判定性 |
|------|-----------|---------|
| rray_windows | 安全的切片访问 | ✅ 编译期检查 |
| ControlFlow | 控制流语义 | ✅ 类型安全 |
| LazyCell/LazyLock | 延迟初始化 | ✅ Send/Sync 检查 |

### 形式化更新

- rray_windows 的边界安全证明
- ControlFlow 的代数性质
- 延迟初始化的生命周期分析

**最后更新**: 2026-03-14
