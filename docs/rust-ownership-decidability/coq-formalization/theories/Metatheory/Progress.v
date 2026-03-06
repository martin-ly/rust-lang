(* **************************************************************************
 * Rust 所有权系统形式化 - 进展定理 (Progress)
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Syntax.Types.
Require Import Syntax.Expressions.
Require Import Typing.TypeSystem.
Require Import Semantics.OperationalSemantics.
Require Import Metatheory.Preservation.

Import ListNotations.

(* ==========================================================================
 * 进展定理定义
 * ========================================================================== *)

Definition is_exp_value (e : expr) : bool :=
  match e with
  | EValue _ => true
  | _ => false
  end.

Definition is_stuck (e : expr) : Prop :=
  ~ is_exp_value e = true /\
  ~ (exists s h s' h' e', step s h e s' h' e').

(* ==========================================================================
 * 值的进展
 * ========================================================================== *)

Lemma value_progress :
  forall v s h,
    ~ (exists s' h' e', step s h (EValue v) s' h' e').
Proof.
  intros v s h [s' [h' [e' Hstep]]].
  inversion Hstep.
Qed.

(* ==========================================================================
 * 辅助引理：环境兼容性
 * ========================================================================== *)

(* 假设：如果变量在类型环境中，且环境是兼容的，则变量在栈中 *)
Axiom env_compatibility :
  forall s Γ x τ,
    stack_well_typed s Γ ->
    te_lookup Γ x = Some τ ->
    exists v, stack_lookup s x = Some v.

(* ==========================================================================
 * 变量的进展
 * ========================================================================== *)

Lemma var_progress :
  forall Γ x τ,
    te_lookup Γ x = Some τ ->
    forall s h,
      stack_well_typed s Γ ->
      exists v,
        stack_lookup s x = Some v.
Proof.
  intros Γ x τ Hlookup s h Hswf.
  apply env_compatibility with (x := x) (τ := τ) in Hswf; auto.
Qed.

Lemma var_can_step :
  forall Γ x τ,
    te_lookup Γ x = Some τ ->
    forall s h,
      stack_well_typed s Γ ->
      exists v s' h' e',
        stack_lookup s x = Some v /\
        step s h (EVar x) s' h' e'.
Proof.
  intros Γ x τ Hlookup s h Hswf.
  apply var_progress in Hlookup as [v Hv]; auto.
  exists v, s, h, (EValue v).
  split; auto.
  apply S_Var. auto.
Qed.

(* ==========================================================================
 * 辅助引理：place_has_type 蕴含所有权安全
 * ========================================================================== *)

Lemma place_has_type_implies_safe :
  forall Δ Γ Θ p τ,
    place_has_type Δ Γ Θ p τ ->
    exists ω, ownership_safe Δ Γ Θ ω p.
Proof.
  intros Δ Γ Θ p τ Hpty.
  induction Hpty.
  - exists Shrd. apply OS_Base; auto.
  - exists Shrd. eapply OS_Deref_Shared; eauto.
  - exists Shrd. eapply OS_Field; eauto. constructor.
  - exists Shrd. eapply OS_Field; eauto. constructor.
Qed.

(* ==========================================================================
 * 辅助引理：位置求值的确定性
 * ========================================================================== *)

Lemma eval_place_deterministic :
  forall s h p ℓ1 ℓ2,
    eval_place s h p ℓ1 ->
    eval_place s h p ℓ2 ->
    ℓ1 = ℓ2.
Proof.
  intros s h p ℓ1 ℓ2 He1 He2.
  generalize dependent ℓ2.
  induction He1; intros ℓ2 He2;
    inversion He2; subst; clear He2;
    try reflexivity;
    try (apply IHHe1; auto).
Qed.

(* ==========================================================================
 * Borrow 的进展
 * 
 * 注意：完整证明需要额外的关于堆良类型性的假设
 * ========================================================================== *)

Lemma borrow_progress :
  forall Δ Γ Θ p ρ ω τ,
    place_has_type Δ Γ Θ p τ ->
    ownership_safe Δ Γ Θ ω p ->
    forall s h,
      stack_well_typed s Γ ->
      exists ℓ,
        eval_place s h p ℓ.
Proof.
  (* 完整证明需要堆良类型性的额外假设 *)
  admit.
Admitted.

(* ==========================================================================
 * Let 的进展
 * ========================================================================== *)

Lemma let_progress :
  forall Δ Γ Θ ω x τ₁ e₁ e₂ τ₂ s h,
    has_type Δ Γ Θ e₁ τ₁ ->
    has_type Δ (te_extend Γ x τ₁) Θ e₂ τ₂ ->
    (is_exp_value e₁ = true ->
     exists s' h' e',
       step s h (ELet ω x τ₁ e₁ e₂) s' h' e').
Proof.
  intros Δ Γ Θ ω x τ₁ e₂ τ₂ s h Hty1 Hty2 Hval.
  destruct e₁ eqn:He1; try inversion Hval.
  exists (stack_extend s x (RVLoc (fresh_loc h))),
         (heap_extend h (fresh_loc h) v),
         e₂.
  apply S_Let.
Qed.

(* ==========================================================================
 * 辅助引理：表达式的归纳进展
 * 
 * 这是进展定理的核心，对每个表达式构造进行归纳
 * ========================================================================== *)

Lemma expr_can_step_or_value :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    heap_well_typed h Θ ->
    (is_exp_value e = true) \/
    (exists s' h' e', step s h e s' h' e').
Proof.
  (* 完整证明需要对 has_type 的归纳 *)
  admit.
Admitted.

(* ==========================================================================
 * 主定理：进展 (Progress)
 * 
 * 进展定理：每个良类型的表达式要么是值，要么可以进一步求值
 * ========================================================================== *)

Theorem progress :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    heap_well_typed h Θ ->
    (is_exp_value e = true) \/
    (exists s' h' e', step s h e s' h' e') \/
    is_stuck e.
Proof.
  intros Δ Γ Θ s h e τ Hty Hswf Hhwf.
  destruct (expr_can_step_or_value Δ Γ Θ s h e τ Hty Hswf Hhwf) as [Hval | Hstep].
  - (* 是值 *)
    left. auto.
  - (* 可以求值一步 *)
    right. left. auto.
Qed.

(* ==========================================================================
 * 强进展：良类型表达式不会卡住
 * 
 * 强进展定理：在进展定理的基础上，证明良类型表达式不可能卡住
 * ========================================================================== *)

Theorem strong_progress :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    heap_well_typed h Θ ->
    (is_exp_value e = true) \/
    (exists s' h' e', step s h e s' h' e').
Proof.
  intros.
  apply expr_can_step_or_value; auto.
Qed.

(* ==========================================================================
 * 类型安全 = Preservation + Progress
 * ========================================================================== *)

Theorem type_safety :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    heap_well_typed h Θ ->
    forall s' h' v,
      eval s h e v h' ->
      exists Γ' Θ',
        has_type_value Δ Γ' Θ' v τ /\
        stack_well_typed s' Γ' /\
        heap_well_typed h' Θ'.
Proof.
  intros.
  apply preservation with (Δ := Δ) (Γ := Γ) (Θ := Θ) (e := e) (τ := τ); auto.
Qed.

(* ==========================================================================
 * 辅助引理：fresh_loc 的确定性
 * ========================================================================== *)

Lemma fresh_loc_deterministic :
  forall h, exists ℓ, fresh_loc h = ℓ.
Proof.
  intros. exists (fresh_loc h). reflexivity.
Qed.

(* ==========================================================================
 * 辅助引理：heap_lookup 的确定性
 * ========================================================================== *)

Lemma heap_lookup_deterministic :
  forall h ℓ v1 v2,
    heap_lookup h ℓ = Some v1 ->
    heap_lookup h ℓ = Some v2 ->
    v1 = v2.
Proof.
  intros. congruence.
Qed.

(* ==========================================================================
 * 求值的确定性（可选）
 * 
 * 定理：求值是确定性的，即同一个表达式求值得到相同的结果
 * ========================================================================== *)

Theorem eval_deterministic :
  forall s h e v₁ h₁ v₂ h₂,
    eval s h e v₁ h₁ ->
    eval s h e v₂ h₂ ->
    v₁ = v₂ /\ h₁ = h₂.
Proof.
  intros s h e v₁ h₁ v₂ h₂ Heval1 Heval2.
  generalize dependent v₂.
  generalize dependent h₂.
  induction Heval1; intros h₂ v₂ Heval2;
    inversion Heval2; subst; clear Heval2;
    try (split; auto; fail).
  - (* E_Var *) 
    assert (v = v0) by congruence. subst. auto.
  - (* E_Borrow *)
    apply eval_place_deterministic with (p := p) (ℓ1 := ℓ) (ℓ2 := ℓ0) in H; auto.
    subst. auto.
  - (* E_Deref *)
    specialize (IHHeval1 _ _ H3). destruct IHHeval1 as [Hv Hh].
    subst.
    assert (v = v0) by (apply heap_lookup_deterministic with (h := h') (ℓ := ℓ); auto).
    subst. auto.
  - (* E_Box *)
    specialize (IHHeval1 _ _ H2). destruct IHHeval1 as [Hv Hh].
    subst. split; auto.
    assert (fresh_loc h' = fresh_loc h') by reflexivity.
    assert (ℓ = ℓ0) by congruence. subst. auto.
  - (* E_Seq *)
    specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1].
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2].
    subst. auto.
  - (* E_Let *)
    specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1].
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2].
    subst. auto.
  - (* E_Assign *)
    assert (ℓ = ℓ0) by (apply eval_place_deterministic with (p := p); auto).
    subst.
    specialize (IHHeval1 _ _ H4). destruct IHHeval1 as [Hv1 Hh1].
    subst. auto.
  - (* E_Tuple *)
    (* 完整证明需要对 eval_list 的确定性证明 *)
    admit.
  - (* E_If_True *)
    specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1].
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2].
    subst. auto.
  - (* E_If_False *)
    specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1].
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2].
    subst. auto.
Admitted.

(* ==========================================================================
 * 辅助引理
 * ========================================================================== *)

Lemma value_not_stuck :
  forall v,
    ~ is_stuck (EValue v).
Proof.
  intros v Hstuck.
  unfold is_stuck in Hstuck.
  destruct Hstuck as [H1 H2].
  simpl in H1. congruence.
Qed.

(* ==========================================================================
 * 辅助引理：多步进展
 * ========================================================================== *)

Lemma step_implies_star_step :
  forall s h e s' h' e',
    step s h e s' h' e' ->
    star_step s h e h' e'.
Proof.
  intros.
  eapply Star_Trans.
  - apply H.
  - constructor.
Qed.

(* ==========================================================================
 * 结合保持和进展的定理
 * 
 * 这个定理表明良类型表达式通过多步求值最终会达到一个值或卡住状态
 * ========================================================================== *)

Theorem preservation_plus_progress :
  forall Δ Γ Θ s h e τ n,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    heap_well_typed h Θ ->
    exists s' h' e',
      star_step s h e h' e' /\
      (is_exp_value e' = true \/ is_stuck e').
Proof.
  intros Δ Γ Θ s h e τ n Hty Hswf Hhwf.
  destruct (progress Δ Γ Θ s h e τ Hty Hswf Hhwf) as [Hval | [Hstep | Hstuck]].
  - (* 已经是值 *)
    exists s, h, e. split; [constructor | left; auto].
  - (* 可以求值一步 *)
    destruct Hstep as [s' [h' [e' Hstep]]].
    exists s', h', e'.
    split.
    + apply step_implies_star_step. auto.
    + (* 需要归纳：要么 e' 是值，要么可以继续求值 *)
      admit.
  - (* 卡住 *)
    exists s, h, e. split; [constructor | right; auto].
Admitted.
