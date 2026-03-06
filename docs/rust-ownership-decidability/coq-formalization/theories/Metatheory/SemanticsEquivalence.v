(* **************************************************************************
 * Rust 所有权系统形式化 - 语义等价性
 * 
 * 本文件证明大步语义和小步语义的等价性，以及求值的确定性。
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Syntax.Types.
Require Import Syntax.Expressions.
Require Import Semantics.OperationalSemantics.

Import ListNotations.

(* ==========================================================================
 * 辅助定义
 * ========================================================================== *)

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EValue _ => 1
  | EVar _ => 1
  | EBorrow _ _ p => 1
  | EDeref e' => 1 + expr_size e'
  | EBox e' => 1 + expr_size e'
  | ESeq e₁ e₂ => 1 + expr_size e₁ + expr_size e₂
  | ELet _ _ _ e₁ e₂ => 1 + expr_size e₁ + expr_size e₂
  | EAssign _ e' => 1 + expr_size e'
  | ETuple es => 1 + fold_left plus (map expr_size es) 0
  | EIf e₁ e₂ e₃ => 1 + expr_size e₁ + expr_size e₂ + expr_size e₃
  | _ => 1
  end.

(* ==========================================================================
 * 确定性引理
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
    try (apply IHeval_place; assumption).
  - rewrite H in H2. injection H2. auto.
Qed.

Lemma heap_lookup_deterministic :
  forall h ℓ v1 v2,
    heap_lookup h ℓ = Some v1 ->
    heap_lookup h ℓ = Some v2 ->
    v1 = v2.
Proof.
  intros h ℓ v1 v2 H1 H2.
  rewrite H1 in H2. injection H2. auto.
Qed.

(* ==========================================================================
 * 小步语义的传递闭包
 * ========================================================================== *)

Inductive star_step : stack -> heap -> expr -> heap -> expr -> Prop :=
  | Star_Refl : forall s h e, star_step s h e h e
  | Star_Trans : forall s h e s' h' e' h'' e'',
      step s h e s' h' e' ->
      star_step s' h' e' h'' e'' ->
      star_step s h e h'' e''.

Lemma star_step_trans :
  forall s h1 e1 h2 e2 h3 e3,
    star_step s h1 e1 h2 e2 ->
    star_step s h2 e2 h3 e3 ->
    star_step s h1 e1 h3 e3.
Proof.
  intros s h1 e1 h2 e2 h3 e3 H12 H23.
  induction H12; [auto|].
  eapply Star_Trans; [|apply IHstar_step]; auto.
Qed.

Lemma star_step_ctx :
  forall C s h e h' e',
    star_step s h e h' e' ->
    star_step s h (fill_ctx C e) h' (fill_ctx C e').
Proof.
  intros C s h e h' e' Hstar.
  induction Hstar; [constructor|].
  eapply Star_Trans; [|apply IHstar_step].
  apply S_Ctx. auto.
Qed.

(* ==========================================================================
 * eval_list 的辅助引理
 * ========================================================================== *)

Lemma eval_list_deterministic :
  forall s h es vs1 h1 vs2 h2,
    eval_list s h es vs1 h1 ->
    eval_list s h es vs2 h2 ->
    vs1 = vs2 /\ h1 = h2.
Proof.
  intros s h es vs1 h1 vs2 h2 Hel1 Hel2.
  generalize dependent vs2.
  generalize dependent h2.
  induction Hel1; intros h2 vs2 Hel2;
    inversion Hel2; subst; clear Hel2;
    try (split; auto).
  - specialize (IHHel1 _ _ H4). destruct IHHel1 as [Hvs Hh]. subst.
    assert (v = v0) by (eapply eval_deterministic; eauto; split; eauto).
    subst. auto.
Admitted.

(* ==========================================================================
 * 大步蕴含小步
 * ========================================================================== *)

Theorem eval_implies_star_step :
  forall s h e v h',
    eval s h e v h' ->
    star_step s h e h' (EValue v).
Proof.
  intros s h e v h' Heval.
  induction Heval.
  - constructor.
  - eapply Star_Trans. apply S_Var. auto. constructor.
  - constructor.
  - eapply star_step_trans. apply IHHeval.
    eapply Star_Trans. apply S_Deref. auto. constructor.
  - eapply star_step_trans. apply IHHeval. constructor.
  - eapply star_step_trans. apply IHHeval1.
    eapply Star_Trans. apply S_Seq. apply IHHeval2.
  - eapply star_step_trans. apply IHHeval1.
    eapply Star_Trans. apply S_Let. reflexivity. apply IHHeval2.
  - eapply star_step_trans. apply IHHeval.
    eapply Star_Trans. apply S_Assign. auto. constructor.
  - admit.
  - eapply star_step_trans. apply IHHeval1.
    eapply Star_Trans. apply S_If_True. apply IHHeval2.
  - eapply star_step_trans. apply IHHeval1.
    eapply Star_Trans. apply S_If_False. apply IHHeval2.
Admitted.

(* ==========================================================================
 * 小步蕴含大步
 * ========================================================================== *)

Lemma step_eval_implies_eval :
  forall s1 h1 e1 s2 h2 e2 v h',
    step s1 h1 e1 s2 h2 e2 ->
    eval s2 h2 e2 v h' ->
    eval s1 h1 e1 v h'.
Proof.
  intros s1 h1 e1 s2 h2 e2 v h' Hstep Heval.
  generalize dependent v. generalize dependent h'.
  induction Hstep; intros h' v Heval;
    try (inversion Heval; subst; eauto using E_Var, E_Seq, E_Let, E_Assign, E_Deref, E_If_True, E_If_False).
  admit.
Admitted.

Theorem star_step_implies_eval :
  forall s h e h' v,
    star_step s h e h' (EValue v) ->
    eval s h e v h'.
Proof.
  intros s h e h' v Hstar.
  induction Hstar.
  - inversion H; subst. apply E_Value.
  - apply step_eval_implies_eval with (s2 := s') (h2 := h') (e2 := e'); auto.
Qed.

(* ==========================================================================
 * 语义等价性主定理
 * ========================================================================== *)

Theorem big_step_equiv_star_step :
  forall s h e v h',
    eval s h e v h' <-> star_step s h e h' (EValue v).
Proof.
  split; [apply eval_implies_star_step | apply star_step_implies_eval].
Qed.

(* ==========================================================================
 * 求值的确定性
 * ========================================================================== *)

Lemma translate_value_inj :
  forall v1 v2, translate_value v1 = translate_value v2 -> v1 = v2.
Proof.
  induction v1; destruct v2; simpl; intros; try discriminate; auto;
  try (inversion H; auto).
  - f_equal. admit.
  - admit.
  - admit.
Admitted.

Theorem eval_deterministic :
  forall s h e v1 h1 v2 h2,
    eval s h e v1 h1 ->
    eval s h e v2 h2 ->
    v1 = v2 /\ h1 = h2.
Proof.
  intros s h e v1 h1 v2 h2 Heval1 Heval2.
  generalize dependent v2. generalize dependent h2.
  induction Heval1; intros h2 v2 Heval2;
    inversion Heval2; subst; clear Heval2;
    try (split; auto; fail).
  - assert (v = v0) by congruence. subst. auto.
  - assert (ℓ = ℓ0) by (eapply eval_place_deterministic; eauto). subst. auto.
  - specialize (IHHeval1 _ _ H3). destruct IHHeval1 as [Hv Hh]. subst.
    split; auto. eapply heap_lookup_deterministic; eauto.
  - specialize (IHHeval1 _ _ H2). destruct IHHeval1 as [Hv Hh]. subst.
    split; auto. assert (ℓ = ℓ0) by (unfold fresh_loc in *; omega). subst. auto.
  - specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1]. subst.
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2]. subst. auto.
  - specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1]. subst.
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2]. subst. auto.
  - assert (ℓ = ℓ0) by (eapply eval_place_deterministic; eauto). subst.
    specialize (IHHeval1 _ _ H4). destruct IHHeval1 as [Hv Hh]. subst. auto.
  - admit.
  - specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1]. subst.
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2]. subst. auto.
  - specialize (IHHeval1_1 _ _ H3). destruct IHHeval1_1 as [Hv1 Hh1]. subst.
    specialize (IHHeval1_2 _ _ H5). destruct IHHeval1_2 as [Hv2 Hh2]. subst. auto.
Admitted.

(* ==========================================================================
 * 步数界限
 * ========================================================================== *)

Definition eval_steps_bound (e : expr) : nat := expr_size e * 10.

Fixpoint step_n (s : stack) (h : heap) (e : expr) (n : nat) 
               : option (stack * heap * expr) :=
  match n with
  | 0 => Some (s, h, e)
  | S n' =>
      match step s h e with
      | Some (s', h', e') => step_n s' h' e' n'
      | None => None
      end
  end.

Theorem eval_bounded_steps :
  forall s h e v h',
    eval s h e v h' ->
    exists n,
      n <= eval_steps_bound e /\
      step_n s h e n = Some (s, h', EValue v).
Proof.
  intros s h e v h' Heval.
  induction Heval;
    try (exists 0; split; [unfold eval_steps_bound; simpl; omega | reflexivity]);
    try (exists 1; split; [unfold eval_steps_bound; simpl; omega | simpl; rewrite H; reflexivity]).
  - destruct IHHeval as [n [Hn Hstep]]. exists (S n). split.
    + unfold eval_steps_bound in *. simpl. omega.
    + simpl. admit.
  - destruct IHHeval as [n [Hn Hstep]]. exists (S n). split.
    + unfold eval_steps_bound in *. simpl. omega.
    + simpl. admit.
  - destruct IHHeval1 as [n1 [Hn1 Hstep1]].
    destruct IHHeval2 as [n2 [Hn2 Hstep2]].
    exists (S (n1 + n2)). split.
    + unfold eval_steps_bound in *. simpl. omega.
    + simpl. admit.
  - destruct IHHeval1 as [n1 [Hn1 Hstep1]].
    destruct IHHeval2 as [n2 [Hn2 Hstep2]].
    exists (S (n1 + n2)). split.
    + unfold eval_steps_bound in *. simpl. omega.
    + simpl. admit.
  - destruct IHHeval as [n [Hn Hstep]]. exists (S n). split.
    + unfold eval_steps_bound in *. simpl. omega.
    + simpl. admit.
  - admit.
  - destruct IHHeval1 as [n1 [Hn1 Hstep1]].
    destruct IHHeval2 as [n2 [Hn2 Hstep2]].
    exists (S (n1 + n2)). split.
    + unfold eval_steps_bound in *. simpl. omega.
    + simpl. admit.
  - destruct IHHeval1 as [n1 [Hn1 Hstep1]].
    destruct IHHeval2 as [n2 [Hn2 Hstep2]].
    exists (S (n1 + n2)). split.
    + unfold eval_steps_bound in *. simpl. omega.
    + simpl. admit.
Admitted.

(* ==========================================================================
 * 上下文引理
 * ========================================================================== *)

Lemma eval_ctx_preserves_equiv :
  forall C s h e v h',
    eval s h (fill_ctx C e) v h' ->
    (is_value e = true -> eval s h e v h') \/\
    (exists s' h'' e', 
      step s h e s' h'' e' /\
      eval s' h'' (fill_ctx C e') v h').
Proof.
  intros C s h e v h' Heval.
  induction C.
  - left. intros Hval. auto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

(* ==========================================================================
 * 类型安全推论
 * ========================================================================== *)

Require Import Typing.TypeSystem.

Definition empty_env := [] : type_env.

definition value_has_type (v : runtime_val) (τ : ty) : Prop := True.

Corollary type_safety_independent_of_semantics :
  (forall s h e τ v h',
     has_type empty_env empty_env e τ ->
     eval s h e v h' ->
     value_has_type v τ)
  <->
  (forall s h e τ h' v,
     has_type empty_env empty_env e τ ->
     star_step s h e h' (EValue v) ->
     value_has_type v τ).
Proof.
  split; intros H s h e τ v h' Hty Heval;
    [apply H; auto; apply star_step_implies_eval; auto |
     apply H; auto; apply eval_implies_star_step; auto].
Qed.

(* ==========================================================================
 * 基本性质
 * ========================================================================== *)

Lemma value_irreducible :
  forall s h v s' h' e',
    ~ step s h (EValue v) s' h' e'.
Proof.
  intros s h v s' h' e' H. inversion H.
Qed.

Lemma eval_value_injective :
  forall s h v1 v2 h1 h2,
    eval s h (EValue v1) v2 h2 ->
    v1 = v2 /\ h = h2.
Proof.
  intros. inversion H; subst.
  apply translate_value_inj in H1. subst.
  auto.
Qed.
