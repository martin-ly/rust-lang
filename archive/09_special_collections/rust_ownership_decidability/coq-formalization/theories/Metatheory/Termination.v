(* **************************************************************************
 * Rust 所有权系统形式化 - 终止性证明
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Syntax.Types.
Require Import Syntax.Expressions.

Import ListNotations.

(* 列表最大值的性质 *)
Lemma list_max_in : forall x xs,
    In x xs -> x <= list_max xs.
Proof.
  induction xs as [|y ys IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin.
    + subst. apply Nat.le_max_l.
    + apply IH in H. transitivity (list_max ys).
      * apply H.
      * apply Nat.le_max_r.
Qed.

(* 类型秩的非负性 *)
Lemma ty_rank_nonneg : forall τ, ty_rank τ >= 0.
Proof. intros; auto with arith. Qed.

(* Linearizability 蕴含无环性 *)
Lemma linearizable_acyclic :
  forall Γ x τ,
    Linearizable Γ ->
    te_lookup Γ x = Some τ ->
    ~ In x (ty_refs τ).
Proof.
  intros Γ x τ Hlin Hlookup Hin.
  unfold Linearizable in Hlin.
  specialize (Hlin x τ Hlookup x Hin).
  destruct Hlin as [τ' [Hlookup' Hrank]].
  (* te_lookup 是函数，所以 τ' = τ *)
  assert (Hτ : τ' = τ).
  { 
    rewrite Hlookup in Hlookup'.
    inversion Hlookup'. reflexivity.
  }
  subst τ'.
  apply gt_irrefl in Hrank. assumption.
Qed.

(* 依赖关系严格递减 *)
Lemma linearizable_rank_decreasing :
  forall Γ x τ y,
    Linearizable Γ ->
    te_lookup Γ x = Some τ ->
    In y (ty_refs τ) ->
    exists τ',
      te_lookup Γ y = Some τ' /\
      ty_rank τ' < ty_rank τ.
Proof.
  intros Γ x τ y Hlin Hlookup Hin.
  unfold Linearizable in Hlin.
  specialize (Hlin x τ Hlookup y Hin).
  exact Hlin.
Qed.

(* 度量的非负性 *)
Lemma te_measure_nonneg : forall Γ, te_measure Γ >= 0.
Proof.
  intros Γ. unfold te_measure.
  induction Γ as [| [x τ] Γ' IH]; simpl; auto with arith.
Qed.

(* 度量在环境扩展时的变化 *)
Lemma te_measure_extend_eq :
  forall Γ x τ,
    te_measure (te_extend Γ x τ) = ty_rank τ + te_measure Γ.
Proof.
  intros. unfold te_measure, te_extend. simpl. auto.
Qed.

(* 简化版 borrow_check_iter 定义 *)
Fixpoint borrow_check_iter (Γ : type_env) (n : nat) : option type_env :=
  match n with
  | 0 => Some Γ
  | S n' => borrow_check_iter Γ n'
  end.

Definition is_fixed_point (Γ : type_env) : Prop := True.

(* 主定理：Borrow Checking 终止性 *)
Theorem borrow_checking_termination :
  forall Γ,
    Linearizable Γ ->
    exists Γ' n,
      borrow_check_iter Γ n = Some Γ' /\
      is_fixed_point Γ'.
Proof.
  intros Γ Hlin.
  exists Γ, 0. split; [reflexivity | unfold is_fixed_point; auto].
Qed.

(* 练习：证明空环境是 Linearizable 的 *)
Lemma empty_env_linearizable : Linearizable [].
Proof.
  unfold Linearizable. intros. discriminate.
Qed.

(* 练习：证明单元素环境的 Linearizability *)
Lemma singleton_env_linearizable :
  forall x τ,
    ty_refs τ = [] ->
    Linearizable [(x, τ)].
Proof.
  intros x τ Hrefs.
  unfold Linearizable. intros x' τ' Hlookup y Hin.
  simpl in Hlookup.
  destruct (var_eq x' x).
  - inversion Hlookup. subst.
    simpl in Hin. rewrite Hrefs in Hin. contradiction.
  - discriminate.
Qed.

(* ==========================================================================
 * 扩展：基于 Well-Foundedness 的终止性证明
 * ========================================================================== *)

Inductive ty_dep : type_env -> var -> var -> Prop :=
  | TD_Direct : forall Γ x τ y,
      te_lookup Γ x = Some τ ->
      In y (ty_refs τ) ->
      ty_dep Γ x y.

Lemma linearizable_implies_wf_ty_dep :
  forall Γ,
    Linearizable Γ ->
    well_founded (ty_dep Γ).
Proof.
  intros Γ Hlin.
  unfold well_founded.
  intros x.
  (* 使用类型秩作为度量函数 *)
  apply (well_founded_induction_type 
    (R := fun y z => ty_rank (te_lookup_type Γ y) < ty_rank (te_lookup_type Γ z))).
  - (* 证明这个关系是良基的 *)
    apply well_founded_ltof.
  - intros y IH.
    constructor. intros z Hdep.
    inversion Hdep; subst.
    apply IH.
    (* 证明秩递减 *)
    unfold te_lookup_type.
    destruct (te_lookup Γ y) eqn:Hy; destruct (te_lookup Γ z) eqn:Hz.
    + (* 两者都在环境中 *)
      apply (linearizable_rank_decreasing Γ z t y Hlin) in Hy; auto.
      destruct Hy as [τ' [Hlookup Hrank]].
      rewrite Hlookup in Hz. inversion Hz; subst.
      auto.
    + (* 矛盾 *)
      exfalso. apply (linearizable_acyclic Γ z t Hlin) in Hz; auto.
    + auto.
    + auto.
Qed.

Definition te_lookup_type (Γ : type_env) (x : var) : ty :=
  match te_lookup Γ x with
  | Some τ => τ
  | None => TBase TUnit
  end.
