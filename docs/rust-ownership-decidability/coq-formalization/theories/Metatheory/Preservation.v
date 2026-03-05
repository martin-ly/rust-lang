(* **************************************************************************
 * Rust 所有权系统形式化 - 类型保持证明 (Preservation)
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Syntax.Types.
Require Import Syntax.Expressions.
Require Import Typing.TypeSystem.
Require Import Semantics.OperationalSemantics.

Import ListNotations.

(* ==========================================================================
 * 栈类型良好性
 * ========================================================================== *)

Definition stack_well_typed (s : stack) (Γ : type_env) : Prop :=
  forall x rv,
    stack_lookup s x = Some rv ->
    exists τ,
      te_lookup Γ x = Some τ /\
      value_has_runtime_type rv τ

with value_has_runtime_type (rv : runtime_val) (τ : ty) : Prop :=
  match rv, τ with
  | RVUnit, TBase TUnit => True
  | RVBool _, TBase TBool => True
  | RVInt _, TBase TI32 => True
  | RVInt _, TBase TI64 => True
  | RVChar _, TBase TChar => True
  | RVString _, TBase TStr => True
  | RVLoc ℓ, TRef ρ ω τ => True
  | RVTuple rvs, TTuple τs => Forall2 value_has_runtime_type rvs τs
  | _, _ => False
  end.

(* ==========================================================================
 * 值的类型判断
 * ========================================================================== *)

Inductive has_type_value : 
  region_env -> type_env -> loan_env -> runtime_val -> ty -> Prop :=
  | HTV_Unit : forall Δ Γ Θ,
      has_type_value Δ Γ Θ RVUnit (TBase TUnit)
  | HTV_Bool : forall Δ Γ Θ b,
      has_type_value Δ Γ Θ (RVBool b) (TBase TBool)
  | HTV_Int : forall Δ Γ Θ n,
      has_type_value Δ Γ Θ (RVInt n) (TBase TI32)
  | HTV_Char : forall Δ Γ Θ c,
      has_type_value Δ Γ Θ (RVChar c) (TBase TChar)
  | HTV_String : forall Δ Γ Θ s,
      has_type_value Δ Γ Θ (RVString s) (TBase TStr)
  | HTV_Ref : forall Δ Γ Θ ℓ ρ ω τ,
      has_type_value Δ Γ Θ (RVLoc ℓ) (TRef ρ ω τ)
  | HTV_Tuple : forall Δ Γ Θ rvs τs,
      Forall3 (has_type_value Δ Γ Θ) rvs τs ->
      has_type_value Δ Γ Θ (RVTuple rvs) (TTuple τs).

Definition heap_well_typed (h : heap) (Θ : loan_env) : Prop := True.

(* ==========================================================================
 * 主定理：类型保持 (Preservation)
 * ========================================================================== *)

Theorem preservation :
  forall Δ Γ Θ s h e τ s' h' v,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    eval s h e v h' ->
    exists Γ' Θ',
      has_type_value Δ Γ' Θ' v τ /\
      stack_well_typed s' Γ' /\
      heap_well_typed h' Θ'.
Proof.
  intros Δ Γ Θ s h e τ s' h' v Hty Hswf Heval.
  generalize dependent Θ.
  generalize dependent Γ.
  induction Heval; intros.
  
  (* Case: E_Value *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + destruct v; simpl in *; try constructor.
    + auto.
    + auto.
    
  (* Case: E_Var *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + destruct v; simpl in *; try constructor.
    + auto.
    + auto.
    
  (* Case: E_Borrow *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + constructor.
    + auto.
    + auto.
    
  (* Case: E_Deref *)
  - inversion Hty; subst.
    specialize (IHHeval _ _ Hswf H4). destruct IHHeval as [Γ' [Θ' [Hv [Hswf' Hhwf]]]].
    exists Γ', Θ'. split; [|split]; auto.
    
  (* Case: E_Box *)
  - inversion Hty; subst.
    specialize (IHHeval _ _ Hswf H3). destruct IHHeval as [Γ' [Θ' [Hv [Hswf' Hhwf]]]].
    exists Γ', Θ'. split; [|split]; auto.
    + constructor.
    + auto.
    + auto.
    
  (* Case: E_Seq *)
  - inversion Hty; subst.
    specialize (IHHeval1 _ _ Hswf H3). destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    specialize (IHHeval2 _ _ Hswf1 H5). destruct IHHeval2 as [Γ2 [Θ2 [Hv2 [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. split; [|split]; auto.
    
  (* Case: E_Let *)
  - inversion Hty; subst.
    specialize (IHHeval1 _ _ Hswf H5). destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    exists (te_extend Γ1 x t), Θ1. split; [|split].
    + auto.
    + admit. (* 扩展环境保持良好性 *)
    + auto.
    
  (* Case: E_Assign *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + constructor.
    + auto.
    + auto.
    
  (* Case: E_Tuple *)
  - inversion Hty; subst.
    admit. (* 列表归纳 *)
    
  (* Case: E_If_True *)
  - inversion Hty; subst.
    specialize (IHHeval1 _ _ Hswf H5). destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    specialize (IHHeval2 _ _ Hswf1 H6). destruct IHHeval2 as [Γ2 [Θ2 [Hv2 [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. split; [|split]; auto.
    
  (* Case: E_If_False *)
  - inversion Hty; subst.
    specialize (IHHeval1 _ _ Hswf H5). destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    specialize (IHHeval2 _ _ Hswf1 H6). destruct IHHeval2 as [Γ2 [Θ2 [Hv2 [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. split; [|split]; auto.
Admitted.

(* ==========================================================================
 * 扩展定理
 * ========================================================================== *)

Lemma eval_preserves_fv :
  forall s h e v h',
    eval s h e v h' ->
    forall x,
      In x (expr_vars e) ->
      exists v', stack_lookup s x = Some v'.
Proof.
  admit. (* 对 eval 进行归纳 *)
Admitted.

Corollary no_type_errors :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    ~ (exists s' h' msg, eval s h e RVUnit h').
Proof.
  admit. (* 假设求值不会返回错误 *)
Admitted.

(* ==========================================================================
 * 小步语义的类型保持
 * ========================================================================== *)

Theorem preservation_small_step :
  forall s h e s' h' e' Δ Γ Θ τ,
    has_type Δ Γ Θ e τ ->
    step s h e s' h' e' ->
    exists Γ' Θ',
      has_type Δ Γ' Θ' e' τ /\
      stack_well_typed s' Γ' /\
      heap_well_typed h' Θ'.
Proof.
  admit. (* 对 step 进行归纳 *)
Admitted.

Theorem preservation_star_step :
  forall s h e h' e' Δ Γ Θ τ,
    has_type Δ Γ Θ e τ ->
    star_step s h e h' e' ->
    exists Γ' Θ',
      has_type Δ Γ' Θ' e' τ /\
      stack_well_typed (cfg_stack (mk_config s h e')) Γ' /\
      heap_well_typed h' Θ'.
Proof.
  admit. (* 对 star_step 进行归纳 *)
Admitted.

(* ==========================================================================
 * 辅助引理
 * ========================================================================== *)

Lemma te_extend_preserves_wf :
  forall Δ Γ x τ,
    ty_wellformed Δ τ ->
    (forall y τ', te_lookup Γ y = Some τ' -> ty_wellformed Δ τ') ->
    forall y τ', te_lookup (te_extend Γ x τ) y = Some τ' -> ty_wellformed Δ τ'.
Proof.
  intros Δ Γ x τ Hwf H Γ' y τ' Hlookup.
  simpl in Hlookup.
  destruct (var_eq y x).
  - inversion Hlookup. subst. auto.
  - apply H. auto.
Qed.

Lemma subtype_preserves_value_type :
  forall Δ τ₁ τ₂ v,
    τ₁ <: τ₂ ->
    value_has_runtime_type v τ₁ ->
    value_has_runtime_type v τ₂.
Proof.
  admit. (* 对子类型关系进行归纳 *)
Admitted.
