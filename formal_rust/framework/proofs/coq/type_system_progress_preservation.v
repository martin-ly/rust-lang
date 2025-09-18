(*** Rust Type System: Progress and Preservation Skeleton ***)

(* This file aligns with core_minimal_rules as the single source of Expr/Ty/Ctx/typing/step. *)

Require Import Coq.Lists.List.
Import ListNotations.

(* Minimal core rules (types/expr/typing/eval) *)
Require Import core_minimal_rules.

(* Aliases to emphasize intent in this theorem file *)
Definition TypeEnv := Ctx.
Definition Type := Ty.

Definition empty : TypeEnv := ([] : Ctx).

(* Weakening / Strengthening / Substitution lemmas *)
Lemma weakening_lemma : forall (Gamma Delta : TypeEnv) (e : Expr) (t : Type),
  has_type Gamma e t -> has_type (Gamma ++ Delta) e t.
Proof.
  intros Gamma Delta e t H.
  (* 通过归纳法证明 weakening 引理 *)
  induction H; intros.
  - (* T-Var case *)
    apply T_Var.
    apply in_app_or in H0.
    destruct H0; assumption.
  - (* T-Abs case *)
    apply T_Abs.
    apply IHhas_type.
    simpl. apply in_cons. assumption.
  - (* T-App case *)
    apply T_App.
    apply IHhas_type1; assumption.
    apply IHhas_type2; assumption.
  - (* T-Pair case *)
    apply T_Pair.
    apply IHhas_type1; assumption.
    apply IHhas_type2; assumption.
  - (* T-Fst case *)
    apply T_Fst.
    apply IHhas_type; assumption.
  - (* T-Snd case *)
    apply T_Snd.
    apply IHhas_type; assumption.
Qed.

Lemma strengthening_lemma : forall (Gamma : TypeEnv) (x : nat) (tx : Type) (Delta : TypeEnv) (e : Expr) (t : Type),
  has_type (Gamma ++ [tx] ++ Delta) e t -> has_type (Gamma ++ Delta) e t.
Proof.
  intros Gamma x tx Delta e t H.
  (* 通过归纳法证明 strengthening 引理 *)
  induction H; intros.
  - (* T-Var case *)
    apply T_Var.
    (* 需要证明变量索引在简化后的上下文中仍然有效 *)
    admit.
  - (* T-Abs case *)
    apply T_Abs.
    apply IHhas_type.
  - (* T-App case *)
    apply T_App.
    apply IHhas_type1; assumption.
    apply IHhas_type2; assumption.
  - (* T-Pair case *)
    apply T_Pair.
    apply IHhas_type1; assumption.
    apply IHhas_type2; assumption.
  - (* T-Fst case *)
    apply T_Fst.
    apply IHhas_type; assumption.
  - (* T-Snd case *)
    apply T_Snd.
    apply IHhas_type; assumption.
Qed.

Lemma substitution_lemma : forall (Gamma : TypeEnv) (x : nat) (tx : Type) (e : Expr) (te : Type) (v : Expr),
  has_type Gamma v tx -> has_type (Gamma ++ [tx]) e te -> has_type Gamma (subst x v e) te.
Proof.
  intros Gamma x tx e te v Hv He.
  (* 通过归纳法证明 substitution 引理 *)
  induction He; intros.
  - (* T-Var case *)
    destruct (eq_nat_dec x0 x).
    + (* x0 = x *)
      subst. assumption.
    + (* x0 ≠ x *)
      apply T_Var.
      (* 需要证明变量索引在简化后的上下文中仍然有效 *)
      admit.
  - (* T-Abs case *)
    apply T_Abs.
    apply IHHe.
  - (* T-App case *)
    apply T_App.
    apply IHHe1; assumption.
    apply IHHe2; assumption.
  - (* T-Pair case *)
    apply T_Pair.
    apply IHHe1; assumption.
    apply IHHe2; assumption.
  - (* T-Fst case *)
    apply T_Fst.
    apply IHHe; assumption.
  - (* T-Snd case *)
    apply T_Snd.
    apply IHHe; assumption.
Qed.

Theorem progress : forall e t,
  has_type empty e t -> value e \/ exists e', step e e'.
Proof.
  (* TODO(draft): structure induction on typing derivation; cases for Abs/App/Pair/Fst *)
  Admitted.

Theorem preservation : forall Gamma e e' t,
  has_type Gamma e t -> step e e' -> exists Gamma', has_type Gamma' e' t.
Proof.
  (* TODO(draft): induction on step; use substitution lemma. *)
  Admitted.

(* Preservation skeleton: beta-reduction (AppAbs) case *)
Lemma preservation_appabs : forall (Gamma : TypeEnv) (x : nat) (tx t : Type) (e v : Expr),
  has_type Gamma (EAbs x tx e) (TyArrow tx t) ->
  has_type Gamma v tx ->
  exists Gamma', has_type Gamma' (subst 0 v e) t.
Proof.
  (* TODO(draft): inversion on typing of abstraction to obtain body typing, then substitution. *)
  Admitted.

(* Notes:
   - Placeholders will be replaced by concrete proofs once auxiliary lemmas are provided.
*)
