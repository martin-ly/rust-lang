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

(* Weakening / Strengthening / Substitution lemmas (placeholders) *)
Axiom weakening_lemma : forall (Gamma Delta : TypeEnv) (e : Expr) (t : Type),
  has_type Gamma e t -> has_type Gamma e t.

Axiom strengthening_lemma : forall (Gamma : TypeEnv) (x : nat) (tx : Type) (Delta : TypeEnv) (e : Expr) (t : Type),
  has_type Gamma e t -> has_type Gamma e t.

Axiom substitution_lemma : forall (Gamma : TypeEnv) (x : nat) (tx : Type) (e : Expr) (te : Type) (v : Expr),
  has_type Gamma v tx -> has_type Gamma e te -> has_type Gamma e te.

Theorem progress : forall e t,
  has_type empty e t -> value e \/ exists e', step e e'.
Proof.
  (* TODO: structure induction on typing derivation; cases for Abs/App/Pair/Fst *)
Admitted.

Theorem preservation : forall Gamma e e' t,
  has_type Gamma e t -> step e e' -> exists Gamma', has_type Gamma' e' t.
Proof.
  (* TODO: induction on step; use substitution lemma. *)
Admitted.

(* Preservation skeleton: beta-reduction (AppAbs) case *)
Lemma preservation_appabs : forall (Gamma : TypeEnv) (x : nat) (tx t : Type) (e v : Expr),
  has_type Gamma (EAbs x tx e) (TyArrow tx t) ->
  has_type Gamma v tx ->
  exists Gamma', has_type Gamma' (subst 0 v e) t.
Proof.
  (* TODO: inversion on typing of abstraction to obtain body typing, then substitution. *)
Admitted.

(* Notes:
   - Placeholders will be replaced by concrete proofs once auxiliary lemmas are provided.
*)
