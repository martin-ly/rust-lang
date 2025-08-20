(*** Rust Type System: Progress and Preservation Skeleton ***)

(* Placeholder syntax: this is a scaffolding file to be refined. *)

Require Import Coq.Lists.List.
Import ListNotations.

(* Minimal core rules (types/expr/typing/eval) *)
Require Import core_minimal_rules.

Parameter Expr TypeEnv Type : Set.
Parameter value : Expr -> Prop.
Parameter step : Expr -> Expr -> Prop.
Parameter has_type : TypeEnv -> Expr -> Type -> Prop.

Axiom empty : TypeEnv.

(* Weakening / Strengthening / Substitution lemmas (placeholders) *)
Axiom weakening_lemma : forall Gamma Delta e t,
  has_type Gamma e t -> has_type (* extension *) (* Gamma,Delta *) Gamma e t.

Axiom strengthening_lemma : forall Gamma x tx Delta e t,
  (* x not free in e, omitted here as placeholder *)
  has_type (* Gamma,x:tx,Delta *) Gamma e t -> has_type (* Gamma,Delta *) Gamma e t.

Axiom substitution_lemma : forall Gamma x tx e te v,
  has_type Gamma v tx -> has_type Gamma e te -> has_type Gamma e te.

Theorem progress : forall e t,
  has_type empty e t -> value e \/ exists e', step e e'.
Proof.
  (* TODO: structure induction on typing derivation; cases for Abs/App/ADT/Ref/etc. *)
Admitted.

Theorem preservation : forall Gamma e e' t,
  has_type Gamma e t -> step e e' -> exists Gamma', has_type Gamma' e' t.
Proof.
  (* TODO: induction on step; use substitution lemma. *)
Admitted.

(* Notes:
   - Replace placeholders with the concrete syntax imported from the project model
   - Align rules T-Var/T-Abs/T-App/T-Ref/T-Deref and E-* as per language spec
*)
