(*** Rust Type System: HM Inference Soundness/Completeness Skeleton ***)

Parameter Expr TypeEnv Type : Set.
Parameter infer : TypeEnv -> Expr -> option Type.
Parameter has_type : TypeEnv -> Expr -> Type -> Prop.

(* Constraints and unification placeholders *)
Parameter Constraint : Set.
Parameter Subst : Set.
Parameter satisfies : Subst -> Constraint -> Prop.
Parameter unify : list Constraint -> option Subst.

Theorem unify_sound : forall C S,
  unify C = Some S -> forall c, In c C -> satisfies S c.
Proof.
Admitted.

Theorem unify_complete : forall C,
  (exists S', forall c, In c C -> satisfies S' c) ->
  exists S, unify C = Some S.
Proof.
Admitted.

Theorem hm_soundness : forall Gamma e t,
  infer Gamma e = Some t -> has_type Gamma e t.
Proof.
  (* TODO: prove by induction on inference; constraints/unification side conditions *)
Admitted.

Theorem hm_completeness : forall Gamma e t,
  has_type Gamma e t -> exists t', infer Gamma e = Some t'.
Proof.
  (* TODO: construct constraints and show unification succeeds *)
Admitted.

Theorem principal_types : forall Gamma e t,
  has_type Gamma e t -> exists tp,
    infer Gamma e = Some tp /\ (* any other typed t is instance of tp *) True.
Proof.
  (* TODO: formalize generalization/instantiation relation *)
Admitted.
