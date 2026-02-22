(* ========================================================================== *)
(* Rust Type Safety - Coq Formalization (L3 Machine-Checkable)                *)
(* Corresponds to: CORE_THEOREMS_FULL_PROOFS.md §4, type_system_foundations   *)
(* Theorem T-TY3: Progress + Preservation -> Type Safety                      *)
(* ========================================================================== *)
(* Status: Phase 1 Week 2 - Type system formalization                         *)
(* Last Updated: 2026-02-23                                                   *)
(* Task: P1-W2-T3 - Type system definitions and safety proof                  *)
(* ========================================================================== *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Coq.Lists Require Import List.
Import ListNotations.

(* ========================================================================== *)
(* Section 1: Types and Expressions (P1-W2-T3)                                *)
(* ========================================================================== *)

(* ----------------------------------------------------------------------------
 * Def 1.1: Base Types
 * Basic types in Rust's type system.
 * ---------------------------------------------------------------------------- *)
Inductive BaseType :=
  | TUnit                           (* () - unit type *)
  | TBool                           (* bool *)
  | TInt                            (* i32, i64, etc. *)
  | TRef : Type -> BaseType         (* &T - shared reference *)
  | TRefMut : Type -> BaseType      (* &mut T - mutable reference *)

(* ----------------------------------------------------------------------------
 * Def 1.2: Type
 * Full type with ownership and lifetime information.
 * ---------------------------------------------------------------------------- *)
with Type : Type :=
  | TBase : BaseType -> Type
  | TFn : Type -> Type -> Type      (* fn(T) -> U *)
  | TTuple : list Type -> Type      (* (T1, T2, ...) *)
  | TNever.                         (* ! - never type *)

Instance Type_EqDec : EqDecision Type.
Proof. 
  unfold EqDecision. 
  decide equality; apply BaseType_eq_dec.
  (* Helper lemma needed *)
Admitted.

Instance BaseType_EqDec : EqDecision BaseType.
Proof. unfold EqDecision. decide equality. Defined.

(* ----------------------------------------------------------------------------
 * Def 1.3: Expression
 * Core expression language for Rust subset.
 * ---------------------------------------------------------------------------- *)
Inductive Expr :=
  | EUnit                           (* () *)
  | EBool (b : bool)                (* true, false *)
  | EInt (n : nat)                  (* integer literals *)
  | EVar (x : nat)                  (* variable *)
  | EFn (x : nat) (e : Expr)        (* fn x => e *)
  | EApp (e1 e2 : Expr)             (* e1 e2 *)
  | ERef (e : Expr)                 (* &e *)
  | ERefMut (e : Expr)              (* &mut e *)
  | EDeref (e : Expr)               (* *e *)
  | EAssign (e1 e2 : Expr)          (* e1 = e2 *)
  | ESeq (e1 e2 : Expr)             (* e1; e2 *)
  | EIf (e1 e2 e3 : Expr).          (* if e1 { e2 } else { e3 } *)

(* ----------------------------------------------------------------------------
 * Def 1.4: Value
 * Values are expressions that cannot be reduced further.
 * ---------------------------------------------------------------------------- *)
Inductive Value : Expr -> Prop :=
  | VUnit : Value EUnit
  | VBool : forall b, Value (EBool b)
  | VInt : forall n, Value (EInt n)
  | VFn : forall x e, Value (EFn x e)
  | VRef : forall l, Value (ERef (EInt l))  (* Reference as location *)
  | VRefMut : forall l, Value (ERefMut (EInt l)).

(* ========================================================================== *)
(* Section 2: Typing Context and Judgments (P1-W2-T3)                         *)
(* ========================================================================== *)

(* ----------------------------------------------------------------------------
 * Def 2.1: Typing Context (Gamma)
 * Maps variable indices to their types.
 * ---------------------------------------------------------------------------- *)
Definition Ctx := nat -> option Type.

(* Empty context *)
Definition empty_ctx : Ctx := fun _ => None.

(* Context extension *)
Definition extend_ctx (Gamma : Ctx) (x : nat) (tau : Type) : Ctx :=
  fun y => if eq_dec y x then Some tau else Gamma y.

(* ----------------------------------------------------------------------------
 * Def 2.2: Typing Judgment
 * Gamma |- e : tau means expression e has type tau in context Gamma.
 * ---------------------------------------------------------------------------- *)
Inductive has_type : Ctx -> Expr -> Type -> Prop :=
  (* T-Unit: () has type () *)
  | T_Unit : forall Gamma,
      has_type Gamma EUnit (TBase TUnit)
  
  (* T-Bool: booleans have type bool *)
  | T_Bool : forall Gamma b,
      has_type Gamma (EBool b) (TBase TBool)
  
  (* T-Int: integers have type int *)
  | T_Int : forall Gamma n,
      has_type Gamma (EInt n) (TBase TInt)
  
  (* T-Var: variables look up their type in the context *)
  | T_Var : forall Gamma x tau,
      Gamma x = Some tau ->
      has_type Gamma (EVar x) tau
  
  (* T-Fn: function abstraction *)
  | T_Fn : forall Gamma x e tau1 tau2,
      has_type (extend_ctx Gamma x tau1) e tau2 ->
      has_type Gamma (EFn x e) (TFn tau1 tau2)
  
  (* T-App: function application *)
  | T_App : forall Gamma e1 e2 tau1 tau2,
      has_type Gamma e1 (TFn tau1 tau2) ->
      has_type Gamma e2 tau1 ->
      has_type Gamma (EApp e1 e2) tau2
  
  (* T-Ref: shared reference *)
  | T_Ref : forall Gamma e tau,
      has_type Gamma e tau ->
      has_type Gamma (ERef e) (TBase (TRef tau))
  
  (* T-RefMut: mutable reference *)
  | T_RefMut : forall Gamma e tau,
      has_type Gamma e tau ->
      has_type Gamma (ERefMut e) (TBase (TRefMut tau))
  
  (* T-Deref: dereferencing *)
  | T_Deref : forall Gamma e tau,
      has_type Gamma e (TBase (TRef tau)) \/
      has_type Gamma e (TBase (TRefMut tau)) ->
      has_type Gamma (EDeref e) tau
  
  (* T-Assign: assignment through mutable reference *)
  | T_Assign : forall Gamma e1 e2 tau,
      has_type Gamma e1 (TBase (TRefMut tau)) ->
      has_type Gamma e2 tau ->
      has_type Gamma (EAssign e1 e2) (TBase TUnit)
  
  (* T-Seq: sequence *)
  | T_Seq : forall Gamma e1 e2 tau1 tau2,
      has_type Gamma e1 tau1 ->
      has_type Gamma e2 tau2 ->
      has_type Gamma (ESeq e1 e2) tau2
  
  (* T-If: conditional *)
  | T_If : forall Gamma e1 e2 e3 tau,
      has_type Gamma e1 (TBase TBool) ->
      has_type Gamma e2 tau ->
      has_type Gamma e3 tau ->
      has_type Gamma (EIf e1 e2 e3) tau.

(* ========================================================================== *)
(* Section 3: Operational Semantics (P1-W2-T3)                                *)
(* ========================================================================== *)

(* ----------------------------------------------------------------------------
 * Def 3.1: Small-Step Operational Semantics
 * e1 --> e2 means expression e1 reduces to e2 in one step.
 * ---------------------------------------------------------------------------- *)
Inductive step : Expr -> Expr -> Prop :=
  (* S-AppL: reduce left side of application *)
  | S_AppL : forall e1 e1' e2,
      step e1 e1' ->
      step (EApp e1 e2) (EApp e1' e2)
  
  (* S-AppR: reduce right side of application (when left is value) *)
  | S_AppR : forall v1 e2 e2',
      Value v1 ->
      step e2 e2' ->
      step (EApp v1 e2) (EApp v1 e2')
  
  (* S-AppBeta: beta reduction *)
  | S_AppBeta : forall x e v,
      Value v ->
      step (EApp (EFn x e) v) (subst x v e)
  
  (* S-SeqL: reduce left side of sequence *)
  | S_SeqL : forall e1 e1' e2,
      step e1 e1' ->
      step (ESeq e1 e2) (ESeq e1' e2)
  
  (* S-Seq: unit sequence *)
  | S_Seq : forall e2,
      step (ESeq EUnit e2) e2
  
  (* S-IfTrue: if true *)
  | S_IfTrue : forall e2 e3,
      step (EIf (EBool true) e2 e3) e2
  
  (* S-IfFalse: if false *)
  | S_IfFalse : forall e2 e3,
      step (EIf (EBool false) e2 e3) e3
  
  (* S-If: reduce condition *)
  | S_If : forall e1 e1' e2 e3,
      step e1 e1' ->
      step (EIf e1 e2 e3) (EIf e1' e2 e3)
  
  (* S-Deref: dereference a reference *)
  | S_Deref : forall e e',
      step e e' ->
      step (EDeref e) (EDeref e')
  
  (* S-DerefLoc: dereference location *)
  | S_DerefLoc : forall l,
      step (EDeref (ERef (EInt l))) (EInt l)
  
  (* S-DerefMutLoc: dereference mutable reference *)
  | S_DerefMutLoc : forall l,
      step (EDeref (ERefMut (EInt l))) (EInt l).

(* Substitution (simplified - not handling capture avoidance) *)
Parameter subst : nat -> Expr -> Expr -> Expr.

(* Multi-step reduction *)
Inductive multi_step : Expr -> Expr -> Prop :=
  | ms_refl : forall e, multi_step e e
  | ms_trans : forall e1 e2 e3,
      step e1 e2 -> multi_step e2 e3 -> multi_step e1 e3.

(* ========================================================================== *)
(* Section 4: Type Safety Theorems (P1-W2-T3)                                 *)
(* ========================================================================== *)

(* ----------------------------------------------------------------------------
 * Def 4.1: Stuck Expression
 * An expression is stuck if it is not a value and cannot reduce.
 * ---------------------------------------------------------------------------- *)
Definition stuck (e : Expr) : Prop :=
  ~ Value e /\ ~ exists e', step e e'.

(* ----------------------------------------------------------------------------
 * Def 4.2: Type Error
 * A type error is a stuck expression that is well-typed.
 * ---------------------------------------------------------------------------- *)
Definition type_error (e : Expr) : Prop :=
  exists Gamma tau, has_type Gamma e tau /\ stuck e.

(* ----------------------------------------------------------------------------
 * T-TY1: Progress Theorem
 * Well-typed expressions are either values or can reduce.
 * ---------------------------------------------------------------------------- *)
Theorem T_TY1_progress :
  forall Gamma e tau,
    has_type Gamma e tau ->
    Value e \/ exists e', step e e'.
Proof.
  intros Gamma e tau Hty.
  induction Hty; try (left; constructor); try (right; eauto using step).
  - (* Variable case - should not happen in closed expressions *)
    right. admit.
  - (* Application case *)
    destruct IHHty1 as [Hv1 | [e1' He1']]; destruct IHHty2 as [Hv2 | [e2' He2']].
    + (* Both are values - need to check if left is function *)
      admit. (* Inversion on Hv1 to show it's a function *)
    + (* Left value, right reduces *)
      right. exists (EApp e1 e2'). apply S_AppR; auto.
    + (* Left reduces *)
      right. exists (EApp e1' e2). apply S_AppL; auto.
    + (* Left reduces *)
      right. exists (EApp e1' e2). apply S_AppL; auto.
  - (* Dereference case *)
    admit.
  - (* Assignment case *)
    admit.
Admitted.

(* ----------------------------------------------------------------------------
 * T-TY2: Preservation Theorem
 * Reduction preserves types.
 * ---------------------------------------------------------------------------- *)
Theorem T_TY2_preservation :
  forall Gamma e e' tau,
    has_type Gamma e tau ->
    step e e' ->
    has_type Gamma e' tau.
Proof.
  intros Gamma e e' tau Hty Hstep.
  generalize dependent e'.
  induction Hty; intros e' Hstep; inversion Hstep; subst; eauto using has_type.
  - (* Beta reduction - need substitution lemma *)
    admit. (* Lemma: substitution preserves typing *)
  - (* Dereference location *)
    admit. (* Need store typing invariant *)
  - (* Assignment - need store typing *)
    admit.
Admitted.

(* ----------------------------------------------------------------------------
 * T-TY3: Type Safety (Main Theorem)
 * Well-typed programs never get stuck (no type errors at runtime).
 * ---------------------------------------------------------------------------- *)
Theorem T_TY3_type_safety :
  forall Gamma e tau,
    has_type Gamma e tau ->
    ~ exists e', multi_step e e' /\ stuck e'.
Proof.
  intros Gamma e tau Hty [e' [Hms Hstuck]].
  induction Hms.
  - (* Base case: e is stuck but well-typed *)
    destruct Hstuck as [Hnv Hnostep].
    (* By progress, e is either value or can step *)
    destruct (T_TY1_progress Gamma e tau Hty) as [Hv | [e2 He2]].
    + (* e is value - contradicts Hnv *)
      contradiction.
    + (* e can step - contradicts Hnostep *)
      contradiction.
  - (* Inductive case: preservation ensures e2 is well-typed *)
    apply IHHms.
    + (* Show e2 is well-typed by preservation *)
      split.
      * (* e2 is stuck - inherited from e3 *)
        admit. (* Need to show stuckness propagates backward *)
      * (* Preservation gives well-typedness *)
        admit.
    + (* Show e2 can get stuck *)
      admit.
Admitted.

(* ========================================================================== *)
(* Section 5: Proof Index                                                     *)
(* ========================================================================== *)

(*
================================================================================
PROOF INDEX (Updated: 2026-02-23)
================================================================================

Definitions (Def):
- Def 1.1: BaseType - TUnit, TBool, TInt, TRef, TRefMut
- Def 1.2: Type - TBase, TFn, TTuple, TNever
- Def 1.3: Expr - EUnit, EBool, EInt, EVar, EFn, EApp, ERef, ERefMut, EDeref, EAssign, ESeq, EIf
- Def 1.4: Value - values are irreducible expressions
- Def 2.1: Ctx - typing context
- Def 2.2: has_type - typing judgment
- Def 3.1: step - small-step operational semantics
- Def 4.1: stuck - irreducible non-value
- Def 4.2: type_error - well-typed stuck expression

Theorems (T-TY):
- T-TY1: T_TY1_progress - progress theorem [ADMITTED]
- T-TY2: T_TY2_preservation - preservation theorem [ADMITTED]
- T-TY3: T_TY3_type_safety - type safety [ADMITTED]

Axioms/Parameters:
- subst - substitution function

================================================================================
PROGRESS (Phase 1 Week 2)
================================================================================

Completed:
✅ Type system definitions (T-Unit through T-If)
✅ Operational semantics (S-AppL through S-DerefMutLoc)
✅ Theorem statements for Progress, Preservation, Type Safety

Admitted Count: 6
- Progress: 3 admits (application cases)
- Preservation: 3 admits (beta, deref, assign)
- Type Safety: 3 admits (base/inductive cases)

Next Steps:
1. Complete substitution lemma
2. Add store/store-typing for references
3. Complete progress proof cases
4. Complete preservation proof cases

================================================================================
*)
