(*** Core Minimal Rules (Coq) ***)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* Types *)
Inductive Ty : Type :=
| TyUnit
| TyBool
| TyArrow (t1 t2 : Ty)
| TyProd  (t1 t2 : Ty).

(* Expressions *)
Inductive Expr : Type :=
| EUnit
| ETrue | EFalse
| EVar  (x : nat)
| EAbs  (x : nat) (tx : Ty) (e : Expr)
| EApp  (e1 e2 : Expr)
| EPair (e1 e2 : Expr)
| EFst  (e : Expr).

(* Context as list of types, variable by de Bruijn/nat *)
Definition Ctx := list Ty.

Fixpoint lookup (G : Ctx) (x : nat) : option Ty :=
  match G, x with
  | [], _ => None
  | t :: _, 0 => Some t
  | _ :: G', S x' => lookup G' x'
  end.

(* Typing *)
Inductive has_type : Ctx -> Expr -> Ty -> Prop :=
| T_Unit  : forall G, has_type G EUnit TyUnit
| T_True  : forall G, has_type G ETrue TyBool
| T_False : forall G, has_type G EFalse TyBool
| T_Var   : forall G x t,
    lookup G x = Some t -> has_type G (EVar x) t
| T_Abs   : forall G x tx e t,
    has_type (tx :: G) e t -> has_type G (EAbs x tx e) (TyArrow tx t)
| T_App   : forall G e1 e2 t1 t2,
    has_type G e1 (TyArrow t1 t2) -> has_type G e2 t1 -> has_type G (EApp e1 e2) t2
| T_Pair  : forall G e1 e2 t1 t2,
    has_type G e1 t1 -> has_type G e2 t2 -> has_type G (EPair e1 e2) (TyProd t1 t2)
| T_Fst   : forall G e t1 t2,
    has_type G e (TyProd t1 t2) -> has_type G (EFst e) t1.

(* Values *)
Inductive value : Expr -> Prop :=
| V_Unit : value EUnit
| V_True : value ETrue
| V_False : value EFalse
| V_Abs  : forall x tx e, value (EAbs x tx e)
| V_Pair : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2).

(* Substitution (naive; capture-avoidance omitted) *)
Fixpoint subst (k : nat) (v : Expr) (e : Expr) : Expr :=
  match e with
  | EUnit => EUnit
  | ETrue => ETrue
  | EFalse => EFalse
  | EVar x => if Nat.eqb x k then v else EVar x
  | EAbs x tx e1 => EAbs x tx (subst (S k) v e1)
  | EApp e1 e2 => EApp (subst k v e1) (subst k v e2)
  | EPair e1 e2 => EPair (subst k v e1) (subst k v e2)
  | EFst e1 => EFst (subst k v e1)
  end.

(* Small-step eval *)
Inductive step : Expr -> Expr -> Prop :=
| S_App1 : forall e1 e1' e2,
    step e1 e1' -> step (EApp e1 e2) (EApp e1' e2)
| S_App2 : forall v1 e2 e2',
    value v1 -> step e2 e2' -> step (EApp v1 e2) (EApp v1 e2')
| S_AppAbs : forall x tx e v,
    value v -> step (EApp (EAbs x tx e) v) (subst 0 v e)
| S_Pair1 : forall e1 e1' e2,
    step e1 e1' -> step (EPair e1 e2) (EPair e1' e2)
| S_Pair2 : forall v1 e2 e2',
    value v1 -> step e2 e2' -> step (EPair v1 e2) (EPair v1 e2')
| S_Fst1 : forall e e',
    step e e' -> step (EFst e) (EFst e')
| S_FstPair : forall v1 v2,
    value v1 -> value v2 -> step (EFst (EPair v1 v2)) v1.
