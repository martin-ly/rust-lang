(*** Core Minimal Rules (Coq) ***)

Require Import Coq.Lists.List.
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
    value v1 -> value v2 -> step (EFst (EPair v1 v2)) v1
with subst : nat -> Expr -> Expr -> Expr :=
(* naive placeholder substitution for illustration; capture-avoidance omitted *)
| Sb_Unit  : forall k v, subst k v EUnit = EUnit
| Sb_True  : forall k v, subst k v ETrue = ETrue
| Sb_False : forall k v, subst k v EFalse = EFalse
| Sb_Var_same  : forall k v, subst k v (EVar k) = v
| Sb_Var_other : forall k v x, x <> k -> subst k v (EVar x) = EVar x
| Sb_Abs : forall k v x tx e,
    subst k v (EAbs x tx e) = EAbs x tx (subst (S k) v e)
| Sb_App : forall k v e1 e2,
    subst k v (EApp e1 e2) = EApp (subst k v e1) (subst k v e2)
| Sb_Pair : forall k v e1 e2,
    subst k v (EPair e1 e2) = EPair (subst k v e1) (subst k v e2)
| Sb_Fst : forall k v e,
    subst k v (EFst e) = EFst (subst k v e).
