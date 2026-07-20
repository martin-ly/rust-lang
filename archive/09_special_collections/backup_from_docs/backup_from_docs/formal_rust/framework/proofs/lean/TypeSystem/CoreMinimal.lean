/-! Core Minimal Rules (Lean) -/

inductive Ty : Type
| unit | bool | arrow (t1 t2 : Ty) | prod (t1 t2 : Ty)
open Ty

inductive Expr : Type
| unit : Expr
| ttrue : Expr
| ffalse : Expr
| var (x : Nat) : Expr
| abs (x : Nat) (tx : Ty) (e : Expr) : Expr
| app (e1 e2 : Expr) : Expr
| pair (e1 e2 : Expr) : Expr
| fst (e : Expr) : Expr
open Expr

def Ctx := List Ty

/-- lookup variable in ctx (de Bruijn-like nat index) -/
def lookup : Ctx → Nat → Option Ty
| [], _ => none
| t :: _, 0 => some t
| _ :: Γ, Nat.succ x => lookup Γ x

/-- typing relation (skeleton) -/
inductive HasType : Ctx → Expr → Ty → Prop
| tUnit  (Γ) : HasType Γ Expr.unit Ty.unit
| tTrue  (Γ) : HasType Γ Expr.ttrue Ty.bool
| tFalse (Γ) : HasType Γ Expr.ffalse Ty.bool
| tVar (Γ x t) (h : lookup Γ x = some t) : HasType Γ (Expr.var x) t
| tAbs (Γ x tx e t)
    (he : HasType (tx :: Γ) e t) : HasType Γ (Expr.abs x tx e) (Ty.arrow tx t)
| tApp (Γ e1 e2 t1 t2)
    (h1 : HasType Γ e1 (Ty.arrow t1 t2)) (h2 : HasType Γ e2 t1) :
    HasType Γ (Expr.app e1 e2) t2
| tPair (Γ e1 e2 t1 t2)
    (h1 : HasType Γ e1 t1) (h2 : HasType Γ e2 t2) :
    HasType Γ (Expr.pair e1 e2) (Ty.prod t1 t2)
| tFst (Γ e t1 t2)
    (h : HasType Γ e (Ty.prod t1 t2)) : HasType Γ (Expr.fst e) t1

/-- values -/
inductive Value : Expr → Prop
| vUnit  : Value Expr.unit
| vTrue  : Value Expr.ttrue
| vFalse : Value Expr.ffalse
| vAbs (x tx e) : Value (Expr.abs x tx e)
| vPair (v1 v2) (h1 : Value v1) (h2 : Value v2) : Value (Expr.pair v1 v2)

/-/ substitution (placeholder; capture avoidance omitted) -/
constant subst : Nat → Expr → Expr → Expr

/-- small-step evaluation (skeleton) -/
inductive Step : Expr → Expr → Prop
| sApp1 (e1 e1' e2) (h : Step e1 e1') : Step (Expr.app e1 e2) (Expr.app e1' e2)
| sApp2 (v1 e2 e2') (hv : Value v1) (h : Step e2 e2') :
    Step (Expr.app v1 e2) (Expr.app v1 e2')
| sAppAbs (x tx e v) (hv : Value v) :
    Step (Expr.app (Expr.abs x tx e) v) (subst 0 v e)
| sPair1 (e1 e1' e2) (h : Step e1 e1') :
    Step (Expr.pair e1 e2) (Expr.pair e1' e2)
| sPair2 (v1 e2 e2') (hv : Value v1) (h : Step e2 e2') :
    Step (Expr.pair v1 e2) (Expr.pair v1 e2')
| sFst1 (e e') (h : Step e e') : Step (Expr.fst e) (Expr.fst e')
| sFstPair (v1 v2) (hv1 : Value v1) (hv2 : Value v2) :
    Step (Expr.fst (Expr.pair v1 v2)) v1
