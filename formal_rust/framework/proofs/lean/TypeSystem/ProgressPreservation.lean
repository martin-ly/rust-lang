/-! Rust Type System: Progress & Preservation (Skeleton) -/

import «TypeSystem».CoreMinimal

open Ty Expr

abbrev Ctx := List Ty
notation:50 "∅" => ([] : Ctx)

abbrev empty : Ctx := ∅

theorem progress (e : Expr) (t : Ty)
  (h : HasType empty e t) : Value e ∨ ∃ e', Step e e' := by
  -- TODO: induction on h; cases for Abs/App/ADT/Ref/…
  admit

variable {Γ : Ctx}

theorem preservation {e e' : Expr} {t : Ty}
  (ht : HasType Γ e t) (hs : Step e e') : ∃ Γ', HasType Γ' e' t := by
  -- TODO: induction on hs; use substitution lemma
  admit

axiom substitution_lemma
  (Γ : Ctx) (x : Nat) (tx : Ty) (e : Expr) (te : Ty) (v : Expr) :
  HasType Γ v tx → HasType Γ e te → HasType Γ e te

/-- Weakening lemma (placeholder) -/
axiom weakening_lemma
  (Γ : Ctx) (Δ : Ctx) (e : Expr) (t : Ty) :
  HasType Γ e t → HasType Γ e t

/-- Strengthening lemma (placeholder) -/
axiom strengthening_lemma
  (Γ : Ctx) (x : Nat) (tx : Ty) (Δ : Ctx) (e : Expr) (t : Ty) :
  HasType Γ e t → HasType Γ e t

/-- Preservation skeleton for β-reduction (AppAbs) case. -/
theorem preservation_appabs
  (Γ : Ctx) (x : Nat) (tx t : Ty) (e v : Expr)
  (habs : HasType Γ (Expr.abs x tx e) (Ty.arrow tx t))
  (hv   : HasType Γ v tx)
  : ∃ Γ', HasType Γ' (CoreMinimal.subst 0 v e) t := by
  -- TODO: Inversion on habs to get HasType (tx :: Γ) e t; then substitution
  admit

/- Notes:
 - Replace placeholders with project-specific syntax and rules
 - Align with T-Var/T-Abs/T-App/T-Ref/T-Deref and E-* semantics
-/
