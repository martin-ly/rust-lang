/-! Rust Type System: Progress & Preservation (Skeleton) -/

universe u

constant Expr : Type
constant Ty   : Type
constant Ctx  : Type

constant value : Expr → Prop
constant step  : Expr → Expr → Prop
constant hasType : Ctx → Expr → Ty → Prop

constant empty : Ctx

theorem progress (e : Expr) (t : Ty)
  (h : hasType empty e t) : value e ∨ ∃ e', step e e' := by
  -- TODO: induction on h; cases for Abs/App/ADT/Ref/…
  admit

variable {Γ : Ctx}

theorem preservation {e e' : Expr} {t : Ty}
  (ht : hasType Γ e t) (hs : step e e') : ∃ Γ', hasType Γ' e' t := by
  -- TODO: induction on hs; use substitution lemma
  admit

axiom substitution_lemma
  (Γ : Ctx) (x : Nat) (tx : Ty) (e : Expr) (te : Ty) (v : Expr) :
  hasType Γ v tx → hasType Γ e te → hasType Γ e te

/-- Weakening lemma (placeholder) -/
axiom weakening_lemma
  (Γ : Ctx) (Δ : Ctx) (e : Expr) (t : Ty) :
  hasType Γ e t → hasType Γ e t

/-- Strengthening lemma (placeholder) -/
axiom strengthening_lemma
  (Γ : Ctx) (x : Nat) (tx : Ty) (Δ : Ctx) (e : Expr) (t : Ty) :
  hasType Γ e t → hasType Γ e t

/- Notes:
 - Replace placeholders with project-specific syntax and rules
 - Align with T-Var/T-Abs/T-App/T-Ref/T-Deref and E-* semantics
-/
