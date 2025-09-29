/-! Rust Type System: HM Inference Soundness/Completeness (Skeleton) -/

constant Expr : Type
constant Ty   : Type
constant Ctx  : Type

constant infer   : Ctx → Expr → Option Ty
constant hasType : Ctx → Expr → Ty → Prop

/-- Constraints and unification placeholders -/
constant Constraint : Type
constant Subst      : Type
constant satisfies  : Subst → Constraint → Prop
constant unify      : List Constraint → Option Subst

/-- Unification soundness (placeholder) -/
axiom unify_sound (C : List Constraint) (S : Subst) :
  unify C = some S → ∀ c, c ∈ C → satisfies S c

/-- Unification completeness (placeholder) -/
axiom unify_complete (C : List Constraint) :
  (∃ S', ∀ c, c ∈ C → satisfies S' c) → ∃ S, unify C = some S

/-- Soundness of HM inference (placeholder) -/
 theorem hm_soundness (Γ : Ctx) (e : Expr) (t : Ty)
  (h : infer Γ e = some t) : hasType Γ e t := by
  admit

/-- Completeness of HM inference (placeholder) -/
 theorem hm_completeness (Γ : Ctx) (e : Expr) (t : Ty)
  (ht : hasType Γ e t) : ∃ t', infer Γ e = some t' := by
  admit

/-- Principal types (placeholder) -/
axiom principal_types (Γ : Ctx) (e : Expr) (t : Ty) :
  hasType Γ e t → ∃ tp, infer Γ e = some tp
