/-! Ownership & Borrowing Invariants (Skeleton) -/

constant Value    : Type
constant Ref      : Type
constant Lifetime : Type

constant immBorrow : Ref → Value → Lifetime → Prop
constant mutBorrow : Ref → Value → Lifetime → Prop
constant within    : Lifetime → Lifetime → Prop  -- l1 within l2

axiom mut_unique
  (r : Ref) (v : Value) (l : Lifetime) :
  mutBorrow r v l → True

axiom imm_alias_readonly
  (r1 r2 : Ref) (v : Value) (l : Lifetime) :
  immBorrow r1 v l → immBorrow r2 v l → True

axiom lifetime_no_escape
  (r : Ref) (v : Value) (l ownerL : Lifetime) :
  (immBorrow r v l ∨ mutBorrow r v l) → within l ownerL → True
