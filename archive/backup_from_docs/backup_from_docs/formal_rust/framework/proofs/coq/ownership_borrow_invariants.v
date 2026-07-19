(*** Ownership & Borrowing Invariants (Skeleton) ***)

Parameter Value Ref Lifetime : Set.
Parameter imm_borrow : Ref -> Value -> Lifetime -> Prop.
Parameter mut_borrow : Ref -> Value -> Lifetime -> Prop.
Parameter within : Lifetime -> Lifetime -> Prop. (* l1 within l2 *)

(* Invariants *)
Axiom mut_unique : forall r v l,
  mut_borrow r v l ->
  (* no other simultaneous borrows; placeholder predicate *) True.

Axiom imm_alias_readonly : forall r1 r2 v l,
  imm_borrow r1 v l -> imm_borrow r2 v l ->
  (* only read effects; placeholder *) True.

Axiom lifetime_no_escape : forall r v l owner_l,
  (imm_borrow r v l \/ mut_borrow r v l) -> within l owner_l ->
  (* borrow does not outlive owner; placeholder *) True.
