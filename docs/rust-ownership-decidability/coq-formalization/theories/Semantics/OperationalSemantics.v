(* **************************************************************************
 * Rust 所有权系统形式化 - 操作语义
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Syntax.Types.
Require Import Syntax.Expressions.

Import ListNotations.

(* ==========================================================================
 * 运行时环境
 * ========================================================================== *)

Definition loc := nat.

Inductive runtime_val : Type :=
  | RVUnit : runtime_val
  | RVBool : bool -> runtime_val
  | RVInt : Z -> runtime_val
  | RVChar : ascii -> runtime_val
  | RVString : string -> runtime_val
  | RVLoc : loc -> runtime_val
  | RVTuple : list runtime_val -> runtime_val
  | RVStruct : type_name -> list (field_name * runtime_val) -> runtime_val
  | RVClosure : fn_name -> list (var * runtime_val) -> runtime_val.

Definition heap := list (loc * runtime_val).

Fixpoint heap_lookup (h : heap) (ℓ : loc) : option runtime_val :=
  match h with
  | [] => None
  | (ℓ', v) :: h' => 
      if Nat.eqb ℓ ℓ' then Some v else heap_lookup h' ℓ
  end.

Definition heap_extend (h : heap) (ℓ : loc) (v : runtime_val) : heap :=
  (ℓ, v) :: h.

Fixpoint heap_update (h : heap) (ℓ : loc) (v : runtime_val) : heap :=
  match h with
  | [] => [(ℓ, v)]
  | (ℓ', v') :: h' => 
      if Nat.eqb ℓ ℓ'
      then (ℓ, v) :: h'
      else (ℓ', v') :: heap_update h' ℓ v
  end.

Definition stack := list (var * runtime_val).

Fixpoint stack_lookup (s : stack) (x : var) : option runtime_val :=
  match s with
  | [] => None
  | (y, v) :: s' => 
      if var_eq x y then Some v else stack_lookup s' x
  end.

Definition stack_extend (s : stack) (x : var) (v : runtime_val) : stack :=
  (x, v) :: s.

Record config : Type := mk_config {
  cfg_stack : stack;
  cfg_heap : heap;
  cfg_expr : expr
}.

(* ==========================================================================
 * 位置求值
 * ========================================================================== *)

Inductive eval_place : stack -> heap -> place -> loc -> Prop :=
  | EP_Var : forall s h x ℓ,
      stack_lookup s x = Some (RVLoc ℓ) ->
      eval_place s h (PVar x) ℓ
  | EP_Deref : forall s h p ℓ v ℓ',
      eval_place s h p ℓ ->
      heap_lookup h ℓ = Some v ->
      True ->
      eval_place s h (PDeref p) ℓ'
  | EP_Field : forall s h p f ℓ ℓ',
      eval_place s h p ℓ ->
      True ->
      eval_place s h (PField p f) ℓ'.

(* ==========================================================================
 * 大步操作语义
 * ========================================================================== *)

Inductive eval : stack -> heap -> expr -> runtime_val -> heap -> Prop :=
  | E_Value : forall s h v,
      eval s h (EValue (translate_value v)) (translate_value v) h
  
  | E_Var : forall s h x v,
      stack_lookup s x = Some v ->
      eval s h (EVar x) v h
  
  | E_Borrow : forall s h p ℓ h' r,
      eval_place s h p ℓ ->
      h' = h ->
      eval s h (EBorrow RStatic Shrd p) (RVLoc ℓ) h'
  
  | E_Deref : forall s h e ℓ v h',
      eval s h e (RVLoc ℓ) h' ->
      heap_lookup h' ℓ = Some v ->
      eval s h (EDeref e) v h'
  
  | E_Box : forall s h e v h' ℓ,
      eval s h e v h' ->
      ℓ = fresh_loc h' ->
      eval s h (EBox e) (RVLoc ℓ) (heap_extend h' ℓ v)
  
  | E_Seq : forall s h e₁ e₂ v₁ v₂ h' h'',
      eval s h e₁ v₁ h' ->
      eval s h' e₂ v₂ h'' ->
      eval s h (ESeq e₁ e₂) v₂ h''
  
  | E_Let : forall s h ω x τ e₁ e₂ v₁ v₂ h' h'' ℓ,
      eval s h e₁ v₁ h' ->
      ℓ = fresh_loc h' ->
      eval (stack_extend (stack_extend s x (RVLoc ℓ)) x (RVLoc ℓ)) 
           (heap_extend h' ℓ v₁) e₂ v₂ h'' ->
      eval s h (ELet ω x τ e₁ e₂) v₂ h''
  
  | E_Assign : forall s h p e ℓ v h' h'',
      eval_place s h p ℓ ->
      eval s h e v h' ->
      h'' = heap_update h' ℓ v ->
      eval s h (EAssign p e) RVUnit h''
  
  | E_Tuple : forall s h es vs h',
      eval_list s h es vs h' ->
      eval s h (ETuple es) (RVTuple vs) h'
  
  | E_If_True : forall s h e₁ e₂ e₃ v h',
      eval s h e₁ (RVBool true) h' ->
      eval s h' e₂ v h' ->
      eval s h (EIf e₁ e₂ e₃) v h'
  
  | E_If_False : forall s h e₁ e₂ e₃ v h',
      eval s h e₁ (RVBool false) h' ->
      eval s h' e₃ v h' ->
      eval s h (EIf e₁ e₂ e₃) v h'

with eval_list : stack -> heap -> list expr -> list runtime_val -> heap -> Prop :=
  | EL_Nil : forall s h,
      eval_list s h [] [] h
  | EL_Cons : forall s h e es v vs h' h'',
      eval s h e v h' ->
      eval_list s h' es vs h'' ->
      eval_list s h (e :: es) (v :: vs) h''

with translate_value : value -> runtime_val :=
  fun v => match v with
  | VUnit => RVUnit
  | VBool b => RVBool b
  | VInt n => RVInt n
  | VChar c => RVChar c
  | VString s => RVString s
  | VLoc ℓ => RVLoc ℓ
  | VTupleV vs => RVTuple (map translate_value vs)
  | _ => RVUnit
  end.

Definition fresh_loc (h : heap) : loc :=
  1 + list_max (map fst h).

Fixpoint list_max_nat (ns : list nat) : nat :=
  match ns with
  | [] => 0
  | n :: ns' => max n (list_max_nat ns')
  end.

(* ==========================================================================
 * 小步操作语义
 * ========================================================================== *)

Inductive eval_ctx : Type :=
  | Hole : eval_ctx
  | CSeq : eval_ctx -> expr -> eval_ctx
  | CLet : mutability -> var -> ty -> eval_ctx -> expr -> eval_ctx
  | CAssign : place -> eval_ctx -> eval_ctx
  | CIf : eval_ctx -> expr -> expr -> eval_ctx
  | CTuple : list runtime_val -> eval_ctx -> list expr -> eval_ctx.

Fixpoint fill_ctx (C : eval_ctx) (e : expr) : expr :=
  match C with
  | Hole => e
  | CSeq C' e' => ESeq (fill_ctx C' e) e'
  | CLet ω x τ C' e' => ELet ω x τ (fill_ctx C' e) e'
  | CAssign p C' => EAssign p (fill_ctx C' e)
  | CIf C' e₁ e₂ => EIf (fill_ctx C' e) e₁ e₂
  | CTuple vs C' es => ETuple (map (fun v => EValue v) vs ++ [fill_ctx C' e] ++ es)
  end.

Inductive step : stack -> heap -> expr -> stack -> heap -> expr -> Prop :=
  | S_Var : forall s h x v,
      stack_lookup s x = Some v ->
      step s h (EVar x) s h (EValue v)
  
  | S_Seq : forall s h v e,
      step s h (ESeq (EValue v) e) s h e
  
  | S_Let : forall s h ω x τ v e ℓ,
      ℓ = fresh_loc h ->
      step s h (ELet ω x τ (EValue v) e) 
           (stack_extend s x (RVLoc ℓ)) 
           (heap_extend h ℓ v) e
  
  | S_Assign : forall s h p v ℓ,
      eval_place s h p ℓ ->
      step s h (EAssign p (EValue v)) s (heap_update h ℓ v) (EValue RVUnit)
  
  | S_Deref : forall s h ℓ v,
      heap_lookup h ℓ = Some v ->
      step s h (EDeref (EValue (RVLoc ℓ))) s h (EValue v)
  
  | S_If_True : forall s h e₁ e₂,
      step s h (EIf (EValue (RVBool true)) e₁ e₂) s h e₁
  
  | S_If_False : forall s h e₁ e₂,
      step s h (EIf (EValue (RVBool false)) e₁ e₂) s h e₂
  
  | S_Ctx : forall s h C e s' h' e',
      step s h e s' h' e' ->
      step s h (fill_ctx C e) s' h' (fill_ctx C e').

Inductive star_step : stack -> heap -> expr -> heap -> expr -> Prop :=
  | Star_Refl : forall s h e, star_step s h e h e
  | Star_Trans : forall s h e s' h' e' s'' h'' e'',
      step s h e s' h' e' ->
      star_step s' h' e' h'' e'' ->
      star_step s h e h'' e''.

(* ==========================================================================
 * 求值的性质
 * ========================================================================== *)

Lemma value_cannot_step :
  forall s h v s' h' e',
    ~ step s h (EValue v) s' h' e'.
Proof.
  intros s h v s' h' e' H.
  inversion H.
Qed.

Theorem big_step_small_step_equivalence :
  forall s h e v h',
    eval s h e v h' <->
    star_step s h e h' (EValue v).
Proof.
  admit. (* 语义等价性证明 *)
Admitted.

(* ==========================================================================
 * 求值示例
 * ========================================================================== *)

Example eval_ex_let :
  let e := e_let "x"%string ti32 (EValue (VInt 5)) (EVar "x"%string) in
  forall s h,
  exists ℓ h',
    eval s h e (RVInt 5) h' /\
    heap_lookup h' ℓ = Some (RVInt 5).
Proof.
  intros e s h. unfold e, e_let, ti32.
  eexists (fresh_loc h). 
  eexists (heap_extend (heap_extend h (fresh_loc h) (RVInt 5)) 
                       (S (fresh_loc h)) (RVInt 5)).
  split.
  - eapply E_Let.
    + apply E_Value. reflexivity.
    + reflexivity.
    + eapply E_Var. simpl. unfold stack_extend. simpl.
      destruct (var_eq "x"%string "x"%string); auto.
  - unfold heap_extend. simpl.
    destruct (Nat.eqb (fresh_loc h) (fresh_loc h)) eqn:Heq.
    + reflexivity.
    + apply Nat.eqb_neq in Heq. contradiction.
Qed.

(* ==========================================================================
 * 内存安全性质
 * ========================================================================== *)

Definition no_use_after_free (h : heap) (e : expr) : Prop :=
  forall ℓ, 
    heap_lookup h ℓ = None ->
    ~ (exists s h' v, eval s h e v h' /\
        accesses_loc h' ℓ).

Definition accesses_loc (h : heap) (ℓ : loc) : Prop :=
  exists v, heap_lookup h ℓ = Some v.

Definition heap_valid (h : heap) : Prop :=
  forall ℓ v, heap_lookup h ℓ = Some v ->
  forall ℓ', In ℓ' (refs_in_val v) ->
  exists v', heap_lookup h ℓ' = Some v'.

Fixpoint refs_in_val (v : runtime_val) : list loc :=
  match v with
  | RVLoc ℓ => [ℓ]
  | RVTuple vs => concat (map refs_in_val vs)
  | RVStruct _ fields => concat (map (fun '(_, v) => refs_in_val v) fields)
  | _ => []
  end.

Definition env_well_typed (s : stack) (Γ : type_env) : Prop :=
  forall x τ, te_lookup Γ x = Some τ ->
  exists v, stack_lookup s x = Some v.

Theorem memory_safety :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    env_well_typed s Γ ->
    heap_valid h ->
    no_use_after_free h e.
Proof.
  admit. (* 内存安全定理证明 *)
Admitted.
