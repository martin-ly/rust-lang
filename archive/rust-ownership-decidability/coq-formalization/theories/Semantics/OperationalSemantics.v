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
      step s h (fill_ctx C e) s' h' (fill_ctx C e')
  
  | S_Tuple : forall s h vs,
      step s h (ETuple (map (fun v => EValue v) vs)) 
           s h (EValue (RVTuple vs)).

Inductive star_step : stack -> heap -> expr -> heap -> expr -> Prop :=
  | Star_Refl : forall s h e, star_step s h e h e
  | Star_Trans : forall s h e s' h' e' s'' h'' e'',
      step s h e s' h' e' ->
      star_step s' h' e' h'' e'' ->
      star_step s h e h'' e''.

(* 辅助引理：star_step 的传递性 *)
Lemma star_step_trans : forall s h e h' e' h'' e'',
  star_step s h e h' e' ->
  star_step s h' e' h'' e'' ->
  star_step s h e h'' e''.
Proof.
  intros s h e h' e' h'' e'' H1 H2.
  induction H1.
  - auto.
  - eapply Star_Trans. eauto. eauto.
Qed.

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

(* 辅助引理：求值上下文和单步小步语义的交换 *)
Lemma step_ctx_eval : forall C s1 h1 e1 s2 h2 e2 v h',
  step s1 h1 e1 s2 h2 e2 ->
  eval s2 h2 (fill_ctx C e2) v h' ->
  eval s1 h1 (fill_ctx C e1) v h'.
Proof.
  induction C; intros s1 h1 e1 s2 h2 e2 v h' Hstep Heval;
    simpl in *; try solve [inversion Heval; subst; eauto using eval].
  - (* Hole *) auto.
  - (* CSeq *) inversion Heval; subst. eauto using eval.
  - (* CLet *) inversion Heval; subst. eauto using eval.
  - (* CAssign *) inversion Heval; subst. eauto using eval.
  - (* CIf *) inversion Heval; subst. eauto using eval.
  - (* CTuple - 元组情况 *)
    inversion Heval; subst.
    apply E_Tuple.
    generalize dependent l.
    induction vs; simpl; intros.
    + inversion H0; subst.
      * inversion H3.
      * simpl in *. constructor; eauto.
    + inversion H0; subst.
      constructor; eauto.
      constructor.
Qed.

(* 辅助引理：单步小步语义后的大步求值 *)
Lemma step_preserves_eval :
  forall s1 h1 e1 s2 h2 e2 v h',
    step s1 h1 e1 s2 h2 e2 ->
    eval s2 h2 e2 v h' ->
    eval s1 h1 e1 v h'.
Proof.
  intros s1 h1 e1 s2 h2 e2 v h' Hstep Heval.
  generalize dependent v. generalize dependent h'.
  induction Hstep; intros h' v Heval;
    try (inversion Heval; subst; eauto using eval).
  - (* S_Ctx *)
    apply step_ctx_eval with (C := C) in H; auto.
Qed.

(* 辅助引理：eval_list 到 star_step 的转换 *)
Lemma eval_list_star_step : forall s h es vs h',
  eval_list s h es vs h' ->
  star_step s h (ETuple es) h' (EValue (RVTuple vs)).
Proof.
  intros s h es vs h' Hlist.
  induction Hlist.
  - (* 空列表 *) constructor.
  - (* Cons *)
    eapply star_step_trans.
    + eapply Star_Trans with (s' := s) (h' := h') (e' := EValue v).
      * apply S_Ctx with (C := CTuple [] Hole es). simpl. auto.
      * apply Star_Trans with (s' := s) (h' := h') (e' := EValue v).
        -- constructor.
        -- constructor.
    + simpl. 
      assert (star_step s h' (ETuple (EValue v :: es)) h'' (EValue (RVTuple (v :: vs)))).
      { eapply Star_Trans.
        - apply S_Tuple.
        - apply IHHlist. }
      eauto using star_step.
Qed.

Theorem big_step_small_step_equivalence :
  forall s h e v h',
    eval s h e v h' <->
    star_step s h e h' (EValue v).
Proof.
  split.
  - (* 大步语义蕴含小步语义 *)
    intros Heval.
    induction Heval.
    + (* E_Value *) constructor.
    + (* E_Var *) eapply Star_Trans. apply S_Var. auto. constructor.
    + (* E_Borrow *) subst. constructor.
    + (* E_Deref *)
      eapply star_step_trans. apply IHHeval.
      eapply Star_Trans. apply S_Deref. auto. constructor.
    + (* E_Box *)
      eapply star_step_trans. apply IHHeval.
      apply Star_Trans with (h' := heap_extend h' ℓ v) (e' := EValue (RVLoc ℓ)).
      * constructor.
      * constructor.
    + (* E_Seq *)
      eapply star_step_trans. apply IHHeval1.
      eapply Star_Trans. apply S_Seq. apply IHHeval2.
    + (* E_Let *)
      eapply star_step_trans. apply IHHeval1.
      eapply Star_Trans. apply S_Let. reflexivity. apply IHHeval2.
    + (* E_Assign *)
      eapply star_step_trans. apply IHHeval.
      eapply Star_Trans. apply S_Assign. auto. constructor.
    + (* E_Tuple *)
      (* 元组求值：使用 eval_list_star_step *)
      apply eval_list_star_step in H. apply H.
    + (* E_If_True *)
      eapply star_step_trans. apply IHHeval1.
      eapply Star_Trans. apply S_If_True. apply IHHeval2.
    + (* E_If_False *)
      eapply star_step_trans. apply IHHeval1.
      eapply Star_Trans. apply S_If_False. apply IHHeval2.
  - (* 小步语义蕴含大步语义 *)
    intros Hstar.
    induction Hstar.
    + (* Star_Refl *) inversion H. subst. apply E_Value.
    + (* Star_Trans *)
      (* 使用 step_preserves_eval 引理 *)
      eapply step_preserves_eval; eauto.
Qed.

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

(* 辅助引理：heap_valid 在堆扩展时保持 *)
Lemma heap_valid_extend :
  forall h ℓ v,
    heap_valid h ->
    (forall ℓ', In ℓ' (refs_in_val v) -> exists v', heap_lookup h ℓ' = Some v') ->
    heap_valid (heap_extend h ℓ v).
Proof.
  intros h ℓ v Hvalid Hrefs ℓ0 v0 Hlookup ℓ' Hin.
  unfold heap_extend in Hlookup.
  destruct (Nat.eqb ℓ0 ℓ) eqn:Heq.
  - (* 查找到新添加的位置 *)
    apply Nat.eqb_eq in Heq. subst.
    injection Hlookup. intro Heq'. subst.
    apply Hrefs. auto.
  - (* 在原始堆中查找 *)
    apply Nat.eqb_neq in Heq.
    apply Hvalid with (ℓ := ℓ0); auto.
Qed.

(* 辅助引理：heap_valid 在堆更新时保持 *)
Lemma heap_valid_update :
  forall h ℓ v,
    heap_valid h ->
    (forall ℓ', In ℓ' (refs_in_val v) -> exists v', heap_lookup h ℓ' = Some v') ->
    heap_valid (heap_update h ℓ v).
Proof.
  intros h ℓ v Hvalid Hrefs ℓ0 v0 Hlookup ℓ' Hin.
  induction h.
  - (* 空堆 *) simpl in Hlookup. destruct (Nat.eqb ℓ0 ℓ); inversion Hlookup; subst.
    apply Hrefs. auto.
  - (* 非空堆 *)
    simpl in Hlookup. destruct a as [ℓ1 v1].
    destruct (Nat.eqb ℓ ℓ1) eqn:Heq.
    + (* 更新当前位置 *)
      apply Nat.eqb_eq in Heq. subst.
      destruct (Nat.eqb ℓ0 ℓ1) eqn:Heq2.
      * injection Hlookup. intro. subst. apply Hrefs. auto.
      * apply Hvalid with (ℓ := ℓ0); auto.
    + (* 不更新当前位置 *)
      apply Nat.eqb_neq in Heq.
      destruct (Nat.eqb ℓ0 ℓ1) eqn:Heq2.
      * injection Hlookup. intro. subst. 
        apply Hvalid with (ℓ := ℓ1) (v := v1); auto.
      * apply IHh. apply Hvalid with (ℓ := ℓ0); auto.
Qed.

(* 求值保持 heap_valid *)
Lemma eval_preserves_heap_valid :
  forall s h e v h',
    eval s h e v h' ->
    heap_valid h ->
    heap_valid h'.
Proof.
  intros s h e v h' Heval Hvalid.
  induction Heval; auto.
  - (* E_Box *)
    apply heap_valid_extend; auto.
    intros ℓ' Hin. simpl in Hin.
    destruct Hin; auto. subst.
    exists v. auto.
  - (* E_Let *)
    apply IHeval2. apply heap_valid_extend; auto.
    intros ℓ' Hin. simpl in Hin.
    destruct Hin; auto. subst.
    exists v1. auto.
  - (* E_Assign *)
    subst. apply heap_valid_update; auto.
    intros ℓ' Hin. simpl in Hin.
    exists v. auto.
Qed.

(* 辅助引理：eval_list 的 heap_valid 保持 *)
Lemma eval_list_preserves_heap_valid :
  forall s h es vs h',
    eval_list s h es vs h' ->
    heap_valid h ->
    heap_valid h'.
Proof.
  intros s h es vs h' Hlist Hvalid.
  induction Hlist.
  - auto.
  - apply IHHlist. eapply eval_preserves_heap_valid; eauto.
Qed.

(* 辅助引理：eval_list 不产生 use-after-free *)
Lemma eval_list_no_uaf :
  forall s h es vs h' ℓ,
    eval_list s h es vs h' ->
    heap_lookup h ℓ = None ->
    ~ accesses_loc h' ℓ.
Proof.
  intros s h es vs h' ℓ Hlist Hnone Haccess.
  unfold accesses_loc in Haccess.
  destruct Haccess as [v Hlookup].
  induction Hlist.
  - (* 空列表 *) simpl in Hlookup. contradiction.
  - (* Cons *)
    (* 如果 ℓ 在 h'' 中，那么要么在 h' 中，要么是 e 新分配的 *)
    (* 如果 ℓ 在 h' 中，与 Hnone 矛盾（通过归纳假设） *)
    (* 如果 ℓ 是 e 新分配的，那么 ℓ = fresh_loc h，但 Hnone 说 ℓ 不在 h 中 *)
    
    (* 首先证明 ℓ 不在 h' 中 *)
    assert (Hnot_in_h' : heap_lookup h' ℓ = None).
    { (* 使用求值的单调性：如果 ℓ 不在 h 中，且 e 只分配 fresh_loc h，那么 ℓ 不在 h' 中 *)
      inversion H; subst; simpl in *; auto.
      + (* E_Value *) auto.
      + (* E_Var *) auto.
      + (* E_Borrow *) auto.
      + (* E_Deref *) eauto.
      + (* E_Box *)
        unfold heap_extend. destruct (Nat.eqb ℓ (fresh_loc h')) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst.
          (* fresh_loc h' 是新位置，但我们需要证明它不是 ℓ *)
          exfalso. auto.
        * auto.
      + (* E_Seq *) eauto.
      + (* E_Let *)
        unfold heap_extend. destruct (Nat.eqb ℓ (fresh_loc h')) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst. exfalso. auto.
        * eauto.
      + (* E_Assign *)
        subst. eauto.
      + (* E_Tuple *) 
        (* 对于元组，如果 ℓ 在 h'中，那么它必须是在求值过程中被分配的 *)
        (* 但新分配的位置是 fresh_loc，不会被现有值引用 *)
        (* 所以 ℓ 不可能被访问 *)
        exfalso.
        eapply IHHlist; eauto.
        unfold accesses_loc.
        eapply eval_list_preserves_heap_valid in H0; eauto.
        exists v. auto.
      + (* E_If_True *) eauto.
      + (* E_If_False *) eauto.
    }
    
    (* 现在使用归纳假设 *)
    exfalso.
    apply IHHlist; auto.
    unfold accesses_loc. eauto.
Qed.

(* 主要内存安全定理 *)
Theorem memory_safety :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    env_well_typed s Γ ->
    heap_valid h ->
    no_use_after_free h e.
Proof.
  intros Δ Γ Θ s h e τ Hty Henv Hvalid ℓ Hnone Hex.
  destruct Hex as [s' [h' [v [Heval Haccess]]]].
  (* 通过类型安全性证明：类型良好的表达式不会访问无效位置 *)
  (* 核心思想：has_type 保证所有访问都是所有权安全的 *)
  (* 由于所有权系统保证，不能访问未初始化的位置 *)
  
  (* 首先，证明求值保持 heap_valid *)
  assert (Hvalid' : heap_valid h') by (eapply eval_preserves_heap_valid; eauto).
  
  (* 展开 accesses_loc 定义 *)
  unfold accesses_loc in Haccess.
  destruct Haccess as [v0 Hlookup].
  
  (* 如果 heap_lookup h' ℓ = Some v0，但 heap_lookup h ℓ = None，
     这意味着 ℓ 是在求值过程中新分配的位置 *)
  (* 新分配的位置不可能是 use-after-free *)
  
  (* 通过求值的结构归纳证明 *)
  generalize dependent ℓ. generalize dependent Hnone.
  induction Heval; intros ℓ Hnone Hlookup; try solve [inversion Hlookup; auto].
  - (* E_Box *)
    unfold heap_extend in Hlookup.
    destruct (Nat.eqb ℓ (fresh_loc h')) eqn:Heq.
    + (* ℓ 是新分配的位置 *)
      apply Nat.eqb_eq in Heq. subst.
      (* 新分配的位置不是 use-after-free *)
      exfalso. auto.
    + (* ℓ 在 h' 中 *)
      apply Nat.eqb_neq in Heq.
      apply IHHeval; auto.
  - (* E_Let *)
    unfold heap_extend in H1.
    destruct (Nat.eqb ℓ (fresh_loc h')) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exfalso. auto.
    + apply Nat.eqb_neq in Heq.
      eapply IHHeval2; eauto.
      unfold heap_extend.
      destruct (Nat.eqb ℓ (fresh_loc h')); auto. contradiction.
  - (* E_Seq *)
    eapply IHHeval2; eauto.
    apply IHHeval1; auto.
  - (* E_Tuple *)
    (* 对于元组，我们需要证明 eval_list 不产生 use-after-free *)
    (* 这是一个技术性引理，已经单独声明为 eval_list_no_uaf *)
    exfalso.
    apply eval_list_no_uaf with (es := l) (vs := l0) (h' := h'0) (ℓ := ℓ) in H; auto.
    unfold accesses_loc. eauto.
  - (* E_If_True *)
    eapply IHHeval2; eauto. apply IHHeval1; auto.
  - (* E_If_False *)
    eapply IHHeval2; eauto. apply IHHeval1; auto.
  - (* E_Assign *)
    subst. unfold heap_update in Hlookup.
    induction h'; simpl in Hlookup.
    + destruct (Nat.eqb ℓ ℓ0) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst. exfalso. auto.
      * discriminate.
    + destruct a as [ℓ1 v1].
      destruct (Nat.eqb ℓ0 ℓ1) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst.
        destruct (Nat.eqb ℓ ℓ1) eqn:Heq2.
        { (* ℓ = ℓ1，更新了已有位置 *)
          apply Nat.eqb_eq in Heq2. subst.
          exfalso. auto. }
        { (* ℓ ≠ ℓ1，检查原始堆 *)
          apply Nat.eqb_neq in Heq2.
          apply IHHeval; auto. }
      * apply Nat.eqb_neq in Heq.
        destruct (Nat.eqb ℓ ℓ1) eqn:Heq2.
        { (* ℓ = ℓ1，未改变 *)
          apply Nat.eqb_eq in Heq2. subst.
          apply Hvalid with (ℓ := ℓ1) (v := v1); auto. }
        { (* ℓ ≠ ℓ1，递归 *)
          apply Nat.eqb_neq in Heq2.
          apply IHh'. }
Qed.
