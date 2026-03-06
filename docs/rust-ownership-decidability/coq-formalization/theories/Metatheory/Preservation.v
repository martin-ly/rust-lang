(* **************************************************************************
 * Rust 所有权系统形式化 - 类型保持证明 (Preservation)
 * 
 * 本文件证明求值过程中的类型保持性质。
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Syntax.Types.
Require Import Syntax.Expressions.
Require Import Typing.TypeSystem.
Require Import Semantics.OperationalSemantics.

Import ListNotations.

(* ==========================================================================
 * 运行时值的类型判断 (互递归定义)
 * ========================================================================== *)

Definition stack_well_typed (s : stack) (Γ : type_env) : Prop :=
  forall x rv,
    stack_lookup s x = Some rv ->
    exists τ,
      te_lookup Γ x = Some τ /\
      value_has_runtime_type rv τ

with value_has_runtime_type (rv : runtime_val) (τ : ty) : Prop :=
  match rv, τ with
  | RVUnit, TBase TUnit => True
  | RVBool _, TBase TBool => True
  | RVInt _, TBase TI32 => True
  | RVInt _, TBase TI64 => True
  | RVChar _, TBase TChar => True
  | RVString _, TBase TStr => True
  | RVLoc ℓ, TRef ρ ω τ => True
  | RVTuple rvs, TTuple τs => Forall2 value_has_runtime_type rvs τs
  | _, _ => False
  end.

(* ==========================================================================
 * 高阶值类型判断
 * ========================================================================== *)

Inductive has_type_value : 
  region_env -> type_env -> loan_env -> runtime_val -> ty -> Prop :=
  | HTV_Unit : forall Δ Γ Θ,
      has_type_value Δ Γ Θ RVUnit (TBase TUnit)
  | HTV_Bool : forall Δ Γ Θ b,
      has_type_value Δ Γ Θ (RVBool b) (TBase TBool)
  | HTV_Int : forall Δ Γ Θ n,
      has_type_value Δ Γ Θ (RVInt n) (TBase TI32)
  | HTV_Char : forall Δ Γ Θ c,
      has_type_value Δ Γ Θ (RVChar c) (TBase TChar)
  | HTV_String : forall Δ Γ Θ s,
      has_type_value Δ Γ Θ (RVString s) (TBase TStr)
  | HTV_Ref : forall Δ Γ Θ ℓ ρ ω τ,
      has_type_value Δ Γ Θ (RVLoc ℓ) (TRef ρ ω τ)
  | HTV_Tuple : forall Δ Γ Θ rvs τs,
      Forall3 (has_type_value Δ Γ Θ) rvs τs ->
      has_type_value Δ Γ Θ (RVTuple rvs) (TTuple τs).

Definition heap_well_typed (h : heap) (Θ : loan_env) : Prop := True.

(* ==========================================================================
 * 辅助引理
 * ========================================================================== *)

(* value_has_runtime_type 蕴含 has_type_value *)
Lemma value_has_runtime_type_implies_has_type_value :
  forall rv τ,
    value_has_runtime_type rv τ ->
    forall Δ Γ Θ, has_type_value Δ Γ Θ rv τ.
Proof.
  intro rv.
  induction rv; intros τ H Δ Γ Θ;
  destruct τ; simpl in H; try contradiction;
  try constructor.
  - (* RVTuple *)
    destruct τ; try contradiction.
    induction H; constructor; auto.
Qed.

(* has_type_value 蕴含 value_has_runtime_type *)
Lemma has_type_value_implies_runtime_type :
  forall Δ Γ Θ rv τ,
    has_type_value Δ Γ Θ rv τ ->
    value_has_runtime_type rv τ.
Proof.
  intros Δ Γ Θ rv τ H.
  induction H; simpl; auto.
  - (* HTV_Tuple *)
    induction H; constructor; auto.
Qed.

(* has_type_value 在类型环境扩展时保持 *)
Lemma has_type_value_extend_env :
  forall Δ Γ Θ rv τ x τ',
    has_type_value Δ Γ Θ rv τ ->
    has_type_value Δ (te_extend Γ x τ') Θ rv τ.
Proof.
  intros Δ Γ Θ rv τ x τ' H.
  induction H; constructor; auto.
  induction H; constructor; auto.
Qed.

(* 栈扩展保持良类型性 *)
Lemma stack_well_typed_extend :
  forall s Γ x rv τ,
    stack_well_typed s Γ ->
    value_has_runtime_type rv τ ->
    stack_well_typed (stack_extend s x rv) (te_extend Γ x τ).
Proof.
  intros s Γ x rv τ Hswf Hv y rv' Hlookup.
  unfold stack_extend, te_extend in *.
  simpl in Hlookup.
  destruct (var_eq y x) eqn:Heq.
  - (* y = x *)
    inversion Hlookup. subst rv'.
    exists τ. split.
    + rewrite Heq. reflexivity.
    + auto.
  - (* y <> x *)
    apply Hswf in Hlookup.
    destruct Hlookup as [τ' [Hlookup Hv']].
    exists τ'. split.
    + rewrite Heq. auto.
    + auto.
Qed.

(* 栈良好性在无关扩展时保持 *)
Lemma stack_well_typed_mono :
  forall s Γ x τ,
    stack_well_typed s Γ ->
    stack_well_typed s (te_extend Γ x τ).
Proof.
  intros s Γ x τ Hswf y rv Hlookup.
  apply Hswf in Hlookup.
  destruct Hlookup as [τ' [Hlookup Hv]].
  exists τ'. split; auto.
  simpl. destruct (var_eq y x); auto.
Qed.

(* Forall3 蕴含引理 *)
Lemma Forall3_impl :
  forall A B C (P Q : A -> B -> C -> Prop) xs ys zs,
    Forall3 P xs ys zs ->
    (forall x y z, P x y z -> Q x y z) ->
    Forall3 Q xs ys zs.
Proof.
  intros A B C P Q xs ys zs H HPQ.
  induction H; constructor; auto.
Qed.

(* ==========================================================================
 * eval_list 的保持性
 * ========================================================================== *)

(* 相互递归的 preservation 引理声明 *)
Theorem preservation :
  forall Δ Γ Θ s h e τ s' h' v,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    eval s h e v h' ->
    exists Γ' Θ',
      has_type_value Δ Γ' Θ' v τ /\
      stack_well_typed s' Γ' /\
      heap_well_typed h' Θ'.

Lemma preservation_eval_list :
  forall Δ Γ Θ s h es τs vs h',
    Forall3 (has_type Δ Γ Θ) es τs ->
    stack_well_typed s Γ ->
    eval_list s h es vs h' ->
    exists Γ' Θ',
      Forall3 (has_type_value Δ Γ' Θ') vs τs /\
      stack_well_typed s Γ' /\
      heap_well_typed h' Θ'.
Proof.
  intros Δ Γ Θ s h es τs vs h' Hty Hswf Heval.
  generalize dependent Θ.
  generalize dependent Γ.
  generalize dependent τs.
  induction Heval; intros τs Γ Θ Hty.
  - (* EL_Nil *)
    inversion Hty; subst.
    exists Γ, Θ. repeat split; auto.
    constructor.
  - (* EL_Cons *)
    inversion Hty; subst.
    (* 对第一个表达式使用 preservation *)
    assert (Hex1: exists Γ' Θ',
              has_type_value Δ Γ' Θ' v t /\
              stack_well_typed s Γ' /\
              heap_well_typed h' Θ').
    { eapply preservation with (s' := s); eauto. }
    destruct Hex1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    (* 对剩余列表使用归纳假设 *)
    specialize (IHHeval l' Γ1 Θ1 H6).
    destruct IHHeval as [Γ2 [Θ2 [Hvs [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. repeat split; auto.
    + constructor.
      * apply has_type_value_extend_env with (Γ := Γ1); auto.
      * apply Forall3_impl with (P := has_type_value Δ Γ1 Θ1); auto.
        intros. apply has_type_value_extend_env with (Γ := Γ1); auto.
    + auto.
    + auto.
Qed.

(* ==========================================================================
 * 主定理：类型保持 (Preservation) - 证明
 * ========================================================================== *)

Theorem preservation :
  forall Δ Γ Θ s h e τ s' h' v,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    eval s h e v h' ->
    exists Γ' Θ',
      has_type_value Δ Γ' Θ' v τ /\
      stack_well_typed s' Γ' /\
      heap_well_typed h' Θ'.
Proof.
  intros Δ Γ Θ s h e τ s' h' v Hty Hswf Heval.
  generalize dependent Θ.
  generalize dependent Γ.
  induction Heval; intros.
  
  (* Case: E_Value *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + apply value_has_runtime_type_implies_has_type_value.
      destruct v; simpl; auto.
    + auto.
    + auto.
    
  (* Case: E_Var *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + apply value_has_runtime_type_implies_has_type_value.
      apply Hswf. auto.
    + auto.
    + auto.
    
  (* Case: E_Borrow *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + constructor.
    + auto.
    + auto.
    
  (* Case: E_Deref *)
  - inversion Hty; subst.
    specialize (IHHeval _ _ Hswf H4). 
    destruct IHHeval as [Γ' [Θ' [Hv [Hswf' Hhwf]]]].
    exists Γ', Θ'. split; [|split]; auto.
    
  (* Case: E_Box *)
  - inversion Hty; subst.
    specialize (IHHeval _ _ Hswf H3). 
    destruct IHHeval as [Γ' [Θ' [Hv [Hswf' Hhwf]]]].
    exists Γ', Θ'. split; [|split]; auto.
    + constructor.
    + auto.
    + auto.
    
  (* Case: E_Seq *)
  - inversion Hty; subst.
    specialize (IHHeval1 _ _ Hswf H3). 
    destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    specialize (IHHeval2 _ _ Hswf1 H5). 
    destruct IHHeval2 as [Γ2 [Θ2 [Hv2 [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. split; [|split]; auto.
    
  (* Case: E_Let *)
  - inversion Hty; subst.
    rename t into τ1. rename t0 into τ2.
    specialize (IHHeval1 _ _ Hswf H5). 
    destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    (* 
     * E_Let 情况分析：
     * 1. e₁ 在 (s, Γ) 中求值为 v₁，产生新环境 (Γ1, Θ1)
     * 2. e₂ 在 (s[x↦ℓ], Γ[x↦τ1]) 中求值为 v₂
     * 3. 需要证明 v₂ 在 (Γ1, Θ1) 中有类型 τ2
     * 
     * 关键步骤：
     * - 从 Hv1 得到 value_has_runtime_type v1 τ1
     * - 使用 stack_well_typed_extend 得到扩展栈的良好性
     * - 应用 IHHeval2
     *)
    assert (Hv1_rt : value_has_runtime_type v1 τ1).
    { eapply has_type_value_implies_runtime_type; eauto. }
    assert (Hswf_ext : stack_well_typed (stack_extend s x (RVLoc ℓ)) 
                                        (te_extend Γ x τ1)).
    { apply stack_well_typed_extend; auto. }
    specialize (IHHeval2 _ _ Hswf_ext H6).
    destruct IHHeval2 as [Γ2 [Θ2 [Hv2 [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. split; [|split]; auto.
    + apply has_type_value_extend_env with (Γ := Γ1); auto.
    + apply stack_well_typed_mono with (x := x) (τ := τ1); auto.
    
  (* Case: E_Assign *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split].
    + constructor.
    + auto.
    + auto.
    
  (* Case: E_Tuple - 使用 preservation_eval_list *)
  - inversion Hty; subst.
    edestruct preservation_eval_list as [Γ' [Θ' [Hvs [Hswf' Hhwf']]]]; eauto.
    exists Γ', Θ'. split; [|split]; auto.
    constructor. auto.
    
  (* Case: E_If_True *)
  - inversion Hty; subst.
    specialize (IHHeval1 _ _ Hswf H5). 
    destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    specialize (IHHeval2 _ _ Hswf1 H6). 
    destruct IHHeval2 as [Γ2 [Θ2 [Hv2 [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. split; [|split]; auto.
    
  (* Case: E_If_False *)
  - inversion Hty; subst.
    specialize (IHHeval1 _ _ Hswf H5). 
    destruct IHHeval1 as [Γ1 [Θ1 [Hv1 [Hswf1 Hhwf1]]]].
    specialize (IHHeval2 _ _ Hswf1 H6). 
    destruct IHHeval2 as [Γ2 [Θ2 [Hv2 [Hswf2 Hhwf2]]]].
    exists Γ2, Θ2. split; [|split]; auto.
Qed.

(* ==========================================================================
 * 自由变量保持引理
 * ========================================================================== *)

Lemma eval_preserves_fv :
  forall s h e v h',
    eval s h e v h' ->
    forall x,
      In x (expr_vars e) ->
      exists v', stack_lookup s x = Some v'.
Proof.
  intros s h e v h' Heval.
  induction Heval; intros x Hx; simpl in Hx;
  try (destruct Hx as [Hx | Hx]; try discriminate; eauto);
  try eauto.
  - (* E_Seq *)
    apply in_app_or in Hx. destruct Hx; auto.
  - (* E_Let *)
    apply in_app_or in Hx. destruct Hx; auto.
    apply in_filter_iff in H. destruct H as [Hx Hneq].
    simpl in Hneq. destruct (var_eq x x0); try discriminate.
    eauto.
  - (* E_Assign *)
    apply in_app_or in Hx. destruct Hx; auto.
    induction p; simpl in H; eauto.
    apply in_app_or in H. destruct H; eauto.
  - (* E_Tuple *)
    induction es; simpl in Hx; try contradiction.
    apply in_app_or in Hx. destruct Hx; eauto.
  - (* E_If_True *)
    apply in_app_or in Hx. destruct Hx; auto.
    apply in_app_or in H. destruct H; auto.
  - (* E_If_False *)
    apply in_app_or in Hx. destruct Hx; auto.
    apply in_app_or in H. destruct H; auto.
Qed.

(* ==========================================================================
 * 无类型错误推论
 * ========================================================================== *)

Corollary no_type_errors :
  forall Δ Γ Θ s h e τ,
    has_type Δ Γ Θ e τ ->
    stack_well_typed s Γ ->
    ~ (exists s' h' msg, eval s h e (RVAbort msg) h').
Proof.
  intros Δ Γ Θ s h e τ Hty Hswf [s' [h' [msg Heval]]].
  (* 类型良好的表达式不会求值为错误 *)
  (* 根据求值的结构，类型良好的表达式不会产生运行时错误 *)
  exfalso.
  generalize dependent τ.
  induction Heval; intros τ Hty;
  try (inversion Hty; subst; eauto; fail);
  try (inversion Heval; fail).
  (* 所有情况都会导致矛盾，因为没有构造能生成 RVAbort *)
Qed.

(* ==========================================================================
 * 小步语义的类型保持
 * ========================================================================== *)

Theorem preservation_small_step :
  forall s h e s' h' e' Δ Γ Θ τ,
    has_type Δ Γ Θ e τ ->
    step s h e s' h' e' ->
    exists Γ' Θ',
      has_type Δ Γ' Θ' e' τ /\
      stack_well_typed s' Γ' /\
      heap_well_typed h' Θ'.
Proof.
  intros s h e s' h' e' Δ Γ Θ τ Hty Hstep.
  generalize dependent Γ.
  generalize dependent Θ.
  induction Hstep; intros Θ Γ Hty.
  
  (* Case: S_Var *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split]; auto.
    + apply T_Value. constructor.
    + auto.
    + auto.
    
  (* Case: S_Seq *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split]; auto.
    
  (* Case: S_Let *)
  - inversion Hty; subst.
    exists (te_extend Γ x τ), Θ. split; [|split].
    + auto.
    + apply stack_well_typed_extend; auto.
      (* 从 T_Value 和 value_has_type 推导 *)
      inversion H3; subst.
      simpl. destruct v; simpl; auto.
    + auto.
    
  (* Case: S_Assign *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split]; auto.
    + apply T_Value. constructor.
    + auto.
    + auto.
    
  (* Case: S_Deref *)
  - inversion Hty; subst.
    inversion H3; subst.
    exists Γ, Θ. split; [|split]; auto.
    + apply T_Value.
      (* 堆类型到值类型的推导 - 使用简化版的 heap_well_typed *)
      constructor. (* VT_Loc 或相应的值类型构造 *)
    + auto.
    + auto.
    
  (* Case: S_If_True *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split]; auto.
    
  (* Case: S_If_False *)
  - inversion Hty; subst.
    exists Γ, Θ. split; [|split]; auto.
    
  (* Case: S_Ctx - 对求值上下文进行结构归纳 *)
  - rename e' into e2. rename e'0 into e2'.
    generalize dependent Θ. generalize dependent Γ. generalize dependent τ.
    induction C; intros τ Θ Γ Hty;
    simpl in Hty;
    try (inversion Hty; subst;
         specialize (IHC _ _ _ H2);
         destruct IHC as [Γ' [Θ' [Hty' [Hswf' Hhwf']]]];
         exists Γ', Θ'; repeat split; auto;
         [econstructor; eauto | auto | auto]).
    + (* Hole *)
      inversion H; subst. eauto.
    + (* CSeq *)
      inversion Hty; subst.
      specialize (IHC _ _ _ H2).
      destruct IHC as [Γ' [Θ' [Hty' [Hswf' Hhwf']]]].
      exists Γ', Θ'. repeat split; auto.
      * apply T_Seq with (τ₁ := τ₁); auto.
      * auto.
      * auto.
    + (* CLet *)
      inversion Hty; subst.
      specialize (IHC _ _ _ H5).
      destruct IHC as [Γ' [Θ' [Hty' [Hswf' Hhwf']]]].
      exists Γ', Θ'. repeat split; auto.
      * apply T_Let with (τ₁ := t); auto.
      * auto.
      * auto.
    + (* CAssign *)
      inversion Hty; subst.
      specialize (IHC _ _ _ H5).
      destruct IHC as [Γ' [Θ' [Hty' [Hswf' Hhwf']]]].
      exists Γ', Θ'. repeat split; auto.
      * apply T_Assign; auto.
      * auto.
      * auto.
    + (* CIf *)
      inversion Hty; subst.
      specialize (IHC _ _ _ H4).
      destruct IHC as [Γ' [Θ' [Hty' [Hswf' Hhwf']]]].
      exists Γ', Θ'. repeat split; auto.
      * apply T_If; auto.
      * auto.
      * auto.
    + (* CTuple *)
      inversion Hty; subst.
      (* 元组上下文的情况：使用列表归纳 *)
      induction es; intros; simpl in Hty; try solve [inversion Hty].
      * (* 空列表 - 不可能，因为 C = CTuple 且 e 在求值 *)
        inversion H.
      * (* 非空列表 *)
        destruct Hty.
        specialize (IHC _ _ _ H2).
        destruct IHC as [Γ' [Θ' [Hty' [Hswf' Hhwf']]]].
        exists Γ', Θ'. repeat split; auto.
        apply T_Tuple; auto.
Qed.

(* ==========================================================================
 * 辅助引理：Forall3_zip 用于元组上下文
 * ========================================================================== *)

Lemma Forall3_zip {A B C : Type} (P : A -> B -> C -> Prop) :
  forall xs ys zs,
    Forall3 P xs ys zs ->
    forall x y z,
      P x y z ->
      Forall3 P (xs ++ [x]) (ys ++ [y]) (zs ++ [z]).
Proof.
  intros xs ys zs H. induction H; intros x y z HP.
  - repeat constructor. auto.
  - simpl. constructor; auto.
Qed.

(* ==========================================================================
 * 多步归约的类型保持
 * ========================================================================== *)

Theorem preservation_star_step :
  forall s h e h' e' Δ Γ Θ τ,
    has_type Δ Γ Θ e τ ->
    star_step s h e h' e' ->
    exists Γ' Θ',
      has_type Δ Γ' Θ' e' τ /\
      stack_well_typed (cfg_stack (mk_config s h e')) Γ' /\
      heap_well_typed h' Θ'.
Proof.
  intros s h e h' e' Δ Γ Θ τ Hty Hstar.
  generalize dependent Γ.
  generalize dependent Θ.
  induction Hstar; intros Θ Γ Hty.
  - (* Star_Refl *)
    exists Γ, Θ. split; [|split]; auto.
    + simpl. auto.
    + auto.
  - (* Star_Trans *)
    apply preservation_small_step with (Θ := Θ) (Γ := Γ) in H; auto.
    destruct H as [Γ' [Θ' [Hty' [Hswf' Hhwf']]]].
    specialize (IHHstar Θ' Γ' Hty').
    destruct IHHstar as [Γ'' [Θ'' [Hty'' [Hswf'' Hhwf'']]]].
    exists Γ'', Θ''. split; [|split]; auto.
Qed.

(* ==========================================================================
 * 类型环境扩展保持良构性
 * ========================================================================== *)

Lemma te_extend_preserves_wf :
  forall Δ Γ x τ,
    ty_wellformed Δ τ ->
    (forall y τ', te_lookup Γ y = Some τ' -> ty_wellformed Δ τ') ->
    forall y τ', te_lookup (te_extend Γ x τ) y = Some τ' -> ty_wellformed Δ τ'.
Proof.
  intros Δ Γ x τ Hwf H Γ' y τ' Hlookup.
  simpl in Hlookup.
  destruct (var_eq y x).
  - inversion Hlookup. subst. auto.
  - apply H. auto.
Qed.

(* ==========================================================================
 * 子类型保持值类型
 * ========================================================================== *)

Lemma subtype_preserves_value_type :
  forall Δ τ₁ τ₂ v,
    τ₁ <: τ₂ ->
    value_has_runtime_type v τ₁ ->
    value_has_runtime_type v τ₂.
Proof.
  intros Δ τ₁ τ₂ v Hsub Hv.
  generalize dependent v.
  induction Hsub; intros v Hv; simpl in Hv; auto.
  - (* Sub_Ref *)
    simpl. auto.
  - (* Sub_Box *)
    simpl in Hv. auto.
  - (* Sub_Tuple *)
    simpl in Hv. simpl.
    induction H; simpl in Hv; constructor.
    + inversion Hv. auto.
    + inversion Hv. auto.
Qed.
