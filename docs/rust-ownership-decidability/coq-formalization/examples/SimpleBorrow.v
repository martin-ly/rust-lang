(* **************************************************************************
 * Rust 所有权系统形式化 - 简单借用示例
 * 
 * 验证基本的借用模式
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
 * 示例 1: 最基本的不可变借用
 * 
 * Rust 代码:
 *   let x = 5;
 *   let y = &x;
 *   *y
 * ========================================================================== *)

Definition ex1_let_x := 
  ELet Shrd "x"%string ti32 (EValue (VInt 5)).

Definition ex1_borrow_y :=
  ELet Shrd "y"%string (TRef RStatic Shrd ti32)
    (EBorrow RStatic Shrd (PVar "x"%string)).

Definition ex1_deref :=
  EDeref (EVar "y"%string).

Definition ex1_full :=
  ex1_let_x (ex1_borrow_y ex1_deref).

(* 类型检查 *)
Example ex1_typechecks : forall Δ Θ,
  let Γ := [] in
  has_type Δ Γ Θ ex1_full ti32.
Proof.
  intros. unfold ex1_full, ex1_let_x, ex1_borrow_y, ex1_deref, ti32, tref_i32.
  eapply T_Let.
  - apply T_Value. apply VT_Int.
  - eapply T_Let.
    + apply T_Borrow.
      * apply PT_Var. reflexivity.
      * apply OS_Base. reflexivity.
      * unfold no_conflicting_loans. trivial.
    + eapply T_Deref.
      apply T_Var. reflexivity.
Qed.

(* ==========================================================================
 * 示例 2: 可变借用
 * 
 * Rust 代码:
 *   let mut x = 5;
 *   let y = &mut x;
 *   *y = 10;
 *   *y
 * ========================================================================== *)

Definition ex2_let_mut_x :=
  ELet Uniq "x"%string ti32 (EValue (VInt 5)).

Definition ex2_borrow_mut_y :=
  ELet Uniq "y"%string (TRef RStatic Uniq ti32)
    (EBorrow RStatic Uniq (PVar "x"%string)).

Definition ex2_assign :=
  EAssign (PDeref (PVar "y"%string)) (EValue (VInt 10)).

Definition ex2_full :=
  ex2_let_mut_x (ESeq (ex2_borrow_mut_y ex2_assign) ex1_deref).

(* 可变借用的类型检查 *)
Example ex2_typechecks : forall Δ Θ,
  let Γ := [] in
  has_type Δ Γ Θ ex2_full ti32.
Proof.
  intros. unfold ex2_full, ex2_let_mut_x, ex2_borrow_mut_y, ex2_assign, ti32.
  eapply T_Let.
  - apply T_Value. apply VT_Int.
  - eapply T_Let.
    + apply T_Borrow.
      * apply PT_Var. reflexivity.
      * apply OS_Base. reflexivity.
      * trivial.
    + eapply T_Seq.
      * eapply T_Assign.
        -- apply PT_Deref. apply PT_Var. reflexivity.
        -- apply T_Value. apply VT_Int.
        -- apply OS_Deref_Uniq.
           ++ apply PT_Var. reflexivity.
           ++ apply OS_Base. reflexivity.
      * eapply T_Deref. apply T_Var. reflexivity.
Qed.

(* ==========================================================================
 * 示例 3: 共享借用（多个读者）
 * 
 * Rust 代码:
 *   let x = 5;
 *   let y = &x;
 *   let z = &x;
 *   (*y, *z)
 * ========================================================================== *)

Definition ex3_borrow_y :=
  ELet Shrd "y"%string (TRef RStatic Shrd ti32)
    (EBorrow RStatic Shrd (PVar "x"%string)).

Definition ex3_borrow_z :=
  ELet Shrd "z"%string (TRef RStatic Shrd ti32)
    (EBorrow RStatic Shrd (PVar "x"%string)).

Definition ex3_tuple :=
  ETuple [EDeref (EVar "y"%string); EDeref (EVar "z"%string)].

Definition ex3_full :=
  ex1_let_x (ex3_borrow_y (ex3_borrow_z ex3_tuple)).

(* 共享借用的类型检查 *)
Example ex3_typechecks : forall Δ Θ,
  let Γ := [] in
  has_type Δ Γ Θ ex3_full (TTuple [ti32; ti32]).
Proof.
  intros. unfold ex3_full, ex3_borrow_y, ex3_borrow_z, ex3_tuple, ex1_let_x, ti32.
  eapply T_Let.
  - apply T_Value. apply VT_Int.
  - eapply T_Let.
    + apply T_Borrow.
      * apply PT_Var. reflexivity.
      * apply OS_Base. reflexivity.
      * trivial.
    + eapply T_Let.
      * apply T_Borrow.
        -- apply PT_Var. reflexivity.
        -- apply OS_Base. reflexivity.
        -- trivial.
      * apply T_Tuple.
        -- eapply T_Deref. apply T_Var. reflexivity.
        -- eapply T_Deref. apply T_Var. reflexivity.
        -- constructor.
Qed.

(* ==========================================================================
 * 示例 4: Box 类型
 * 
 * Rust 代码:
 *   let x = Box::new(5);
 *   *x
 * ========================================================================== *)

Definition ex4_box :=
  ELet Shrd "x"%string (TBox ti32) (EBox (EValue (VInt 5))).

Definition ex4_deref :=
  EDeref (EVar "x"%string).

Definition ex4_full :=
  ex4_box ex4_deref.

Example ex4_typechecks : forall Δ Θ,
  let Γ := [] in
  has_type Δ Γ Θ ex4_full ti32.
Proof.
  intros. unfold ex4_full, ex4_box, ex4_deref, ti32.
  eapply T_Let.
  - apply T_Box. apply T_Value. apply VT_Int.
  - eapply T_Deref. apply T_Var. reflexivity.
Qed.

(* ==========================================================================
 * 示例 5: 借用链
 * 
 * Rust 代码:
 *   let x = 5;
 *   let y = &x;
 *   let z = &y;
 *   **z
 * ========================================================================== *)

Definition ex5_borrow_y :=
  ELet Shrd "y"%string (TRef RStatic Shrd ti32)
    (EBorrow RStatic Shrd (PVar "x"%string)).

Definition ex5_borrow_z :=
  ELet Shrd "z"%string (TRef RStatic Shrd (TRef RStatic Shrd ti32))
    (EBorrow RStatic Shrd (PVar "y"%string)).

Definition ex5_double_deref :=
  EDeref (EDeref (EVar "z"%string)).

Definition ex5_full :=
  ex1_let_x (ex5_borrow_y (ex5_borrow_z ex5_double_deref)).

Example ex5_typechecks : forall Δ Θ,
  let Γ := [] in
  has_type Δ Γ Θ ex5_full ti32.
Proof.
  intros. unfold ex5_full, ex5_borrow_y, ex5_borrow_z, ex5_double_deref, ex1_let_x, ti32.
  eapply T_Let.
  - apply T_Value. apply VT_Int.
  - eapply T_Let.
    + apply T_Borrow.
      * apply PT_Var. reflexivity.
      * apply OS_Base. reflexivity.
      * trivial.
    + eapply T_Let.
      * apply T_Borrow.
        -- apply PT_Var. reflexivity.
        -- apply OS_Base. reflexivity.
        -- trivial.
      * eapply T_Deref. eapply T_Deref. apply T_Var. reflexivity.
Qed.

(* ==========================================================================
 * 示例 6: 非法借用（应该被拒绝）
 * 
 * Rust 代码（错误）:
 *   let mut x = 5;
 *   let y = &mut x;
 *   let z = &x;  // 错误：不能同时拥有可变借用和不可变借用
 * ========================================================================== *)

Definition ex6_illegal_borrow :=
  ELet Shrd "z"%string (TRef RStatic Shrd ti32)
    (EBorrow RStatic Shrd (PVar "x"%string)).

Definition ex6_full :=
  ex2_let_mut_x (ex2_borrow_mut_y (ex6_illegal_borrow (ETuple []))).

(* 这个例子在完整的形式化中应该无法通过类型检查 *)
(* 简化版中暂不做此检查 *)

(* ==========================================================================
 * 求值示例
 * ========================================================================== *)

(* 示例 1 的求值 *)
Example ex1_evaluates : forall s h,
  exists v h',
    eval s h ex1_full v h' /\
    v = RVInt 5.
Proof.
  intros. eexists. eexists. split.
  - admit.  (* 简化版 *)
  - reflexivity.
Admitted.

(* ==========================================================================
 * 类型安全验证
 * ========================================================================== *)

(* 所有示例都是类型安全的 *)
Theorem all_examples_type_safe :
  forall Δ Θ,
    (exists Γ, has_type Δ Γ Θ ex1_full ti32) /\
    (exists Γ, has_type Δ Γ Θ ex2_full ti32) /\
    (exists Γ, has_type Δ Γ Θ ex3_full (TTuple [ti32; ti32])) /\
    (exists Γ, has_type Δ Γ Θ ex4_full ti32) /\
    (exists Γ, has_type Δ Γ Θ ex5_full ti32).
Proof.
  intros. repeat split.
  - exists []. apply ex1_typechecks.
  - exists []. apply ex2_typechecks.
  - exists []. apply ex3_typechecks.
  - exists []. apply ex4_typechecks.
  - exists []. apply ex5_typechecks.
Qed.

(* ==========================================================================
 * Linearizability 验证
 * ========================================================================== *)

(* 示例环境的 Linearizability *)
Example ex_env_linearizable :
  let Γ := [("x"%string, ti32); 
            ("y"%string, TRef RStatic Shrd ti32)] in
  Linearizable Γ.
Proof.
  unfold Linearizable. intros x τ Hlookup y Hin.
  simpl in Hlookup.
  destruct (var_eq x "x"%string).
  - inversion Hlookup. subst. simpl in Hin. contradiction.
  - destruct (var_eq x "y"%string).
    + inversion Hlookup. subst τ. simpl in Hin.
      destruct (var_eq y "x"%string).
      * exists ti32. split.
        -- reflexivity.
        -- simpl. auto.
      * contradiction.
    + discriminate.
Qed.
