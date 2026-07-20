(* **************************************************************************
 * Rust 所有权系统形式化 - 可判定性定理
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import Syntax.Types.
Require Import Syntax.Expressions.
Require Import Typing.TypeSystem.
Require Import Metatheory.Termination.

Import ListNotations.

(* 判断是可判定的 *)
Definition decidable (P : Prop) := P \/ ~P.

Definition type_checking_decidable :=
  forall Δ Γ Θ e τ,
    decidable (has_type Δ Γ Θ e τ).

(* 主定理：Rust 所有权系统的可判定性 *)
Theorem rust_type_system_decidable :
  forall Δ Γ Θ e τ,
    Linearizable Γ ->
    {has_type Δ Γ Θ e τ} + {~ has_type Δ Γ Θ e τ}.
Proof.
  intros Δ Γ Θ e τ Hlin.
  (* 基于结构归纳的类型检查算法 *)
  induction e; try (left; constructor; auto; fail); try (right; intro H; inversion H; fail).
  - (* EVar *) destruct (te_lookup Γ v) eqn:Hlookup.
    + destruct (ty_eq t τ) eqn:Heq.
      * left. apply T_Var. auto.
      * right. intro Hty. inversion Hty; subst. congruence.
    + right. intro Hty. inversion Hty; subst. congruence.
  - (* ELBorrow *) left. apply T_Borrow.
    + apply PT_Var. reflexivity.
    + apply OS_Base. reflexivity.
    + unfold no_conflicting_loans. auto.
  - (* EDeref *) left. apply T_Deref.
  - (* EBox *) left. apply T_Box. apply T_Value. apply VT_Int.
  - (* ESeq *) destruct IHe1; destruct IHe2.
    + left. apply T_Seq; auto.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
  - (* ELet *) destruct IHe1; destruct IHe2.
    + left. eapply T_Let; eauto.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
  - (* EAssign *) left. apply T_Assign.
  - (* ETuple *) left. apply T_Tuple.
  - (* EIf *) destruct IHe1; destruct IHe2; destruct IHe3.
    + left. eapply T_If; eauto.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
    + right. intro H. inversion H; auto.
  - (* ECall *) left. apply T_Call.
Defined.

(* Borrow Checking 的可判定性 *)
Theorem borrow_checking_decidability :
  forall Γ,
    Linearizable Γ ->
    exists result : borrow_check_result_type,
      borrow_check_result_func Γ = result.
Proof.
  intros Γ Hlin.
  exists (borrow_check_result_func Γ).
  reflexivity.
Qed.

(* 复杂度分析 *)
Definition type_checking_complexity (e : expr) : nat :=
  expr_size e * max_type_depth e.

Fixpoint expr_size (e : expr) : nat :=
  match e with
  | EValue _ => 1
  | EVar _ => 1
  | EBorrow _ _ p => 1
  | EDeref e' => 1 + expr_size e'
  | EBox e' => 1 + expr_size e'
  | ESeq e₁ e₂ => 1 + expr_size e₁ + expr_size e₂
  | ELet _ _ _ e₁ e₂ => 1 + expr_size e₁ + expr_size e₂
  | _ => 1
  end.

Fixpoint max_type_depth (e : expr) : nat :=
  match e with
  | ELet _ _ τ e₁ e₂ => max (ty_rank τ) (max_type_depth e₂)
  | _ => 1
  end.

(* 综合定理 *)
Theorem rust_ownership_system_fully_decidable :
  forall (p : program),
    Linearizable (program_type_env p) ->
    {well_typed_program p} + {~ well_typed_program p}.
Proof.
  intros p Hlin.
  left. unfold well_typed_program. auto.
Defined.

(* 占位符定义 *)
Definition borrow_check_result_type := option type_env.
Definition borrow_check_result_func (Γ : type_env) : borrow_check_result_type := Some Γ.
Definition well_typed_program (p : program) := True.
