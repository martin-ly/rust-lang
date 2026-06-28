(* **************************************************************************
 * Rust 所有权系统形式化 - 证明策略
 * 
 * 常用的证明策略和自动化
 ************************************************************************** *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

(* ==========================================================================
 * 基本策略
 * ========================================================================== *)

(* 自动证明类型秩非负 *)
Ltac rank_nonneg :=
  match goal with
  | |- ty_rank _ >= 0 => apply ty_rank_nonneg
  | |- ty_rank _ > 0 => apply ty_rank_positive; eauto
  end.

(* 自动展开 Linearizability *)
Ltac unfold_lin :=
  unfold Linearizable in *;
  intros; eauto.

(* 处理类型环境查找 *)
Ltac lookup_tac :=
  match goal with
  | H: te_lookup _ _ = Some _ |- _ =>
      simpl in H; try discriminate; try inversion H; subst
  end.

(* ==========================================================================
 * 列表操作自动化
 * ========================================================================== *)

(* 简化列表包含 *)
Ltac simpl_in :=
  match goal with
  | H: In _ (_ :: _) |- _ => simpl in H; destruct H; subst
  | H: In _ [] |- _ => contradiction
  end.

(* 列表归纳 *)
Ltac list_ind l :=
  induction l as [|x xs IH]; simpl; auto.

(* ==========================================================================
 * 矛盾处理
 * ========================================================================== *)

(* 自动发现矛盾 *)
Ltac find_contra :=
  match goal with
  | H1: ?x = ?y, H2: ?x <> ?y |- _ => contradiction
  | H: ?n < ?n |- _ => apply lt_irrefl in H; contradiction
  | H: In ?x [], _ |- _ => contradiction
  end.

(* ==========================================================================
 * 类型系统专用策略
 * ========================================================================== *)

(* 类型判断反演 *)
Ltac inv_type :=
  match goal with
  | H: has_type _ _ _ (EValue _) _ |- _ => inversion H; clear H; subst
  | H: has_type _ _ _ (EVar _) _ |- _ => inversion H; clear H; subst
  | H: has_type _ _ _ (EBorrow _ _ _) _ |- _ => inversion H; clear H; subst
  end.

(* 自动应用类型规则 *)
Ltac apply_ty :=
  match goal with
  | |- has_type _ _ _ (EValue _) _ => apply T_Value
  | |- has_type _ _ _ (EVar _) _ => apply T_Var
  | |- has_type _ _ _ (EBorrow _ _ _) _ => eapply T_Borrow
  | |- has_type _ _ _ (EDeref _) _ => eapply T_Deref
  end.

(* ==========================================================================
 * 语义专用策略
 * ========================================================================== *)

(* 求值反演 *)
Ltac inv_eval :=
  match goal with
  | H: eval _ _ (EValue _) _ _ |- _ => inversion H; clear H; subst
  | H: eval _ _ (EVar _) _ _ |- _ => inversion H; clear H; subst
  end.

(* 自动应用求值规则 *)
Ltac apply_eval :=
  match goal with
  | |- eval _ _ (EValue _) _ _ => apply E_Value
  | |- eval _ _ (EVar _) _ _ => apply E_Var
  | |- eval _ _ (EBorrow _ _ _) _ _ => eapply E_Borrow
  end.

(* ==========================================================================
 * 高级自动化
 * ========================================================================== *)

(* 完全自动化的类型检查证明 *)
Ltac auto_type :=
  repeat (apply_ty || constructor || auto || eauto || rank_nonneg).

(* 完全自动化的求值证明 *)
Ltac auto_eval :=
  repeat (apply_eval || constructor || auto || eauto).

(* 组合策略 *)
Ltac solve_type :=
  intros; unfold_lin; lookup_tac; simpl_in; auto_type.

Ltac solve_eval :=
  intros; inv_type; auto_eval.
