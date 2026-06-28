(* **************************************************************************
 * Rust 所有权系统形式化 - 表达式定义
 ************************************************************************** *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Types.

Import ListNotations.

(* ==========================================================================
 * 位置表达式 (Place Expressions)
 * ========================================================================== *)

Inductive place : Type :=
  | PVar : var -> place                 (* x *)
  | PDeref : place -> place             (* *p *)
  | PField : place -> field_name -> place  (* p.f *)
  | PIndex : place -> expr -> place.    (* p[e] *)

(* ==========================================================================
 * 模式 (Patterns)
 * ========================================================================== *)

Inductive pattern : Type :=
  | PWildcard : pattern                 (* _ *)
  | PBind : var -> pattern              (* x *)
  | PLit : literal -> pattern           (* 字面量 *)
  | PTuple : list pattern -> pattern    (* (p₁, ..., pₙ) *)
  | PStruct : type_name -> list (field_name * pattern) -> pattern
  | PVariant : type_name -> string -> list pattern -> pattern.

(* ==========================================================================
 * 字面量
 * ========================================================================== *)

Inductive literal : Type :=
  | LUnit : literal
  | LBool : bool -> literal
  | LInt : Z -> literal
  | LChar : ascii -> literal
  | LString : string -> literal.

(* ==========================================================================
 * 表达式
 * ========================================================================== *)

Inductive expr : Type :=
  (* 值和变量 *)
  | EValue : value -> expr
  | EVar : var -> expr
  
  (* 借用和解引用 *)
  | EBorrow : region -> mutability -> place -> expr   (* &ρ ω p *)
  | EDeref : expr -> expr                             (* *e *)
  
  (* 装箱 *)
  | EBox : expr -> expr                               (* box e *)
  
  (* 元组和结构体 *)
  | ETuple : list expr -> expr                        (* (e₁, ..., eₙ) *)
  | EStruct : type_name -> list (field_name * expr) -> expr
  | EField : expr -> field_name -> expr               (* e.f *)
  | EIndex : expr -> expr -> expr                     (* e₁[e₂] *)
  
  (* 控制流 *)
  | ESeq : expr -> expr -> expr                       (* e₁; e₂ *)
  | ELet : mutability -> var -> ty -> expr -> expr -> expr  (* let ω x: τ = e₁; e₂ *)
  | EAssign : place -> expr -> expr                   (* p = e *)
  | ECall : fn_name -> list ty -> list expr -> expr   (* fn::<T>(args) *)
  | EMatch : expr -> list (pattern * expr) -> expr    (* match e { ... } *)
  | EIf : expr -> expr -> expr -> expr                (* if e₁ { e₂ } else { e₃ } *)
  | ELoop : expr -> expr                              (* loop { e } *)
  | EBreak : option expr -> expr                      (* break e *)
  | EContinue : expr                                  (* continue *)
  | EReturn : expr -> expr                            (* return e *)
  
  (* 错误/中止 *)
  | EAbort : string -> expr                           (* abort! *)

(* ==========================================================================
 * 值 (运行时)
 * ========================================================================== *)

with value : Type :=
  | VUnit : value
  | VBool : bool -> value
  | VInt : Z -> value
  | VChar : ascii -> value
  | VString : string -> value
  | VLoc : nat -> value                       (* 内存位置 ℓ *)
  | VTupleV : list value -> value
  | VStructV : type_name -> list (field_name * value) -> value
  | VEnumV : type_name -> string -> list value -> value
  | VRefV : nat -> mutability -> value        (* 引用值：位置和可变性 *)
  | VBoxV : nat -> value -> value             (* Box 值：位置和内部值 *)
  | VClosure : fn_name -> list value -> value (* 闭包：函数名和捕获的环境 *).

(* ==========================================================================
 * 函数定义
 * ========================================================================== *)

Record fn_decl : Type := mk_fn {
  fn_name_decl : fn_name;
  fn_rvars : list rvar;                    (* 区域参数 *)
  fn_params : list (var * ty);             (* 参数 *)
  fn_ret_ty : ty;                          (* 返回类型 *)
  fn_body : expr                           (* 函数体 *)
}.

(* 程序 *)
Definition program := list fn_decl * expr.  (* 函数定义列表和主表达式 *)

(* ==========================================================================
 * 位置操作
 * ========================================================================== *)

(* 位置中的变量 *)
Fixpoint place_vars (p : place) : list var :=
  match p with
  | PVar x => [x]
  | PDeref p' => place_vars p'
  | PField p' _ => place_vars p'
  | PIndex p' e => place_vars p' ++ expr_vars e
  end

with expr_vars (e : expr) : list var :=
  match e with
  | EValue _ => []
  | EVar x => [x]
  | EBorrow _ _ p => place_vars p
  | EDeref e' => expr_vars e'
  | EBox e' => expr_vars e'
  | ETuple es => flat_map expr_vars es
  | EStruct _ fields => flat_map (fun '(_, e) => expr_vars e) fields
  | EField e' _ => expr_vars e'
  | EIndex e₁ e₂ => expr_vars e₁ ++ expr_vars e₂
  | ESeq e₁ e₂ => expr_vars e₁ ++ expr_vars e₂
  | ELet _ x _ e₁ e₂ => expr_vars e₁ ++ (filter (fun y => negb (var_eq x y)) (expr_vars e₂))
  | EAssign p e' => place_vars p ++ expr_vars e'
  | ECall _ _ es => flat_map expr_vars es
  | EMatch e' arms => expr_vars e' ++ flat_map (fun '(pat, e) => 
      expr_vars e) arms  (* 简化版，不考虑模式绑定 *)
  | EIf e₁ e₂ e₃ => expr_vars e₁ ++ expr_vars e₂ ++ expr_vars e₃
  | ELoop e' => expr_vars e'
  | EBreak (Some e') => expr_vars e'
  | EBreak None => []
  | EContinue => []
  | EReturn e' => expr_vars e'
  | EAbort _ => []
  end.

(* 判断表达式是否为值 *)
Fixpoint is_value (e : expr) : bool :=
  match e with
  | EValue _ => true
  | _ => false
  end.

(* 判断表达式是否是位置 *)
Fixpoint is_place (e : expr) : option place :=
  match e with
  | EVar x => Some (PVar x)
  | EDeref e' => 
      match is_place e' with
      | Some p => Some (PDeref p)
      | None => None
      end
  | EField e' f =>
      match is_place e' with
      | Some p => Some (PField p f)
      | None => None
      end
  | _ => None
  end.

(* ==========================================================================
 * 辅助定义
 * ========================================================================== *)

(* 空表达式（用于错误情况） *)
Definition e_nop := EValue VUnit.

(* 创建 let 表达式的便利函数 *)
Definition e_let (x : var) (τ : ty) (e₁ e₂ : expr) : expr :=
  ELet Shrd x τ e₁ e₂.

Definition e_let_mut (x : var) (τ : ty) (e₁ e₂ : expr) : expr :=
  ELet Uniq x τ e₁ e₂.

(* ==========================================================================
 * 示例
 * ========================================================================== *)

(* let x = 5; x *)
Example ex_let_var : expr :=
  e_let "x"%string ti32 (EValue (VInt 5)) (EVar "x"%string).

(* &x *)
Example ex_borrow : expr :=
  EBorrow RStatic Shrd (PVar "x"%string).

(* &mut x *)
Example ex_borrow_mut : expr :=
  EBorrow RStatic Uniq (PVar "x"%string).

(* let mut x = 5; *x = 10; x *)
Example ex_assign : expr :=
  e_let_mut "x"%string ti32 (EValue (VInt 5))
    (ESeq 
      (EAssign (PDeref (PVar "x"%string)) (EValue (VInt 10)))
      (EDeref (EVar "x"%string))).
