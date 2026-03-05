(* **************************************************************************
 * Rust 所有权系统形式化 - 类型定义
 * Formalization of Rust Ownership System - Type Definitions
 * 
 * 本文件定义 Rust 核心类型系统的语法
 ************************************************************************** *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.BinNums.

Import ListNotations.

(* ==========================================================================
 * 基本定义
 * ========================================================================== *)

(* 变量名 *)
Definition var := string.
Definition var_eq := string_dec.

(* 区域变量 *)
Definition rvar := string.
Definition rvar_eq := string_dec.

(* 结构体/枚举名称 *)
Definition type_name := string.

(* 字段名 *)
Definition field_name := string.

(* 函数名 *)
Definition fn_name := string.

(* ==========================================================================
 * 基础类型
 * ========================================================================== *)

Inductive base_ty : Type :=
  | TUnit : base_ty                    (* () *)
  | TBool : base_ty                    (* bool *)
  | TI8 : base_ty | TI16 : base_ty | TI32 : base_ty | TI64 : base_ty | TI128 : base_ty | TISize : base_ty
  | TU8 : base_ty | TU16 : base_ty | TU32 : base_ty | TU64 : base_ty | TU128 : base_ty | TUSize : base_ty
  | TChar : base_ty                    (* char *)
  | TStr : base_ty.                    (* str *)

(* ==========================================================================
 * 可变性
 * ========================================================================== *)

Inductive mutability : Type :=
  | Uniq : mutability                  (* 唯一/可变: &mut *)
  | Shrd : mutability.                 (* 共享/不可变: & *)

(* 可变性比较: ω₁ ≤ ω₂ 表示 ω₁ 比 ω₂ 更受限 *)
Definition mut_leq (ω₁ ω₂ : mutability) : Prop :=
  match ω₁, ω₂ with
  | Shrd, _ => True                    (* Shrd 是最小元素 *)
  | Uniq, Uniq => True
  | Uniq, Shrd => False
  end.

Notation "ω₁ '<=' ω₂" := (mut_leq ω₁ ω₂) (at level 70).

(* ==========================================================================
 * 区域 (Lifetime/Region)
 * ========================================================================== *)

Inductive region : Type :=
  | RStatic : region                   (* 'static *)
  | RVar : rvar -> region              (* 'r *)
  | RUnion : region -> region -> region. (* ρ₁ ∪ ρ₂ *)

(* 区域变量在区域中的出现 *)
Fixpoint rv_in_region (rv : rvar) (ρ : region) : Prop :=
  match ρ with
  | RStatic => False
  | RVar rv' => rv = rv'
  | RUnion ρ₁ ρ₂ => rv_in_region rv ρ₁ \/ rv_in_region rv ρ₂
  end.

(* ==========================================================================
 * 类型定义
 * ========================================================================== *)

Inductive ty : Type :=
  | TBase : base_ty -> ty              (* 基础类型 *)
  | TRef : region -> mutability -> ty -> ty  (* &ρ ω τ *)
  | TBox : ty -> ty                    (* Box<τ> *)
  | TTuple : list ty -> ty             (* (τ₁, ..., τₙ) *)
  | TStruct : type_name -> list ty -> ty     (* struct<T> *)
  | TEnum : type_name -> list ty -> ty       (* enum<T> *)
  | TNever : ty.                       (* ! - never type *)

(* ==========================================================================
 * 辅助函数：列表最大值 *)
Fixpoint list_max (ns : list nat) : nat :=
  match ns with
  | [] => 0
  | n :: ns' => max n (list_max ns')
  end.

(* ==========================================================================
 * 类型上的操作
 * ========================================================================== *)

(* 类型的秩 (Rank) - 用于终止性证明 *)
Fixpoint ty_rank (τ : ty) : nat :=
  match τ with
  | TBase _ => 0
  | TRef _ _ τ' => 1 + ty_rank τ'
  | TBox τ' => 1 + ty_rank τ'
  | TTuple τs => list_max (map ty_rank τs)
  | TStruct _ τs => list_max (map ty_rank τs)
  | TEnum _ τs => list_max (map ty_rank τs)
  | TNever => 0
  end.

(* 类型的自由变量 *)
Fixpoint ty_fv (τ : ty) : list var :=
  match τ with
  | TBase _ => []
  | TRef _ _ τ' => ty_fv τ'
  | TBox τ' => ty_fv τ'
  | TTuple τs => flat_map ty_fv τs
  | TStruct _ τs => flat_map ty_fv τs
  | TEnum _ τs => flat_map ty_fv τs
  | TNever => []
  end.

(* 类型的自由区域变量 *)
Fixpoint ty_frv (τ : ty) : list rvar :=
  match τ with
  | TBase _ => []
  | TRef ρ _ τ' => region_frv ρ ++ ty_frv τ'
  | TBox τ' => ty_frv τ'
  | TTuple τs => flat_map ty_frv τs
  | TStruct _ τs => flat_map ty_frv τs
  | TEnum _ τs => flat_map ty_frv τs
  | TNever => []
  end

with region_frv (ρ : region) : list rvar :=
  match ρ with
  | RStatic => []
  | RVar rv => [rv]
  | RUnion ρ₁ ρ₂ => region_frv ρ₁ ++ region_frv ρ₂
  end.

(* ==========================================================================
 * 类型环境 (Type Environment)
 * ========================================================================== *)

Definition type_env := list (var * ty).

(* 查找变量类型 *)
Fixpoint te_lookup (Γ : type_env) (x : var) : option ty :=
  match Γ with
  | [] => None
  | (y, τ) :: Γ' => if var_eq x y then Some τ else te_lookup Γ' x
  end.

(* 扩展类型环境 *)
Definition te_extend (Γ : type_env) (x : var) (τ : ty) : type_env :=
  (x, τ) :: Γ.

(* 类型环境的域 *)
Fixpoint te_dom (Γ : type_env) : list var :=
  match Γ with
  | [] => []
  | (x, _) :: Γ' => x :: te_dom Γ'
  end.

(* ==========================================================================
 * Linearizability 定义 - 终止性的关键
 * ========================================================================== *)

(* 获取类型中所有引用的变量 *)
Fixpoint ty_refs (τ : ty) : list var :=
  match τ with
  | TBase _ => []
  | TRef _ _ τ' => ty_refs τ'
  | TBox τ' => ty_refs τ'
  | TTuple τs => flat_map ty_refs τs
  | TStruct _ τs => flat_map ty_refs τs
  | TEnum _ τs => flat_map ty_refs τs
  | TNever => []
  end.

(* Linearizability: 类型环境的良基性条件 *)
Definition Linearizable (Γ : type_env) : Prop :=
  forall x τ,
    te_lookup Γ x = Some τ ->
    forall y, In y (ty_refs τ) ->
    exists τ',
      te_lookup Γ y = Some τ' /\
      ty_rank τ > ty_rank τ'.

(* 类型环境的度量 - 用于终止性证明 *)
Definition te_measure (Γ : type_env) : nat :=
  fold_left plus (map (fun p => ty_rank (snd p)) Γ) 0.

(* ==========================================================================
 * 子类型关系 (简化版)
 * ========================================================================== *)

(* 区域包含关系：ρ₁ ⊇ ρ₂ 表示 ρ₁ 比 ρ₂ 活得更长 *)
Inductive subregion : region -> region -> Prop :=
  | SR_Refl : forall ρ, subregion ρ ρ
  | SR_Static : forall ρ, subregion RStatic ρ
  | SR_Union_L : forall ρ₁ ρ₂ ρ,
      subregion ρ₁ ρ ->
      subregion (RUnion ρ₁ ρ₂) ρ
  | SR_Union_R : forall ρ₁ ρ₂ ρ,
      subregion ρ₂ ρ ->
      subregion (RUnion ρ₁ ρ₂) ρ.

Notation "ρ₁ '⊇' ρ₂" := (subregion ρ₂ ρ₁) (at level 70).

(* 子类型关系 *)
Inductive subtype : ty -> ty -> Prop :=
  | Sub_Refl : forall τ, subtype τ τ
  | Sub_Base : forall B, subtype (TBase B) (TBase B)
  | Sub_Ref : forall ρ₁ ρ₂ ω τ₁ τ₂,
      ρ₂ ⊇ ρ₁ ->                    (* 反变：更长生命周期 *)
      subtype τ₁ τ₂ ->              (* 协变：更具体类型 *)
      subtype (TRef ρ₁ ω τ₁) (TRef ρ₂ ω τ₂)
  | Sub_Box : forall τ₁ τ₂,
      subtype τ₁ τ₂ ->
      subtype (TBox τ₁) (TBox τ₂)
  | Sub_Tuple : forall τs₁ τs₂,
      Forall2 subtype τs₁ τs₂ ->
      subtype (TTuple τs₁) (TTuple τs₂).

Notation "τ₁ '<:' τ₂" := (subtype τ₁ τ₂) (at level 70).

(* ==========================================================================
 * 良构性判断
 * ========================================================================== *)

(* 区域环境：区域变量到区域解释 *)
Definition region_env := list (rvar * region).

Fixpoint re_lookup (Δ : region_env) (rv : rvar) : option region :=
  match Δ with
  | [] => None
  | (r, ρ) :: Δ' => if rvar_eq rv r then Some ρ else re_lookup Δ' rv
  end.

(* 类型良构性 *)
Inductive ty_wellformed : region_env -> ty -> Prop :=
  | WF_Base : forall Δ B, ty_wellformed Δ (TBase B)
  | WF_Ref : forall Δ ρ ω τ,
      region_wellformed Δ ρ ->
      ty_wellformed Δ τ ->
      ty_wellformed Δ (TRef ρ ω τ)
  | WF_Box : forall Δ τ,
      ty_wellformed Δ τ ->
      ty_wellformed Δ (TBox τ)
  | WF_Tuple : forall Δ τs,
      Forall (ty_wellformed Δ) τs ->
      ty_wellformed Δ (TTuple τs)
  | WF_Struct : forall Δ name τs,
      Forall (ty_wellformed Δ) τs ->
      ty_wellformed Δ (TStruct name τs)
  | WF_Enum : forall Δ name τs,
      Forall (ty_wellformed Δ) τs ->
      ty_wellformed Δ (TEnum name τs)
  | WF_Never : forall Δ, ty_wellformed Δ TNever

with region_wellformed : region_env -> region -> Prop :=
  | WF_RStatic : forall Δ, region_wellformed Δ RStatic
  | WF_RVar : forall Δ rv,
      (exists ρ, re_lookup Δ rv = Some ρ) ->
      region_wellformed Δ (RVar rv)
  | WF_RUnion : forall Δ ρ₁ ρ₂,
      region_wellformed Δ ρ₁ ->
      region_wellformed Δ ρ₂ ->
      region_wellformed Δ (RUnion ρ₁ ρ₂).

(* ==========================================================================
 * 引理和性质
 * ========================================================================== *)

(* 秩的非负性 *)
Lemma ty_rank_nonneg : forall τ, ty_rank τ >= 0.
Proof. intros; auto with arith. Qed.

(* 度量在环境扩展时的变化 *)
Lemma te_measure_extend :
  forall Γ x τ,
    te_measure (te_extend Γ x τ) = ty_rank τ + te_measure Γ.
Proof.
  intros. unfold te_measure, te_extend.
  simpl. auto.
Qed.

(* ==========================================================================
 * 示例类型
 * ========================================================================== *)

(* i32 *)
Definition ti32 := TBase TI32.

(* &i32 *)
Definition tref_i32 := TRef RStatic Shrd ti32.

(* &mut i32 *)
Definition tref_mut_i32 := TRef RStatic Uniq ti32.

(* Box<i32> *)
Definition tbox_i32 := TBox ti32.

(* (i32, &i32) *)
Definition ttuple_example := TTuple [ti32; tref_i32].

(* 计算类型的秩 *)
Example rank_i32 : ty_rank ti32 = 0.
Proof. reflexivity. Qed.

Example rank_ref_i32 : ty_rank tref_i32 = 1.
Proof. reflexivity. Qed.

Example rank_box_i32 : ty_rank tbox_i32 = 1.
Proof. reflexivity. Qed.

Example rank_tuple : ty_rank ttuple_example = 1.
Proof. reflexivity. Qed.
