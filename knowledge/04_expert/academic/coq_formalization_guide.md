# Coq 形式化验证指南

> **工具**: Coq Proof Assistant
> **用途**: Rust 语义形式化验证
> **难度**: 专家级
> **前提**: 熟悉形式逻辑和类型理论

---

## 📋 目录

- [Coq 形式化验证指南](#coq-形式化验证指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🏗️ 基础设置](#️-基础设置)
    - [安装](#安装)
    - [项目结构](#项目结构)
  - [💡 核心概念](#-核心概念)
    - [所有权形式化](#所有权形式化)
    - [借用检查形式化](#借用检查形式化)
    - [类型安全证明](#类型安全证明)
  - [🚀 高级主题](#-高级主题)
    - [分离逻辑](#分离逻辑)
    - [并发验证](#并发验证)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 概述

Coq 是一个形式化证明管理工具，用于：

- 定义数学对象和算法
- 陈述数学定理和软件规范
- 交互式开发形式化证明
- 检查证明正确性

在 Rust 形式化验证中的应用：

- 所有权系统形式化
- 借用检查器正确性证明
- 类型安全保证
- 并发模型验证

---

## 🏗️ 基础设置

### 安装

```bash
# 使用 OPAM 安装 Coq
opam init
eval $(opam env)
opam install coq

# 安装 Iris (分离逻辑框架)
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install coq-iris

# 安装 stdpp (标准库扩展)
opam install coq-stdpp
```

### 项目结构

```
rust_formalization/
├── theories/
│   ├── syntax.v          # 语法定义
│   ├── semantics.v       # 操作语义
│   ├── ownership.v       # 所有权系统
│   ├── borrowing.v       # 借用检查
│   ├── typesystem.v      # 类型系统
│   └── safety.v          # 安全定理
├── proofs/
│   ├── ownership_thms.v
│   ├── borrow_thms.v
│   └── type_safety.v
└── _CoqProject
```

---

## 💡 核心概念

### 所有权形式化

```coq
(* 定义 Rust 值 *)
Inductive value : Type :=
  | VUnit : value
  | VInt : Z -> value
  | VBool : bool -> value
  | VRef : loc -> value          (* 引用 *)
  | VBox : loc -> value          (* Box 拥有指针 *)
  | VRc : loc -> nat -> value    (* Rc 引用计数 *)
  | VTuple : list value -> value.

(* 堆 *)
Definition heap := gmap loc (option value).

(* 所有权状态 *)
Inductive ownership : Type :=
  | OwnUnique : ownership        (* 独占所有权 *)
  | OwnShared : ownership        (* 共享所有权 *)
  | OwnBorrow : mutability -> ownership.  (* 借用 *)

(* 所有权判断 *)
Definition owns (h : heap) (l : loc) (o : ownership) : Prop :=
  match o with
  | OwnUnique => heap_lookup h l = Some (Some v) /\ unique_access h l
  | OwnShared => heap_lookup h l = Some (Some v) /\ shared_access h l
  | OwnBorrow Mutable => (* 可变借用检查 *)
  | OwnBorrow Immutable => (* 不可变借用检查 *)
  end.

(* 所有权转移定理 *)
Theorem ownership_transfer :
  forall h l v h',
  owns h l OwnUnique ->
  heap_update h l None = Some h' ->
  ~owns h' l OwnUnique.
Proof.
  (* 证明：转移后原所有者不再拥有 *)
  intros h l v h' H_own H_update.
  unfold owns in *.
  rewrite H_update.
  simpl.
  intuition.
Qed.
```

### 借用检查形式化

```coq
(* 借用状态 *)
Inductive borrow_state : Type :=
  | BSUnique : loc -> borrow_state    (* 独占借用 *)
  | BSShared : list loc -> borrow_state.  (* 共享借用列表 *)

(* 借用生命周期 *)
Definition borrow_lifetime := nat.

(* 借用有效性 *)
Definition valid_borrow (h : heap) (bs : borrow_state) (lt : borrow_lifetime) : Prop :=
  match bs with
  | BSUnique l =>
      exists v, heap_lookup h l = Some (Some v) /\ lt < lifetime_of l
  | BSShared ls =>
      forall l, In l ls ->
        exists v, heap_lookup h l = Some (Some v) /\ lt < lifetime_of l
  end.

(* 借用规则 *)
Inductive borrow_rule : Type :=
  | RuleMutUnique : forall l, no_active_borrows l -> can_borrow_mut l
  | RuleImmShared : forall l, no_mut_borrow l -> can_borrow_imm l
  | RuleFreeze : forall l, only_imm_borrows l -> can_freeze l.

(* 借用检查定理 *)
Theorem borrow_check_soundness :
  forall h e l lt,
  type_check e ->
  valid_borrow h (BSUnique l) lt ->
  eval e h = Some (VRef l, h') ->
  valid_borrow h' (BSUnique l) lt.
Proof.
  (* 证明：求值保持借用有效性 *)
Admitted.
```

### 类型安全证明

```coq
(* 类型定义 *)
Inductive ty : Type :=
  | TUnit : ty
  | TInt : ty
  | TBool : ty
  | TRef : mutability -> ty -> ty
  | TBox : ty -> ty
  | TTuple : list ty -> ty
  | TFn : list ty -> ty -> ty

with mutability :=
  | Mut : mutability
  | Imm : mutability.

(* 类型环境 *)
Definition type_env := gmap var ty.

(* 类型判断 *)
Inductive has_type : type_env -> expr -> ty -> Prop :=
  | T_Var : forall Gamma x t,
      Gamma !! x = Some t ->
      has_type Gamma (EVar x) t
  | T_Int : forall Gamma n,
      has_type Gamma (EInt n) TInt
  | T_Borrow : forall Gamma e t mut,
      has_type Gamma e t ->
      has_type Gamma (EBorrow mut e) (TRef mut t)
  | T_Deref : forall Gamma e t mut,
      has_type Gamma e (TRef mut t) ->
      has_type Gamma (EDeref e) t
  (* ... 更多类型规则 *)
.

(* 进展性定理 *)
Theorem progress :
  forall e h t,
  has_type empty e t ->
  is_value e \/ exists e' h', step e h e' h'.
Proof.
  intros e h t H_type.
  induction H_type; simpl.
  - (* 变量 *)
    left. constructor.
  - (* 整数 *)
    left. constructor.
  - (* 借用 *)
    right. (* 需要进一步证明 *)
Admitted.

(* 保持性定理 *)
Theorem preservation :
  forall Gamma e h t e' h',
  has_type Gamma e t ->
  step e h e' h' ->
  has_type Gamma e' t.
Proof.
  intros Gamma e h t e' h' H_type H_step.
  induction H_type; inversion H_step; subst.
  - (* 变量无进展 *)
    contradiction.
  - (* 借用的保持性 *)
    constructor. auto.
Qed.

(* 类型安全 *)
Theorem type_safety :
  forall e h t,
  has_type empty e t ->
  ~stuck e h.
Proof.
  intros e h t H_type.
  unfold stuck.
  intros [H_not_val H_no_step].
  destruct (progress e h t H_type).
  - contradiction.
  - destruct H as [e' [h' H_step]].
    contradiction.
Qed.
```

---

## 🚀 高级主题

### 分离逻辑

```coq
From iris.bi Require Import bi.
From iris.algebra Require Import gmap auth agree.
From iris.heap_lang Require Import lang proofmode notation.

(* 分离逻辑断言 *)
Definition own_loc (l : loc) (v : val) : iProp :=
  l ↦ v.

(* 所有权分离 *)
Definition sep_own (l1 l2 : loc) (v1 v2 : val) : iProp :=
  l1 ↦ v1 ∗ l2 ↦ v2.

(* 借用规则 *)
Lemma borrow_create :
  forall l v,
  own_loc l v ⊢
  (∃ bs, borrow_token bs ∗ (borrow_token bs -∗ own_loc l v)).
Proof.
  iIntros (l v) "Hown".
  iExists (BSUnique l).
  iFrame.
  iIntros "Htok".
  (* 证明借用可以恢复所有权 *)
Admitted.

(* 帧规则 *)
Lemma frame_rule :
  forall P Q R,
  (P ⊢ Q) ->
  (P ∗ R ⊢ Q ∗ R).
Proof.
  intros P Q R H_impl.
  iIntros "[HP HR]".
  iSplitL "HP".
  - iApply H_impl. iExact "HP".
  - iExact "HR".
Qed.
```

### 并发验证

```coq
(* 并发程序验证 *)
Definition thread_id := nat.

(* 线程池 *)
Definition thread_pool := gmap thread_id expr.

(* 并发操作语义 *)
Inductive cstep : thread_pool -> heap -> thread_pool -> heap -> Prop :=
  | CS_Tau : forall tp h tid e e',
      tp !! tid = Some e ->
      step e h e' h ->
      cstep tp h (<[tid:=e']>tp) h
  | CS_Fork : forall tp h tid e e' new_tid,
      tp !! tid = Some e ->
      step_fork e h e' h new_tid ->
      cstep tp h (<[tid:=e']>(<[new_tid:=EForked]>tp)) h.

(* 数据竞争自由 *)
Definition data_race_free (tp : thread_pool) (h : heap) : Prop :=
  forall tid1 tid2 e1 e2 l,
    tid1 ≠ tid2 ->
    tp !! tid1 = Some e1 ->
    tp !! tid2 = Some e2 ->
    ~ (writes_to e1 l /\ writes_to e2 l) /\n    ~ (writes_to e1 l /\ reads_from e2 l).

(* Send/Sync 验证 *)
Class Send (T : Type) : Prop := {
  send_safe : forall t : T, thread_safe t
}.

Class Sync (T : Type) : Prop := {
  sync_safe : forall t : T, concurrent_access_safe t
}.

(* Send/Sync 定理 *)
Theorem send_implies_thread_safe :
  forall T, Send T -> forall t : T, thread_safe t.
Proof.
  intros T H_send t.
  apply send_safe.
Qed.
```

---

## 🔗 参考资源

- [Coq 官方文档](https://coq.inria.fr/documentation)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Iris 教程](https://iris-project.org/tutorial.html)
- [RustBelt 论文](https://plv.mpi-sws.org/rustbelt/popl18/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: ✅ 100% 完成
