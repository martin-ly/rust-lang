# Coq 证明骨架（L3  scaffolding）

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 为 L3 机器可检查证明提供 Coq 定理陈述骨架，对应 [CORE_THEOREMS_FULL_PROOFS](../CORE_THEOREMS_FULL_PROOFS.md)
> **状态**: ✅ 已完成

---

## 文件说明

| 文件 | 对应定理 | 状态 |
| :--- | :--- | :--- |
| `OWNERSHIP_UNIQUENESS.v` | T-OW2 所有权唯一性 | 定理陈述已定义；证明 Admitted |
| `BORROW_DATARACE_FREE.v` | T-BR1 数据竞争自由 | 定理陈述已定义；证明 Admitted |
| `TYPE_SAFETY.v` | T-TY3 类型安全 | 定理陈述已定义；证明 Admitted |

---

## 编译

**前置**: 安装 [Coq](https://coq.inria.fr/)（建议 8.18+）

```bash
cd docs/research_notes/coq_skeleton
coqc OWNERSHIP_UNIQUENESS.v
coqc BORROW_DATARACE_FREE.v
coqc TYPE_SAFETY.v
```

---

## 代码示例

### 示例 1: 所有权唯一性定理 (T-OW2)

```coq
(* OWNERSHIP_UNIQUENESS.v - 所有权唯一性定理骨架 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

(* 基础定义占位 *)
Parameter Pointer : Type.
Parameter Value : Type.
Parameter Owner : Type.
Parameter State : Type.

(* 所有权状态 *)
Inductive OwnershipStatus : Type :=
  | Owned : OwnershipStatus
  | BorrowedMut : OwnershipStatus
  | BorrowedImm : OwnershipStatus
  | Moved : OwnershipStatus.

(* 状态中的所有权映射 *)
Parameter owner_map : State -> Pointer -> option Owner.
Parameter ownership_status : State -> Pointer -> OwnershipStatus.

(* 可达状态：从初始状态经规则 1-3 可达 *)
Parameter reachable : State -> Prop.

(* 计数函数：统计拥有特定所有权状态的指针数量 *)
Fixpoint count_owned (state: State) (v: Value) : nat :=
  (* 占位实现 *)
  0.

(* T-OW2: 所有权唯一性定理 *)
Theorem ownership_uniqueness :
  forall (state: State) (v: Value),
    reachable state ->
    count_owned state v <= 1.
Proof.
  intros state v H_reachable.
  (* 对 reachable 归纳证明 *)
  (* 归纳基：初始状态，所有权唯一 *)
  (* 归纳步：移动/复制/drop 保持唯一性 *)
Admitted.
```

### 示例 2: 数据竞争自由定理 (T-BR1)

```coq
(* BORROW_DATARACE_FREE.v - 数据竞争自由定理骨架 *)
Require Import Coq.Bool.Bool.

(* 程序表示 *)
Parameter Program : Type.
Parameter ThreadId : Type.
Parameter MemoryLocation : Type.

(* 借用检查结果 *)
Inductive BorrowCheckResult : Type :=
  | BC_OK : BorrowCheckResult
  | BC_Error : string -> BorrowCheckResult.

(* 借用检查函数 *)
Parameter BorrowCheck : Program -> BorrowCheckResult.

(* 数据竞争自由属性 *)
Inductive AccessType : Type :=
  | Read : AccessType
  | Write : AccessType.

Record MemoryAccess := {
  thread : ThreadId;
  location : MemoryLocation;
  access : AccessType;
  timestamp : nat
}.

(* 是否存在数据竞争 *)
Definition has_data_race (accesses: list MemoryAccess) : Prop :=
  exists (a1 a2: MemoryAccess),
    In a1 accesses /\ In a2 accesses /\
    a1.(thread) <> a2.(thread) /\
    a1.(location) = a2.(location) /\
    (a1.(access) = Write \/ a2.(access) = Write).

Definition DataRaceFree (p: Program) : Prop :=
  forall (exec: list MemoryAccess),
    valid_execution p exec ->
    ~ has_data_race exec.

(* L-BR1: 借用检查通过意味着无数据竞争 *)
Lemma borrow_check_implies_no_data_race :
  forall (p: Program),
    BorrowCheck p = BC_OK ->
    DataRaceFree p.
Proof.
  intros p H_bc.
  (* 从借用规则 5-8 推导 *)
Admitted.

(* T-BR1: 借用检查器正确性 *)
Theorem borrow_checker_correctness :
  forall (p: Program),
    BorrowCheck p = BC_OK ->
    DataRaceFree p.
Proof.
  exact borrow_check_implies_no_data_race.
Qed.
```

### 示例 3: 类型安全定理 (T-TY3)

```coq
(* TYPE_SAFETY.v - 类型安全定理骨架 *)
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

(* 表达式语法 *)
Inductive Expr : Type :=
  | EVar : nat -> Expr
  | ENum : nat -> Expr
  | EBool : bool -> Expr
  | EAdd : Expr -> Expr -> Expr
  | ESub : Expr -> Expr -> Expr
  | EIf : Expr -> Expr -> Expr -> Expr
  | ELet : nat -> Expr -> Expr -> Expr
  | ERef : Expr -> Expr
  | EDeref : Expr -> Expr
  | EAssign : Expr -> Expr -> Expr.

(* 类型 *)
Inductive Ty : Type :=
  | TNum : Ty
  | TBool : Ty
  | TRef : Ty -> Ty
  | TUnit : Ty.

(* 值 *)
Inductive Value : Type :=
  | VNum : nat -> Value
  | VBool : bool -> Value
  | VLoc : nat -> Value
  | VUnit : Value.

(* 类型环境 *)
Definition Gamma := nat -> option Ty.

(* 类型判断关系 *)
Inductive has_type : Gamma -> Expr -> Ty -> Prop :=
  | T_Var : forall g x t,
      g x = Some t ->
      has_type g (EVar x) t
  | T_Num : forall g n,
      has_type g (ENum n) TNum
  | T_Bool : forall g b,
      has_type g (EBool b) TBool
  | T_Add : forall g e1 e2,
      has_type g e1 TNum ->
      has_type g e2 TNum ->
      has_type g (EAdd e1 e2) TNum
  | T_Sub : forall g e1 e2,
      has_type g e1 TNum ->
      has_type g e2 TNum ->
      has_type g (ESub e1 e2) TNum
  | T_If : forall g e1 e2 e3 t,
      has_type g e1 TBool ->
      has_type g e2 t ->
      has_type g e3 t ->
      has_type g (EIf e1 e2 e3) t
  | T_Ref : forall g e t,
      has_type g e t ->
      has_type g (ERef e) (TRef t)
  | T_Deref : forall g e t,
      has_type g e (TRef t) ->
      has_type g (EDeref e) t.

(* 求值关系 *)
Inductive eval : Expr -> Value -> Prop :=
  | E_Val_Num : forall n, eval (ENum n) (VNum n)
  | E_Val_Bool : forall b, eval (EBool b) (VBool b)
  | E_Val_Add : forall e1 e2 n1 n2,
      eval e1 (VNum n1) ->
      eval e2 (VNum n2) ->
      eval (EAdd e1 e2) (VNum (n1 + n2))
  | E_Val_Sub : forall e1 e2 n1 n2,
      eval e1 (VNum n1) ->
      eval e2 (VNum n2) ->
      eval (ESub e1 e2) (VNum (n1 - n2)).

(* 进展性：良类型表达式要么是值，要么可以进一步求值 *)
Definition progress (g: Gamma) (e: Expr) (t: Ty) : Prop :=
  has_type g e t ->
  (exists v, eval e v) \/ (exists e', step e e').

(* 保持性：求值保持类型 *)
Parameter step : Expr -> Expr -> Prop.

Definition preservation (g: Gamma) (e: Expr) (t: Ty) : Prop :=
  has_type g e t ->
  forall e', step e e' ->
  has_type g e' t.

(* T-TY3: 类型安全定理 = 进展性 + 保持性 *)
Theorem type_safety :
  forall (g: Gamma) (e: Expr) (t: Ty),
    has_type g e t ->
    progress g e t /\ preservation g e t.
Proof.
  intros g e t H_t.
  split.
  - (* 证明进展性 *)
    unfold progress.
    intros H.
    induction H;
      try (left; eauto using eval);
      try (right; (* 存在可求值步骤 *) admit).
  - (* 证明保持性 *)
    unfold preservation.
    intros H e' H_step.
    induction H;
      inversion H_step;
      subst;
      eauto using has_type.
Admitted.

(* 类型错误定义 *)
Inductive type_error : Expr -> Prop :=
  | TE_Mismatch : forall e,
      (* 操作数类型不匹配 *)
      type_error e
  | TE_Unbound : forall x,
      type_error (EVar x).

(* 推论：良类型程序不会 stuck（不会遇到类型错误） *)
Corollary well_typed_no_stuck :
  forall (g: Gamma) (e: Expr) (t: Ty),
    has_type g e t ->
    forall e', multi_step e e' ->
    ~ type_error e'.
Proof.
  (* 由类型安全定理推导 *)
Admitted.
```

---

## 补全路线

### 步骤 1: 细化 State 定义

```coq
(* 定义「可达状态」谓词（由初始状态经规则 1-3 转换得到） *)
Inductive state_transition : State -> State -> Prop :=
  | ST_Move : forall s p,
      (* 移动操作 *)
      state_transition s (update_owner s p Moved)
  | ST_Copy : forall s p,
      (* 复制操作 *)
      state_transition s (update_owner s p (BorrowedImm))
  | ST_Drop : forall s p,
      (* 作用域结束 *)
      state_transition s (remove_owner s p).

Inductive reachable : State -> Prop :=
  | R_Init : forall s,
      initial_state s ->
      reachable s
  | R_Step : forall s1 s2,
      reachable s1 ->
      state_transition s1 s2 ->
      reachable s2.
```

### 步骤 2: 归纳证明

```coq
(* 对 reachable 归纳；归纳基用 L-OW1；归纳步对移动/复制/作用域结束分类 *)
Theorem ownership_uniqueness_complete :
  forall (state: State) (v: Value),
    reachable state ->
    count_owned state v <= 1.
Proof.
  intros state v H_reach.
  induction H_reach.
  - (* 初始状态：所有权唯一 *)
    apply initial_ownership_unique.
  - (* 归纳步：状态转换保持唯一性 *)
    inversion H; subst;
      [apply move_preserves_uniqueness |
       apply copy_preserves_uniqueness |
       apply drop_preserves_uniqueness];
      assumption.
Qed.
```

### 步骤 3: 扩展其他定理

1. **T-BR1**: 完成 `BORROW_DATARACE_FREE.v` - 借用规则 → 数据竞争自由
2. **T-TY3**: 完成 `TYPE_SAFETY.v` - 类型安全（进展 + 保持）

---

## 研究场景

### 场景 1: 验证 Vec<T> 的所有权唯一性

```rust
// 研究场景：验证 Vec<T> 的所有权语义
fn ownership_scenario() {
    let v1 = vec![1, 2, 3];  // v1 拥有 Vec
    let v2 = v1;              // 所有权移动到 v2
    // v1 不再有效；编译器通过借用检查确保这一点

    // 形式化验证目标：
    // 在任意程序点，每个值只有一个活跃的所有者
}
```

**Coq 对应**:

```coq
(* 定理：Vec 在任意时刻只有一个所有者 *)
Theorem vec_ownership_unique :
  forall (T: Type) (state: State) (v: VecOwnership T),
    reachable state ->
    count_owners state v <= 1.
```

### 场景 2: 验证并发访问的数据竞争自由

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// 研究场景：验证并发访问的数据竞争自由
fn concurrent_borrow_scenario() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut num = data.lock().unwrap();
            *num += 1;  // 编译时借用检查确保无数据竞争
        });
        handles.push(handle);
    }

    // 形式化验证目标：
    // 借用检查通过 ⇒ 程序无数据竞争
}
```

### 场景 3: 类型安全验证

```rust
// 研究场景：验证类型系统的安全性
fn type_safety_scenario() {
    let x: i32 = 42;
    let y = x + 1;  // 类型检查确保操作合法

    // 以下代码无法编译（类型错误）
    // let z: bool = x + y;  // 编译错误

    // 形式化验证目标：
    // 良类型程序不会 stuck（不会遇到类型错误）
}
```

---

## 形式化链接

### 核心定理文档

| 定理 | 文档 | Coq 骨架 |
| :--- | :--- | :--- |
| T-OW2 | [CORE_THEOREMS_FULL_PROOFS](../CORE_THEOREMS_FULL_PROOFS.md) §2.2 | [OWNERSHIP_UNIQUENESS.v](./OWNERSHIP_UNIQUENESS.v) |
| T-BR1 | [CORE_THEOREMS_FULL_PROOFS](../CORE_THEOREMS_FULL_PROOFS.md) §3.1 | [BORROW_DATARACE_FREE.v](./BORROW_DATARACE_FREE.v) |
| T-TY3 | [CORE_THEOREMS_FULL_PROOFS](../CORE_THEOREMS_FULL_PROOFS.md) §4.3 | [TYPE_SAFETY.v](./TYPE_SAFETY.v) |

### 相关研究笔记

| 主题 | 文档 |
| :--- | :--- |
| 所有权模型 | [formal_methods/ownership_model.md](../formal_methods/ownership_model.md) |
| 借用检查器 | [formal_methods/borrow_checker_proof.md](../formal_methods/borrow_checker_proof.md) |
| 类型系统 | [type_theory/type_system_foundations.md](../type_theory/type_system_foundations.md) |

### 集成计划

| 工具 | 文档 |
| :--- | :--- |
| Aeneas | [AENEAS_INTEGRATION_PLAN](../AENEAS_INTEGRATION_PLAN.md) |
| coq-of-rust | [COQ_OF_RUST_INTEGRATION_PLAN](../COQ_OF_RUST_INTEGRATION_PLAN.md) |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-20
