# L3机器可检查证明实施指南

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **证明深度**: L3 (机器可检查)
> **目标**: 将核心定理从L2完整证明提升到L3机器可检查证明

---

## 一、L3证明概述

### 1.1 证明深度层级

| 层级 | 名称 | 特点 | 机器可检查 | 本体系状态 |
| :--- | :--- | :--- | :--- | :--- |
| L1 | 证明思路 | 高层论证步骤，文字描述 | 否 | 100% |
| L2 | 完整证明 | 含归纳基/步、辅助引理 | 否 | 80% |
| **L3** | **机器证明** | **Coq/Lean等证明助手可验证** | **是** | **10%** |
| L4 | 自动化生成 | 从代码自动生成证明 | 是 | 未来 |

### 1.2 L3证明目标

本阶段目标是为以下核心定理建立L3机器可检查证明：

1. **T-OW2**: 所有权唯一性定理
2. **T-BR1**: 数据竞争自由定理
3. **T-TY3**: 类型安全定理

---

## 二、工具链选择

### 2.1 推荐方案: Coq + Iris

**理由**:

1. RustBelt使用Iris框架成功验证了Rust核心库
2. Iris专为并发分离逻辑设计，适合Rust的 ownership 模型
3. 有丰富的Rust相关证明基础设施

### 2.2 环境搭建

```bash
# 使用OPAM安装Coq
opam init
eval $(opam env)
opam install coq.8.18.0

# 安装Iris
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-iris

# 验证安装
coqtop --version
```

---

## 三、T-OW2所有权唯一性L3证明

### 3.1 定理回顾

**T-OW2 (所有权唯一性)**: 对于任何值v，在任意时刻，最多存在一个变量x使得所有权状态为Owned且绑定值为v。

### 3.2 Iris中的状态表示

```coq
From iris.algebra Require Import base gmap.
From iris.bi Require Import bi.
From iris.proofmode Require Import tactics.

(* 定义值类型 *)
Parameter Value : Type.
Parameter Value_eq_dec : EqDecision Value.

(* 定义变量类型 *)
Definition Var := nat.

(* 所有权状态 *)
Inductive OwnStatus :=
  | Owned : OwnStatus
  | Moved : OwnStatus
  | Dropped : OwnStatus.

(* 状态: 变量到(值×所有权状态)的映射 *)
Definition State := gmap Var (Value * OwnStatus).

(* 所有权唯一性谓词 *)
Definition ownership_unique (σ : State) : Prop :=
  forall (v : Value) (x1 x2 : Var),
    σ !! x1 = Some (v, Owned) ->
    σ !! x2 = Some (v, Owned) ->
    x1 = x2.
```

### 3.3 状态转移规则

```coq
(* 状态转移关系 *)
Inductive step : State -> State -> Prop :=
  (* 移动: x移动到y *)
  | StepMove : forall σ x y v,
      σ !! x = Some (v, Owned) ->
      σ !! y = None ->
      step σ (<[x := (v, Moved)]> (<[y := (v, Owned)]> σ))

  (* 复制(Copy类型): x复制到y *)
  | StepCopy : forall σ x y v,
      σ !! x = Some (v, Owned) ->
      σ !! y = None ->
      step σ (<[y := (v, Owned)]> σ)

  (* Drop: 作用域结束 *)
  | StepDrop : forall σ x v,
      σ !! x = Some (v, Owned) ->
      step σ (<[x := (v, Dropped)]> σ).

(* 可达状态 *)
Inductive reachable : State -> Prop :=
  | ReachInit : forall σ,
      (forall v, (forall x, σ !! x = Some (v, Owned) ->
                   forall y, σ !! y = Some (v, Owned) -> x = y)) ->
      reachable σ
  | ReachStep : forall σ1 σ2,
      reachable σ1 ->
      step σ1 σ2 ->
      reachable σ2.
```

### 3.4 主定理证明骨架

```coq
Theorem T_OW2_ownership_uniqueness :
  forall σ : State, reachable σ -> ownership_unique σ.
Proof.
  intros σ Hreach.
  induction Hreach as [σ Hinit | σ1 σ2 Hreach IH Hstep].

  - (* 基础情况: 初始状态 *)
    unfold ownership_unique.
    intros v x1 x2 H1 H2.
    apply (Hinit v x1 H1 x2 H2).

  - (* 归纳步骤: 状态转移保持唯一性 *)
    unfold ownership_unique in *.
    intros v x1 x2 H1 H2.

    inversion Hstep; subst; clear Hstep.

    + (* 移动步骤 *)
      (* 分情况讨论x1, x2的位置 *)
      admit.

    + (* 复制步骤 *)
      admit.

    + (* Drop步骤 *)
      admit.
Admitted.
```

---

## 四、T-BR1数据竞争自由L3证明

### 4.1 定理回顾

**T-BR1 (数据竞争自由)**: 借用检查器保证程序是数据竞争自由的。

### 4.2 并发模型形式化

```coq
From iris.heap_lang Require Import lang.
From iris.algebra Require Import excl auth gmap.

(* 内存位置 *)
Definition Loc := nat.

(* 访问类型 *)
Inductive Access := Read | Write.

(* 数据竞争定义 *)
Definition data_race (a1 a2 : (nat * Loc * Access)) : Prop :=
  let (_, l1, ac1) := a1 in
  let (_, l2, ac2) := a2 in
  l1 = l2 /\ (ac1 = Write \/ ac2 = Write).

(* 数据竞争自由 *)
Definition data_race_free (accesses : list (nat * Loc * Access)) : Prop :=
  forall i j a1 a2,
    accesses !! i = Some a1 ->
    accesses !! j = Some a2 ->
    i <> j ->
    ~ data_race a1 a2.
```

### 4.3 主定理证明骨架

```coq
Theorem T_BR1_borrow_checker_correctness P :
  borrow_check P = OK ->
  forall accesses, trace_accesses P accesses -> data_race_free accesses.
Proof.
  intros Hcheck accesses Htrace.

  (* 反证: 假设存在数据竞争 *)
  unfold data_race_free.
  intros i j a1 a2 Hi Hj Hneq Hrace.

  (* 从借用检查规则推导矛盾 *)
  destruct a1 as [t1 l1 ac1].
  destruct a2 as [t2 l2 ac2].
  unfold data_race in Hrace.
  destruct Hrace as [Heql Hwrite].

  (* 使用资源代数中的排他性推导矛盾 *)
  admit.
Admitted.
```

---

## 五、T-TY3类型安全L3证明

### 5.1 类型系统形式化

```coq
From iris.heap_lang Require Import lang.

(* 类型 *)
Inductive ty :=
  | TInt : ty
  | TBool : ty
  | TUnit : ty
  | TRef : ty -> ty
  | TFn : ty -> ty -> ty.

(* 类型环境 *)
Definition ctx := gmap string ty.

(* 类型判断: Gamma |- e : tau *)
Inductive typed (Gamma : ctx) : expr -> ty -> Prop :=
  | TInt_typed n :
      Gamma |- (Lit $ LitInt n) : TInt
  | TBool_typed b :
      Gamma |- (Lit $ LitBool b) : TBool
  | TVar_typed x tau :
      Gamma !! x = Some tau ->
      Gamma |- (Var x) : tau
  | TAdd_typed e1 e2 :
      Gamma |- e1 : TInt ->
      Gamma |- e2 : TInt ->
      Gamma |- (e1 + e2) : TInt
  | TLam_typed x e tau1 tau2 :
      (<[x := tau1]> Gamma) |- e : tau2 ->
      Gamma |- (Lam x e) : TFn tau1 tau2
  | TApp_typed e1 e2 tau1 tau2 :
      Gamma |- e1 : TFn tau1 tau2 ->
      Gamma |- e2 : tau1 ->
      Gamma |- (App e1 e2) : tau2
where "Gamma '|-' e ':' tau" := (typed Gamma e tau).
```

### 5.2 进展性定理

```coq
Theorem T_TY1_progress (Gamma : ctx) (e : expr) (tau : ty) :
  Gamma |- e : tau ->
  is_val e \/ exists e', head_step e None e' None.
Proof.
  intros Hty.
  induction Hty.

  - (* 整数 *)
    left. by apply is_val_lit.

  - (* 布尔 *)
    left. by apply is_val_lit.

  - (* 变量 *)
    admit.

  - (* 加法 *)
    admit.

  - (* Lambda *)
    left. by apply is_val_lam.

  - (* 应用 *)
    admit.
Admitted.
```

---

## 六、与Aeneas工具链对接

### 6.1 安装Aeneas

```bash
# 克隆仓库
git clone https://github.com/AeneasVerif/aeneas.git
cd aeneas

# 设置Charon
make setup-charon

# 构建
make
```

### 6.2 Rust到Lean翻译示例

```bash
# Rust代码
cat > example.rs << 'EOF'
fn incr(x: u32) -> u32 {
    x + 1
}
EOF

# 生成LLBC
charon cargo --preset=aeneas

# 翻译成Lean
./bin/aeneas -backend lean example.llbc
```

---

## 七、验证与测试

### 7.1 Coq文件编译验证

```bash
cd docs/research_notes/coq_skeleton
coq_makefile -f _CoqProject -o Makefile
make
```

### 7.2 证明完整性检查

```bash
# 检查Admitted数量
grep -r "Admitted" *.v | wc -l
# 目标: 0

# 检查Qed数量
grep -r "Qed" *.v | wc -l
```

---

## 八、里程碑

| 里程碑 | 目标日期 | 验收标准 |
| :--- | :--- | :--- |
| M1 | Week 4 | T-OW2骨架细化完成 |
| M2 | Week 8 | T-OW2 L3证明完成 |
| M3 | Week 12 | T-BR1 L3证明完成 |
| M4 | Week 16 | T-TY3 L3证明完成 |
| M5 | Week 20 | Aeneas对接完成 |
| M6 | Week 24 | CI集成完成 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-20
**状态**: 进行中 - L3机器证明实施中
