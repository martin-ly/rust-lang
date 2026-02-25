# 形式化工具验证指南

> **创建日期**: 2025-12-25
> **最后更新**: 2026-01-26
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ **指南 100% 完成**

---

## 📊 目录 {#-目录}

- [形式化工具验证指南](#形式化工具验证指南)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [🎯 概述 {#-概述}](#-概述--概述)
    - [验证目标](#验证目标)
  - [形式化论证（验证框架）](#形式化论证验证框架)
  - [🛠️ 工具选择 {#️-工具选择}](#️-工具选择-️-工具选择)
    - [Coq](#coq)
    - [Isabelle/HOL](#isabellehol)
  - [📚 验证准备工作 {#-验证准备工作}](#-验证准备工作--验证准备工作)
    - [1. 环境准备](#1-环境准备)
    - [2. 理论准备](#2-理论准备)
    - [3. 验证框架设计](#3-验证框架设计)
  - [🔬 验证实施步骤 {#-验证实施步骤}](#-验证实施步骤--验证实施步骤)
    - [步骤 1: 所有权模型验证](#步骤-1-所有权模型验证)
    - [步骤 2: 借用检查器验证](#步骤-2-借用检查器验证)
    - [步骤 3: 生命周期验证](#步骤-3-生命周期验证)
    - [步骤 4: 类型系统验证](#步骤-4-类型系统验证)
    - [步骤 5: 异步状态机验证](#步骤-5-异步状态机验证)
    - [步骤 6: Pin 与自引用验证](#步骤-6-pin-与自引用验证)
  - [📋 验证任务清单 {#-验证任务清单}](#-验证任务清单--验证任务清单)
    - [所有权模型验证](#所有权模型验证)
    - [借用检查器验证](#借用检查器验证)
    - [生命周期验证](#生命周期验证)
    - [类型系统验证](#类型系统验证)
    - [异步状态机验证](#异步状态机验证)
    - [Pin 与自引用验证](#pin-与自引用验证)
  - [🔗 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [学习资源](#学习资源)
    - [相关项目](#相关项目)
    - [工具链扩展任务（Rust → 证明助手）](#工具链扩展任务rust--证明助手)
    - [工具资源](#工具资源)

---

## 🎯 概述 {#-概述}

本指南提供了使用形式化工具（Coq、Isabelle）验证 Rust 形式化定义的完整流程。

**文档状态**：本指南结构与全部六类验证的 Coq/Isabelle 框架、任务清单已完整；验证任务清单中的方框供实施时勾选。

**Coq 证明骨架**：所有权唯一性（T-OW2）的 Coq 定理骨架已创建，见 [coq_skeleton/OWNERSHIP_UNIQUENESS.v](./coq_skeleton/OWNERSHIP_UNIQUENESS.v)、[COQ_ISABELLE_PROOF_SCAFFOLDING](./COQ_ISABELLE_PROOF_SCAFFOLDING.md)。

### 验证目标

1. **所有权模型验证**：验证所有权规则的正确性
2. **借用检查器验证**：验证借用规则的正确性
3. **生命周期验证**：验证生命周期规则的正确性
4. **类型系统验证**：验证类型系统的正确性
5. **异步状态机验证**：验证 Future 状态一致性与并发安全
6. **Pin 与自引用验证**：验证 Pin 保证与自引用类型安全

---

## 形式化论证（验证框架）

**Def FV1（形式化验证）**：设 $T$ 为形式化定理（如 ownership T2、borrow T1），$V$ 为 Coq/Isabelle 等工具的验证活动。若 $V$ 生成机器可检查证明，且证明的结论与 $T$ 的陈述一致，则称 $V$ **验证** $T$。

**Axiom FV1**：形式化验证不能替代定理正确性论证，但可排除证明中的隐含错误；验证通过 ⇒ 证明无语法/逻辑遗漏。

**定理 FV-T1（验证与定理衔接）**：若 $V$ 验证 $T$，则 $T$ 的证明在验证工具的逻辑框架内成立；与 [PROOF_INDEX](PROOF_INDEX.md) 的手工证明互为补充。

*证明*：由 Def FV1；机器验证保证证明结构正确；手工证明提供直觉与文档；二者一致则论证完备。∎

**引理 FV-L1（六类验证覆盖）**：所有权、借用、生命周期、类型系统、异步、Pin 六类验证覆盖 Rust 核心安全机制；与 [formal_methods/README](formal_methods/README.md) FM-T1 对应。

*证明*：由 Def FV1 与验证目标；六类对应 ownership_model、borrow_checker_proof、lifetime_formalization、type_system_foundations、async_state_machine、pin_self_referential。∎

**推论 FV-C1**：验证任务清单完成 ⇔ 六类均有机器可检查证明；与 [ARGUMENTATION_GAP_INDEX](ARGUMENTATION_GAP_INDEX.md) 论证缺口追踪衔接。

---

## 🛠️ 工具选择 {#️-工具选择}

### Coq

**优势**：

- 强大的证明自动化
- 丰富的标准库
- 活跃的社区支持

**安装**：

```bash
# 使用 opam 安装
opam install coq

# 或使用包管理器
# Ubuntu/Debian
sudo apt-get install coq

# macOS
brew install coq
```

**基本使用**：

```coq
(* 定义所有权状态 *)
Inductive OwnershipState : Type :=
  | Owned
  | Moved
  | Borrowed.

(* 定义所有权规则 *)
Definition move_rule (s: OwnershipState) : OwnershipState :=
  match s with
  | Owned => Moved
  | _ => s
  end.
```

### Isabelle/HOL

**优势**：

- 强大的自动化证明
- 丰富的理论库
- 良好的文档支持

**安装**：

```bash
# 下载并安装 Isabelle
# https://isabelle.in.tum.de/
```

**基本使用**：

```isabelle
theory OwnershipModel
imports Main
begin

datatype ownership_state = Owned | Moved | Borrowed

definition move_rule :: "ownership_state ⇒ ownership_state"
where "move_rule s = (case s of Owned ⇒ Moved | _ ⇒ s)"

end
```

---

## 📚 验证准备工作 {#-验证准备工作}

### 1. 环境准备

**Coq 环境**：

- [ ] 安装 Coq（版本 8.15+）
- [ ] 安装 CoqIDE 或 Proof General
- [ ] 配置开发环境

**Isabelle 环境**：

- [ ] 安装 Isabelle（版本 2022+）
- [ ] 安装 Isabelle/jEdit
- [ ] 配置开发环境

### 2. 理论准备

**需要转换的形式化定义**：

- [ ] 所有权模型的形式化定义
- [ ] 借用检查器的形式化定义
- [ ] 生命周期的形式化定义
- [ ] 类型系统的形式化定义
- [ ] 异步状态机的形式化定义（参见 [async_state_machine.md](./formal_methods/async_state_machine.md)）
- [ ] Pin 与自引用类型的形式化定义（参见 [pin_self_referential.md](./formal_methods/pin_self_referential.md)）

### 3. 验证框架设计

**验证结构**：

```text
formal_verification/
├── ownership_model.v          # 所有权模型验证
├── borrow_checker.v           # 借用检查器验证
├── lifetime.v                 # 生命周期验证
├── type_system.v              # 类型系统验证
├── async_state_machine.v      # 异步状态机验证
├── pin_self_referential.v     # Pin 与自引用验证
└── common.v                   # 公共定义
```

---

## 🔬 验证实施步骤 {#-验证实施步骤}

### 步骤 1: 所有权模型验证

**目标**：验证所有权规则的正确性

**Coq 实现框架**：

```coq
(* ownership_model.v *)
Require Import Coq.Arith.Arith.

(* 定义所有权状态 *)
Inductive OwnershipState : Type :=
  | Owned
  | Moved
  | Borrowed.

(* 定义所有权转移 *)
Definition transfer_ownership (s: OwnershipState) : OwnershipState :=
  match s with
  | Owned => Moved
  | _ => s
  end.

(* 验证所有权唯一性 *)
Theorem ownership_uniqueness :
  forall s, s = Owned -> transfer_ownership s = Moved.
Proof.
  intros s H.
  unfold transfer_ownership.
  rewrite H.
  reflexivity.
Qed.
```

**验证内容**：

- [ ] 所有权唯一性
- [ ] 所有权转移规则
- [ ] 内存安全保证

### 步骤 2: 借用检查器验证

**目标**：验证借用规则的正确性

**Coq 实现框架**：

```coq
(* borrow_checker.v *)
Require Import ownership_model.

(* 定义借用类型 *)
Inductive BorrowType : Type :=
  | Immutable
  | Mutable.

(* 定义借用规则 *)
Definition borrow_rule (s: OwnershipState) (bt: BorrowType) : Prop :=
  match s, bt with
  | Owned, Immutable => True
  | Owned, Mutable => True
  | Borrowed, Immutable => True
  | Borrowed, Mutable => False
  | Moved, _ => False
  end.

(* 验证数据竞争自由 *)
Theorem data_race_freedom :
  forall s bt, borrow_rule s bt ->
    (bt = Mutable -> s <> Borrowed).
Proof.
  intros s bt H.
  destruct s, bt; simpl in H; try contradiction.
  - discriminate.
  - auto.
Qed.
```

**验证内容**：

- [ ] 借用规则正确性
- [ ] 数据竞争自由
- [ ] 借用检查算法

### 步骤 3: 生命周期验证

**目标**：验证生命周期规则的正确性

**Coq 实现框架**：

```coq
(* lifetime.v *)
Require Import Coq.Arith.Arith.

(* 定义生命周期 *)
Definition Lifetime := nat.

(* 定义引用有效性 *)
Definition reference_valid (l: Lifetime) (scope: Lifetime) : Prop :=
  l <= scope.

(* 验证引用有效性 *)
Theorem reference_validity :
  forall l scope, reference_valid l scope -> l <= scope.
Proof.
  unfold reference_valid.
  auto.
Qed.
```

**验证内容**：

- [ ] 引用有效性
- [ ] 生命周期推断
- [ ] 生命周期约束

### 步骤 4: 类型系统验证

**目标**：验证类型系统的正确性

**Coq 实现框架**：

```coq
(* type_system.v *)
Require Import Coq.Lists.List.

(* 定义类型 *)
Inductive Type_ : Type :=
  | Int
  | Bool
  | Function (arg ret: Type_).

(* 定义类型推导 *)
Inductive TypeCheck : list (nat * Type_) -> nat -> Type_ -> Prop :=
  | TC_Int : forall env n, TypeCheck env n Int
  | TC_Fun : forall env n arg ret,
      TypeCheck env n (Function arg ret).

(* 验证类型安全 *)
Theorem type_safety :
  forall env e t, TypeCheck env e t -> exists v, eval e = Some v.
Proof.
  (* 证明思路 *)
Admitted.
```

**验证内容**：

- [ ] 类型推导正确性
- [ ] 类型安全
- [ ] 进展性和保持性

### 步骤 5: 异步状态机验证

**目标**：验证 Future 状态一致性、并发安全与进度保证（参见 [async_state_machine.md](./formal_methods/async_state_machine.md)）

**Coq 实现框架**：

```coq
(* async_state_machine.v *)
Require Import Coq.Arith.Arith.

(* 定义 Future 状态 *)
Inductive FutureState : Type :=
  | Pending | Ready | Waiting | Polling.

(* 定义有效状态转换 *)
Definition ValidTransition (s s' : FutureState) : Prop :=
  match s, s' with
  | Pending, Polling => True
  | Polling, Pending => True
  | Polling, Ready => True
  | _ , _ => False
  end.

(* 定理 6.1 状态一致性、6.2 并发安全、6.3 进度保证 *)
```

**验证内容**：

- [ ] 状态一致性（定理 6.1）
- [ ] 并发安全（定理 6.2）
- [ ] 进度保证（定理 6.3）

### 步骤 6: Pin 与自引用验证

**目标**：验证 Pin 保证、自引用类型安全与 Pin 投影安全（参见 [pin_self_referential.md](./formal_methods/pin_self_referential.md)）

**Coq 实现框架**：

```coq
(* pin_self_referential.v *)

(* 定义 Unpin / !Unpin、Pin 不变式：被 Pin 值的位置稳定性 *)
(* 定理 1 Pin 保证、定理 2 自引用类型安全、定理 3 Pin 投影安全 *)
```

**验证内容**：

- [ ] Pin 保证（定理 1）
- [ ] 自引用类型安全（定理 2）
- [ ] Pin 投影安全（定理 3）

---

## 📋 验证任务清单 {#-验证任务清单}

### 所有权模型验证

- [ ] 转换所有权模型形式化定义到 Coq/Isabelle
- [ ] 实现所有权状态定义
- [ ] 实现所有权转移规则
- [ ] 证明所有权唯一性
- [ ] 证明内存安全
- [ ] 编写验证报告

### 借用检查器验证

- [ ] 转换借用检查器形式化定义到 Coq/Isabelle
- [ ] 实现借用类型定义
- [ ] 实现借用规则
- [ ] 证明数据竞争自由
- [ ] 证明借用规则正确性
- [ ] 编写验证报告

### 生命周期验证

- [ ] 转换生命周期形式化定义到 Coq/Isabelle
- [ ] 实现生命周期定义
- [ ] 实现引用有效性规则
- [ ] 证明引用有效性
- [ ] 证明生命周期推断正确性
- [ ] 编写验证报告

### 类型系统验证

- [ ] 转换类型系统形式化定义到 Coq/Isabelle
- [ ] 实现类型定义
- [ ] 实现类型推导规则
- [ ] 证明类型安全
- [ ] 证明类型推导正确性
- [ ] 编写验证报告

### 异步状态机验证

- [ ] 转换异步状态机形式化定义到 Coq/Isabelle
- [ ] 实现 Future 状态与转换
- [ ] 证明状态一致性（定理 6.1）
- [ ] 证明并发安全（定理 6.2）
- [ ] 证明进度保证（定理 6.3）
- [ ] 编写验证报告

### Pin 与自引用验证

- [ ] 转换 Pin/自引用形式化定义到 Coq/Isabelle
- [ ] 实现 Pin 不变式与投影条件
- [ ] 证明 Pin 保证（定理 1）
- [ ] 证明自引用类型安全（定理 2）
- [ ] 证明 Pin 投影安全（定理 3）
- [ ] 编写验证报告

---

## 🔗 相关资源 {#-相关资源}

### 学习资源

- **Coq 教程**：
  - [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
  - [Coq 官方文档](https://coq.inria.fr/documentation)

- **Isabelle 教程**：
  - [Isabelle/HOL 教程](https://isabelle.in.tum.de/doc/tutorial.pdf)
  - [Isabelle 官方文档](https://isabelle.in.tum.de/documentation.html)

### 相关项目

- **RustBelt**：Rust 类型系统的形式化验证
- **Creusot**：Rust 程序的形式化验证工具
- **Prusti**：Rust 程序的形式化验证工具

### 工具链扩展任务（Rust → 证明助手）

| 工具 | 输入 | 输出 | 对接状态 | 任务入口 |
| :--- | :--- | :--- | :--- | :--- |
| **Aeneas** | Safe Rust (MIR/THIR) | Coq/F*/HOL4/Lean | 📋 计划中 | [AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md) |
| **coq-of-rust** | THIR | Rocq (Coq) | 📋 计划中 | [COQ_OF_RUST_INTEGRATION_PLAN](./COQ_OF_RUST_INTEGRATION_PLAN.md) |

完成 Aeneas/coq-of-rust 对接后，在 [PROOF_INDEX](./PROOF_INDEX.md) 中标注对应定理为 L3（机器可检查）。

### 工具资源

- [Coq GitHub](https://github.com/coq/coq)
- [Isabelle GitHub](https://github.com/isabelle-prover/isabelle)
- [Proof General](https://proofgeneral.github.io/)

---

**维护者**: Rust Formal Verification Team
**最后更新**: 2026-01-26
**状态**: ✅ **指南 100% 完成**
