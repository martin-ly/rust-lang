# Sound Borrow-Checking via Symbolic Semantics

> **来源**: POPL 2024 (ACM SIGPLAN Symposium on Principles of Programming Languages)
> **作者**: Son Ho, Aymeric Fromherz, Jonathan Protzenko (Microsoft Research)
> **难度**: 🔴 高级
> **前置知识**: Aeneas, 符号执行, 分离逻辑

---

## 目录

- [Sound Borrow-Checking via Symbolic Semantics](#sound-borrow-checking-via-symbolic-semantics)
  - [目录](#目录)
  - [摘要](#摘要)
  - [1. 引言](#1-引言)
    - [1.1 问题背景](#11-问题背景)
    - [1.2 贡献概述](#12-贡献概述)
  - [2. 符号化语义基础](#2-符号化语义基础)
    - [2.1 符号值](#21-符号值)
    - [2.2 符号化状态](#22-符号化状态)
    - [2.3 路径约束](#23-路径约束)
  - [3. LLBC: Low-Level Borrow Calculus](#3-llbc-low-level-borrow-calculus)
    - [3.1 设计哲学](#31-设计哲学)
    - [3.2 核心构造](#32-核心构造)
    - [3.3 与 MIR 的关系](#33-与-mir-的关系)
  - [4. 符号化执行语义](#4-符号化执行语义)
    - [4.1 小步语义](#41-小步语义)
    - [4.2 Borrow 和 Loan](#42-borrow-和-loan)
    - [4.3 重新组织规则](#43-重新组织规则)
  - [5. HLPL: High-Level Pointer Language](#5-hlpl-high-level-pointer-language)
    - [5.1 中间层设计](#51-中间层设计)
    - [5.2 模拟关系](#52-模拟关系)
  - [6. 形式化验证](#6-形式化验证)
    - [6.1 正确性声明](#61-正确性声明)
    - [6.2 模拟证明](#62-模拟证明)
    - [6.3 组合性](#63-组合性)
  - [7. 工具实现](#7-工具实现)
    - [7.1 Aeneas 集成](#71-aeneas-集成)
    - [7.2 验证流程](#72-验证流程)
  - [参考文献](#参考文献)

---

## 摘要

本文档介绍 POPL 2024 论文 "Sound Borrow-Checking for Rust via Symbolic Semantics" 的核心贡献：

1. **LLBC (Low-Level Borrow Calculus)**：显式表示借用和贷款的中间语言
2. **符号化执行语义**：跟踪符号值和路径约束的操作语义
3. **HLPL (High-Level Pointer Language)**：连接高层抽象和低层实现的桥梁
4. **声音性证明**：通过模拟关系证明借用检查的正确性

该方法已集成到 Aeneas 工具中，支持自动化的 Rust 程序验证。

---

## 1. 引言

### 1.1 问题背景

Rust 的借用检查器在编译期验证内存安全，但其内部工作机制复杂：

```rust
fn example(v: &mut Vec<i32>) {
    v.push(v.len());  // 同时使用 &mut v 和 &v
}
```

这里的两阶段借用涉及复杂的生命周期分析。如何形式化验证借用检查器的正确性？

**现有方法**：

- **RustBelt**：基于 Iris 分离逻辑，手动证明
- **类型系统**：复杂，难以验证优化

### 1.2 贡献概述

**本文献方法**：

1. 将 Rust 翻译为 LLBC（显式借用/贷款）
2. 定义 LLBC 的符号化执行语义
3. 通过 HLPL 连接到低层指针操作
4. 证明模拟关系确保声音性

---

## 2. 符号化语义基础

### 2.1 符号值

符号执行使用符号值代替具体值：

```
符号值 s ::= α | β | γ | ...    (符号常量)
         | n | true | false     (具体值)
         | s₁ + s₂              (符号表达式)
         | f(s₁, ..., sₙ)       (符号函数应用)
```

**示例**：

```rust
// Rust 代码
let x = read_input();
let y = x + 1;

// 符号化表示
x ↦ α      (α 是输入符号)
y ↦ α + 1  (符号表达式)
```

### 2.2 符号化状态

```
符号状态 Σ ::= (M, P, B, L)

M: 内存映射 (Location → SymbolicValue)
P: 路径约束 (PathCondition)
B: 借用集合 (BorrowSet)
L: 贷款集合 (LoanSet)
```

**内存模型**：

```
M := Map<Place, SymbolicValue>

Place ::= x              (局部变量)
       | Place.f        (字段投影)
       | Place[n]       (索引)
```

### 2.3 路径约束

路径约束记录执行路径的条件：

```
路径约束 P ::= true
            | P ∧ e
            | P ∧ ¬e

其中 e 是符号布尔表达式
```

**示例**：

```rust
if x > 0 {
    y = 1;
} else {
    y = 2;
}

// 路径 1: P = (α > 0), y ↦ 1
// 路径 2: P = (α ≤ 0), y ↦ 2
```

---

## 3. LLBC: Low-Level Borrow Calculus

### 3.1 设计哲学

LLBC 的核心思想：**将隐式借用显式化**

Rust 借用是隐式的：

```rust
let x = &mut v;  // 借用 v
*x = 42;         // 使用借用
// 借用隐式结束
```

LLBC 使其显式：

```llbc
borrow_mut x from v;  // 显式创建借用
loan v to x;          // v 被冻结
write x 42;           // 通过借用写入
end_loan x;           // 显式结束借用
```

### 3.2 核心构造

**语法**：

```
值 v ::= n | true | false | () | ptr ℓ | ⊥

表达式 e ::= v
          | x
          | e₁ + e₂
          | &p       (创建共享借用)
          | &mut p   (创建可变借用)
          | *e       (解引用)
          | borrow p (创建 loan)

命令 c ::= skip
        | x := e
        | c₁; c₂
        | if e then c₁ else c₂
        | while e do c
        | start_loan(x, p)   (开始贷款)
        | end_loan(x)        (结束贷款)
        | reborrow(x, y)     (重新借用)

位置 p ::= x | p.f | p[n]
```

**类型**：

```
τ ::= Int | Bool | Unit | &τ | &mut τ | Box<τ>
```

### 3.3 与 MIR 的关系

LLBC 与 Rust 的 MIR (Mid-level IR) 对应：

| MIR 构造 | LLBC 构造 | 说明 |
|----------|-----------|------|
| `_1 = &_2` | `x := &y` | 共享借用 |
| `_1 = &mut _2` | `x := &mut y` | 可变借用 |
| `StorageDead` | `end_loan` | 生命周期结束 |
| `Drop` | 隐式/显式 drop | 析构 |

**关键区别**：LLBC 显式跟踪借用-贷款关系。

---

## 4. 符号化执行语义

### 4.1 小步语义

**配置**：(Γ, Σ, c)

- Γ: 全局上下文（函数定义）
- Σ: 符号状态
- c: 当前命令

**规则示例**：

```
(* 赋值 *)
Γ ⊢ (Σ, x := v) → (Σ[x ↦ v], skip)

(* 条件 - 真分支 *)
Γ ⊢ (Σ, if true then c₁ else c₂) → (Σ, c₁)

(* 条件 - 假分支 *)
Γ ⊢ (Σ, if false then c₁ else c₂) → (Σ, c₂)

(* 条件 - 符号值 *)
Γ ⊢ ((M, P, B, L), if s then c₁ else c₂)
  → 分支 1: ((M, P ∧ s, B, L), c₁)
     分支 2: ((M, P ∧ ¬s, B, L), c₂)
```

### 4.2 Borrow 和 Loan

**创建可变借用**：

```
(* &mut p *)
Σ(p) = loc(ℓ, v)     (* p 指向位置 ℓ，值为 v *)
fresh α              (* 新符号值 *)
fresh β              (* 新借用标签 *)
─────────────────────────────────────────
Γ ⊢ (Σ, x := &mut p) → (Σ', skip)

其中 Σ' = Σ[  x ↦ ptr(ℓ, β, Mutable),
              p ↦ loan(ℓ, β, x, v),  (* p 被冻结 *)
              B ↦ B ∪ {(β, Mutable, ℓ)},
              L ↦ L ∪ {(ℓ, β, x)} ]
```

**创建共享借用**：

```
(* &p *)
Σ(p) = loc(ℓ, v)
fresh β
─────────────────────────────────────────
Γ ⊢ (Σ, x := &p) → (Σ', skip)

其中 Σ' = Σ[  x ↦ ptr(ℓ, β, Shared),
              p ↦ loan(ℓ, β, x, v),
              B ↦ B ∪ {(β, Shared, ℓ)},
              L ↦ L ∪ {(ℓ, β, x)} ]
```

**使用借用**：

```
(* 读取 *)
Σ(x) = ptr(ℓ, β, perm)
(β, perm, ℓ) ∈ B    (* 借用有效 *)
─────────────────────────────────────────
Γ ⊢ (Σ, y := *x) → (Σ[y ↦ M(ℓ)], skip)

(* 写入 - 可变借用 *)
Σ(x) = ptr(ℓ, β, Mutable)
(β, Mutable, ℓ) ∈ B
─────────────────────────────────────────
Γ ⊢ (Σ, *x := v) → (Σ[M(ℓ) ↦ v], skip)
```

### 4.3 重新组织规则

LLBC 允许状态重组以模拟 Rust 的自动行为：

```
(* Reorg-End-Loan: 结束贷款，恢复原始值 *)
(ℓ, β, x, v) ∈ L    (* x 对 ℓ 的贷款 *)
Σ(x) = ⊥            (* x 不再使用 *)
─────────────────────────────────────────
Σ ⇒ Σ[  p ↦ loc(ℓ, v),  (* 恢复原始位置 *)
        L ↦ L \\ {(ℓ, β, x, v)},
        B ↦ B \\ {(β, _, ℓ)} ]

(* Reorg-End-Pointer: 结束指针，合并值 *)
Σ(x) = ptr(ℓ, β, _)
(ℓ, β, y, v) ∈ L    (* y 是贷款者 *)
─────────────────────────────────────────
Σ ⇒ Σ[  y ↦ loc(ℓ, v'),  (* 更新贷款值 *)
        x ↦ ⊥ ]
```

**重组的非确定性**：

- 重组可以在任何时间发生
- 不同的重组选择可能导致不同结果
- 某些选择可能导致 stuck（模拟 UB）

---

## 5. HLPL: High-Level Pointer Language

### 5.1 中间层设计

HLPL 作为 LLBC 和底层指针操作之间的中间层：

```
Rust ──▶ MIR ──▶ LLBC ──▶ HLPL ──▶ PL (Pointer Language)
                          ↑
                          └── 本文献焦点
```

**HLPL 特性**：

- 没有显式的 borrow/loan
- 保留抽象指针概念
- 值与位置分离

**HLPL 状态**：

```
Σ_H ::= (M, P)

M: Map<Place, Value>
Value ::= n | true | ptr(ℓ) | loc(ℓ, v)
```

### 5.2 模拟关系

**目标**：证明 LLBC 和 HLPL 之间的模拟关系

```
模拟关系 R ⊆ State_LLBC × State_HLPL

R(Σ_L, Σ_H) 当且仅当：
1. 路径约束等价
2. 内存内容一致（考虑 loan）
3. 借用关系保持
```

**引理 (HLPL → PL)**：

HLPL 到 PL（底层指针语言）的模拟是标准的：

- 将 `ptr ℓ` 映射到具体地址
- 将 `loc ℓ v` 映射到堆内存

**定理 (LLBC → PL)**：

通过 HLPL 的传递性：

```
LLBC ↝ HLPL ↝ PL

如果 LLBC 程序是 well-typed，则其在 PL 中的执行是安全的。
```

---

## 6. 形式化验证

### 6.1 正确性声明

**定理 (借用检查声音性)**：

对于所有 Rust 程序 P：

```
如果 rustc 接受 P（通过借用检查），
则 P 在 LLBC 语义下不会导致 UB。
```

**更强的声明**（部分函数正确性）：

```
如果 P 通过借用检查，
则对于所有输入，P 的 LLBC 执行不会 stuck。
```

### 6.2 模拟证明

**引理 (前向模拟)**：

```
∀ Σ₁, Σ₁', Σ₂.
  R(Σ₁, Σ₂) ∧ Σ₁ → Σ₁'
  ⇒ ∃ Σ₂'. Σ₂ →* Σ₂' ∧ R(Σ₁', Σ₂')
```

**证明策略**：

1. 对 LLBC 求值规则归纳
2. 对每个规则，构造对应的 HLPL 执行序列
3. 保持模拟关系

**引理 (后向模拟)**：

类似地证明 HLPL 到 LLBC 的反向关系。

### 6.3 组合性

**模块验证**：

```
如果模块 A 和 B 分别验证通过，
则 A ∘ B（组合）也验证通过。
```

这是通过分离逻辑的 frame rule 实现的。

---

## 7. 工具实现

### 7.1 Aeneas 集成

符号化执行语义已集成到 Aeneas：

```
Aeneas 流程：

1. Rust 源码
   ↓ (rustc)
2. MIR
   ↓ (Aeneas 前端)
3. LLBC
   ↓ (符号化执行)
4. 符号化状态序列
   ↓ (翻译成后端)
5. Coq / HOL4 / F* 代码
```

### 7.2 验证流程

**使用 Aeneas 验证 Rust 程序**：

```bash
# 安装 Aeneas
cargo install aeneas

# 验证程序
aeneas verify --backend coq program.rs

# 生成 Coq 证明目标
coq_makefile -f _CoqProject -o Makefile
make
```

**示例**：

```rust
// Rust 程序
fn sum(v: &[i32]) -> i32 {
    let mut s = 0;
    for x in v {
        s += x;
    }
    s
}
```

```coq
(* 生成的 Coq 规范 *)
Theorem sum_correct :
  forall (v: list i32),
  sum v = fold_left Int.add v 0.
Proof.
  (* Aeneas 自动生成证明 *)
Qed.
```

---

## 参考文献

1. **Ho, S., Fromherz, A., & Protzenko, J.** (2024). Sound Borrow-Checking for Rust via Symbolic Semantics. *POPL '24*.

2. **Ho, S., & Protzenko, J.** (2022). Aeneas: Rust Verification by Functional Translation. *POPL '22*.

3. **Jung, R., et al.** (2018). RustBelt: Securing the foundations of Rust. *POPL '18*.

4. **Matsushita, Y., et al.** (2022). RustHornBelt: A semantic foundation for functional verification of Rust programs with unsafe code. *PLDI '22*.

5. **King, J. C.** (1976). Symbolic execution and program testing. *Communications of the ACM*.

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
*状态: 完成*
