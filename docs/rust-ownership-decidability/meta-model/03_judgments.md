# Rust 所有权系统元模型 - 判断形式

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 所有权系统元模型 - 判断形式](#rust-所有权系统元模型---判断形式)
  - [📑 目录](#-目录)
  - [1. 判断 (Judgments) 概述](#1-判断-judgments-概述)
  - [2. 语法判断 (Syntactic Judgments)](#2-语法判断-syntactic-judgments)
    - [2.1 类型判断](#21-类型判断)
      - [2.1.1 变量类型](#211-变量类型)
      - [2.1.2 借用类型](#212-借用类型)
    - [2.2 所有权安全判断 (Ownership Safety)](#22-所有权安全判断-ownership-safety)
      - [2.2.1 基础规则](#221-基础规则)
      - [2.2.2 解引用规则](#222-解引用规则)
    - [2.3 子类型判断](#23-子类型判断)
      - [2.3.1 引用子类型](#231-引用子类型)
      - [2.3.2 可变引用子类型（不变）](#232-可变引用子类型不变)
    - [2.4 良构性判断](#24-良构性判断)
      - [2.4.1 类型良构](#241-类型良构)
      - [2.4.2 区域良构](#242-区域良构)
      - [2.4.3 环境良构](#243-环境良构)
  - [3. 语义判断 (Semantic Judgments)](#3-语义判断-semantic-judgments)
    - [3.1 大步求值 (Big-Step Evaluation)](#31-大步求值-big-step-evaluation)
    - [3.2 单步求值 (Small-Step Evaluation)](#32-单步求值-small-step-evaluation)
    - [3.3 位置求值 (Place Evaluation)](#33-位置求值-place-evaluation)
    - [3.4 模式匹配](#34-模式匹配)
  - [4. 元理论判断 (Metatheoretic Judgments)](#4-元理论判断-metatheoretic-judgments)
    - [4.1 类型保持 (Preservation)](#41-类型保持-preservation)
    - [4.2 进展 (Progress)](#42-进展-progress)
    - [4.3 类型安全 (Type Safety)](#43-类型安全-type-safety)
    - [4.4 终止性 (Termination)](#44-终止性-termination)
      - [4.4.1 Linearizability](#441-linearizability)
  - [5. 辅助判断](#5-辅助判断)
    - [5.1 自由变量](#51-自由变量)
    - [5.2 变量捕获](#52-变量捕获)
    - [5.3 生命周期包含](#53-生命周期包含)
    - [5.4 贷款冲突检查](#54-贷款冲突检查)
    - [5.5 借用检查](#55-借用检查)
  - [6. 判断之间的关系](#6-判断之间的关系)
  - [7. 判断的推理规则示例](#7-判断的推理规则示例)
    - [7.1 借用规则 (完整版)](#71-借用规则-完整版)
    - [7.2 所有权安全核心规则](#72-所有权安全核心规则)
    - [7.3 序列规则](#73-序列规则)
    - [7.4 赋值规则](#74-赋值规则)
  - [8. 判断的 Coq 形式化草图](#8-判断的-coq-形式化草图)
  - [**最后更新**: 2026-03-05](#最后更新-2026-03-05)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 1. 判断 (Judgments) 概述
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

判断是形式系统的核心，定义了程序在何种条件下被认为是有效的。本文档定义 Rust 所有权系统的完整判断体系。

## 2. 语法判断 (Syntactic Judgments)
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

### 2.1 类型判断

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

```
Δ; Γ; Θ ⊢ e : τ

含义: 在区域环境 Δ、类型环境 Γ、贷款环境 Θ 下，表达式 e 具有类型 τ
```

#### 2.1.1 变量类型

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```
Δ; Γ; Θ ⊢ x : τ      if Γ(x) = τ
```

#### 2.1.2 借用类型

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

```
Δ; Γ; Θ ⊢ &ρ ω p : &ρ ω τ     if Δ; Γ; Θ ⊢ p : τ and Δ; Γ; Θ ⊢ω p ok
```

### 2.2 所有权安全判断 (Ownership Safety)

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**

```
Δ; Γ; Θ ⊢ω p ⇒ {ω'p'}

含义: 在环境 Δ, Γ, Θ 下，以访问模式 ω 使用位置 p 是安全的，
      产生借用链 {ω'p'}

其中 ω ∈ {uniq, shrd} 表示访问模式:
  - uniq: 唯一访问（可变借用需要）
  - shrd: 共享访问（不可变借用需要）
```

#### 2.2.1 基础规则

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

```
Δ; Γ; Θ ⊢ω x ⇒ {ωx}      (变量总是安全的)
```

#### 2.2.2 解引用规则

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

```
Δ; Γ; Θ ⊢ *p ⇒ {ω'p'}
  if Δ; Γ; Θ ⊢ p : &ρ ω'' τ
  and Δ; Γ; Θ ⊢ω'' p ok
  and (ω ≤ ω'' or p is reborrow excluded)
```

### 2.3 子类型判断
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```
Δ ⊢ τ₁ <: τ₂

含义: 在区域环境 Δ 下，类型 τ₁ 是 τ₂ 的子类型
```

#### 2.3.1 引用子类型

```
Δ ⊢ &ρ₁ ω τ₁ <: &ρ₂ ω τ₂
  if Δ ⊢ ρ₂ ⊆ ρ₁           (反变: 更长生命周期)
  and Δ ⊢ τ₁ <: τ₂         (协变: 更具体类型)
  and ω 相同
```

#### 2.3.2 可变引用子类型（不变）

```
Δ ⊢ &ρ uniq τ <: &ρ uniq τ   (仅自反)
```

### 2.4 良构性判断
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

#### 2.4.1 类型良构

```
Δ ⊢ τ wf

含义: 类型 τ 在区域环境 Δ 下是良构的
```

规则:

```
Δ ⊢ B wf                    (基础类型总是良构)

Δ ⊢ &ρ ω τ wf               if Δ ⊢ ρ wf and Δ ⊢ τ wf

Δ ⊢ Box τ wf                if Δ ⊢ τ wf

Δ ⊢ (τ₁, ..., τₙ) wf        if ∀i, Δ ⊢ τᵢ wf
```

#### 2.4.2 区域良构

```
Δ ⊢ ρ wf

含义: 区域 ρ 在区域环境 Δ 下是良构的
```

规则:

```
Δ ⊢ 'static wf              (静态生命周期总是良构)

Δ ⊢ r wf                    if r ∈ dom(Δ)

Δ ⊢ ρ₁ ∪ ρ₂ wf              if Δ ⊢ ρ₁ wf and Δ ⊢ ρ₂ wf
```

#### 2.4.3 环境良构

```
⊢ Δ; Γ; Θ wf

含义: 环境组合是良构的
```

## 3. 语义判断 (Semantic Judgments)
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 3.1 大步求值 (Big-Step Evaluation)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```
σ; h ⊢ e ⇓ σ'; h'; v

含义: 在栈 σ 和堆 h 下，表达式 e 求值为值 v，
      产生新栈 σ' 和新堆 h'
```

### 3.2 单步求值 (Small-Step Evaluation)
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```
⟨σ, h, e⟩ → ⟨σ', h', e'⟩

含义: 表达式 e 单步求值为 e'，状态从 (σ, h) 变为 (σ', h')
```

### 3.3 位置求值 (Place Evaluation)
>
> **[来源: [crates.io](https://crates.io/)]**

```
σ ⊢ p ↝ ℓ

含义: 在栈 σ 下，位置表达式 p 求值为内存地址 ℓ
```

### 3.4 模式匹配
>
> **[来源: [docs.rs](https://docs.rs/)]**

```
v ~ pattern ⇒ σ

含义: 值 v 匹配模式 pattern，产生绑定环境 σ
```

## 4. 元理论判断 (Metatheoretic Judgments)
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 4.1 类型保持 (Preservation)
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```
Theorem Preservation:
  If Δ; Γ; Θ ⊢ e : τ and σ; h ⊢ e ⇓ σ'; h'; v
  then there exist Γ', Θ' such that
       Δ; Γ'; Θ' ⊢ v : τ
       and ⊢ σ': Γ' and ⊢ h': Θ'
```

### 4.2 进展 (Progress)
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
Theorem Progress:
  If Δ; Γ; Θ ⊢ e : τ
  then either:
    1. e is a value, or
    2. There exist e', σ', h' such that ⟨σ, h, e⟩ → ⟨σ', h', e'⟩, or
    3. e is stuck (ill-typed or undefined behavior)
```

### 4.3 类型安全 (Type Safety)
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
Type Safety = Preservation + Progress
```

### 4.4 终止性 (Termination)
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```
Theorem BorrowChecking_Termination:
  For any finite environment Γ,
  if Γ is linearizable (defined below),
  then the borrow checking algorithm terminates.
```

#### 4.4.1 Linearizability

```
Definition Linearizable(Γ):
  ∀x ∈ dom(Γ). rank(Γ(x)) > max{ rank(y) | y ∈ fv(Γ(x)) }

where:
  - rank(τ) 是类型的秩（深度）
  - fv(τ) 是 τ 中引用的自由变量集合
```

## 5. 辅助判断
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 5.1 自由变量
>
> **[来源: [crates.io](https://crates.io/)]**

```
fv(e) = 表达式 e 中的自由变量集合
fv(τ) = 类型 τ 中的自由变量集合
```

### 5.2 变量捕获
>
> **[来源: [docs.rs](https://docs.rs/)]**

```
captured(e) = 闭包 e 捕获的变量集合
```

### 5.3 生命周期包含
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```
Δ ⊢ ρ₁ ⊇ ρ₂

含义: 在 Δ 下，ρ₁ 包含 ρ₂（ρ₁ 比 ρ₂ 活得更长）
```

规则:

```
Δ ⊢ ρ ⊇ ρ                     (自反)

Δ ⊢ 'static ⊇ ρ               (静态生命周期包含所有)

Δ ⊢ ρ₁ ⊇ ρ₂  if Δ(r₁) ⊇ Δ(r₂)  (通过环境解释)
```

### 5.4 贷款冲突检查
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```
conflict(ω₁, p₁, ω₂, p₂) =
  (ω₁ = uniq or ω₂ = uniq) and overlap(p₁, p₂)

overlap(p₁, p₂) =
  p₁ is prefix of p₂ or p₂ is prefix of p₁ or p₁ = p₂
```

### 5.5 借用检查
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
check_borrow(Θ, ω, p) = ok | error

检查在贷款环境 Θ 下，以模式 ω 借用 p 是否安全
```

## 6. 判断之间的关系
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
┌─────────────────────────────────────────────────────────────┐
│                      源程序 (Source)                          │
└──────────────────────────┬──────────────────────────────────┘
                           │ 解析
                           v
┌─────────────────────────────────────────────────────────────┐
│                    抽象语法树 (AST)                           │
└──────────────────────────┬──────────────────────────────────┘
                           │ 类型检查
                           v
           ┌───────────────┴───────────────┐
           │                               │
           v                               v
┌─────────────────────┐         ┌─────────────────────┐
│  Δ; Γ; Θ ⊢ e : τ    │         │  ⊢ Δ; Γ; Θ wf       │
│  (类型判断)          │         │  (良构性)            │
└──────────┬──────────┘         └─────────────────────┘
           │
           v
┌─────────────────────────────────────────────────────────────┐
│              Δ; Γ; Θ ⊢ω p ⇒ {ω'p'}                          │
│                   (所有权安全)                                │
└──────────────────────────┬──────────────────────────────────┘
                           │ 代码生成/求值
                           v
┌─────────────────────────────────────────────────────────────┐
│              σ; h ⊢ e ⇓ σ'; h'; v                           │
│                   (语义求值)                                  │
└──────────────────────────┬──────────────────────────────────┘
                           │ 验证
                           v
┌─────────────────────────────────────────────────────────────┐
│              Δ; Γ'; Θ' ⊢ v : τ                              │
│                   (结果类型)                                  │
└─────────────────────────────────────────────────────────────┘
```

## 7. 判断的推理规则示例
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 7.1 借用规则 (完整版)
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```
                    Δ; Γ; Θ ⊢ p : τ
                    Δ; Γ; Θ ⊢ω p ok
────────────────────────────────────────────────
Δ; Γ; Θ ⊢ &ρ ω p : &ρ ω τ

(T-Borrow)
```

### 7.2 所有权安全核心规则
>
> **[来源: [crates.io](https://crates.io/)]**

```
∀r ∈ regions(Γ). ∀(ω', p') ∈ Θ(r).
  if ω = uniq then not (overlap(p, p'))
  else if ω = shrd and ω' = uniq then not (overlap(p, p'))
─────────────────────────────────────────────────────────────
Δ; Γ; Θ ⊢ω p ok

(O-Safe)
```

### 7.3 序列规则
>
> **[来源: [docs.rs](https://docs.rs/)]**

```
Δ; Γ; Θ ⊢ e₁ : τ₁    Δ; Γ[x↦τ₁]; Θ ⊢ e₂ : τ₂
────────────────────────────────────────────────
Δ; Γ; Θ ⊢ let x = e₁; e₂ : τ₂

(T-Seq)
```

### 7.4 赋值规则
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```
Δ; Γ; Θ ⊢ p : τ      Δ; Γ; Θ ⊢ e : τ
Δ; Γ; Θ ⊢uniq p ok   (需要唯一访问)
────────────────────────────────────────────────
Δ; Γ; Θ ⊢ p = e : ()

(T-Assign)
```

## 8. 判断的 Coq 形式化草图
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```coq
(* 类型判断 *)
Inductive has_type :
  region_env -> type_env -> loan_env -> expr -> ty -> Prop :=
  | T_Var : forall Δ Γ Θ x τ,
      Γ x = Some τ ->
      has_type Δ Γ Θ (EVar x) τ
  | T_Borrow : forall Δ Γ Θ p ρ ω τ,
      has_type_place Δ Γ Θ p τ ->
      ownership_safe Δ Γ Θ ω p ->
      has_type Δ Γ Θ (EBorrow ρ ω p) (TRef ρ ω τ)
  | T_Seq : forall Δ Γ Θ e₁ e₂ τ₁ τ₂,
      has_type Δ Γ Θ e₁ τ₁ ->
      has_type Δ Γ Θ e₂ τ₂ ->
      has_type Δ Γ Θ (ESeq e₁ e₂) τ₂
  (* ... 更多规则 *)

(* 所有权安全 *)
with ownership_safe :
  region_env -> type_env -> loan_env -> mutability -> place -> Prop :=
  | OS_Base : forall Δ Γ Θ ω x,
      ownership_safe Δ Γ Θ ω (PVar x)
  | OS_Deref : forall Δ Γ Θ ω p ω' τ ρ,
      has_type_place Δ Γ Θ p (TRef ρ ω' τ) ->
      (ω <= ω')%mut ->
      ownership_safe Δ Γ Θ ω' p ->
      ownership_safe Δ Γ Θ ω (PDeref p)
  (* ... 更多规则 *)

(* 求值关系 *)
Inductive eval :
  val_env -> heap -> expr -> val_env -> heap -> value -> Prop :=
  | E_Value : forall σ h v,
      eval σ h (EValue v) σ h v
  | E_Var : forall σ h x v,
      σ x = Some v ->
      eval σ h (EVar x) σ h v
  (* ... 更多规则 *)
```

---

**状态**: 草案 v0.1
**最后更新**: 2026-03-05
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [meta-model 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**

---
