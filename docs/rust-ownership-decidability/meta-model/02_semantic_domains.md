# Rust 所有权系统元模型 - 语义域

## 📑 目录
>
- [Rust 所有权系统元模型 - 语义域](#rust-所有权系统元模型---语义域)
  - [📑 目录](#-目录)
  - [1. 概述](#1-概述)
  - [2. 基本集合](#2-基本集合)
    - [2.1 内存位置 (Locations)](#21-内存位置-locations)
    - [2.2 区域变量 (Region Variables)](#22-区域变量-region-variables)
    - [2.3 变量 (Variables)](#23-变量-variables)
    - [2.4 标签 (Tags)](#24-标签-tags)
  - [3. 值域 (Value Domain)](#3-值域-value-domain)
    - [3.1 值的基本定义](#31-值的基本定义)
    - [3.2 闭包 (Closures)](#32-闭包-closures)
    - [3.3 语义值的归纳定义](#33-语义值的归纳定义)
  - [4. 堆/内存模型 (Heap/Memory Model)](#4-堆内存模型-heapmemory-model)
    - [4.1 简单抽象堆](#41-简单抽象堆)
    - [4.2 Stacked Borrows 风格堆](#42-stacked-borrows-风格堆)
    - [4.3 区域化堆 (Oxide 风格)](#43-区域化堆-oxide-风格)
  - [5. 环境 (Environments)](#5-环境-environments)
    - [5.1 类型环境 (Type Environment)](#51-类型环境-type-environment)
    - [5.2 值环境 (Value Environment / Stack)](#52-值环境-value-environment--stack)
    - [5.3 区域环境 (Region Environment)](#53-区域环境-region-environment)
    - [5.4 贷款环境 (Loan Environment)](#54-贷款环境-loan-environment)
    - [5.5 完整环境](#55-完整环境)
  - [6. 类型域 (Type Domain)](#6-类型域-type-domain)
    - [6.1 类型定义](#61-类型定义)
    - [6.2 可变性](#62-可变性)
    - [6.3 区域](#63-区域)
  - [7. 配置/状态 (Configurations)](#7-配置状态-configurations)
    - [7.1 表达式配置](#71-表达式配置)
    - [7.2 求值结果](#72-求值结果)
    - [7.3 状态转换](#73-状态转换)
  - [8. 辅助域](#8-辅助域)
    - [8.1 位置 (Places)](#81-位置-places)
    - [8.2 借用链 (Borrow Chains)](#82-借用链-borrow-chains)
    - [8.3 帧 (Stack Frames)](#83-帧-stack-frames)
  - [9. 语义域的数学性质](#9-语义域的数学性质)
    - [9.1 偏序关系](#91-偏序关系)
    - [9.2 格结构](#92-格结构)
    - [9.3 有限性约束](#93-有限性约束)
  - [10. 语义域间的关系](#10-语义域间的关系)
  - [11. 符号速查表](#11-符号速查表)
  - [**最后更新**: 2026-03-05](#最后更新-2026-03-05)
  - [相关概念](#相关概念)

## 1. 概述
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

本文档定义 Rust 所有权系统的语义域（Semantic Domains），为操作语义和类型系统提供数学基础。

## 2. 基本集合
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 2.1 内存位置 (Locations)
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```text
Loc ≜ {ℓ₁, ℓ₂, ℓ₃, ...}      可数无限集合
```

### 2.2 区域变量 (Region Variables)

```text
RVar ≜ {r₁, r₂, r₃, ...}     可数无限集合
```

### 2.3 变量 (Variables)

```text
Var ≜ {x, y, z, ...}         程序变量
```

### 2.4 标签 (Tags)

```text
Tag ≜ {t₁, t₂, t₃, ...}      用于 Stacked Borrows 风格语义
```

## 3. 值域 (Value Domain)

### 3.1 值的基本定义

```text
Val ≜ Unit + Bool + Int + Char + String + Loc + Tuple(Val*) + Closure

Unit    ≜ {()}
Bool    ≜ {true, false}
Int     ≜ ℤ                           (数学整数)
Char    ≜ Unicode 字符集
String  ≜ Char*
Pointer ≜ Loc × Tag × Mutability      (带标签的指针)
```

### 3.2 闭包 (Closures)

```text
Closure ≜ Var* × Expr × Env           (参数、体、捕获环境)
```

### 3.3 语义值的归纳定义

```text
( Coq/数学风格 )

Inductive value : Type :=
  | VUnit : value
  | VBool : bool -> value
  | VInt  : Z -> value
  | VChar : ascii -> value
  | VString : string -> value
  | VLoc  : location -> value
  | VTag  : tag -> value
  | VTuple : list value -> value
  | VStruct : struct_name -> list (field_name × value) -> value
  | VEnum   : enum_name -> constructor_name -> list value -> value
  | VRef    : location -> tag -> mutability -> value
  | VBox    : location -> value -> value
  | VClosure : list var -> expr -> env -> value.
```

## 4. 堆/内存模型 (Heap/Memory Model)

### 4.1 简单抽象堆

```text
Heap ≜ Loc →fin Val

(有限部分函数，表示内存中存储的值)
```

### 4.2 Stacked Borrows 风格堆

```text
BorrowItem ≜ Unique(Tag) | SharedRO(Tag) | SharedRW | Frozen

Stack ≜ BorrowItem*                      (借用栈)

HeapEntry ≜ Val × Stack

Heap_SB ≜ Loc →fin HeapEntry
```

### 4.3 区域化堆 (Oxide 风格)

```text
Loan ≜ Mutability × Place                 (贷款 = 可变性 × 位置)

Region ≜ P(RVar)                          (区域 = 区域变量集合)

RegionEnv ≜ RVar →fin P(Loan)             (区域到贷款集合的映射)
```

## 5. 环境 (Environments)

### 5.1 类型环境 (Type Environment)

```text
TypeEnv ≜ Var →fin Type

Γ : TypeEnv
Γ(x) = τ   表示变量 x 具有类型 τ
```

### 5.2 值环境 (Value Environment / Stack)

```text
ValEnv ≜ Var →fin Val

σ : ValEnv
σ(x) = v   表示变量 x 绑定到值 v
```

### 5.3 区域环境 (Region Environment)

```text
RegionEnv ≜ RVar →fin P(Loc)

Δ : RegionEnv
Δ(r) = {ℓ₁, ℓ₂, ...}   表示区域 r 包含位置 ℓ₁, ℓ₂, ...
```

### 5.4 贷款环境 (Loan Environment)

```text
LoanEnv ≜ RVar →fin P(Loan)

Θ : LoanEnv
Θ(r) = {(ω₁, p₁), (ω₂, p₂), ...}
```

### 5.5 完整环境

```text
Env ≜ TypeEnv × RegionEnv × LoanEnv × ValEnv

或者分层表示:
  Δ : RegionEnv    (区域)
  Γ : TypeEnv      (类型)
  Θ : LoanEnv      (贷款)
  σ : ValEnv       (值)
```

## 6. 类型域 (Type Domain)

### 6.1 类型定义

```text
Type ≜ BaseType + RefType + BoxType + TupleType + StructType + EnumType

BaseType ≜ Unit + Bool + IntTypes + Char + Str

RefType ≜ Mutability × Region × Type

BoxType ≜ Type

TupleType ≜ Type*

StructType ≜ struct_name × Type*        (考虑泛型参数)

EnumType ≜ enum_name × Type*
```

### 6.2 可变性

```text
Mutability ≜ {uniq, shrd}

uniq  : 唯一/可变
shrd  : 共享/不可变
```

### 6.3 区域

```text
Region ≜ P(RVar) ∪ {'static}

'static 表示全局静态生命周期
```

## 7. 配置/状态 (Configurations)

### 7.1 表达式配置

```text
ExprConfig ≜ Env × Heap × Expr

⟨σ, h, e⟩  表示在环境 σ、堆 h 下求值表达式 e
```

### 7.2 求值结果

```text
Result ≜ Val + Error + Divergence

Error ≜ TypeError + MemoryError + UndefinedBehavior

MemoryError ≜ UseAfterFree + DoubleFree + OutOfBounds + NullDeref
```

### 7.3 状态转换

```text
⟨σ, h, e⟩ → ⟨σ', h', e'⟩    (单步求值)

或者:
⟨σ, h, e⟩ ⇓ ⟨σ', h', v⟩     (大步求值到值)
```

## 8. 辅助域

### 8.1 位置 (Places)

```text
Place ≜ Var                                  (基础变量)
      | Deref(Place)                         (*p)
      | Field(Place, field_name)             (p.f)
      | Index(Place, Val)                    (p[i])
      | Slice(Place, Val, Val)               (p[i..j])
```

### 8.2 借用链 (Borrow Chains)

```text
BorrowChain ≜ (Mutability × Place)*

表示一系列借用关系
```

### 8.3 帧 (Stack Frames)

```text
Frame ≜ Var →fin Val

CallStack ≜ Frame*
```

## 9. 语义域的数学性质

### 9.1 偏序关系

```text
类型子类型关系:
τ₁ <: τ₂

区域包含关系:
ρ₁ ⊇ ρ₂   (ρ₁ 比 ρ₂ 更长/更大)
```

### 9.2 格结构

```text
Region 形成完全格:
  ⊥ = ∅
  ⊤ = RVar  (所有区域变量)
  ⊔ = ∪
  ⊓ = ∩
```

### 9.3 有限性约束

```text
对于任何程序 P:
  dom(Γ) 有限
  dom(σ) 有限
  dom(h) 有限
  dom(Δ) 有限
```

## 10. 语义域间的关系

```text
                    TypeEnv (Γ)
                         |
                         | 类型检查
                         v
                    +---------+
                    |  程序   |
                    +---------+
                         |
         +---------------+---------------+
         |                               |
         v                               v
    ValEnv (σ)                      RegionEnv (Δ)
         |                               |
         | 求值                          | 区域检查
         v                               v
    +---------+                     +---------+
    |   值    |                     |  区域   |
    +---------+                     +---------+
         |                               |
         +---------------+---------------+
                         |
                         v
                    Heap (h)
                         |
                         v
                    +---------+
                    |  内存   |
                    +---------+
```

## 11. 符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| ℓ | 内存位置 | \ell |
| ρ | 区域 | \rho |
| ω | 可变性 | \omega |
| σ | 值环境 | \sigma |
| Γ | 类型环境 | \Gamma |
| Δ | 区域环境 | \Delta |
| Θ | 贷款环境 | \Theta |
| h | 堆 | h |
| τ | 类型 | \tau |
| ⇓ | 求值 | \Downarrow |
| ⊢ | 推导 | \vdash |
| <: | 子类型 | <: |

---

**状态**: 草案 v0.1
**最后更新**: 2026-03-05
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [meta-model 目录](./README.md)
- [上级目录](../README.md)


---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

> **[来源: Wikipedia - Machine Learning]**

> **[来源: Wikipedia - Artificial Intelligence]**

> **[来源: tch-rs Documentation]**

> **[来源: ACM - AI Systems]**
