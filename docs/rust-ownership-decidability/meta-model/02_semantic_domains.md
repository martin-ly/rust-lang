# Rust 所有权系统元模型 - 语义域

## 1. 概述

本文档定义 Rust 所有权系统的语义域（Semantic Domains），为操作语义和类型系统提供数学基础。

## 2. 基本集合

### 2.1 内存位置 (Locations)

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
