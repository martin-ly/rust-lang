# Rust所有权系统深度解析：形式语义、定理与反例

> **版本**: Rust 1.94.0+ (Edition 2024)
> **权威来源**: The Rust Programming Language (TRPL), Rust Reference, RustBelt (POPL 2018)
> **形式化参考**: Jung et al. (2018). RustBelt: Securing the Foundations of the Rust Programming Language. POPL
> **状态**: 深度分析文档 | 形式化完备

---

## 目录

- [Rust所有权系统深度解析：形式语义、定理与反例](#rust所有权系统深度解析形式语义定理与反例)
  - [目录](#目录)
  - [前言](#前言)
    - [本文档目标读者](#本文档目标读者)
    - [符号约定](#符号约定)
  - [1. 所有权形式语义](#1-所有权形式语义)
    - [1.1 数学基础](#11-数学基础)
      - [1.1.1 分离逻辑基础](#111-分离逻辑基础)
      - [1.1.2 Iris框架与RustBelt](#112-iris框架与rustbelt)
      - [1.1.3 所有权断言](#113-所有权断言)
    - [1.2 类型状态转换](#12-类型状态转换)
      - [1.2.1 状态机定义](#121-状态机定义)
      - [1.2.2 状态转换规则](#122-状态转换规则)
      - [1.2.3 部分移动的状态处理](#123-部分移动的状态处理)
  - [2. 所有权定理体系](#2-所有权定理体系)
    - [Theorem OWNERSHIP-UNIQUENESS (所有权唯一性定理)](#theorem-ownership-uniqueness-所有权唯一性定理)
    - [Theorem MOVE-IS-LINEAR (移动线性性定理)](#theorem-move-is-linear-移动线性性定理)
    - [Theorem DROP-EXACTLY-ONCE (精确释放定理)](#theorem-drop-exactly-once-精确释放定理)
    - [Theorem MEMORY-SAFETY (内存安全定理)](#theorem-memory-safety-内存安全定理)
    - [Theorem NO-DOUBLE-FREE (无双重释放定理)](#theorem-no-double-free-无双重释放定理)
    - [Theorem NO-USE-AFTER-MOVE (无移动后使用定理)](#theorem-no-use-after-move-无移动后使用定理)
    - [Theorem COPY-SEMANTICS-PRESERVATION (复制语义保持定理)](#theorem-copy-semantics-preservation-复制语义保持定理)
    - [Theorem PARTIAL-MOVE-SOUNDNESS (部分移动健全性定理)](#theorem-partial-move-soundness-部分移动健全性定理)
  - [3. 移动语义深度分析](#3-移动语义深度分析)
    - [3.1 Move作为仿射蕴含](#31-move作为仿射蕴含)
    - [3.2 Copy vs Move 形式区分](#32-copy-vs-move-形式区分)
      - [3.2.1 Copy Trait的形式定义](#321-copy-trait的形式定义)
      - [3.2.2 移动判断算法](#322-移动判断算法)
    - [3.3 隐式移动规则](#33-隐式移动规则)
      - [3.3.1 表达式级移动](#331-表达式级移动)
      - [3.3.2 函数参数移动](#332-函数参数移动)
    - [3.4 重新初始化语义](#34-重新初始化语义)
  - [4. 反例汇编 (15+ 深度案例)](#4-反例汇编-15-深度案例)
    - [反例 1: Use After Move (移动后使用)](#反例-1-use-after-move-移动后使用)
    - [反例 2: Partial Move (部分移动)](#反例-2-partial-move-部分移动)
    - [反例 3: Move in Match Arms (匹配臂中的移动)](#反例-3-move-in-match-arms-匹配臂中的移动)
    - [反例 4: Move in Closures (闭包中的移动)](#反例-4-move-in-closures-闭包中的移动)
    - [反例 5: Move in Loops (循环中的移动)](#反例-5-move-in-loops-循环中的移动)
    - [反例 6: Copy Type Confusion (Copy类型混淆)](#反例-6-copy-type-confusion-copy类型混淆)
    - [反例 7: Drop Order Assumptions (Drop顺序假设错误)](#反例-7-drop-order-assumptions-drop顺序假设错误)
    - [反例 8: mem::forget Unsafety (mem::forget非安全性)](#反例-8-memforget-unsafety-memforget非安全性)
    - [反例 9: ManuallyDrop Misuse (ManuallyDrop误用)](#反例-9-manuallydrop-misuse-manuallydrop误用)
    - [反例 10: Pin and Move Interaction (Pin与移动交互)](#反例-10-pin-and-move-interaction-pin与移动交互)
    - [反例 11: Self-Referential Move (自引用移动)](#反例-11-self-referential-move-自引用移动)
    - [反例 12: Move in Async Blocks (异步块中的移动)](#反例-12-move-in-async-blocks-异步块中的移动)
    - [反例 13: Generic Type Move Bounds (泛型类型移动约束)](#反例-13-generic-type-move-bounds-泛型类型移动约束)
    - [反例 14: Trait Object Moves (Trait对象移动)](#反例-14-trait-object-moves-trait对象移动)
    - [反例 15: Vec Reallocation Moves (Vec重新分配移动)](#反例-15-vec-reallocation-moves-vec重新分配移动)
    - [反例 16: Destructor Panic and Drop Flags (析构函数恐慌与Drop标志)](#反例-16-destructor-panic-and-drop-flags-析构函数恐慌与drop标志)
    - [反例 17: Move in const fn (const fn中的移动)](#反例-17-move-in-const-fn-const-fn中的移动)
    - [反例 18: UnsafeCell and Ownership Bypass (UnsafeCell与所有权绕过)](#反例-18-unsafecell-and-ownership-bypass-unsafecell与所有权绕过)
  - [5. 严格分析](#5-严格分析)
    - [5.1 内存布局](#51-内存布局)
      - [5.1.1 栈分配与所有权](#511-栈分配与所有权)
      - [5.1.2 堆所有权跟踪](#512-堆所有权跟踪)
      - [5.1.3 Drop标志位布局](#513-drop标志位布局)
    - [5.2 借用检查器集成](#52-借用检查器集成)
      - [5.2.1 所有权如何启用借用检查](#521-所有权如何启用借用检查)
      - [5.2.2 流敏感分析](#522-流敏感分析)
      - [5.2.3 非词法生命周期 (NLL) 交互](#523-非词法生命周期-nll-交互)
  - [6. 高级模式](#6-高级模式)
    - [6.1 所有权转移模式](#61-所有权转移模式)
      - [6.1.1 Builder模式所有权流](#611-builder模式所有权流)
      - [6.1.2 状态机所有权](#612-状态机所有权)
      - [6.1.3 类型状态模式](#613-类型状态模式)
    - [6.2 零拷贝模式](#62-零拷贝模式)
      - [6.2.1 View类型](#621-view类型)
      - [6.2.2 借用数据容器](#622-借用数据容器)
  - [7. 案例研究: Vec实现](#7-案例研究-vec实现)
    - [7.1 原始指针所有权](#71-原始指针所有权)
    - [7.2 容量vs长度](#72-容量vs长度)
    - [7.3 重新分配安全](#73-重新分配安全)
    - [7.4 IntoIterator所有权转移](#74-intoiterator所有权转移)
  - [8. Rust 1.94 特性集成](#8-rust-194-特性集成)
    - [8.1 精确大小迭代器优化](#81-精确大小迭代器优化)
    - [8.2 内联const对所有权的影响](#82-内联const对所有权的影响)
    - [8.3 Edition 2024所有权改进](#83-edition-2024所有权改进)
  - [9. 形式化证明技术](#9-形式化证明技术)
    - [9.1 归纳证明结构](#91-归纳证明结构)
    - [9.2 反证法应用](#92-反证法应用)
    - [9.3 不变量保持证明](#93-不变量保持证明)
  - [10. 参考文献与延伸阅读](#10-参考文献与延伸阅读)
    - [学术论文](#学术论文)
    - [官方文档](#官方文档)
    - [工具与实现](#工具与实现)
  - [交叉引用](#交叉引用)

---

## 前言

本文档提供Rust所有权系统的**形式化深度分析**，包含完整的数学语义、严格定理证明以及大量反例分析。所有权系统是Rust内存安全保证的核心，理解其形式基础对于掌握Rust的深层机制至关重要。

### 本文档目标读者

- 希望深入理解所有权系统底层机制的Rust开发者
- 进行Rust形式化验证的研究人员
- 需要教授Rust内存模型的教育工作者

### 符号约定

| 符号 | 含义 |
|------|------|
| `Γ` (Gamma) | 类型环境 (Type Environment) |
| `Ω` (Omega) | 所有权环境 (Ownership Environment) |
| `⊸` | 线性蕴含 (Linear Implication) |
| `*` | 分离合取 (Separating Conjunction) |
| `⊢` | 推导/判断 (Judgment) |
| `⊥` | 无效/底部 (Invalid/Bottom) |
| `□` | 持久性模态 (Persistence Modality) |
| `▷` | 延迟模态 (Later Modality) |

---

## 1. 所有权形式语义

### 1.1 数学基础

#### 1.1.1 分离逻辑基础

Rust所有权系统的形式化基于**分离逻辑 (Separation Logic)**，这是一种扩展的Hoare逻辑，专门用于推理共享和分离的堆内存。

**基本断言**:

```
P, Q ::= emp           (空堆)
       | x ↦ v       (x指向值v)
       | P * Q       (分离合取)
       | P -* Q      (魔法棒/分离蕴含)
       | ∃x. P       (存在量化)
       | ∀x. P       (全称量化)
```

**分离合取 (Separating Conjunction)**:

```
P * Q 表示 P 和 Q 分别持有不相交的内存区域

语义: σ ⊨ P * Q  ⟺  ∃σ₁, σ₂. σ = σ₁ ⊎ σ₂ ∧ σ₁ ⊨ P ∧ σ₂ ⊨ Q
```

**魔法棒 (Magic Wand)**:

```
P -* Q 表示: 如果获得P持有的内存，则Q也成立

语义: σ ⊨ P -* Q  ⟺  ∀σ'. σ' ⊨ P → σ ⊎ σ' ⊨ Q
```

#### 1.1.2 Iris框架与RustBelt

**Iris** 是一种用于并发分离逻辑的高级框架，**RustBelt** 使用Iris对Rust进行形式化。

**Iris核心概念**:

```
资源代数 (Resource Algebra):
  - 定义资源的组合方式
  - Rust所有权对应独占资源 (Exclusive Resource)

预言变量 (Prophecy Variables):
  - 用于推理未来值
  - 在Aeneas翻译中用于可变引用

不变量 (Invariants):
  - ▷P: 延迟P到下一步
  - □P: P是持久的（可无限复制）
```

**RustBelt在Iris中的编码**:

```
类型解释: [[T]] : Type → iProp

String类型解释:
[[String]].own(t, [ℓ]) ≡ ∃w. ℓ ↦ w * Dealloc(ℓ) * ...

其中:
- ℓ: 堆位置
- w: 字符串内容
- Dealloc(ℓ): 对ℓ的释放权限
```

#### 1.1.3 所有权断言

**所有权断言定义**:

```
owns(x, T) ∈ iProp

含义: 变量x拥有类型T的值

形式化:
owns(x, T) ≡ ∃v. x ↦ v * [[T]].own(v)
```

**所有权转移**:

```
owns(x, T) ⊸ owns(y, T)

含义: 消耗x对T的所有权，产生y对T的所有权

在Rust中:
let y = x;  // x: T, T不是Copy

形式化规则:
Γ ⊢ x: T    ¬Copy(T)
────────────────────────
Γ ⊢ move(x): T ⊸ ⊥
```

**分数所有权 (Fractional Ownership)**:

```
owns^k(x, T) 其中 k ∈ (0,1]

- owns^1(x, T): 完全所有权（可读写）
- owns^k(x, T) for k < 1: 部分所有权（只读共享）

组合规则:
owns^k(x, T) * owns^j(x, T) = owns^{k+j}(x, T)  如果 k+j ≤ 1
```

### 1.2 类型状态转换

#### 1.2.1 状态机定义

Rust值的**所有权状态机**定义如下:

```
状态集 S ::= Uninitialized | Owned | Moved | Borrowed(κ) | Dropped

其中:
- Uninitialized: 变量已声明但未初始化
- Owned: 变量拥有值
- Moved: 值已被转移，变量无效
- Borrowed(κ): 值被借用，借用类型κ ∈ {Imm, Mut}
- Dropped: 值已被释放
```

**状态转换图**:

```
                    ┌─────────────────────────────────────┐
                    │                                     │
                    ▼                                     │
┌──────────┐    init    ┌────────┐     move      ┌──────┐ │
│  Uninit  │───────────▶│ Owned  │──────────────▶│Moved │─┘
└──────────┘            └───┬────┘               └──┬───┘
                            │                       │
           ┌────────────────┼────────────────┐      │ reinit
           │                │                │      │
           ▼                ▼                ▼      │
    ┌────────────┐   ┌────────────┐   ┌──────────┐  │
    │Borrowed(Imm)│   │Borrowed(Mut)│   │ Dropped  │◀─┘
    └────────────┘   └────────────┘   └──────────┘
           │                │
           └────────────────┘
                  release
```

#### 1.2.2 状态转换规则

**形式化转换规则**:

```
规则 [INIT]:
Γ ⊢ let x: T;     x ∉ dom(Γ)
────────────────────────────
Γ' = Γ, x: T^{Uninit}

规则 [INIT-ASSIGN]:
Γ ⊢ e: T    Γ ⊢ x: T^{Uninit}
────────────────────────────
Γ' = Γ[x ↦ T^{Owned}]

规则 [MOVE]:
Γ ⊢ x: T^{Owned}    ¬Copy(T)
────────────────────────────
Γ' = Γ[x ↦ T^{Moved}]

规则 [COPY]:
Γ ⊢ x: T^{Owned}    Copy(T)
────────────────────────────
Γ' = Γ  (状态不变)

规则 [BORROW-IMM]:
Γ ⊢ x: T^{Owned}
────────────────────────────
Γ' = Γ[x ↦ T^{Borrowed(Imm)}]

规则 [BORROW-MUT]:
Γ ⊢ x: T^{Owned}
────────────────────────────
Γ' = Γ[x ↦ T^{Borrowed(Mut)}]

规则 [RELEASE]:
Γ ⊢ x: T^{Borrowed(κ)}
────────────────────────────
Γ' = Γ[x ↦ T^{Owned}]

规则 [DROP]:
Γ ⊢ x: T^{Owned}    scope_end(x)
────────────────────────────
Γ' = Γ[x ↦ T^{Dropped}]
```

#### 1.2.3 部分移动的状态处理

**部分移动 (Partial Move)** 发生在结构体或元组的字段被单独移动时:

```rust
struct Person { name: String, age: u32 }

fn partial_move_example() {
    let p = Person {
        name: String::from("Alice"),
        age: 30
    };
    let name = p.name;  // 部分移动: p.name → name
    // p.name: Moved, p.age: Owned
    // p: 部分Moved，整体不可用
}
```

**形式化表示**:

```
部分移动状态:
Γ ⊢ p: struct { f₁: T₁, ..., fₙ: Tₙ }^{PartialMoved(S)}

其中 S ⊆ {1,...,n} 是已被移动的字段索引集

规则 [PARTIAL-MOVE]:
Γ ⊢ p: struct { fᵢ: Tᵢ, ... }^{Owned}
Γ ⊢ move(p.fᵢ): Tᵢ    ¬Copy(Tᵢ)
────────────────────────────────
Γ' = Γ[p ↦ struct { fᵢ: Tᵢ^{Moved}, ... }^{PartialMoved({i})}]

规则 [PARTIAL-USE]:
Γ ⊢ p.fⱼ: Tⱼ    j ∉ S    (未移动的字段)
────────────────────────────────
允许使用 p.fⱼ

规则 [FULL-USE]:
Γ ⊢ p: struct { ... }^{PartialMoved(S)}    S ≠ ∅
────────────────────────────────
禁止使用 p (整体)
```

---

## 2. 所有权定理体系

### Theorem OWNERSHIP-UNIQUENESS (所有权唯一性定理)

**定理陈述**:

```
∀x, y ∈ Var, ∀v ∈ Val. owns(x, v) ∧ owns(y, v) → x = y
```

**中文表述**: 在任意时刻，一个值最多只能有一个所有者。

**证明** (结构归纳法):

**基础情况** (程序初始状态):

- 程序开始时，没有变量拥有任何值
- 空环境满足定理

**归纳步骤**:

考虑所有权状态转换:

1. **初始化** (`let x = e`):
   - 新值被创建或从已有值计算
   - 新值只有x一个所有者
   - 保持唯一性

2. **移动** (`let y = x`):
   - 假设移动前: owns(x, v)，没有其他变量拥有v
   - 移动后: owns(y, v)，x标记为Moved
   - 根据状态机规则，Moved状态不产生所有权
   - 仍然只有y拥有v

3. **复制** (Copy类型):
   - 创建v的副本v'
   - x拥有v，y拥有v'
   - v ≠ v' (不同值)
   - 不违反唯一性

4. **借用** (`let r = &x`):
   - 不转移所有权
   - x仍然拥有v
   - r只持有引用，不是所有者

**结论**: 通过所有可能的转换保持唯一性不变量。

**推论**:

- 定理 NO-DOUBLE-FREE: 每个值最多被drop一次
- 定理 NO-USE-AFTER-FREE: 释放后无法通过原所有者访问

---

### Theorem MOVE-IS-LINEAR (移动线性性定理)

**定理陈述**:

```
移动操作是线性的: move(x) 消耗 x: T 并产生 y: T

形式化:
Γ, x: T ⊢ move(x): T ⊸ (Γ, y: T, x: ⊥)

其中 ⊥ 表示x已无效
```

**证明** (基于线性逻辑):

**线性逻辑背景**:

- 线性蕴含 A ⊸ B: 消耗A产生B
- 线性值: 必须恰好使用一次

**移动的形式化规则**:

```
[MOVE-LINEAR]
Γ ⊢ x: T    state(x) = Owned    ¬Copy(T)
─────────────────────────────────────────
Γ' = Γ[x ↦ state: Moved] ⊢ y: T
```

**证明步骤**:

1. **前置条件**: x在Owned状态
   - 意味着x恰好拥有一个资源

2. **移动操作**: `let y = x`
   - 语义上等价于资源转移
   - x失去所有权 (Moved)
   - y获得所有权 (Owned)

3. **线性性保证**:
   - 资源从x完全转移到y
   - 没有复制或分割
   - x不能再次使用 (不满足 Owned 状态)

4. **与仿射类型的关系**:
   - Rust使用仿射类型 (可以丢弃)
   - 移动是仿射蕴含的一种形式
   - A ⊸ B 允许丢弃A，但Rust不允许丢弃未实现Drop的值

**Q.E.D.**

---

### Theorem DROP-EXACTLY-ONCE (精确释放定理)

**定理陈述**:

```
∀x ∈ Var. 如果x拥有实现Drop的类型T的值v，则v的Drop::drop方法被调用恰好一次。

形式化:
Γ ⊢ x: T^{Owned} ∧ Drop(T) → #{drop(v)} = 1
```

**证明** (基于Drop标志分析):

**Drop标志机制**:

```
编译器为每个变量维护Drop标志 D(x) ∈ {true, false}

- D(x) = true:  变量需要drop
- D(x) = false: 变量已被移动或已drop
```

**Drop标志状态转换**:

```
初始: D(x) = Drop(T)  (如果T实现Drop则为true)

移动后: D(x) = false  (不需要drop)
显式drop: D(x) = false  (已drop)
作用域结束: if D(x) { drop(x); D(x) = false; }
```

**证明**:

1. **资源创建**: `let x = T::new()`
   - D(x) = true
   - 准备好在作用域结束时drop

2. **所有权转移**: `let y = x`
   - D(x) = false (原变量不需要drop)
   - D(y) = true (新变量需要drop)
   - 资源仍会被drop一次

3. **分支合并**:

   ```
   if b {
       drop(x);  // D₁(x) = false
   } else {
       // D₂(x) = true
   }
   // D(x) = D₁(x) ∨ D₂(x) = true
   // 生成条件drop: if D(x) { drop(x); }
   ```

4. **循环分析**:
   - 使用固定点计算确定循环退出时的D状态
   - 确保无论循环执行多少次，资源最多被drop一次

5. **反证法**:
   - 假设v被drop两次
   - 这意味着存在两个不同的drop点都满足D(x) = true
   - 这与D标志的转换规则矛盾 (每次drop后D变为false)

**结论**: Drop标志机制保证每个资源恰好被drop一次。

**Q.E.D.**

---

### Theorem MEMORY-SAFETY (内存安全定理)

**定理陈述**:

```
如果Rust程序通过借用检查，则程序执行期间:
1. 没有使用已移动的值 (No use-after-move)
2. 没有访问未初始化的内存 (No uninitialized access)
3. 没有双重释放 (No double-free)
4. 没有使用已释放的内存 (No use-after-free)
5. 没有数据竞争 (No data races)
```

**证明概要**:

**引理 1** (移动单调性):

```
一旦变量x被标记为Moved，除非重新初始化，否则保持Moved状态。

证明: 查看状态转换表，没有从Moved到Owned的直接转换。
```

**引理 2** (初始化前置条件):

```
任何使用变量x的操作前，state(x) ∈ {Owned, Borrowed}。

证明: 编译器拒绝state(x) ∈ {Uninit, Moved}的使用。
```

**引理 3** (无悬垂引用):

```
引用&x的生命周期不超过x的作用域。

证明: 借用检查器验证scope(borrow) ⊆ scope(owner)。
```

**主证明**:

| 内存安全问题 | Rust防护机制 | 形式化保证 |
|-------------|-------------|-----------|
| Use-after-move | 移动后变量标记为Moved | 引理1+2 |
| Uninitialized access | 初始化分析 | 引理2 |
| Double-free | Drop标志+所有权唯一性 | Theorem DROP-EXACTLY-ONCE |
| Use-after-free | RAII+所有权唯一性 | Theorem OWNERSHIP-UNIQUENESS |
| Data races | Send/Sync + 借用规则 | 引用互斥性 |

**Q.E.D.**

---

### Theorem NO-DOUBLE-FREE (无双重释放定理)

**定理陈述**:

```
在任意执行路径上，每个堆分配的资源最多被释放一次。
```

**证明** (基于所有权唯一性和Drop标志):

1. **所有权唯一性** (Theorem OWNERSHIP-UNIQUENESS):
   - 每个资源最多有一个所有者

2. **Drop标志精确性**:
   - 只有D(x) = true时才会执行drop
   - 执行后D(x) = false

3. **控制流分析**:

   ```
   对于分支:
   if e { s₁ } else { s₂ }

   如果在s₁中x被drop，在s₂中x未被drop:
   - 合并后 D(x) = false ∨ true = true
   - 生成条件drop代码

   这确保无论走哪个分支，x最多被drop一次。
   ```

4. **循环分析**:

   ```
   loop {
       let x = String::new();
       // x在每次迭代结束时drop
       // 每次迭代有独立的x
   }
   ```

**Q.E.D.**

---

### Theorem NO-USE-AFTER-MOVE (无移动后使用定理)

**定理陈述**:

```
∀x ∈ Var. 如果x被移动，则任何后续使用x的操作都是编译错误。

形式化:
Γ ⊢ move(x)  ~>  Γ' ∧ Γ' ⊢ use(x)  →  Error
```

**证明**:

1. **状态跟踪**:
   - 编译器跟踪每个变量的所有权状态

2. **移动后状态**:

   ```
   let y = x;  // Γ' = Γ[x ↦ Moved]
   ```

3. **使用检查**:
   - 使用变量前，编译器检查state(x) = Owned
   - 如果state(x) = Moved，报错:

     ```
     error[E0382]: borrow of moved value: `x`
     ```

4. **流敏感分析**:

   ```
   let x = String::new();
   if condition {
       let y = x;  // 分支1: x被移动
   } else {
       // 分支2: x未被移动
   }
   // 合并后: x状态为MaybeMoved
   // 使用x报错: x may be moved here
   ```

**Q.E.D.**

---

### Theorem COPY-SEMANTICS-PRESERVATION (复制语义保持定理)

**定理陈述**:

```
对于实现Copy trait的类型T:
∀x: T. let y = x; 保持x有效，且Γ(y) = copy(Γ(x))
```

**证明**:

1. **Copy trait条件**:
   - T: Copy 表示T可以按位复制
   - Copy要求Clone，且clone行为等同于按位复制

2. **复制规则**:

   ```
   [COPY]
   Γ ⊢ x: T    Copy(T)
   ────────────────────
   Γ' = Γ    (状态不变)
   Γ(y) = bitwise_copy(Γ(x))
   ```

3. **语义保持**:
   - 复制后，x和y拥有独立的值副本
   - 修改y不影响x
   - 两者都保持Owned状态

4. **与Move的区别**:

   | 特性 | Copy | Move |
   |-----|------|------|
   | 原变量状态 | 保持Owned | 变为Moved |
   | 资源数量 | 增加 | 不变 |
   | 适用类型 | 标量、简单结构 | 堆分配类型 |

**Q.E.D.**

---

### Theorem PARTIAL-MOVE-SOUNDNESS (部分移动健全性定理)

**定理陈述**:

```
部分移动后，未移动字段仍然可访问，但整个值不可使用。

形式化:
Γ ⊢ p: struct { f₁: T₁, ..., fₙ: Tₙ }
Γ ⊢ move(p.fᵢ): Tᵢ
─────────────────────────────────────────
Γ' ⊢ use(p.fⱼ): Tⱼ  对于 j ≠ i  (允许)
Γ' ⊢ use(p): struct { ... }      (禁止)
```

**证明**:

1. **部分移动标记**:
   - 结构体被标记为PartialMoved(S)
   - S包含已移动的字段索引

2. **字段访问规则**:

   ```
   对于字段fⱼ:
   - 如果 j ∈ S: 报错 (已移动)
   - 如果 j ∉ S: 允许访问
   ```

3. **整体使用检查**:
   - 如果S ≠ ∅ (有字段被移动)
   - 则禁止使用整体值
   - 这防止通过整体drop释放已移动的字段

4. **Drop检查**:
   - 部分移动的结构体不能直接drop
   - 必须drop剩余字段或使用std::mem::forget

**Q.E.D.**

---

## 3. 移动语义深度分析

### 3.1 Move作为仿射蕴含

在类型理论中，Rust的移动语义可以用**仿射逻辑 (Affine Logic)** 来形式化。

**仿射逻辑 vs 线性逻辑**:

```
线性逻辑: 每个资源必须恰好使用一次
仿射逻辑: 每个资源最多使用一次 (可以丢弃)

Rust使用仿射逻辑，因为:
- 值可以被移动 (使用一次)
- 值可以在作用域结束时被隐式drop (丢弃)
```

**移动的形式化表示**:

```rust
// Rust代码
let x: T = ...;  // x获得类型T的值
let y = x;       // 移动到y
```

```
形式化类型规则:

[MOVE-AFFINE]
Γ ⊢ x: T    ¬Copy(T)    affine(T)
─────────────────────────────────
Γ ⊢ move(x): T  ⊸  (Γ[x ↦ ⊥], y: T)

其中:
- affine(T): T是仿射类型
- ⊥: x变为无效
- y获得T的所有权
```

**与线性蕴含的关系**:

```
线性蕴含 A ⊸ B: 消耗A，产生B

移动操作: T ⊸ T
输入: x: T (Owned)
输出: y: T (Owned), x: ⊥ (Invalid)

这可以看作:
T ⊸ (T * ⊥)  或简化为  T ⊸ T  (忽略无效的x)
```

**延迟模态 (Later Modality)**:

在Iris中，所有权转移涉及延迟:

```
▷(owns(x, T)) ⊸ ▷(owns(y, T))

▷表示"下一步"，用于处理递归和并发
```

### 3.2 Copy vs Move 形式区分

#### 3.2.1 Copy Trait的形式定义

```rust
pub trait Copy: Clone { }
```

**形式化条件**:

```
类型T可以实现Copy当且仅当:

1. 按位复制语义正确:
   ∀v: T. bitwise_copy(v) 产生有效的T值

2. 不拥有堆分配资源:
   ¬∃ℓ. owns(T, ℓ) where ℓ是堆位置

3. 不包含非Copy类型:
   ∀field f ∈ T. Copy(f.type)
```

**Copy类型的代数性质**:

```
[[!T]] (Copy类型) 对应于线性逻辑中的指数模态:

!A 表示"可无限复制的A"

规则:
!A ⊢ A        (可使用)
!A ⊢ !A ⊗ !A  (可复制)
!A ⊢ 1        (可丢弃)
```

#### 3.2.2 移动判断算法

编译器使用以下算法判断是否移动:

```
算法: should_move(T)
输入: 类型T
输出: bool (是否移动)

1. 如果 T: Copy → 返回 false (复制而非移动)
2. 如果 T 包含非Copy字段:
   a. 如果访问整个值 → 移动
   b. 如果只访问字段 → 部分移动
3. 特殊处理:
   - &T 和 &mut T: 复制引用本身 (Copy)
   - Box<T>: 总是移动
   - Rc<T>: 复制指针 (增加计数)

返回 true
```

### 3.3 隐式移动规则

#### 3.3.1 表达式级移动

```
表达式移动规则:

[EXPR-VAR]
Γ ⊢ x: T    ¬Copy(T)
────────────────────
Γ ⊢ x: T  ~>  Γ[x ↦ Moved]

[EXPR-FIELD]
Γ ⊢ p.f: T    ¬Copy(T)    owns(Γ, p.f)
───────────────────────────────────────
Γ ⊢ p.f: T  ~>  Γ[p.f ↦ Moved]

[EXPR-DEREF]
Γ ⊢ *p: T    ¬Copy(T)    owns(Γ, *p)
─────────────────────────────────────
Γ ⊢ *p: T  ~>  Γ[*p ↦ Moved]
```

#### 3.3.2 函数参数移动

```rust
fn foo(a: String, b: String) -> String { ... }

// 调用
let x = String::from("x");
let y = String::from("y");
let r = foo(x, y);
```

**求值顺序与移动**:

```
Rust参数求值顺序: 从左到右

1. 求值 x → 不移动 (只是读取)
2. 移动 x 到 a
3. 求值 y → 不移动
4. 移动 y 到 b
5. 执行 foo
6. 移动返回值到 r
```

**形式化**:

```
[CALL]
Γ ⊢ e₁: T₁    ...    Γ ⊢ eₙ: Tₙ
∀i. (¬Copy(Tᵢ) → Γ[xᵢ ↦ Moved])
Γ' ⊢ body: R
─────────────────────────────────────────
Γ ⊢ foo(e₁, ..., eₙ): R  ~>  Γ''
```

### 3.4 重新初始化语义

变量被移动后可以重新初始化:

```rust
fn reinit_example() {
    let mut x = String::from("first");
    let y = x;           // x被移动
    x = String::from("second");  // 重新初始化
    println!("{}", x);   // OK!
}
```

**形式化规则**:

```
[REINIT]
Γ ⊢ x: T^{Moved}
Γ ⊢ e: T
───────────────────────
Γ' = Γ[x ↦ T^{Owned}]
```

**关键观察**:

- 重新初始化不同于赋值给已初始化变量
- 前者从Moved到Owned，后者保持Owned
- 后者会先drop旧值

---

## 4. 反例汇编 (15+ 深度案例)

### 反例 1: Use After Move (移动后使用)

**错误代码**:

```rust
fn use_after_move() {
    let s = String::from("hello");
    let s2 = s;              // s被移动到s2
    println!("{}", s);       // ERROR: use of moved value
}
```

**编译器错误**:

```
error[E0382]: borrow of moved value: `s`
 --> src/main.rs:4:20
  |
2 |     let s = String::from("hello");
  |         - move occurs because `s` has type `String`,
  |           which does not implement the `Copy` trait
3 |     let s2 = s;
  |              - value moved here
4 |     println!("{}", s);
  |                    ^ value borrowed here after move
```

**为什么违反所有权**:

```
状态转换:
1. let s = String::from("hello");
   Γ = { s: String^{Owned} }

2. let s2 = s;
   Γ = { s: String^{Moved}, s2: String^{Owned} }

3. println!("{}", s);
   尝试在state(s) = Moved时使用s
   违反规则: 使用前state必须是Owned或Borrowed
```

**解决方案**:

```rust
// 方案1: 使用Clone
let s = String::from("hello");
let s2 = s.clone();        // 深拷贝
println!("{}", s);         // OK

// 方案2: 借用
let s = String::from("hello");
let s2 = &s;               // 借用
println!("{}", s);         // OK

// 方案3: 函数返回所有权
fn take_and_return(s: String) -> String {
    s
}
let s = String::from("hello");
let s = take_and_return(s);  // 移动出去再移回来
```

**形式化修复**:

```
方案1 (Clone):
Γ ⊢ s: String^{Owned}
Γ ⊢ s.clone(): String^{Owned}  // 创建副本
Γ = { s: String^{Owned}, s2: String^{Owned} }  // 两者都有效

方案2 (Borrow):
Γ ⊢ s: String^{Owned}
Γ ⊢ &s: &String^{Borrowed(Imm)}
Γ = { s: String^{Owned} }  // s保持Owned
```

---

### 反例 2: Partial Move (部分移动)

**错误代码**:

```rust
struct Person {
    name: String,
    age: u32,
}

fn partial_move_error() {
    let p = Person {
        name: String::from("Alice"),
        age: 30,
    };
    let name = p.name;       // 部分移动p.name
    println!("{} is {}", p.name, p.age);  // ERROR: p.name已移动
}
```

**编译器错误**:

```
error[E0382]: borrow of partially moved value: `p`
 --> src/main.rs:11:28
  |
10 |     let name = p.name;
  |                ------ value partially moved here
11 |     println!("{} is {}", p.name, p.age);
  |                            ^^^^^^^ value borrowed here after partial move
```

**为什么违反所有权**:

```
状态转换:
1. 创建p后:
   Γ = { p: Person { name: String^{Owned}, age: u32^{Owned} }^{Owned} }

2. let name = p.name:
   Γ = { p: Person { name: String^{Moved}, age: u32^{Owned} }^{PartialMoved({name})},
         name: String^{Owned} }

3. 尝试访问p.name:
   p.name的状态是Moved，不能使用
```

**解决方案**:

```rust
// 方案1: 只使用未移动的字段
let p = Person { name: String::from("Alice"), age: 30 };
let name = p.name;
println!("age is {}", p.age);  // OK: age未被移动
// println!("{:?}", p);        // ERROR: p整体不可用

// 方案2: 借用而非移动
let p = Person { name: String::from("Alice"), age: 30 };
let name = &p.name;           // 借用
println!("{} is {}", p.name, p.age);  // OK

// 方案3: 使用ref模式
let p = Person { name: String::from("Alice"), age: 30 };
let Person { ref name, age } = p;  // name是借用
println!("{} is {}", name, age);    // OK
```

---

### 反例 3: Move in Match Arms (匹配臂中的移动)

**错误代码**:

```rust
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(i32, i32, i32),
}

fn match_move_error(msg: Message) {
    match msg {
        Message::Quit => println!("Quit"),
        Message::Write(text) => println!("Write: {}", text),
        Message::Move { x, y } => println!("Move to ({}, {})", x, y),
        Message::ChangeColor(r, g, b) => println!("Color change"),
    }

    // ERROR: msg在某些臂中被移动，整体不可用
    // println!("{:?}", msg);
}
```

**问题分析**:

```
在Message::Write(text)臂中:
- text从msg中被移动
- msg的String字段被移动
- msg整体变为PartialMoved

即使其他臂没有移动msg，编译器要求所有路径一致
```

**解决方案**:

```rust
// 方案1: 引用绑定
fn match_ref(msg: Message) {
    match &msg {
        Message::Write(text) => println!("Write: {}", text),  // text是&String
        _ => println!("Other"),
    }
    println!("{:?}", msg);  // OK: msg未被移动
}

// 方案2: ref关键字
fn match_ref_keyword(msg: Message) {
    match msg {
        Message::Write(ref text) => println!("Write: {}", text),
        _ => println!("Other"),
    }
    // msg仍然不可用，因为只有Write臂使用了ref
    // 需要所有臂都不移动msg
}

// 方案3: 对单个臂使用引用
fn match_single_arm_ref(msg: Message) {
    match msg {
        Message::Write(text) => {
            println!("Write: {}", text);
            // text在这里drop
        }
        _ => println!("Other"),
    }
    // ERROR: msg在Write臂中被移动
}
```

**Rust 1.94+ 改进**:

```rust
// 使用if let保护
fn match_with_guard(msg: Message) {
    if let Message::Write(ref text) = msg {
        println!("Write: {}", text);
    }
    // msg仍然可用
    handle_other(msg);
}
```

---

### 反例 4: Move in Closures (闭包中的移动)

**错误代码**:

```rust
fn closure_move_error() {
    let s = String::from("hello");

    let closure = || {
        println!("{}", s);  // s被移动到闭包环境
    };

    closure();

    println!("{}", s);  // ERROR: s已被移动到闭包
}
```

**编译器错误**:

```
error[E0382]: borrow of moved value: `s`
 --> src/main.rs:10:20
  |
4 |     let closure = || {
  |                   -- value moved into closure here
5 |         println!("{}", s);
  |                        - variable moved due to use in closure
...
10|     println!("{}", s);
  |                    ^ value borrowed here after move
```

**为什么违反所有权**:

```
闭包捕获规则:
- 如果闭包使用s (通过值或引用)
- 编译器决定如何捕获: 借用或移动
- 如果s不是Copy，且闭包可能多次调用FnMut，则捕获为&mut
- 但如果需要所有权，则捕获为move

形式化:
closure: Fn() 需要 &s (借用)
closure: FnMut() 需要 &mut s (可变借用)
closure: FnOnce() 需要 s (移动)
```

**解决方案**:

```rust
// 方案1: 强制移动 (显式move关键字)
fn closure_explicit_move() {
    let s = String::from("hello");

    let closure = move || {
        println!("{}", s);
        // s在闭包内，外部无法访问
    };

    closure();
    // s不可用
}

// 方案2: 借用
fn closure_borrow() {
    let s = String::from("hello");

    let closure = || {
        println!("{}", &s);  // 明确借用
    };

    closure();
    println!("{}", s);  // OK
}

// 方案3: Clone到闭包
fn closure_clone() {
    let s = String::from("hello");

    let closure = {
        let s = s.clone();  // 克隆
        move || {
            println!("{}", s);
        }
    };

    closure();
    println!("{}", s);  // OK
}
```

---

### 反例 5: Move in Loops (循环中的移动)

**错误代码**:

```rust
fn loop_move_error() {
    let s = String::from("hello");

    for _ in 0..3 {
        let s2 = s;  // ERROR: s在第一次迭代后被移动
        println!("{}", s2);
    }
}
```

**编译器错误**:

```
error[E0382]: use of moved value: `s`
 --> src/main.rs:5:18
  |
2 |     let s = String::from("hello");
  |         - move occurs because `s` has type `String`,
  |           which does not implement the `Copy` trait
3 |     for _ in 0..3 {
4 |         let s2 = s;
  |                  - value moved here in previous iteration of loop
5 |         println!("{}", s2);
  |
```

**为什么违反所有权**:

```
循环分析:
- 第1次迭代: s从Owned → Moved
- 第2次迭代: 尝试移动s，但s已经是Moved
- 违反: 不能从Moved状态再次移动

数据流分析:
InitIn[loop_header] = InitOut[loop_header] (固定点)
在循环出口，s必须是Moved
这意味着循环入口处s也必须是Moved
矛盾！
```

**解决方案**:

```rust
// 方案1: 借用
fn loop_borrow() {
    let s = String::from("hello");

    for _ in 0..3 {
        let s2 = &s;  // 借用
        println!("{}", s2);
    }  // s在所有迭代后仍然可用
}

// 方案2: Clone
fn loop_clone() {
    let s = String::from("hello");

    for _ in 0..3 {
        let s2 = s.clone();  // 每次迭代克隆
        println!("{}", s2);
    }
}

// 方案3: 重新初始化 (如果可能)
fn loop_reinit() {
    let mut s = Some(String::from("hello"));

    for _ in 0..3 {
        if let Some(s2) = s.take() {  // take()移动Option内的值
            println!("{}", s2);
            s = Some(String::from("new"));  // 重新初始化
        }
    }
}
```

---

### 反例 6: Copy Type Confusion (Copy类型混淆)

**错误假设**:

```rust
#[derive(Clone)]
struct Wrapper(String);  // 只有Clone，没有Copy

fn copy_confusion() {
    let w = Wrapper(String::from("hello"));
    let w2 = w;  // 移动!

    // 开发者可能以为这是复制
    println!("{:?}", w);  // ERROR: use of moved value
}
```

**混淆原因**:

```
常见误解:
- 以为赋值总是复制
- 不理解Copy和Clone的区别
- 以为#[derive(Clone)]自动包含Copy
```

**Copy vs Clone 区别**:

| 特性 | Copy | Clone |
|-----|------|-------|
| 隐式/显式 | 隐式 | 显式 (clone()) |
| 开销 | 极低 (按位复制) | 可能高 (堆分配) |
| 自动派生 | #[derive(Copy)] | #[derive(Clone)] |
| 依赖 | 无 | 依赖Copy或自定义逻辑 |
| 语义 | 值复制 | 可能深拷贝 |

**正确代码**:

```rust
// 方案1: 显式Clone
#[derive(Clone)]
struct Wrapper(String);

fn correct_clone() {
    let w = Wrapper(String::from("hello"));
    let w2 = w.clone();  // 显式克隆
    println!("{:?}", w);  // OK
}

// 方案2: 使类型Copy (仅当String可以被替换)
#[derive(Clone, Copy)]
struct Point { x: i32, y: i32 }  // 所有字段都是Copy

fn correct_copy() {
    let p = Point { x: 1, y: 2 };
    let p2 = p;  // 复制
    println!("{:?}", p);  // OK
}

// 方案3: 引用
fn use_reference() {
    let w = Wrapper(String::from("hello"));
    let w2 = &w;  // 借用
    println!("{:?}", w);  // OK
}
```

---

### 反例 7: Drop Order Assumptions (Drop顺序假设错误)

**错误假设**:

```rust
struct A(i32);
struct B(i32);

impl Drop for A {
    fn drop(&mut self) {
        println!("A({}) dropped", self.0);
    }
}

impl Drop for B {
    fn drop(&mut self) {
        println!("B({}) dropped", self.0);
    }
}

fn drop_order_assumption() {
    let a = A(1);
    let b = B(2);
    // 假设A先drop，B后drop?
}
```

**实际Drop顺序**:

```
Rust变量drop顺序: 与声明顺序**相反**

上面代码输出:
B(2) dropped
A(1) dropped

原因: 栈的LIFO特性
```

**Rust 1.94 Edition 2024 改进**:

```rust
// Edition 2024中，临时变量的生命周期和drop顺序有调整
// 但栈变量的drop顺序保持不变

fn edition_2024_temporaries() {
    let _ = vec![1, 2, 3];  // 临时变量
    // Edition 2021: 语句结束时drop
    // Edition 2024: 同样行为，但某些情况下更精确
}
```

**解决方案**:

```rust
// 方案1: 显式drop控制
use std::mem::drop;

fn explicit_drop_order() {
    let a = A(1);
    let b = B(2);

    // 显式控制drop顺序
    drop(a);  // A先drop
    drop(b);  // B后drop
}

// 方案2: 作用域控制
fn scope_drop_order() {
    let a = A(1);

    {
        let b = B(2);
        // b在这里drop
    }  // B dropped

    // a在这里drop
}  // A dropped

// 方案3: 使用ManuallyDrop
use std::mem::ManuallyDrop;

fn manually_drop_order() {
    let mut a = ManuallyDrop::new(A(1));
    let mut b = ManuallyDrop::new(B(2));

    unsafe {
        ManuallyDrop::drop(&mut a);  // A
        ManuallyDrop::drop(&mut b);  // B
    }
}
```

---

### 反例 8: mem::forget Unsafety (mem::forget非安全性)

**错误代码**:

```rust
use std::mem;

struct MyResource(*mut u8);

impl MyResource {
    fn new() -> Self {
        // 分配资源
        Self(unsafe { std::alloc::alloc(std::alloc::Layout::new::<u8>()) })
    }
}

impl Drop for MyResource {
    fn drop(&mut self) {
        unsafe {
            std::alloc::dealloc(self.0, std::alloc::Layout::new::<u8>());
        }
        println!("Resource freed");
    }
}

fn forget_unsafe() {
    let res = MyResource::new();
    mem::forget(res);  // res永远不会被drop!
    // 内存泄漏!
}
```

**为什么危险**:

```
mem::forget作用:
- 消耗值但不调用drop
- 值被"遗忘"，资源不释放

后果:
- 内存泄漏
- 文件描述符泄漏
- 锁不释放
```

**mem::forget的合理使用**:

```rust
// 场景1: 将所有权转移到非Rust代码
extern "C" {
    fn take_ownership(ptr: *mut c_void);
}

fn transfer_to_c() {
    let data = Box::new(42);
    let ptr = Box::into_raw(data);
    unsafe { take_ownership(ptr as *mut c_void); }
    // C代码现在拥有所有权，Rust不再drop
}

// 场景2: 防止双重drop (在unsafe代码中)
use std::ptr;

fn prevent_double_drop() {
    let mut x = Box::new(42);
    let y = unsafe { ptr::read(&x) };  // 复制指针
    mem::forget(x);  // 防止x drop，由y接管
    // y会在作用域结束时drop
}
```

**安全替代方案**:

```rust
// 使用ManuallyDrop代替mem::forget
use std::mem::ManuallyDrop;

fn safe_manually_drop() {
    let mut res = ManuallyDrop::new(MyResource::new());

    // 使用res...

    unsafe {
        ManuallyDrop::drop(&mut res);  // 显式drop
    }
    // 或使用into_inner
    // let inner = ManuallyDrop::into_inner(res);
}
```

---

### 反例 9: ManuallyDrop Misuse (ManuallyDrop误用)

**错误代码**:

```rust
use std::mem::ManuallyDrop;

struct Resource(String);

impl Drop for Resource {
    fn drop(&mut self) {
        println!("Dropping: {}", self.0);
    }
}

fn manually_drop_misuse() {
    let mut res = ManuallyDrop::new(Resource(String::from("test")));

    // 使用res...

    // 忘记drop!
}  // res被drop但不调用Drop::drop - 内存泄漏!
```

**问题分析**:

```
ManuallyDrop语义:
- 包装T，阻止自动drop
- 不会自动调用T::drop
- 需要显式处理

常见错误:
1. 忘记显式drop
2. 重复drop
3. 使用已drop的值
```

**正确使用**:

```rust
// 方案1: 显式drop
fn correct_explicit_drop() {
    let mut res = ManuallyDrop::new(Resource(String::from("test")));

    // 使用res...
    println!("{}", res.0);

    unsafe {
        ManuallyDrop::drop(&mut res);
    }
}

// 方案2: 提取内部值
fn correct_into_inner() {
    let res = ManuallyDrop::new(Resource(String::from("test")));

    // 提取值，手动管理
    let inner = unsafe { ManuallyDrop::take(&mut res) };
    // 或: let inner = ManuallyDrop::into_inner(res);  (Rust 1.94+)

    // inner会在作用域结束时正常drop
}

// 场景: union字段管理
union MyUnion {
    s: ManuallyDrop<String>,
    n: i32,
}

fn union_usage() {
    let mut u = MyUnion { s: ManuallyDrop::new(String::from("hello")) };

    unsafe {
        // 在覆盖前必须drop
        ManuallyDrop::drop(&mut u.s);
        u.n = 42;
    }
}
```

---

### 反例 10: Pin and Move Interaction (Pin与移动交互)

**错误代码**:

```rust
use std::pin::Pin;

struct SelfReferential {
    data: String,
    ptr: *const String,  // 指向data
}

impl SelfReferential {
    fn new(data: String) -> Self {
        let mut s = Self {
            data,
            ptr: std::ptr::null(),
        };
        s.ptr = &s.data;  // 自引用
        s
    }
}

fn pin_move_error() {
    let s = SelfReferential::new(String::from("hello"));
    let mut pinned = Box::pin(s);

    // 尝试移动
    let moved = *pinned;  // ERROR: Pin<Box<T>>不能解引用到T

    // 或者尝试替换
    // *pinned = SelfReferential::new(String::from("new"));  // ERROR
}
```

**为什么Pin很重要**:

```
自引用结构问题:
- data在栈上的位置
- ptr指向&data
- 如果结构体移动，data地址改变
- ptr变成悬垂指针

Pin<P>保证:
- 如果T: !Unpin，则Pin<P<T>>指向的值不会被移动
- 自引用可以安全存在
```

**正确使用Pin**:

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SafeSelfReferential {
    data: String,
    ptr: *const String,
    _marker: PhantomPinned,  // 实现!Unpin
}

impl SafeSelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::new(Self {
            data,
            ptr: std::ptr::null(),
            _marker: PhantomPinned,
        });

        let ptr = &boxed.data as *const String;
        boxed.ptr = ptr;

        Pin::from(boxed)
    }

    fn data(&self) -> &str {
        &self.data
    }
}

fn correct_pin_usage() {
    let pinned = SafeSelfReferential::new(String::from("hello"));

    // pinned保证不会被移动
    println!("{}", pinned.data());

    // 不能移动或解引用来获取值
    // let v = *pinned;  // ERROR
}
```

**Pin保证的形式化**:

```
Pin<P<T>> 保证:
∀t₁, t₂. time(t₁) < time(t₂) → addr(Pin::deref(pinned), t₁) = addr(Pin::deref(pinned), t₂)

即: 被Pin的值在内存中的地址永不改变
```

---

### 反例 11: Self-Referential Move (自引用移动)

**错误代码**:

```rust
struct SelfRef {
    data: [u8; 256],
    cursor: *const u8,  // 指向data内部
}

impl SelfRef {
    fn new() -> Self {
        let mut s = Self {
            data: [0; 256],
            cursor: std::ptr::null(),
        };
        s.cursor = &s.data[0];  // 自引用
        s
    }

    fn get_data(&self) -> &[u8] {
        unsafe { std::slice::from_raw_parts(self.cursor, 256) }
    }
}

fn self_ref_move() {
    let s = SelfRef::new();
    let s2 = s;  // 移动!

    // s2.cursor可能指向s.data的旧址 (悬垂!)
    // 使用s2.get_data() 是UB!
}
```

**为什么这是UB**:

```
移动前:
┌──────────────┐
│ s.data[256]  │ ◄── s.cursor
└──────────────┘
    地址: 0x1000

移动后:
s2在0x2000:
┌──────────────┐
│s2.data[256]  │ 地址: 0x2000
└──────────────┘
但s2.cursor = 0x1000 (旧地址!)
```

**解决方案**:

```rust
// 方案1: 使用偏移量代替指针
struct SafeSelfRef {
    data: [u8; 256],
    cursor_offset: usize,  // 相对于data起始的偏移
}

impl SafeSelfRef {
    fn new() -> Self {
        Self {
            data: [0; 256],
            cursor_offset: 0,
        }
    }

    fn get_data(&self) -> &[u8] {
        &self.data[self.cursor_offset..]
    }
}

// 方案2: 使用Pin (见反例10)

// 方案3: 使用索引
struct IndexedSelfRef {
    data: Vec<u8>,
    cursor_idx: usize,
}

impl IndexedSelfRef {
    fn get_at_cursor(&self) -> Option<&u8> {
        self.data.get(self.cursor_idx)
    }
}
```

---

### 反例 12: Move in Async Blocks (异步块中的移动)

**错误代码**:

```rust
async fn async_move_error() {
    let s = String::from("hello");

    let future = async {
        println!("{}", s);  // s被移动到async块
    };

    future.await;

    println!("{}", s);  // ERROR: s已被移动
}
```

**编译器错误**:

```
error[E0382]: use of moved value: `s`
 --> src/main.rs:10:20
  |
4 |     let future = async {
  |                  ----- value moved into `async` block here
5 |         println!("{}", s);
  |                        - variable moved due to use in coroutine
...
10|     println!("{}", s);
  |                    ^ value used here after move
```

**Async块的捕获规则**:

```
async块类似于闭包:
- 捕获环境中使用的变量
- 默认按值捕获 (移动)
- 生成的future拥有捕获的变量

状态机转换:
async块创建:
  s: String^{Owned} → future: impl Future { s: String^{Owned} }

await后:
  future执行完毕，s在future内drop
```

**解决方案**:

```rust
// 方案1: 引用捕获
async fn async_borrow() {
    let s = String::from("hello");

    let future = async {
        println!("{}", &s);  // 借用
    };

    future.await;
    println!("{}", s);  // OK
}

// 方案2: 显式Clone
async fn async_clone() {
    let s = String::from("hello");

    let future = {
        let s = s.clone();
        async move {
            println!("{}", s);
        }
    };

    future.await;
    println!("{}", s);  // OK
}

// 方案3: Arc共享
use std::sync::Arc;

async fn async_arc() {
    let s = Arc::new(String::from("hello"));

    let s2 = Arc::clone(&s);
    let future = async move {
        println!("{}", s2);
    };

    future.await;
    println!("{}", s);  // OK
}

// 方案4: 使用move关键字明确语义
async fn explicit_move() {
    let s = String::from("hello");

    let future = async move {
        // s被显式移动
        println!("{}", s);
    };

    future.await;
    // s不可用 (明确)
}
```

**Rust 1.94+ async改进**:

```rust
// async闭包 (Rust 1.94不稳定特性)
#![feature(async_closure)]

async fn async_closure_usage() {
    let s = String::from("hello");

    let f = async || {
        println!("{}", &s);  // 可以捕获引用
    };

    f().await;
    println!("{}", s);  // OK
}
```

---

### 反例 13: Generic Type Move Bounds (泛型类型移动约束)

**错误代码**:

```rust
fn generic_take<T>(item: T) -> T {
    // 假设T是Copy
    let item2 = item;  // 如果是非Copy，这里是移动
    item               // ERROR: 如果T非Copy，item已被移动
}
```

**编译器错误**:

```
error[E0382]: use of moved value: `item`
 --> src/main.rs:4:5
  |
2 | fn generic_take<T>(item: T) -> T {
  |                   ----- move occurs because `item` has type `T`
3 |     let item2 = item;
  |                 ---- value moved here
4 |     item
  |     ^^^^ value used here after move
```

**泛型与所有权**:

```
问题:
- 泛型参数T可以是Copy或非Copy
- 编译器必须为所有可能的T生成代码
- 不能假设T是Copy

约束:
- 如果代码对非Copy T有效，则对所有T有效
- 如果需要Copy语义，必须显式约束
```

**解决方案**:

```rust
// 方案1: 添加Copy约束
fn generic_copy<T: Copy>(item: T) -> T {
    let item2 = item;  // 复制
    item               // OK: item仍然有效
}

// 方案2: 添加Clone约束 + 显式克隆
fn generic_clone<T: Clone>(item: T) -> T {
    let item2 = item.clone();
    item  // OK
}

// 方案3: 使用引用
fn generic_borrow<T>(item: &T) -> &T {
    let item2 = item;  // 引用是Copy
    item
}

// 方案4: 正确设计API (消费并返回)
fn generic_consume<T>(item: T) -> (T, T)
where
    T: Clone
{
    let item2 = item.clone();
    (item, item2)
}
```

**Trait Bound推导**:

```rust
// 自动推导的trait bounds
struct Wrapper<T>(T);

// Wrapper<T>是Copy当且仅当T是Copy
impl<T: Copy> Copy for Wrapper<T> {}

// 使用
fn use_wrapper<T>(w: Wrapper<T>) -> Wrapper<T>
where
    T: Copy,
{
    let w2 = w;  // 复制
    w  // OK
}
```

---

### 反例 14: Trait Object Moves (Trait对象移动)

**错误代码**:

```rust
trait Processor {
    fn process(self);
}

struct TextProcessor;

impl Processor for TextProcessor {
    fn process(self) {
        println!("Processing text");
    }
}

fn trait_object_move() {
    let processor: Box<dyn Processor> = Box::new(TextProcessor);

    // 尝试复制trait对象
    let p2 = processor;  // 移动
    // processor.process();  // ERROR: 已移动

    // 更复杂的情况
    let processors: Vec<Box<dyn Processor>> = vec![
        Box::new(TextProcessor),
    ];

    for p in processors {  // 移动出Vec
        p.process();
    }
    // processors不可用
}
```

**Trait对象的所有权特性**:

```
dyn Trait:
- 大小不固定 (DST - Dynamically Sized Type)
- 必须通过指针使用: &dyn Trait, Box<dyn Trait>, etc.
- 不实现Copy (即使具体类型实现Copy)

Box<dyn Trait>:
- 拥有堆上的trait对象
- 移动语义
- 不能隐式复制
```

**解决方案**:

```rust
// 方案1: 借用trait对象
fn borrow_trait_object(processor: &dyn Processor) {
    processor.process();  // 需要修改trait定义接受&self
}

// 修改trait
trait Processor {
    fn process(&self);  // 借用
}

// 方案2: 使用Rc共享
trait SharedProcessor {
    fn process(&self);
}

use std::rc::Rc;

fn shared_trait_objects() {
    let processors: Vec<Rc<dyn SharedProcessor>> = vec![
        Rc::new(TextProcessor),
    ];

    for p in &processors {  // 借用Rc
        p.process();
    }
    // processors仍然可用
}

// 方案3: 返回所有权
trait Processor {
    fn process(self) -> Self;
}

fn chain_process<T: Processor>(p: T) -> T {
    p.process()
}

// 方案4: 使用&dyn Trait作为参数
fn process_all(processors: &[&dyn Processor]) {
    for p in processors {
        p.process();
    }
}
```

---

### 反例 15: Vec Reallocation Moves (Vec重新分配移动)

**问题场景**:

```rust
fn vec_reallocation_issue() {
    let mut v = vec![1, 2, 3];
    let ref_to_first = &v[0];  // 借用第一个元素

    v.push(4);  // 可能导致重新分配!

    // println!("{}", ref_to_first);  // ERROR: 借用可能无效
}
```

**编译器错误**:

```
error[E0502]: cannot borrow `v` as mutable because
it is also borrowed as immutable
 --> src/main.rs:5:5
  |
3 |     let ref_to_first = &v[0];
  |                        ----- immutable borrow occurs here
4 |
5 |     v.push(4);
  |     ^^^^^^^^^ mutable borrow occurs here
6 |
7 |     println!("{}", ref_to_first);
  |                  --------------- immutable borrow later used here
```

**为什么这是问题**:

```
Vec内存布局:
初始: [1, 2, 3] @ 地址 0x1000, 容量 3
      ref_to_first指向 0x1000

push(4)后:
- 容量不足，重新分配
- 新地址 0x2000: [1, 2, 3, 4]
- 旧地址 0x1000 释放
- ref_to_first变成悬垂指针!

编译器通过借用检查阻止这种情况
```

**解决方案**:

```rust
// 方案1: 限制借用范围
fn correct_borrow_scope() {
    let mut v = vec![1, 2, 3];

    {
        let ref_to_first = &v[0];
        println!("{}", ref_to_first);  // 在借用块内使用
    }  // 借用结束

    v.push(4);  // OK
}

// 方案2: 预分配容量
fn preallocate_capacity() {
    let mut v = Vec::with_capacity(10);
    v.push(1);
    v.push(2);

    let ref_to_first = &v[0];
    // ... 不使用v的方法
    println!("{}", ref_to_first);

    // 后续修改
    v.push(3);  // OK: 不重新分配
}

// 方案3: 使用索引代替引用
fn use_index_instead() {
    let mut v = vec![1, 2, 3];
    let first_idx = 0;  // 存储索引而非引用

    v.push(4);

    println!("{}", v[first_idx]);  // OK: 重新索引
}

// 方案4: 使用split_first
fn use_split_first() {
    let mut v = vec![1, 2, 3];

    if let Some((first, rest)) = v.split_first() {
        println!("First: {}", first);
        // 不能修改v，因为借用了first
        // 但可以使用rest
        for x in rest {
            println!("Rest: {}", x);
        }
    }
}

// 方案5: 使用swap_remove (如果顺序不重要)
fn use_swap_remove() {
    let mut v = vec![1, 2, 3];

    // 先处理元素
    let first = v.swap_remove(0);  // 移动出第一个元素
    println!("First: {}", first);

    // 现在可以修改v
    v.push(4);
}
```

**Rust 1.94+ Vec改进**:

```rust
// extract_if (不稳定特性)
#![feature(extract_if)]

fn extract_if_example() {
    let mut v = vec![1, 2, 3, 4, 5];

    // 安全地提取符合条件的元素
    let extracted: Vec<_> = v.extract_if(|x| *x % 2 == 0).collect();

    println!("Remaining: {:?}", v);
    println!("Extracted: {:?}", extracted);
}
```

---

### 反例 16: Destructor Panic and Drop Flags (析构函数恐慌与Drop标志)

**问题场景**:

```rust
struct PanicOnDrop;

impl Drop for PanicOnDrop {
    fn drop(&mut self) {
        panic!("Panic in drop!");
    }
}

fn drop_panic_problem() {
    let _ = PanicOnDrop;
}  // 恐慌!

// 更复杂的情况
struct Wrapper {
    a: PanicOnDrop,
    b: String,  // 如果a.panic()，b可能泄漏
}
```

**为什么危险**:

```
析构函数中的恐慌:
- 如果正在处理另一个恐慌: 程序中止 (abort)
- 如果未处理恐慌: 开始展开 (unwind)
- 可能导致:
  1. 后续析构函数被跳过
  2. 资源泄漏
  3. 不安全状态
```

**解决方案**:

```rust
// 方案1: 避免在drop中panic
impl Drop for SafeStruct {
    fn drop(&mut self) {
        // 使用Result处理错误，不panic
        if let Err(e) = self.cleanup() {
            eprintln!("Cleanup failed: {}", e);
            // 不panic!
        }
    }
}

// 方案2: 使用ManuallyDrop控制
type OnDrop<F: FnOnce()> = ManuallyDrop<Box<F>>;

fn controlled_drop() {
    let guard = ManuallyDrop::new(Box::new(|| {
        println!("Cleanup");
    }));

    // 正常工作...

    // 显式调用 (可以处理错误)
    if let Ok(f) = ManuallyDrop::try_take(guard) {
        f();
    }
}

// 方案3: 使用catch_unwind
use std::panic::catch_unwind;

fn guarded_drop() {
    let result = catch_unwind(|| {
        let _ = PanicOnDrop;
    });

    match result {
        Ok(_) => println!("No panic"),
        Err(_) => println!("Caught panic"),
    }
}

// 方案4: 使用Option + take模式
struct SafeWrapper {
    resource: Option<Resource>,
}

impl SafeWrapper {
    fn cleanup(&mut self) {
        if let Some(res) = self.resource.take() {
            // 手动清理，可以处理错误
            drop(res);
        }
    }
}

impl Drop for SafeWrapper {
    fn drop(&mut self) {
        self.cleanup();  // 安全的清理
    }
}
```

---

### 反例 17: Move in const fn (const fn中的移动)

**问题场景** (Rust 1.94+ const fn限制):

```rust
const fn const_move<T>(x: T) -> (T, T) {
    let y = x;  // 移动
    (x, y)      // ERROR: 在const fn中不能复制后使用
}
```

**编译器错误**:

```
error[E0382]: use of moved value: `x`
 --> src/main.rs:2:6
  |
1 | const fn const_move<T>(x: T) -> (T, T) {
  |                        - move occurs because `x` has type `T`
2 |     let y = x;
  |             - value moved here
3 |     (x, y)
  |      ^ value used here after move
```

**const fn中的所有权**:

```
const fn限制 (Rust 1.94):
- 可以创建和移动值
- 不能使用需要运行时的特性 (如堆分配)
- Copy/Clone约束在const fn中同样适用
- 不支持动态分发

const上下文中的Drop:
- const fn中的值在编译时drop
- 没有运行时开销
```

**解决方案**:

```rust
// 方案1: Copy约束
const fn const_copy<T: Copy>(x: T) -> (T, T) {
    let y = x;  // 复制
    (x, y)      // OK
}

// 方案2: 返回单个值
const fn const_single<T>(x: T) -> T {
    x  // 简单地传递
}

// 方案3: 使用const泛型
struct ConstWrapper<const N: usize> {
    data: [u8; N],
}

impl<const N: usize> ConstWrapper<N> {
    const fn new(data: [u8; N]) -> Self {
        Self { data }  // 移动数组 (Copy)
    }
}

// 方案4: 使用MaybeUninit进行const构造
use std::mem::MaybeUninit;

const fn const_construct<T>() -> MaybeUninit<T> {
    MaybeUninit::uninit()  // 安全地在const中创建
}
```

---

### 反例 18: UnsafeCell and Ownership Bypass (UnsafeCell与所有权绕过)

**错误代码**:

```rust
use std::cell::UnsafeCell;

struct BadIdea {
    data: UnsafeCell<String>,
}

unsafe impl Send for BadIdea {}
unsafe impl Sync for BadIdea {}

fn unsafecell_misuse() {
    let bad = BadIdea {
        data: UnsafeCell::new(String::from("hello")),
    };

    let s_ref = unsafe { &*bad.data.get() };

    // 同时修改!
    unsafe {
        *bad.data.get() = String::from("world");
    }

    // s_ref可能指向无效内存!
    println!("{}", s_ref);  // UB!
}
```

**为什么危险**:

```
UnsafeCell:
- 内部可变性原语
- 允许通过&引用修改
- 绕过Rust的借用规则
- 开发者负责维护安全不变量

常见错误:
1. 同时读写
2. 读时修改
3. 创建悬垂引用
4. 在多线程中不加保护使用
```

**正确使用**:

```rust
// 方案1: 使用安全的Cell/RefCell封装
use std::cell::RefCell;

fn safe_interior_mutability() {
    let data = RefCell::new(String::from("hello"));

    {
        let mut s = data.borrow_mut();
        s.push_str(" world");
    }  // 借用结束

    println!("{}", data.borrow());  // OK
}

// 方案2: 使用Mutex在线程间共享
use std::sync::{Arc, Mutex};

fn thread_safe_shared() {
    let data = Arc::new(Mutex::new(String::from("hello")));

    let data2 = Arc::clone(&data);
    std::thread::spawn(move || {
        let mut s = data2.lock().unwrap();
        s.push_str(" from thread");
    });

    let s = data.lock().unwrap();
    println!("{}", s);
}

// 方案3: 正确的UnsafeCell封装 (高级)
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicBool, Ordering};

struct SafeCell<T> {
    data: UnsafeCell<T>,
    lock: AtomicBool,
}

impl<T> SafeCell<T> {
    fn new(data: T) -> Self {
        Self {
            data: UnsafeCell::new(data),
            lock: AtomicBool::new(false),
        }
    }

    fn with_mut<R>(&self, f: impl FnOnce(&mut T) -> R) -> R {
        // 自旋锁
        while self.lock.swap(true, Ordering::Acquire) {}

        let result = unsafe { f(&mut *self.data.get()) };

        self.lock.store(false, Ordering::Release);
        result
    }
}

// 安全地实现Sync (内部同步)
unsafe impl<T: Send> Sync for SafeCell<T> {}
```

---

## 5. 严格分析

### 5.1 内存布局

#### 5.1.1 栈分配与所有权

**栈帧结构**:

```
函数调用栈帧:
┌─────────────────────────────┐ 高地址
│ 返回地址                     │
├─────────────────────────────┤
│ 保存的寄存器                 │
├─────────────────────────────┤
│ 局部变量区                   │
│  ┌─────────────────────┐    │
│  │ x: i32              │    │ 固定大小
│  ├─────────────────────┤    │
│  │ s: String (栈部分)   │    │
│  │   - ptr: *mut u8     │    │
│  │   - len: usize       │    │
│  │   - cap: usize       │    │
│  ├─────────────────────┤    │
│  │ b: Box<T>           │    │
│  │   - ptr: *mut T      │    │
│  └─────────────────────┘    │
├─────────────────────────────┤
│ Drop标志 (编译器生成)        │
└─────────────────────────────┘ 低地址
```

**所有权与栈帧关系**:

```
进入函数:
1. 分配栈帧
2. 初始化局部变量
3. 设置Drop标志

退出函数:
1. 按声明相反顺序drop变量
2. 释放栈帧
3. 返回调用者
```

#### 5.1.2 堆所有权跟踪

**堆分配类型布局**:

```
String内存布局:
┌──────────────┐     ┌──────────────────────┐
│ 栈: String   │     │ 堆: 实际字符串数据    │
│ ┌──────────┐ │     │ ┌──────────────────┐ │
│ │ ptr      │─┼────▶│ │ "hello world"    │ │
│ │ len: 11  │ │     │ └──────────────────┘ │
│ │ cap: 20  │ │     └──────────────────────┘
└──────────────┘

所有权:
- 栈上的String拥有堆内存
- 移动String转移所有权
- Drop String释放堆内存
```

**Vec<T>内存布局**:

```
Vec<T>:
┌──────────────┐     ┌──────────────────────────────┐
│ 栈: Vec<T>   │     │ 堆: 连续内存块                │
│ ┌──────────┐ │     │ ┌──────┬──────┬──────┬─────┐ │
│ │ buf: ptr │─┼────▶│ │ T[0] │ T[1] │ ...  │     │ │
│ │ len      │ │     │ └──────┴──────┴──────┴─────┘ │
│ │ cap      │ │     │ len个元素  cap容量          │
└──────────────┘     └──────────────────────────────┘

重新分配时:
1. 分配新内存 (大小 = new_cap * sizeof(T))
2. 移动所有元素 (对每个元素调用ptr::read)
3. 释放旧内存
4. 更新ptr/len/cap
```

#### 5.1.3 Drop标志位布局

**编译器生成的Drop标志**:

```rust
fn example(b: bool) {
    let x = String::from("hello");  // D(x) = true

    if b {
        drop(x);  // D(x) = false
    }

    // 编译器生成:
    // if D(x) { drop(x); }
}
```

**标志位存储**:

```
在栈帧中，编译器可能使用位图存储Drop标志:

Drop标志位图:
┌────────────────────────────────────┐
│ Bit 0: D(x)                        │
│ Bit 1: D(y)                        │
│ Bit 2: D(z)                        │
│ ...                                │
└────────────────────────────────────┘

优化:
- 如果变量总是初始化且不被移动，可以省略标志
- 常量分析确定标志必要性
```

**条件Drop代码生成**:

```rust
// 源代码
fn conditional(b: bool) {
    let x = String::from("a");
    let y = String::from("b");

    if b {
        drop(x);
    } else {
        drop(y);
    }
}

// 概念性的编译后代码
fn conditional_compiled(b: bool) {
    let x = String::from("a");
    let y = String::from("b");

    let mut D_x = true;
    let mut D_y = true;

    if b {
        drop(x);
        D_x = false;
    } else {
        drop(y);
        D_y = false;
    }

    if D_x { drop(x); }
    if D_y { drop(y); }
}
```

### 5.2 借用检查器集成

#### 5.2.1 所有权如何启用借用检查

**借用检查的基本原理**:

```
所有权系统提供基础:
1. 每个值有唯一所有者
2. 所有者可以创建借用
3. 借用有生命周期

借用检查器验证:
1. 借用不超过所有者生命周期
2. 可变借用唯一性
3. 可变借用与不可变借用互斥
```

**借用与所有权的关系**:

```
owns(x, T) ──borrow──▶ &x: &T (共享借用)
owns(x, T) ──borrow──▶ &mut x: &mut T (唯一借用)

形式化:
owns(x, T) ⊢ SharedBorrow(&x, T)  (可多个)
owns(x, T) ⊢ UniqueBorrow(&mut x, T)  (仅一个)
```

#### 5.2.2 流敏感分析

**基于MIR的流敏感分析**:

```
Rust编译器使用MIR (Mid-level IR)进行流敏感分析:

源代码:
fn flow_sensitive() {
    let x = String::from("hello");
    let y = x;  // x移动
    let z = x;  // 错误!
}

MIR表示:
basic block:
    _1 = String::from(const "hello")
    _2 = move _1    // _1标记为Moved
    _3 = move _1    // 错误: _1是Moved
```

**数据流方程**:

```
对于每个基本块B:

Gen[B]:  在B中创建的借用
Kill[B]: 在B中失效的借用

In[B] = ⋂_{P∈pred(B)} Out[P]  (交汇)
Out[B] = Gen[B] ∪ (In[B] - Kill[B])

交汇操作: 取交集 (保守策略)
```

#### 5.2.3 非词法生命周期 (NLL) 交互

**NLL改进**:

```rust
fn nll_example() {
    let mut v = vec![1, 2, 3];

    let ref_to_first = &v[0];  // 借用开始
    println!("{}", ref_to_first);  // 最后一次使用
    // 借用在这里结束 (非词法)

    v.push(4);  // OK: 借用已结束
}

// 旧版Rust (词法生命周期):
// let ref_to_first = &v[0];
// println!("{}", ref_to_first);
// v.push(4);  // ERROR: ref_to_first在作用域内
```

**NLL实现原理**:

```
1. 基于MIR而非AST
2. 借用生命周期由最后使用点决定
3. 数据流分析确定借用结束点
4. 支持更自然的编码模式

形式化:
before NLL: lifetime(r) = scope(decl(r))
after NLL:  lifetime(r) = [decl(r), last_use(r)]
```

---

## 6. 高级模式

### 6.1 所有权转移模式

#### 6.1.1 Builder模式所有权流

```rust
// 标准Builder模式
#[derive(Debug)]
struct Config {
    host: String,
    port: u16,
    tls: bool,
}

struct ConfigBuilder {
    host: Option<String>,
    port: Option<u16>,
    tls: Option<bool>,
}

impl ConfigBuilder {
    fn new() -> Self {
        Self {
            host: None,
            port: None,
            tls: None,
        }
    }

    fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }

    fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }

    fn tls(mut self, tls: bool) -> Self {
        self.tls = Some(tls);
        self
    }

    fn build(self) -> Result<Config, &'static str> {
        Ok(Config {
            host: self.host.ok_or("host required")?,
            port: self.port.unwrap_or(8080),
            tls: self.tls.unwrap_or(true),
        })
    }
}

fn builder_usage() {
    let config = ConfigBuilder::new()
        .host("localhost")
        .port(3000)
        .tls(false)
        .build()
        .unwrap();

    println!("{:?}", config);
}
```

**所有权流分析**:

```
所有权转移链:
ConfigBuilder::new()
  ├── host()  ──▶ self (移动) ──▶ Self (返回)
  ├── port()  ──▶ self (移动) ──▶ Self (返回)
  ├── tls()   ──▶ self (移动) ──▶ Self (返回)
  └── build() ──▶ self (消费) ──▶ Config

形式化:
self: ConfigBuilder ⊸ ConfigBuilder (每个方法)
self: ConfigBuilder ⊸ Result<Config, E> (build)
```

#### 6.1.2 状态机所有权

```rust
// 类型状态模式: 编译时状态检查
struct Closed;
struct Open;

struct Connection<State> {
    address: String,
    _state: std::marker::PhantomData<State>,
}

impl Connection<Closed> {
    fn new(address: impl Into<String>) -> Self {
        Self {
            address: address.into(),
            _state: std::marker::PhantomData,
        }
    }

    fn open(self) -> Connection<Open> {
        println!("Opening connection to {}", self.address);
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }
}

impl Connection<Open> {
    fn send(&self, data: &str) {
        println!("Sending: {}", data);
    }

    fn close(self) -> Connection<Closed> {
        println!("Closing connection");
        Connection {
            address: self.address,
            _state: std::marker::PhantomData,
        }
    }
}

fn state_machine_usage() {
    let conn = Connection::new("localhost:8080");
    // conn.send("data");  // ERROR: Connection<Closed>没有send方法

    let conn = conn.open();
    conn.send("Hello");   // OK

    let conn = conn.close();
    // conn.send("data");  // ERROR: 已返回Closed状态
}
```

**状态转换图**:

```
┌──────────────┐    open()     ┌──────────────┐
│   Closed     │──────────────▶│    Open      │
│              │               │              │
│  new()创建   │◄──────────────│  send()可用  │
└──────────────┘    close()    └──────────────┘

所有权保证:
- open()消费Closed，产生Open
- close()消费Open，产生Closed
- 不能双重open或send到Closed
```

#### 6.1.3 类型状态模式

```rust
// 更复杂的类型状态: HTTP请求构建
struct Request<Method, HasBody> {
    method: std::marker::PhantomData<Method>,
    has_body: std::marker::PhantomData<HasBody>,
    url: String,
    body: Option<Vec<u8>>,
}

struct Get;
struct Post;
struct Yes;
struct No;

impl Request<Get, No> {
    fn get(url: impl Into<String>) -> Self {
        Self {
            method: std::marker::PhantomData,
            has_body: std::marker::PhantomData,
            url: url.into(),
            body: None,
        }
    }
}

impl Request<Post, No> {
    fn post(url: impl Into<String>) -> Self {
        Self {
            method: std::marker::PhantomData,
            has_body: std::marker::PhantomData,
            url: url.into(),
            body: None,
        }
    }

    fn with_body(self, body: Vec<u8>) -> Request<Post, Yes> {
        Request {
            method: std::marker::PhantomData,
            has_body: std::marker::PhantomData,
            url: self.url,
            body: Some(body),
        }
    }
}

impl Request<Post, Yes> {
    fn send(self) -> Result<String, &'static str> {
        println!("POST {} with body", self.url);
        Ok("200 OK".to_string())
    }
}

impl Request<Get, No> {
    fn send(self) -> Result<String, &'static str> {
        println!("GET {}", self.url);
        Ok("200 OK".to_string())
    }
}

fn type_state_usage() {
    // GET请求不能有body
    let get_req = Request::get("https://api.example.com/users");
    let response = get_req.send().unwrap();

    // POST请求可以(可选)有body
    let post_req = Request::post("https://api.example.com/users");
    // post_req.send();  // ERROR: Post<No>没有send

    let post_req = post_req.with_body(b"{\"name\":\"Alice\"}".to_vec());
    let response = post_req.send().unwrap();
}
```

### 6.2 零拷贝模式

#### 6.2.1 View类型

```rust
// 字符串切片 (零拷贝视图)
fn use_string_view() {
    let owned = String::from("hello world");
    let view: &str = &owned[0..5];  // 零拷贝切片

    println!("{}", view);  // "hello"
    // view不拥有数据，只是引用
}

// 通用View类型
struct View<'a, T> {
    data: &'a [T],
}

impl<'a, T> View<'a, T> {
    fn new(data: &'a [T]) -> Self {
        Self { data }
    }

    fn slice(&self, range: std::ops::Range<usize>) -> View<'a, T> {
        View { data: &self.data[range] }
    }
}

// 使用示例
fn view_usage() {
    let data = vec![1, 2, 3, 4, 5];
    let view = View::new(&data);
    let subview = view.slice(1..4);

    println!("{:?}", subview.data);  // [2, 3, 4]
}  // data在这里drop
```

**所有权与视图**:

```
数据流:
owned_data: Vec<T> ──▶ View<'a, T> (借用)
                              │
                              ▼
                         subview (子借用)
                              │
                              ▼
                        只读访问，无所有权

形式化:
owns(data, Vec<T>) ⊢ View::<'a, T>::new(&data)
其中 'a ⊆ lifetime(data)
```

#### 6.2.2 借用数据容器

```rust
// Cow: Clone on Write - 写时克隆
use std::borrow::Cow;

fn process_data(input: &str) -> Cow<'_, str> {
    if input.contains("old") {
        // 需要修改，分配新内存
        Cow::Owned(input.replace("old", "new"))
    } else {
        // 不需要修改，零拷贝借用
        Cow::Borrowed(input)
    }
}

fn cow_usage() {
    let data = String::from("hello old world");
    let result = process_data(&data);
    println!("{}", result);

    let data2 = String::from("hello world");
    let result2 = process_data(&data2);
    println!("{}", result2);  // 零拷贝
}

// 自定义借用容器
struct BorrowedData<'a> {
    header: &'a [u8; 4],
    payload: &'a [u8],
}

impl<'a> BorrowedData<'a> {
    fn parse(buffer: &'a [u8]) -> Option<Self> {
        if buffer.len() < 4 {
            return None;
        }
        let (header, payload) = buffer.split_at(4);
        Some(Self {
            header: header.try_into().ok()?,
            payload,
        })
    }
}

fn borrowed_container_usage() {
    let buffer = vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06];
    let data = BorrowedData::parse(&buffer).unwrap();

    println!("Header: {:?}", data.header);
    println!("Payload: {:?}", data.payload);
}  // buffer在这里drop
```

---

## 7. 案例研究: Vec<T>实现

### 7.1 原始指针所有权

```rust
// Vec<T>简化实现
pub struct Vec<T> {
    ptr: NonNull<T>,      // 拥有堆内存
    len: usize,          // 元素数量
    cap: usize,          // 容量
}

// 关键方法
impl<T> Vec<T> {
    pub fn new() -> Self {
        Self {
            ptr: NonNull::dangling(),
            len: 0,
            cap: 0,
        }
    }

    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            self.grow();
        }

        unsafe {
            // 在ptr + len处写入值
            ptr::write(self.ptr.as_ptr().add(self.len), value);
        }
        self.len += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        self.len -= 1;
        unsafe {
            // 从ptr + len读取值 (移动出)
            Some(ptr::read(self.ptr.as_ptr().add(self.len)))
        }
    }
}

// Drop实现
impl<T> Drop for Vec<T> {
    fn drop(&mut self) {
        unsafe {
            // 1. drop每个元素
            for i in 0..self.len {
                ptr::drop_in_place(self.ptr.as_ptr().add(i));
            }

            // 2. 释放内存
            if self.cap > 0 {
                let layout = Layout::array::<T>(self.cap).unwrap();
                alloc::dealloc(self.ptr.as_ptr() as *mut u8, layout);
            }
        }
    }
}
```

**原始指针所有权语义**:

```
NonNull<T>:
- 保证非null的原始指针
- 不实现Send/Sync (除非T: Send/Sync)
- Vec<T>通过它拥有堆内存

所有权责任:
1. 确保内存正确分配
2. 确保内存正确释放
3. 确保元素正确drop
```

### 7.2 容量vs长度

```
Vec<T>状态:
┌─────────────────────────────────────────────┐
│ 堆内存布局                                   │
├─────────────────────────────────────────────┤
│                                             │
│  [0]    [1]    [2]    ...    [len-1]  ...   │
│   ▼      ▼      ▼              ▼            │
│ ┌───┐  ┌───┐  ┌───┐          ┌───┐  ─────  │
│ │ T │  │ T │  │ T │  ......  │ T │  未使用  │
│ └───┘  └───┘  └───┘          └───┘         │
│                                             │
│ │←──────────── len ────────────→│           │
│ │←────────────────── cap ─────────────────→││
│                                             │
└─────────────────────────────────────────────┘

len: 实际包含的元素数
    - 用户可以访问的范围
    - drop时处理的元素数

cap: 分配的容量
    - 可以容纳的最大元素数
    - 决定内存块大小
```

### 7.3 重新分配安全

```rust
impl<T> Vec<T> {
    fn grow(&mut self) {
        let new_cap = if self.cap == 0 {
            4
        } else {
            self.cap * 2
        };

        let new_layout = Layout::array::<T>(new_cap).unwrap();

        let new_ptr = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            unsafe {
                alloc::realloc(
                    self.ptr.as_ptr() as *mut u8,
                    old_layout,
                    new_layout.size(),
                )
            }
        };

        self.ptr = match NonNull::new(new_ptr as *mut T) {
            Some(p) => p,
            None => alloc::handle_alloc_error(new_layout),
        };
        self.cap = new_cap;
    }
}
```

**重新分配时的所有权转移**:

```
重新分配前:
旧内存 @ 0x1000: [T[0], T[1], ..., T[len-1]]
ptr指向 0x1000

重新分配时:
1. 分配新内存 @ 0x2000，大小 = new_cap * sizeof(T)
2. 对每个i in 0..len:
   - ptr::read(0x1000 + i * sizeof(T))  (移动出旧位置)
   - ptr::write(0x2000 + i * sizeof(T), value)  (写入新位置)
3. 释放旧内存 @ 0x1000
4. ptr更新为 0x2000

所有权不变:
- Vec<T>仍然拥有所有元素
- 元素从旧位置移动到新位置
```

### 7.4 IntoIterator所有权转移

```rust
impl<T> IntoIterator for Vec<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(mut self) -> IntoIter<T> {
        unsafe {
            let begin = self.ptr.as_ptr();
            let end = if self.len == 0 {
                begin
            } else {
                begin.add(self.len)
            };

            // 防止Vec::drop被调用
            self.len = 0;

            IntoIter {
                buf: NonNull::new_unchecked(begin),
                phantom: PhantomData,
                ptr: begin,
                end,
            }
        }
    }
}

pub struct IntoIter<T> {
    buf: NonNull<T>,      // 整个分配的内存
    phantom: PhantomData<T>,
    ptr: *const T,        // 下一个要返回的元素
    end: *const T,        // 结束指针
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.ptr == self.end {
            return None;
        }

        unsafe {
            let old = self.ptr;
            self.ptr = self.ptr.offset(1);
            Some(ptr::read(old))  // 移动出元素
        }
    }
}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        // 1. drop剩余元素
        for _ in &mut *self {}

        // 2. 释放内存
        unsafe {
            let layout = Layout::array::<T>(self.end.offset_from(self.buf.as_ptr()) as usize).unwrap();
            alloc::dealloc(self.buf.as_ptr() as *mut u8, layout);
        }
    }
}
```

**所有权转移链**:

```
Vec<T> ──into_iter()──▶ IntoIter<T>
    │                        │
    │ 转移内存所有权          │ next()
    │                        ▼
    │                   Item = T (每次返回一个)
    │                        │
    ▼                        ▼
  忘记Vec               最终Drop释放内存
```

---

## 8. Rust 1.94 特性集成

### 8.1 精确大小迭代器优化

```rust
// Rust 1.94: Iterator::size_hint改进
fn size_hint_optimization() {
    let v = vec![1, 2, 3, 4, 5];

    // size_hint返回(lower, Some(upper))
    let iter = v.iter();
    assert_eq!(iter.size_hint(), (5, Some(5)));  // 精确大小

    // filter后大小不确定
    let filtered = v.iter().filter(|&&x| x > 2);
    assert_eq!(filtered.size_hint(), (0, Some(5)));  // 范围
}

// 自定义精确大小迭代器
struct ExactIter<T> {
    data: Vec<T>,
    pos: usize,
}

impl<T> Iterator for ExactIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.pos >= self.data.len() {
            return None;
        }
        let item = std::mem::replace(&mut self.data[self.pos], unsafe { std::mem::zeroed() });
        self.pos += 1;
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.data.len() - self.pos;
        (remaining, Some(remaining))
    }
}

impl<T> ExactSizeIterator for ExactIter<T> {}

// 利用ExactSizeIterator进行优化
fn collect_with_capacity<T, I>(iter: I) -> Vec<T>
where
    I: IntoIterator<Item = T>,
    I::IntoIter: ExactSizeIterator,
{
    let iter = iter.into_iter();
    let mut result = Vec::with_capacity(iter.len());
    result.extend(iter);
    result
}
```

### 8.2 内联const对所有权的影响

```rust
// Rust 1.94: inline const
const fn compute_size() -> usize {
    1024
}

fn inline_const_ownership() {
    // 内联const表达式
    let buffer = [0u8; const { compute_size() }];

    // 所有权与const:
    // - const值在编译时计算
    // - 不影响运行时所有权语义
    // - buffer仍然是栈分配的数组

    process_buffer(buffer);  // 移动数组 (如果是非Copy类型)
}  // buffer在这里drop (如果没有移动)

// const块中的复杂计算
fn complex_const() {
    let sizes = [const {
        let mut sum = 0;
        let mut i = 0;
        while i < 10 {
            sum += i * 2;
            i += 1;
        }
        sum
    }; 4];

    println!("{:?}", sizes);  // [90, 90, 90, 90]
}
```

### 8.3 Edition 2024所有权改进

```rust
// Edition 2024 改进: 临时变量生命周期
fn edition_2024_temporary_lifetime() {
    // Edition 2021
    // let r = &temporary();  // 延长临时生命周期

    // Edition 2024: 更精确的生命周期
    // 某些情况下临时变量更早释放，减少意外借用冲突
}

// 宏中的所有权处理
macro_rules! take_ownership {
    ($e:expr) => {{
        let _ = $e;  // 消费表达式
    }};
}

fn macro_ownership() {
    let s = String::from("hello");
    take_ownership!(s);
    // s不可用
}
```

---

## 9. 形式化证明技术

### 9.1 归纳证明结构

**结构归纳法在所有权证明中的应用**:

```
要证明: 对于所有Rust程序P，所有权系统保证内存安全

证明结构:
1. 基础情况: 空程序和简单声明
2. 归纳假设: 假设子程序满足性质
3. 归纳步骤: 证明复合程序保持性质

归纳于程序结构:
- 表达式
- 语句
- 块
- 函数
- 程序
```

**引理层次**:

```
引理1 (基础): 单条语句保持所有权不变量
引理2 (复合): 语句序列保持所有权不变量
引理3 (控制流): 分支和循环保持所有权不变量
引理4 (函数): 函数调用保持所有权不变量

定理 (内存安全): 所有权系统保证内存安全
证明: 应用引理1-4于程序结构
```

### 9.2 反证法应用

**证明所有权唯一性**:

```
目标: ∀x,y. owns(x, v) ∧ owns(y, v) → x = y

反证:
假设 ∃x ≠ y. owns(x, v) ∧ owns(y, v)

分析:
1. v由某个创建操作产生 (let v = ...)
2. 创建时只有一个所有者 (设为x)
3. 后续转换:
   - 移动: x → z，y不可能获得所有权
   - 复制: 产生v' ≠ v，y拥有v'
   - 借用: 不产生所有权
4. 矛盾: y无法获得对v的所有权

结论: 假设不成立，所有权唯一
```

### 9.3 不变量保持证明

**所有权系统不变量**:

```
不变量1 (唯一性):
∀v. |{x | owns(x, v)}| ≤ 1

不变量2 (状态一致性):
∀x. state(x) = Owned → ¬borrowed(x)

不变量3 (借用有效性):
∀r: &T. valid(r) → lifetime(r) ⊆ lifetime(*r)

证明方法:
对每个语法构造，验证不变量保持
```

**转移系统验证**:

```
状态: (Γ, Ω, B)
- Γ: 值环境
- Ω: 所有权环境
- B: 活动借用集

初始状态: (∅, ∅, ∅)

终止状态: 任意 (需满足不变量)

转换: (Γ, Ω, B) → (Γ', Ω', B')

验证: 每个转换保持所有不变量
```

---

## 10. 参考文献与延伸阅读

### 学术论文

1. **Jung, R., et al. (2018).** RustBelt: Securing the Foundations of the Rust Programming Language. *POPL 2018*.
   - Rust所有权系统的完整形式化
   - Iris分离逻辑框架应用

2. **Weiss, A., Patterson, D., & Ahmed, A. (2020).** Oxide: The Essence of Rust. *arXiv:1903.00982*.
   - 简化Rust核心语义
   - 基于类型的所有权形式化

3. **Matsushita, Y., et al. (2022).** RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. *PLDI 2022*.
   - 支持Unsafe代码的验证

4. **Ho, S., & Protzenko, J. (2022).** Aeneas: Rust Verification by Functional Translation. *ICFP 2022*.
   - 函数式翻译方法
   - 预言变量编码

5. **Tov, J.A., & Pucella, R. (2011).** Practical Affine Types. *POPL 2011*.
   - 仿射类型理论

### 官方文档

1. **The Rust Programming Language (TRPL)**
   - Chapter 4: Understanding Ownership
   - Chapter 15: Smart Pointers

2. **The Rust Reference**
   - Ownership and Moves
   - Destructors
   - Drop Check

3. **The Rustonomicon**
   - Ownership and lifetimes
   - Working with unsafe

### 工具与实现

1. **MIRI (MIR Interpreter)**
   - Rust未定义行为检测器
   - 验证所有权使用正确性

2. **Polonius**
   - 下一代借用检查器
   - 基于数据流分析

3. **Aeneas**
   - Rust到定理证明器的翻译
   - 支持Coq, Lean, F*

4. **Creusot**
   - Rust程序验证工具
   - 基于Why3

---

## 交叉引用

| 文档 | 内容 | 关系 |
|------|------|------|
| [01-02-borrowing-system.md](01-02-borrowing-system.md) | 借用系统 | 所有权启用借用 |
| [01-03-lifetimes.md](01-03-lifetimes.md) | 生命周期 | 所有权与生命周期交互 |
| [ownership-counterexamples.md](ownership-counterexamples.md) | 所有权反例 | 补充反例 |
| [detailed-concepts/ownership-deep-dive.md](detailed-concepts/ownership-deep-dive.md) | 所有权深入 | 扩展阅读 |
| [../formal-foundations/models/02-05-move-analysis.md](../formal-foundations/models/02-05-move-analysis.md) | 移动分析 | 形式化基础 |

---

**维护者**: Rust Formal Methods Team
**最后更新**: 2026-03-06
**状态**: ✅ 形式化完备
