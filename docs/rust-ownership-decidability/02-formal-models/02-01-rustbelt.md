# RustBelt: Rust的形式化基础

> **权威来源**: Ralf Jung et al. (2018). *RustBelt: Securing the Foundations of the Rust Programming Language*. POPL 2018
> **扩展工作**: RustHornBelt (2022), Iris Separation Logic

## 目录

- [RustBelt: Rust的形式化基础](#rustbelt-rust的形式化基础)
  - [目录](#目录)
  - [1. RustBelt概述](#1-rustbelt概述)
    - [1.1 项目目标](#11-项目目标)
    - [1.2 核心架构](#12-核心架构)
  - [2. λRust: Rust核心语言](#2-λrust-rust核心语言)
    - [2.1 语法定义](#21-语法定义)
    - [2.2 操作语义](#22-操作语义)
  - [3. Iris分离逻辑基础](#3-iris分离逻辑基础)
    - [3.1 核心概念](#31-核心概念)
    - [3.2 分离逻辑断言](#32-分离逻辑断言)
  - [4. 类型的语义模型](#4-类型的语义模型)
    - [4.1 所有权谓词](#41-所有权谓词)
    - [4.2 Box类型的详细解释](#42-box类型的详细解释)
  - [5. 生命周期逻辑](#5-生命周期逻辑)
    - [5.1 生命周期的语义](#51-生命周期的语义)
    - [5.2 借用命题](#52-借用命题)
  - [6. Send与Sync的语义](#6-send与sync的语义)
    - [6.1 Send Trait](#61-send-trait)
    - [6.2 Sync Trait](#62-sync-trait)
    - [6.3 示例分析](#63-示例分析)
  - [7. 形式化验证流程](#7-形式化验证流程)
    - [7.1 验证Safe API](#71-验证safe-api)
    - [7.2 发现的标准库Bug](#72-发现的标准库bug)
  - [8. RustBelt的扩展](#8-rustbelt的扩展)
    - [8.1 RustHornBelt](#81-rusthornbelt)
    - [8.2 Aeneas](#82-aeneas)
  - [参考文献](#参考文献)

## 1. RustBelt概述

### 1.1 项目目标

```text
┌─────────────────────────────────────────────────────────────────────┐
│                      RustBelt 核心目标                               │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  问题: Rust广泛使用unsafe代码实现标准库，如何确保其安全性？           │
│                                                                     │
│  解决方案:                                                          │
│  1. 形式化建模Rust的核心语言 λRust                                   │
│  2. 在Iris分离逻辑中定义类型的语义模型                                │
│  3. 证明safe API的语义正确性                                         │
│  4. 为unsafe代码提供验证义务                                         │
│                                                                     │
│  成果: 发现Rust标准库中未知的soundness bug                            │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 核心架构

```text
RustBelt架构层次:

┌──────────────────────────────────────────────────────────────┐
│                    Safe Rust 程序                             │
├──────────────────────────────────────────────────────────────┤
│                    Safe API 抽象                              │
│         (Vec, HashMap, Rc, RefCell, etc.)                    │
├──────────────────────────────────────────────────────────────┤
│                    Unsafe 实现                                │
│         (原始指针, 手动内存管理, 外部调用)                      │
├──────────────────────────────────────────────────────────────┤
│                    λRust 核心语言                             │
│         (MIR级别的形式化模型)                                 │
├──────────────────────────────────────────────────────────────┤
│                    Iris 分离逻辑                              │
│         (高阶并发分离逻辑框架)                                │
├──────────────────────────────────────────────────────────────┤
│                    Coq 证明                                   │
│         (机器检查的形式化证明)                                │
└──────────────────────────────────────────────────────────────┘
```

## 2. λRust: Rust核心语言

### 2.1 语法定义

```text
λRust 语法 (简化):

e ∈ Expr ::=
  | x                     变量
  | ()                    单位值
  | (e₁, ..., eₙ)         元组
  | injᵢ e                注入 (sum类型)
  | λx.e                  函数抽象
  | e₁ e₂                 函数应用
  | new e                 堆分配
  | *e                    解引用
  | e₁ ← e₂               赋值
  | drop e                显式释放
  | &^{mut} e             借用
  | fork e                线程派生

τ ∈ Type ::=
  | 1                     单位类型
  | τ₁ × τ₂               乘积类型
  | τ₁ + τ₂               和类型
  | τ₁ → τ₂               函数类型
  | own_{n} τ             拥有指针 (Box)
  | &^{α} τ               共享引用
  | &^{mut α} τ           可变引用

α ∈ Lifetime ::= 生命周期变量
```

### 2.2 操作语义

```text
小步操作语义 (简化):

(λx.e) v  ↦  e[v/x]                          (β-归约)

new v  ↦  ℓ    (ℓ是新位置, ℓ ↦ v加入堆)

*ℓ  ↦  v      (如果 ℓ ↦ v 在堆中)

ℓ ← v  ↦  ()  (更新 ℓ ↦ v' 为 ℓ ↦ v)

drop ℓ  ↦  ()  (从堆中移除 ℓ ↦ v)

fork e  ↦  创建新线程执行e
```

## 3. Iris分离逻辑基础

### 3.1 核心概念

Iris是一个**高阶并发分离逻辑**框架：

```text
Iris的关键特性:

1. 高阶幽灵状态 (Higher-Order Ghost State)
   - 允许任意复杂的不变量
   - 支持自定义资源代数

2. 模态算子 (Modalities)
   - ▷ (Later): 下一步成立
   - □ (Persistence): 持久真
   - ◇ (Update): 原子更新

3. 不变量 (Invariants)
   - P^N: 在命名空间N中的不变量P
   - 可共享的资源断言

4. 资源代数 (Resource Algebras)
   - 定义自定义资源组合规则
```

### 3.2 分离逻辑断言

```text
基本断言:

ℓ ↦ v        - 位置ℓ包含值v (points-to)
P * Q        - P和Q同时成立 (分离合取)
P ∨ Q        - P或Q成立
P ⇒ Q        - P蕴含Q
∀x. P        - 全称量词
∃x. P        - 存在量词
□P           - P是持久的 (可无限复制)
▷P           - P在下一步成立

所有权断言:
Own(γ, a)    - 拥有幽灵状态γ的值a
```

## 4. 类型的语义模型

### 4.1 所有权谓词

```text
类型语义的核心: 所有权谓词

[[τ]].own : ThreadId → list Val → iProp

对于类型τ，线程t拥有值列表v̄:

[[1]].own(t, []) ≡ True                      (单位类型)

[[τ₁ × τ₂]].own(t, v̄₁ ++ v̄₂) ≡
  [[τ₁]].own(t, v̄₁) * [[τ₂]].own(t, v̄₂)      (乘积)

[[τ₁ + τ₂]].own(t, injᵢ v̄) ≡
  [[τᵢ]].own(t, v̄)                           (和类型)

[[own_{n} τ]].own(t, [ℓ]) ≡
  ∃v̄. ℓ ↦ v̄ * ▷[[τ]].own(t, v̄) * Dealloc(ℓ)  (拥有指针)

[[&^{mut α} τ]].own(t, [ℓ]) ≡
  &^{α}(∃v̄. ℓ ↦ v̄ * ▷[[τ]].own(t, v̄))        (可变借用)

[[&^{α} τ]].share(t, [ℓ]) ≡
  ∀t'. &^{α}(∃v̄. ℓ ↦ v̄ * ▷[[τ]].share(t', v̄)) (共享借用)
```

### 4.2 Box类型的详细解释

```rust
// Box<T> 的语义
let b: Box<i32> = Box::new(42);
```

```text
语义解释:

[[Box<i32>]].own(t, [ℓ]) ≡
  ∃n. ℓ ↦ [n] * Dealloc(ℓ, size(i32)) * ▷(n = 42)

含义:
- ℓ: 堆上的位置
- ℓ ↦ [n]: 该位置包含值n
- Dealloc(ℓ, ...): 拥有释放权限
- ▷: 递归的guard
```

## 5. 生命周期逻辑

### 5.1 生命周期的语义

```text
生命周期作为区域:

Region α ⊆ CFG  (控制流图的子集)

生命周期上下文:
[[L]] ≡ ★_{α∈L} ([α]₁ * ([α]₁ ⇒ ◇[↑α]))

其中:
- [α]₁: 生命周期α存活的token
- [↑α]: 生命周期α结束的权限
- ◇: update modality
```

### 5.2 借用命题

```text
借用命题 (Borrow Propositions):

&^{α} P  ≡  在生命周期α期间暂时持有P

性质:
- 当α结束时，P返回原所有者
- 借用期间原所有者被"冻结"

重新借用:
&^{α}(∃v̄. ℓ ↦ v̄ * P) 可以通过&^{β}重新借用
其中 β ⊆ α
```

## 6. Send与Sync的语义

### 6.1 Send Trait

```rust
pub unsafe auto trait Send { }
```

```text
语义定义:

τ: Send  ≡  [[τ]].own 不依赖于线程id

即:
∀t, t'. [[τ]].own(t, v̄) ⇔ [[τ]].own(t', v̄)

意义: 类型可以安全地在线程间转移所有权
```

### 6.2 Sync Trait

```rust
pub unsafe auto trait Sync { }
```

```text
语义定义:

τ: Sync  ≡  &τ: Send

即:
[[&τ]].own 不依赖于线程id

意义: 类型可以安全地被多线程共享引用
```

### 6.3 示例分析

| 类型 | Send | Sync | 原因 |
|------|------|------|------|
| i32 | ✓ | ✓ | 可复制，无内部状态 |
| String | ✓ | ✓ | 堆数据转移安全 |
| `Rc<T>` | ✗ | ✗ | 引用计数非线程安全 |
| `Arc<T>` | ✓ | ✓ | 原子引用计数 |
| `Cell<T>` | ✗ | ✗ | 内部可变性非线程安全 |
| `Mutex<T>` | ✓ | ✗ | 提供同步，但本身需Send |

## 7. 形式化验证流程

### 7.1 验证Safe API

```rust
// 要验证的API
pub fn swap<T>(x: &mut T, y: &mut T) {
    unsafe {
        let p = x as *mut T;
        let q = y as *mut T;
        std::ptr::swap(p, q);
    }
}
```

```text
验证步骤:

1. 形式化规范:
   ∀T. {x: &mut^{α} T * y: &mut^{α} T} swap(x, y) {x: &mut^{α} T * y: &mut^{α} T}

2. 证明unsafe实现满足规范:
   - ptr::swap 的安全性依赖于不重叠
   - &mut保证x和y不重叠

3. Coq中完成机器检查的证明
```

### 7.2 发现的标准库Bug

```rust
// 问题代码 (已修复)
impl<T> Borrow<T> for RefCell<T> {
    fn borrow(&self) -> &T {
        // 问题: 返回的引用比RefCell活得长
    }
}

// 修复: 返回Ref而非&T
```

## 8. RustBelt的扩展

### 8.1 RustHornBelt

RustHornBelt = RustBelt + RustHorn

- 整合CHC-based验证
- 支持功能正确性证明
- 预言变量编码可变借用

### 8.2 Aeneas

- 从LLBC提取纯函数
- 支持特征/抽象
- Lean后端证明

---

## 参考文献

1. Jung, R., et al. (2018). RustBelt: Securing the Foundations of the Rust Programming Language. *POPL*.
2. Jung, R., et al. (2017). Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning. *POPL*.
3. Krebbers, R., et al. (2017). MoSeL: A General, Extensible Modal Framework for Interactive Proofs in Separation Logic. *ICFP*.
4. Matsushita, Y., et al. (2022). RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. *PLDI*.
