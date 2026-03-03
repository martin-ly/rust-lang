# RustBelt 深度解读

> RustBelt: Securing the Foundations of the Rust Programming Language (Jung et al., POPL 2018)
>
> 本文档提供RustBelt论文的全面技术解读，涵盖λ_Rust核心语言、Iris分离逻辑框架、所有权谓词语义和标准库验证。

---

## 目录

- [RustBelt 深度解读](#rustbelt-深度解读)
  - [目录](#目录)
  - [1. 论文概述](#1-论文概述)
    - [1.1 核心问题](#11-核心问题)
    - [1.2 主要贡献](#12-主要贡献)
    - [1.3 技术路线](#13-技术路线)
  - [2. λ\_Rust 核心语言](#2-λ_rust-核心语言)
    - [2.1 语法定义](#21-语法定义)
    - [2.2 关键设计决策](#22-关键设计决策)
    - [2.3 操作语义](#23-操作语义)
  - [3. Iris 分离逻辑框架](#3-iris-分离逻辑框架)
    - [3.1 资源代数（Resource Algebra）](#31-资源代数resource-algebra)
    - [3.2 高阶协议（Higher-Order Protocols）](#32-高阶协议higher-order-protocols)
    - [3.3 不变量（Invariants）](#33-不变量invariants)
    - [3.4 幽灵状态（Ghost State）](#34-幽灵状态ghost-state)
  - [4. 所有权谓词语义](#4-所有权谓词语义)
    - [4.1 核心定义](#41-核心定义)
    - [4.2 类型解释](#42-类型解释)
    - [4.3 共享借用语义](#43-共享借用语义)
  - [5. 标准库验证](#5-标准库验证)
    - [5.1 `Cell<T>`](#51-cellt)
    - [5.2 `RefCell<T>`](#52-refcellt)
    - [5.3 `Rc<T>` 和 `Arc<T>`](#53-rct-和-arct)
    - [5.4 `Mutex<T>` 和 `RwLock<T>`](#54-mutext-和-rwlockt)
    - [5.5 `UnsafeCell<T>`](#55-unsafecellt)
  - [6. Send 和 Sync 的语义](#6-send-和-sync-的语义)
    - [6.1 形式化定义](#61-形式化定义)
    - [6.2 验证方法](#62-验证方法)
  - [7. Coq 实现结构](#7-coq-实现结构)
    - [7.1 代码统计](#71-代码统计)
    - [7.2 核心模块](#72-核心模块)
  - [8. 理论意义](#8-理论意义)
    - [8.1 对Rust语言的影响](#81-对rust语言的影响)
    - [8.2 对形式化方法的贡献](#82-对形式化方法的贡献)
  - [9. 局限性与后续工作](#9-局限性与后续工作)
  - [参考](#参考)

---

## 1. 论文概述

### 1.1 核心问题

**问题陈述**：如何证明Rust的类型系统确实提供了它所承诺的内存安全保证？

具体挑战：

1. **Unsafe代码验证**：约30%的标准库使用`unsafe`块
2. **内部可变性**：`Cell`、`RefCell`等类型在类型系统外进行变异
3. **并发原语**：`Mutex`、`RwLock`的线程安全性
4. **引用计数**：`Rc`、`Arc`的正确性

### 1.2 主要贡献

1. **λ_Rust**: Rust核心语言的CPS（Continuation-Passing Style）形式化
2. **分离逻辑语义**: 使用Iris框架定义所有权
3. **标准库验证**: 验证Cell, RefCell, Rc, Arc, Mutex等核心类型
4. **机器检查证明**: 约19,000行Coq代码，完全形式化验证

### 1.3 技术路线

```text
Rust源代码
    ↓ 提取核心语言
λ_Rust（CPS中间表示）
    ↓ 定义语义
Iris分离逻辑模型
    ↓ 验证
安全定理证明
    ↓ 机器检查
Coq形式化
```

---

## 2. λ_Rust 核心语言

### 2.1 语法定义

```text
表达式:
  e ::= x                    变量
     | ()                   单位值
     | n                    整数
     | (e, e)               元组
     | ℓ := e; e            赋值（顺序组合）
     | !ℓ                   解引用
     | ref(e)               创建引用（Box::new）
     | &ℓ                   创建共享引用
     | &mut ℓ               创建可变引用
     | newlock e            创建锁
     | acquire e in x.e     获取锁
     | fork{e}              创建线程
     | ...

值:
  v ::= ()                   单位
     | n                    整数
     | (v, v)               元组
     | ℓ                    内存位置
     | &ℓ                   共享引用
     | &mut ℓ               可变引用
     | lock(γ, ℓ)           锁值（携带幽灵名称和位置）
```

### 2.2 关键设计决策

**CPS风格转换**:

```rust
// 原始Rust
let x = f();
g(x);

// λ_Rust CPS形式
f()(λx. g(x)(λ_. ...))
```

CPS的优势：

1. **显式控制流**：继续（continuation）作为一等值
2. **简化求值上下文**：只需处理尾部位置
3. **便于推理**：顺序组合明确

**显式内存位置**：

```text
位置 ℓ ∈ Loc 表示堆内存地址

存储 σ : Loc ⇀ Value 映射位置到值
```

### 2.3 操作语义

**小步语义示例**：

```text
[E-Var]
────────────────────────
⟨x, σ⟩ → ⟨σ(x), σ⟩

[E-Ref]
⟨e, σ⟩ → ⟨v, σ'⟩
ℓ fresh
────────────────────────
⟨ref(e), σ⟩ → ⟨ℓ, σ'[ℓ ↦ v]⟩

[E-Assign]
────────────────────────
⟨ℓ := v; e, σ⟩ → ⟨e, σ[ℓ ↦ v]⟩

[E-Deref]
ℓ ∈ dom(σ)
────────────────────────
⟨!ℓ, σ⟩ → ⟨σ(ℓ), σ⟩

[E-Fork]
────────────────────────
⟨fork{e}, σ⟩ → ⟨(), σ⟩  同时创建新线程 ⟨e, σ⟩ → ...
```

---

## 3. Iris 分离逻辑框架

Iris是一个高阶并发分离逻辑框架，RustBelt基于它构建。

### 3.1 资源代数（Resource Algebra）

资源代数定义了可组合的资源：

```text
资源代数 RA = (Carriers, ⋅, ε, Owns, Valid)

⋅ : 资源组合（必须兼容）
ε : 单位元
Owns : 所有权断言
Valid : 有效性谓词
```

**分数所有权**：

```text
ℓ ↦{q} v  表示对位置ℓ的分数所有权，份额q ∈ (0,1]

ℓ ↦{1} v   ≡ 完全所有权（可写）
ℓ ↦{q} v (q<1)  只读所有权

ℓ ↦{q₁} v ⋅ ℓ ↦{q₂} v = ℓ ↦{q₁+q₂} v  (当q₁+q₂ ≤ 1)
```

### 3.2 高阶协议（Higher-Order Protocols）

Iris支持高阶谓词，可以量化断言：

```coq
(* 谓词作为参数 *)
Definition protocol (P : iProp) : iProp := ...

(* 递归协议 *)
Definition recursive_protocol : iProp :=
  μ rec. P ∗ ▷ rec.
```

### 3.3 不变量（Invariants）

不变量表示始终成立的断言：

```text
inv(γ, P)  表示资源γ在任何时候都满足P

关键规则：
- 创建：P 可以创建 inv(γ, P)
- 访问：可以临时"打开"不变量（需遵守约束）
- 持久性：inv(γ, P) 是持久的（可以复制）
```

**RefCell的运行时检查**使用不变量建模：

```text
inv(cell, ∃n. cell.borrow_count ↦ n ∧ (n = 0 ∨ n > 0 ∧ 只读))
```

### 3.4 幽灵状态（Ghost State）

幽灵状态用于推理中的辅助信息：

```text
幽灵变量 γ 携带逻辑信息，不影响运行时行为

用途：
1. 跟踪引用计数
2. 记录借用状态
3. 建立协议之间的关联
```

---

## 4. 所有权谓词语义

### 4.1 核心定义

**类型所有权谓词**：

```text
[T].own(t, v)  表示：在线程t中，值v拥有类型T

这个谓词是类型相关的，每种类型有不同的定义。
```

**所有权的多态性**：

```text
own : Type → ThreadID → Value → iProp

读作："类型T在线程t中的值v的所有权"
```

### 4.2 类型解释

**基本类型**：

```text
[i32].own(t, n) ≡ ⌜n ∈ ℤ⌝

[bool].own(t, b) ≡ ⌜b ∈ {true, false}⌝

[()].own(t, ()) ≡ True
```

**`Box<T>`**：

```text
[Box<T>].own(t, ℓ) ≡ ℓ ↦ ? ∗ [T].own(t, v)
                    where σ(ℓ) = v

Box拥有堆位置ℓ，且ℓ的内容满足T的所有权
```

**元组**：

```text
[(T₁, T₂)].own(t, (v₁, v₂)) ≡ [T₁].own(t, v₁) ∗ [T₂].own(t, v₂)

分离合取（∗）表示两部分独立拥有
```

### 4.3 共享借用语义

**共享借用**：

```text
[&'a T].own(t, ℓ) ≡ ∃v. ℓ ↦ v ∗ [T].shr(a, t, v)

共享借用将所有权转换为共享权限
```

**共享权限（shr）**：

```text
[T].shr(a, t, v)  表示线程t在时间a可以共享访问v

关键特性：
- 可复制的（persistent）
- 可能有读权限
- 不保证独占访问
```

**可变借用**：

```text
[&'a mut T].own(t, ℓ) ≡ ∃v. ℓ ↦ v ∗ [T].own(t, v) ∗ borrowed(a, ℓ)

包含：
1. 堆内容所有权
2. 类型T的完整所有权
3. 借用标记（确保原位置不被访问）
```

---

## 5. 标准库验证

### 5.1 `Cell<T>`

**Cell**提供内部可变性：

```rust
impl<T: Copy> Cell<T> {
    pub fn get(&self) -> T { ... }
    pub fn set(&self, val: T) { ... }
}
```

**形式化规范**：

```text
[Cell<T>].own(t, ℓ) ≡ ∃v. ℓ ↦ v ∗ [T].own(t, v)

get方法规范：
{[Cell<T>].own(t, c)}
  c.get()
{x. x = v ∗ [Cell<T>].own(t, c)}

set方法规范：
{[Cell<T>].own(t, c) ∗ [T].own(t, v)}
  c.set(v)
{[Cell<T>].own(t, c)}
```

**验证要点**：

- `get`返回值的副本（T: Copy）
- `set`替换内部值
- 不涉及共享借用，只需独占所有权

### 5.2 `RefCell<T>`

**RefCell**提供运行时借用检查：

```rust
impl<T> RefCell<T> {
    pub fn borrow(&self) -> Ref<T> { ... }
    pub fn borrow_mut(&self) -> RefMut<T> { ... }
}
```

**形式化规范**：

```text
[RefCell<T>].own(t, ℓ_cell) ≡
  ∃ℓ_data ℓ_count v n.
    ℓ_cell ↦ (ℓ_data, ℓ_count) ∗
    ℓ_data ↦ v ∗ [T].own(t, v) ∗
    ℓ_count ↦ n ∗
    (n = 0 ∨ n > 0 ∗ 只读模式)

borrow() 规范：
{[RefCell<T>].own(t, rc)}
  rc.borrow()
{r. ∃'a. r: Ref<'a, T> ∗ [Ref<'a, T>].own(t, r)}

borrow_mut() 规范：
{[RefCell<T>].own(t, rc)}
  rc.borrow_mut()
{r. ∃'a. r: RefMut<'a, T> ∗ [RefMut<'a, T>].own(t, r)}
```

**运行时检查形式化**：

```text
borrow()操作：
1. 读取borrow_count
2. 如果是usize::MAX（已有可变借用），panic
3. 否则，borrow_count += 1

borrow_mut()操作：
1. 读取borrow_count
2. 如果不为0，panic
3. 设置为usize::MAX
```

### 5.3 `Rc<T>` 和 `Arc<T>`

**Rc**使用引用计数：

```rust
impl<T> Rc<T> {
    pub fn new(val: T) -> Rc<T> { ... }
    pub fn clone(&self) -> Rc<T> { ... }
}

impl<T> Drop for Rc<T> {
    fn drop(&mut self) { ... }
}
```

**形式化规范**：

```text
[Rc<T>].own(t, ℓ_rc) ≡
  ∃ℓ_data ℓ_count v n γ.
    ℓ_rc ↦ (ℓ_data, ℓ_count) ∗
    ℓ_data ↦ v ∗ [T].own(t, v) ∗
    ℓ_count ↦ n ∗ ⌜n > 0⌝ ∗
    own_refcount(γ, n)  (* 幽灵引用计数 *)

clone() 规范：
{[Rc<T>].own(t, rc)}
  rc.clone()
{rc'. [Rc<T>].own(t, rc) ∗ [Rc<T>].own(t, rc')}

drop() 规范（通过Drop trait）：
{[Rc<T>].own(t, rc)}
  drop(rc)
{[T].own(t, v) 如果这是最后一个引用}
```

**引用计数不变量**：

```text
不变量：引用计数 ≥ 1（只要存在Rc）
当引用计数降为0时：释放T

幽灵状态own_refcount(γ, n)确保计数准确性
```

### 5.4 `Mutex<T>` 和 `RwLock<T>`

**Mutex**提供互斥访问：

```rust
impl<T> Mutex<T> {
    pub fn new(val: T) -> Mutex<T> { ... }
    pub fn lock(&self) -> MutexGuard<T> { ... }
}
```

**形式化规范**：

```text
[Mutex<T>].own(t, ℓ_mutex) ≡
  ∃ℓ_data γ_lock v.
    ℓ_mutex ↦ (ℓ_data, lock_state) ∗
    ℓ_data ↦ v ∗ [T].own(t, v) ∗
    is_lock(γ_lock, ℓ_data, [T].own(-, v))

lock() 规范：
{[Mutex<T>].own(t, m)}
  m.lock()
{g. ∃'a. g: MutexGuard<'a, T> ∗
      [MutexGuard<'a, T>].own(t, g) ∗
      [T].own(t, g.deref())}
```

**锁协议**：

```text
is_lock(γ, ℓ, P) 表示：
- ℓ是一个锁
- 持有锁时拥有资源P
- 释放锁时归还P
```

### 5.5 `UnsafeCell<T>`

**UnsafeCell**是所有内部可变性的基础：

```rust
pub struct UnsafeCell<T: ?Sized> {
    value: T,
}
```

**形式化规范**：

```text
[UnsafeCell<T>].own(t, ℓ) ≡ ℓ ↦ ? ∗ unsafe_permission(ℓ)

UnsafeCell本身不保证安全，它只是：
- 标记可能存在别名
- 告诉编译器不要基于别名做优化

安全封装（如Cell、RefCell）负责维护不变量
```

---

## 6. Send 和 Sync 的语义

### 6.1 形式化定义

**Send**：

```text
T: Send ⟺ ∀t₁, t₂, v. [T].own(t₁, v) ⟹ [T].own(t₂, v)

解释：所有权可以安全地从一个线程转移到另一个线程
```

**Sync**：

```text
T: Sync ⟺ ∀t, v. [T].own(t, v) ⟹ [&T].shr(⊤, t, &v)

解释：可以安全地在多个线程间共享不可变引用
```

### 6.2 验证方法

**验证T: Send**：

```coq
(* 证明所有权与线程ID无关 *)
Lemma T_Send : forall t1 t2 v,
  T_own t1 v ⊢ T_own t2 v.
Proof.
  (* 根据T的结构进行归纳 *)
Qed.
```

**验证T: Sync**：

```coq
(* 证明可以从所有权创建共享引用 *)
Lemma T_Sync : forall t v,
  T_own t v ⊢ shr T ⊤ t (addr_of v).
Proof.
  (* 根据T的结构进行归纳 *)
Qed.
```

**关键验证**：

| 类型 | Send | Sync | 证明策略 |
|------|------|------|----------|
| `Cell<T>` | T: Send | 否 | 内部可变性 |
| `RefCell<T>` | T: Send | 否 | 运行时借用 |
| `Rc<T>` | 否 | T: Send+Sync | 非原子计数 |
| `Arc<T>` | T: Send+Sync | T: Send+Sync | 原子计数 |
| `Mutex<T>` | T: Send | T: Send | 互斥保证 |

---

## 7. Coq 实现结构

### 7.1 代码统计

```text
总代码量：约19,000行Coq

分布：
- Iris框架扩展：8,000行
- λ_Rust定义：2,500行
- 类型解释：3,500行
- 标准库验证：5,000行
```

### 7.2 核心模块

```text
lambda_rust/
├── lang/                    # 语言定义
│   ├── syntax.v            # 语法
│   ├── semantics.v         # 操作语义
│   └── tactics.v           # 证明策略
├── logic/                   # 逻辑
│   ├── iris_extra/         # Iris扩展
│   ├── protocols.v         # 协议定义
│   └── borrow.v            # 借用逻辑
├── typing/                  # 类型系统
│   ├── types.v             # 类型定义
│   ├── type_interp.v       # 类型解释
│   └── send_sync.v         # Send/Sync验证
└── examples/                # 标准库验证
    ├── cell.v
    ├── refcell.v
    ├── rc.v
    ├── arc.v
    └── mutex.v
```

---

## 8. 理论意义

### 8.1 对Rust语言的影响

1. **Unsafe代码指导**：明确了unsafe代码需要维护的不变量
2. **标准库审查**：发现了若干潜在问题（后续已修复）
3. **类型系统信心**：为Rust的内存安全声明提供了数学基础

### 8.2 对形式化方法的贡献

1. **分离逻辑应用**：展示了分离逻辑验证真实语言的能力
2. **Iris框架验证**：验证了一个重要的并发逻辑框架
3. **方法学贡献**：高阶协议 + 幽灵状态的模式

---

## 9. 局限性与后续工作

**RustBelt的局限性**：

1. **覆盖范围**：只验证了核心库的一部分
2. **Unsafe代码**：需要人工编写规范
3. **自动化程度**：证明过程需要大量人工干预
4. **语言特性**：一些高级特性（如async/await）未覆盖

**后续工作**：

1. **RustBelt-reloaded**：改进的模型和更多验证
2. **Stacked Borrows**：别名规则形式化
3. **Tree Borrows**：改进的别名模型
4. **Aeneas**：针对safe Rust的自动化验证工具

---

## 参考

1. [RustBelt Paper](https://plv.mpi-sws.org/rustbelt/popl18/) - 原始论文
2. [RustBelt Coq代码](https://gitlab.mpi-sws.org/iris/lambda-rust) - 完整形式化
3. [Iris Project](https://iris-project.org/) - 分离逻辑框架
4. [Stacked Borrows](https://plv.mpi-sws.org/rustbis/stacked-borrows/) - 别名模型

---

*RustBelt是Rust形式化验证领域的里程碑工作，为理解和验证Rust的内存安全保证提供了坚实的理论基础。*
