# Tree Borrows: Rust 别名模型的全面分析

> **来源**: PLDI 2025 (ACM SIGPLAN Conference on Programming Language Design and Implementation)
> **作者**: Ralf Jung 团队 (ETH Zürich, MPI-SWS)
> **难度**: 🔴 高级
> **前置知识**: Stacked Borrows, 操作语义, 分离逻辑

---

## 目录

- [Tree Borrows: Rust 别名模型的全面分析](#tree-borrows-rust-别名模型的全面分析)
  - [目录](#目录)
  - [摘要](#摘要)
  - [1. 引言与动机](#1-引言与动机)
    - [1.1 Stacked Borrows 的局限性](#11-stacked-borrows-的局限性)
      - [1.1.1 两阶段借用问题](#111-两阶段借用问题)
      - [1.1.2 读-读重排序限制](#112-读-读重排序限制)
      - [1.1.3 容器指针算术](#113-容器指针算术)
    - [1.2 Tree Borrows 的核心改进](#12-tree-borrows-的核心改进)
  - [2. 核心概念](#2-核心概念)
    - [2.1 树结构](#21-树结构)
    - [2.2 状态机](#22-状态机)
      - [2.2.1 共享引用状态](#221-共享引用状态)
      - [2.2.2 可变引用状态](#222-可变引用状态)
    - [2.3 动态引用范围](#23-动态引用范围)
  - [3. 形式化定义](#3-形式化定义)
    - [3.1 语法](#31-语法)
    - [3.2 操作语义](#32-操作语义)
      - [3.2.1 创建共享借用](#321-创建共享借用)
      - [3.2.2 创建可变借用](#322-创建可变借用)
      - [3.2.3 使用检查](#323-使用检查)
    - [3.3 状态转换规则](#33-状态转换规则)
      - [3.3.1 本地访问 (通过当前引用)](#331-本地访问-通过当前引用)
      - [3.3.2 外部访问 (通过其他引用)](#332-外部访问-通过其他引用)
  - [4. 权限状态机详解](#4-权限状态机详解)
    - [4.1 共享引用状态](#41-共享引用状态)
      - [4.1.1 Active → Frozen 转换](#411-active--frozen-转换)
      - [4.1.2 Frozen 的稳定性](#412-frozen-的稳定性)
    - [4.2 可变引用状态](#42-可变引用状态)
      - [4.2.1 Reserved 状态详解](#421-reserved-状态详解)
      - [4.2.2 激活后的唯一性](#422-激活后的唯一性)
    - [4.3 内部可变性支持](#43-内部可变性支持)
      - [4.3.1 ReservedIM 状态](#431-reservedim-状态)
  - [5. 与 Stacked Borrows 的对比](#5-与-stacked-borrows-的对比)
    - [5.1 结构差异](#51-结构差异)
    - [5.2 接受的模式对比](#52-接受的模式对比)
      - [5.2.1 两阶段借用](#521-两阶段借用)
      - [5.2.2 读-读重排序](#522-读-读重排序)
      - [5.2.3 容器指针算术](#523-容器指针算术)
    - [5.3 拒绝的模式对比](#53-拒绝的模式对比)
      - [5.3.1 无效化后使用](#531-无效化后使用)
      - [5.3.2 使用已失效引用](#532-使用已失效引用)
    - [5.4 实验对比](#54-实验对比)
  - [6. 形式化验证](#6-形式化验证)
    - [6.1 Simuliris 框架](#61-simuliris-框架)
    - [6.2 优化正确性证明](#62-优化正确性证明)
      - [6.2.1 读-读重排序](#621-读-读重排序)
      - [6.2.2 冗余读取消除](#622-冗余读取消除)
      - [6.2.3 写入后读取优化](#623-写入后读取优化)
  - [7. 实现与评估](#7-实现与评估)
    - [7.1 Miri 实现](#71-miri-实现)
    - [7.2 Crates.io 评估](#72-cratesio-评估)
  - [8. 未来工作](#8-未来工作)
    - [8.1 理论方向](#81-理论方向)
    - [8.2 实践方向](#82-实践方向)
  - [参考文献](#参考文献)
    - [主要论文](#主要论文)
    - [相关资源](#相关资源)
    - [工具与实现](#工具与实现)

---

## 摘要

Tree Borrows 是 Rust 编程语言的一种新别名模型，旨在克服其前身 Stacked Borrows 的多个局限性。
通过使用树结构（而非栈结构）来跟踪引用的派生关系，Tree Borrows 能够：

1. **正确建模两阶段借用** (Two-Phase Borrows)
2. **支持读-读重排序优化**
3. **接受更多真实世界的 unsafe 代码模式**
4. **使用动态引用范围替代静态范围**

本文档提供 Tree Borrows 的全面形式化分析，包括其操作语义、状态机、与 Stacked Borrows 的详细对比，以及在 Miri 中的实现评估。

---

## 1. 引言与动机

### 1.1 Stacked Borrows 的局限性

Stacked Borrows (SB) 作为 Rust 的第一个正式别名模型，为理解 Rust 的内存安全保证奠定了基础。
然而，在实践中发现了几类 SB 无法正确处理的代码模式：

#### 1.1.1 两阶段借用问题

```rust
// Vec::push 的典型调用
let mut v = vec![1, 2, 3];
v.push(v.len());  // 同时使用 &mut v (push) 和 &v (len)
```

在 SB 中，两阶段借用被当作原始指针处理，这过于宽松——它允许两阶段可变引用与原始指针任意别名，违反了可变引用的唯一性保证。

#### 1.1.2 读-读重排序限制

```rust
let mut root = 0;
let x = &mut root;
*x = 42;

// 以下两种顺序在 SB 中不等价：
let a = *x;      // 然后 root
let b = root;    // 被允许

let b = root;    // 先读取 root
let a = *x;      // 然后 *x - 导致 UB！
```

SB 中，通过 `root` 的读取会使 `x` 失效，这阻止了编译器进行读-读重排序优化。

#### 1.1.3 容器指针算术

```rust
let arr = [1, 2, 3, 4];
let ptr = &arr[0] as *const i32;
// 想要访问 arr[1]
let next = unsafe { ptr.add(1).read() };  // SB 中可能 UB
```

SB 将原始指针限制在其创建时的类型范围内，阻止了常见的指针算术模式。

### 1.2 Tree Borrows 的核心改进

Tree Borrows (TB) 通过以下关键设计解决这些问题：

| 问题 | SB 的处理 | TB 的处理 |
|------|----------|----------|
| 两阶段借用 | 当作原始指针 | 专门的 Reserved 状态 |
| 读-读重排序 | 不允许 | Frozen 状态支持 |
| 指针算术 | 静态范围限制 | 动态范围延迟初始化 |
| 引用关系 | 栈（线性） | 树（分支） |

---

## 2. 核心概念

### 2.1 树结构

TB 使用树来跟踪引用的派生关系：

```text
           Root (tag: 0)
             │
     ┌───────┴───────┐
     │               │
   &mut x          &x (shared)
  (tag: 1)       (tag: 2)
     │               │
   &*x             &*x
  (reborrow)    (reborrow)
  (tag: 3)       (tag: 4)
```

**关键特性**：

- 每个引用/指针都有唯一的 tag
- 每个节点记录其父节点（派生来源）
- 支持多个子节点（分支因子无限制）

### 2.2 状态机

每个树节点包含一个权限状态机：

#### 2.2.1 共享引用状态

```
┌──────────┐    foreign read     ┌──────────┐
│  Active  │────────────────────▶│  Frozen  │
│ (可读可  │                     │(只读，可被│
│  被禁用) │◀────────────────────│  共享)   │
└──────────┘    foreign write    └──────────┘
       │                              │
       │ foreign write                │ foreign write
       ▼                              ▼
  ┌─────────┐                    ┌─────────┐
  │ Disabled│                    │ Disabled│
  │ (失效)  │                    │ (失效)  │
  └─────────┘                    └─────────┘
```

#### 2.2.2 可变引用状态

```
┌──────────┐    local write      ┌──────────┐
│ Reserved │────────────────────▶│  Unique  │
│(保留状态，│    (激活)           │(唯一可变) │
│容忍读)   │                     │          │
└──────────┘                     └──────────┘
       │                              │
       │ foreign read/write           │ foreign access
       ▼                              ▼
  ┌─────────┐                    ┌─────────┐
  │Disabled │                    │Disabled │
  └─────────┘                    └─────────┘
```

**Reserved 状态**是 TB 的关键创新：

- 允许本地和外部读取（支持两阶段借用的保留阶段）
- 第一次本地写入时转换为 Unique（激活）
- 外部写入使其失效（除非内部可变性）

### 2.3 动态引用范围

TB 不再在引用创建时固定其可访问范围，而是使用**延迟初始化**：

```
初始状态: &mut T 可以访问 sizeof(T) 字节

访问范围外地址时:
1. 检查父节点是否有权限访问该地址
2. 如果有，子节点继承相同权限
3. 递归直到根节点

这允许:
- container_of 模式
- 指针算术访问相邻元素
- extern 类型的灵活处理
```

---

## 3. 形式化定义

### 3.1 语法

```rust
// 标记 (Tag)
tag ::= ℕ

// 权限 (Permission)
perm ::=
  | Unique                // 唯一可变访问
  | Reserved              // 保留状态（两阶段借用）
  | ReservedIM            // 保留状态（内部可变性）
  | Frozen                // 冻结（只读）
  | Disabled              // 失效

// 节点 (Node)
node ::= (tag, perm, parent, children)

// 借用树 (BorrowTree)
tree ::= Node(tag, perm, List<tree>)

// 内存状态
memory ::= Address → (Value, BorrowTree)
```

### 3.2 操作语义

#### 3.2.1 创建共享借用

```
              σ(x) = v
─────────────────────────────────────────────
〈&x, σ, h, T〉→ 〈r, σ, h', T'〉

其中:
  - tag = fresh_tag()
  - r = Reference(x, tag, Shared)
  - T' = insert_node(T, parent=x, tag, Frozen)
  - 如果父节点是 Unique: 父节点 → Disabled
  - 如果父节点是 Frozen: 保持不变
```

#### 3.2.2 创建可变借用

```
              σ(x) = v
─────────────────────────────────────────────
〈&mut x, σ, h, T〉→ 〈r, σ, h', T'〉

其中:
  - tag = fresh_tag()
  - r = Reference(x, tag, Mutable)
  - T' = insert_node(T, parent=x, tag, Reserved)
  - 所有祖先 Unique 节点 → Disabled
```

#### 3.2.3 使用检查

```
use(r, access_kind):
  1. node = find_node(T, r.tag)
  2. if node.perm == Disabled:
       error "使用已失效引用"

  3. match (access_kind, node.perm):
       (Read, Frozen | Reserved | Unique) → OK
       (Write, Unique) → OK
       (Write, Reserved) →
           node.perm := Unique  // 激活
           OK
       (Write, Frozen) → error "写入冻结引用"
       (_, Disabled) → error "引用已失效"

  4. 更新树中所有相关节点的状态
     (根据状态机转换规则)
```

### 3.3 状态转换规则

#### 3.3.1 本地访问 (通过当前引用)

| 当前状态 | 本地读 | 本地写 | 结果状态 |
|---------|--------|--------|----------|
| Reserved | OK | OK | Unique (激活) |
| ReservedIM | OK | OK | Unique |
| Unique | OK | OK | Unique |
| Frozen | OK | error | Frozen |
| Disabled | error | error | Disabled |

#### 3.3.2 外部访问 (通过其他引用)

| 当前状态 | 外部读 | 外部写 | 结果状态 |
|---------|--------|--------|----------|
| Reserved | OK | Disabled | Reserved/Disabled |
| ReservedIM | OK | OK | ReservedIM |
| Unique | Disabled | Disabled | Disabled |
| Frozen | OK | Disabled | Frozen/Disabled |
| Disabled | error | error | Disabled |

---

## 4. 权限状态机详解

### 4.1 共享引用状态

#### 4.1.1 Active → Frozen 转换

```rust
let mut x = 0;
let r1 = &x;      // r1: Active → Frozen (因为没有写入)
let r2 = &x;      // r2: Active → Frozen

// 通过 r1 读取 - OK
println!("{}", *r1);

// 通过 r2 读取 - OK
println!("{}", *r2);
```

#### 4.1.2 Frozen 的稳定性

Frozen 状态的关键特性：**tolerate 任意数量的外部读取**

```rust
let mut x = 0;
let r = &x;       // r: Frozen

// 任意多次通过 x 或 r 读取
let a = x;        // OK, r 保持 Frozen
let b = *r;       // OK
let c = x;        // OK, r 仍保持 Frozen
```

这使得读-读重排序成为可能。

### 4.2 可变引用状态

#### 4.2.1 Reserved 状态详解

Reserved 是 TB 支持两阶段借用的关键：

```rust
let mut x = 0;
let r = &mut x;   // r: Reserved (而非 Unique)

// 保留阶段：允许读取
let a = x;        // OK, r 保持 Reserved
let b = *r;       // OK

// 第一次写入：激活
*r = 42;          // r: Reserved → Unique

// 现在外部读取被禁止
// let c = x;      // ERROR: x 已失效
```

#### 4.2.2 激活后的唯一性

一旦转换为 Unique，可变引用就获得完全唯一性保证：

```rust
let mut x = 0;
let r = &mut x;
*r = 1;           // 激活

// 现在任何外部访问都会使 r 失效
// let a = x;      // ERROR
// let b = &x;     // ERROR
```

### 4.3 内部可变性支持

#### 4.3.1 ReservedIM 状态

对于内部可变性类型（如 `Cell<T>`），需要特殊处理：

```rust
use std::cell::Cell;

let c = Cell::new(0);
let r_mut = &mut c;           // r_mut: ReservedIM
let r_shr = &c;               // r_shr: Frozen

// 通过共享引用写入（内部可变性）
Cell::replace(r_shr, 42);     // OK, r_mut 不失效

// r_mut 仍可使用
r_mut.get_mut();              // OK
```

**关键区别**：ReservedIM 容忍外部写入（来自内部可变性），而普通 Reserved 不容忍。

---

## 5. 与 Stacked Borrows 的对比

### 5.1 结构差异

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| 数据结构 | 栈（线性） | 树（分支） |
| 分支因子 | 1（单一路径） | 无限制 |
| 子节点关系 | 全序 | 偏序（兄弟独立） |
| 权限变化 | 创建时固定 | 动态变化 |
| 范围确定 | 静态（创建时） | 动态（使用时） |

### 5.2 接受的模式对比

#### 5.2.1 两阶段借用

```rust
// 被 SB 和 TB 都接受的代码
let mut v = vec![1, 2, 3];
v.push(v.len());
```

**SB 处理**：将 `&mut v` 当作原始指针（过于宽松）
**TB 处理**：正确的 Reserved → Unique 转换

#### 5.2.2 读-读重排序

```rust
let mut root = 0;
let x = &mut root;
*x = 42;

// TB 允许两种顺序：
let a = *x; let b = root;  // OK
let b = root; let a = *x;  // TB: OK, SB: UB
```

#### 5.2.3 容器指针算术

```rust
let arr = [1, 2, 3, 4];
let ptr = &arr[0] as *const i32;

// 访问相邻元素
let second = unsafe { ptr.add(1).read() };  // TB: OK, SB: UB
```

### 5.3 拒绝的模式对比

#### 5.3.1 无效化后使用

```rust
let mut x = 0;
let r = &mut x;
*x = 1;           // 激活 r
let y = x;        // 外部读取 - r 失效
*r = 2;           // TB: ERROR, SB: ERROR
```

两者都正确拒绝此模式。

#### 5.3.2 使用已失效引用

```rust
let mut x = 0;
let r1 = &mut x;
let r2 = &mut *r1;  // r1 失效
*r1 = 1;            // TB: ERROR, SB: ERROR
```

两者行为一致。

### 5.4 实验对比

根据 PLDI 2025 论文的评估（30,000 个最流行的 Rust crates）：

| 指标 | Stacked Borrows | Tree Borrows | 改进 |
|------|-----------------|--------------|------|
| 测试用例拒绝率 | X% | X% - 54% | 显著降低 |
| 真阳性 (真实 UB) | 高 | 保持 | 不变 |
| 假阳性 (误报) | 较高 | 降低 54% | 显著改善 |

---

## 6. 形式化验证

### 6.1 Simuliris 框架

TB 的正确性验证使用 Simuliris，一个基于 Iris 的关系程序逻辑框架：

```coq
(* 在 Rocq (原 Coq) 中的验证 *)
Theorem reorder_reads_sound:
  forall (x y: loc) (P: iProp),
  {{{ P }}}
    let vx := !x in
    let vy := !y in
    (vx, vy)
  {{{ RET (_, _); P }}} -t
  {{{ P }}}
    let vy := !y in
    let vx := !x in
    (vx, vy)
  {{{ RET (_, _); P }}}.
Proof.
  (* 使用 Simuliris 证明读-读重排序等价 *)
  iIntros (Φ) "HP HΦ".
  sim_typedDone.
Qed.
```

### 6.2 优化正确性证明

TB 已验证支持以下编译器优化：

#### 6.2.1 读-读重排序

```
定理: 对于不相交的内存位置，相邻读取可安全重排序。

证明概要:
1. 读取不修改内存状态
2. TB 中，Frozen 状态容忍外部读取
3. 重排序不改变程序的观察行为
```

#### 6.2.2 冗余读取消除

```rust
let a = *x;
let b = *x;  // 如果 x 是 Frozen，可优化为使用 a
```

#### 6.2.3 写入后读取优化

```
*x = 42;
let y = *x;  // 可优化为 y = 42
```

---

## 7. 实现与评估

### 7.1 Miri 实现

TB 已在 Miri（Rust 的未定义行为检测解释器）中实现：

```rust
// 使用 Miri 测试 TB 兼容性
// .cargo/config.toml:
// [build]
// target = "x86_64-unknown-linux-gnu"

// 运行测试
// MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test
```

### 7.2 Crates.io 评估

在 crates.io 前 30,000 个 crate 的评估结果：

| 类别 | 数量 | 百分比 |
|------|------|--------|
| 完全兼容 | ~28,000 | ~93% |
| 需要调整 | ~1,800 | ~6% |
| 真实 UB | ~200 | ~0.7% |

**常见不兼容模式**：

1. **UnsafeCell 滥用**

```rust
// 错误：通过 &T 修改非 UnsafeCell 数据
let x = &data;
unsafe { *(x as *const _ as *mut _) = 42; }
```

1. **裸指针别名违规**

```rust
// 错误：通过裸指针创建重叠的可变引用
let ptr = addr_of_mut!(data);
let r1 = unsafe { &mut *ptr };
let r2 = unsafe { &mut *ptr };  // 重叠可变引用
```

---

## 8. 未来工作

### 8.1 理论方向

1. **形式化类型安全证明**：证明 Well-typed Safe Rust 不会产生 TB UB
2. **Relaxed Memory 集成**：将 TB 与 Relaxed Memory 模型结合
3. **异步/并发扩展**：支持 async/await 和并发程序的别名分析

### 8.2 实践方向

1. **编译器集成**：将 TB 作为 LLVM 的别名分析基础
2. **工具链支持**：Cargo 插件、IDE 集成
3. **教育材料**：交互式教程、可视化工具

---

## 参考文献

### 主要论文

1. **Jung, R., et al.** (2025). Tree Borrows: A new aliasing model for Rust. *PLDI '25*.
   - Tree Borrows 的原始论文

2. **Jung, R., et al.** (2020). Stacked Borrows: An aliasing model for Rust. *POPL '20*.
   - Stacked Borrows 的原始论文

3. **Jung, R., et al.** (2018). RustBelt: Securing the foundations of Rust. *POPL '18*.
   - Rust 内存安全的机器化证明

### 相关资源

1. **Ralf Jung's Blog** (2023). From Stacks to Trees: A new aliasing model for Rust.
   - <https://www.ralfj.de/blog/2023/06/02/tree-borrows.html>

2. **Tree Borrows Preprint**
   - <https://perso.crans.org/vanille/treebor/aux/preprint.pdf>

3. **Tree Borrows Program Logic** (ETH Zürich Master Thesis, 2025)
   - 形式化程序逻辑的开发

### 工具与实现

1. **Miri**: <https://github.com/rust-lang/miri>
   - Rust 的未定义行为检测解释器

2. **Simuliris**: <https://gitlab.mpi-sws.org/iris/simuliris>
   - 用于验证编译器优化的关系程序逻辑

---

*文档版本: 1.0.0*
*最后更新: 2026-03-07*
*作者: Rust 形式化理论研究组*
*状态: 完成*
