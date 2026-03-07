# Verus 用户指南

> **Verus**: 用于验证 Rust 系统代码正确性的工具
> **难度**: 🟡 中级 → 🔴 高级
> **状态**: 积极开发中，Rust 1.94+ 支持良好

---

## 目录

- [Verus 用户指南](#verus-用户指南)
  - [目录](#目录)
  - [1. Verus 简介](#1-verus-简介)
    - [1.1 什么是 Verus](#11-什么是-verus)
    - [1.2 设计哲学](#12-设计哲学)
    - [1.3 验证能力范围](#13-验证能力范围)
  - [2. Verus 的工作原理](#2-verus-的工作原理)
    - [2.1 架构概述](#21-架构概述)
    - [2.2 验证流程](#22-验证流程)
    - [2.3 SMT 求解器集成](#23-smt-求解器集成)
  - [3. 形式化基础](#3-形式化基础)
    - [3.1 规范的形式化语义](#31-规范的形式化语义)
    - [3.2 所有权与分离逻辑](#32-所有权与分离逻辑)
    - [3.3 验证条件生成](#33-验证条件生成)
  - [4. 安装与配置](#4-安装与配置)
    - [4.1 快速安装](#41-快速安装)
    - [4.2 项目结构](#42-项目结构)
    - [4.3 基本用法](#43-基本用法)
  - [5. 规范系统](#5-规范系统)
    - [5.1 基本规范宏](#51-基本规范宏)
    - [5.2 ensures、requires、invariant](#52-ensuresrequiresinvariant)
    - [5.3 证明块（proof blocks）](#53-证明块proof-blocks)
  - [6. 所有权与验证](#6-所有权与验证)
    - [6.1 借用规则验证](#61-借用规则验证)
    - [6.2 幽灵类型（Ghost Types）](#62-幽灵类型ghost-types)
  - [7. 证明技术](#7-证明技术)
    - [7.1 归纳证明](#71-归纳证明)
    - [7.2 量化与 forall](#72-量化与-forall)
    - [7.3 线性幽灵状态](#73-线性幽灵状态)
  - [8. 实战示例](#8-实战示例)
    - [8.1 验证 Vec 操作](#81-验证-vec-操作)
    - [8.2 链表操作验证](#82-链表操作验证)
    - [8.3 排序算法验证](#83-排序算法验证)
  - [9. Verus 与其他工具对比](#9-verus-与其他工具对比)
  - [10. 最佳实践与常见陷阱](#10-最佳实践与常见陷阱)
    - [10.1 最佳实践](#101-最佳实践)
  - [11. 限制与未来发展](#11-限制与未来发展)
    - [当前限制](#当前限制)
    - [未来发展方向](#未来发展方向)
  - [参考](#参考)

---

## 1. Verus 简介

### 1.1 什么是 Verus

Verus 是由 VMware Research 开发的 Rust 验证工具，专注于**系统级代码**的功能正确性验证。

```
Verus 特点:
- 原生 Rust 语法（规范用宏嵌入）
- 分离证明代码与执行代码
- 基于 Z3 SMT 求解器
- 支持不安全代码验证（实验性）
- 零运行时开销（规范完全擦除）
```

**与其他验证工具的关键区别：**

Verus 设计用于验证**真实世界的系统代码**，如操作系统、文件系统、网络协议等。它通过将 Rust 代码和规范转换为 SMT-LIB 格式，利用 Z3 求解器进行自动验证。

### 1.2 设计哲学

| 方面 | 说明 |
|:---|:---|
| **零开销** | 规范在编译后完全擦除，不影响运行时性能 |
| **自动化** | 大部分证明自动完成，减少手动干预 |
| **可组合** | 支持模块化验证，函数可独立验证 |
| **实用** | 针对真实系统代码设计，支持 unsafe 代码 |
| **原生集成** | 规范嵌入在 Rust 代码中，无需外部规范语言 |

### 1.3 验证能力范围

- ✅ **算术与位运算**: 整数、位操作、位向量
- ✅ **数据结构**: 数组、向量、链表、树
- ✅ **指针与引用**: 所有权验证、借用检查
- ✅ **循环与递归**: 自动归纳、循环不变式
- ✅ **不安全代码**: 实验性支持，可验证原始指针操作
- ✅ **并发**: 支持原子操作验证
- ✅ **幽灵状态**: 线性幽灵类型、权限追踪

---

## 2. Verus 的工作原理

### 2.1 架构概述

```
┌─────────────────────────────────────────────────────────────────┐
│                        Verus 架构                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   Rust 源码 + 规范      ┌─────────────┐     ┌─────────────┐     │
│   (verus! 宏内)   ───→ │  Verus 前端  │ ──→ │ VIR (中间)  │     │
│                        └─────────────┘     └──────┬──────┘     │
│                                                    ↓            │
│                                             ┌─────────────┐     │
│                                             │  SMT-LIB    │     │
│                                             │  转换       │     │
│                                             └──────┬──────┘     │
│                                                    ↓            │
│                                             ┌─────────────┐     │
│                                             │  Z3 Solver  │     │
│                                             └──────┬──────┘     │
│                                                    ↓            │
│                                          ┌─────────────────┐    │
│                                          │  验证结果       │    │
│                                          │  ✅ VERIFIED    │    │
│                                          │  ❌ FAILED      │    │
│                                          └─────────────────┘    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 验证流程

Verus 的验证流程分为以下几个阶段：

1. **解析阶段**: 使用 Rust 编译器解析源码，提取 MIR
2. **规范提取**: 从 `verus!` 宏中提取规范注解
3. **VIR 生成**: 生成 Verus Intermediate Representation
4. **VC 生成**: 生成验证条件 (Verification Conditions)
5. **SMT 编码**: 将 VC 编码为 SMT-LIB 格式
6. **求解验证**: 使用 Z3 求解器验证

### 2.3 SMT 求解器集成

Verus 使用 Z3 作为后端求解器，支持以下理论：

| 理论 | 用途 | 示例 |
|:---|:---|:---|
| **QF_UFLIA** | 线性整数算术 | `x + y > 0` |
| **QF_UFBV** | 位向量 | `x & 0xFF` |
| **QF_AUFLIA** | 数组理论 | `arr[i]` |
| **Quantifiers** | 量词推理 | `forall(\|i\| ...)` |

---

## 3. 形式化基础

### 3.1 规范的形式化语义

Verus 中的规范可以形式化为**霍尔三元组 (Hoare Triple)**：

$$
\\{P\\}\ C\ \\{Q\\}
$$

其中：

- $P$: 前置条件 (requires)
- $C$: 程序代码
- $Q$: 后置条件 (ensures)

**定义 3.1 (函数规范)**

函数 $f$ 的规范是一个元组 $(Pre_f, Post_f)$，其中：

$$
Pre_f: Input \rightarrow \mathbb{B} \\
Post_f: Input \times Output \rightarrow \mathbb{B}
$$

**示例：**

```rust
fn divide(x: int, y: int) -> (r: int)
    requires y != 0           // Pre(x, y) := (y ≠ 0)
    ensures r * y == x        // Post(x, y, r) := (r × y = x)
```

### 3.2 所有权与分离逻辑

Verus 将 Rust 的所有权系统编码为**分离逻辑 (Separation Logic)**：

**定义 3.2 (所有权断言)**

对于资源 $r$，所有权断言记为 $Own(r)$：

$$
Own(r) ::= \\
\quad \top \quad \text{(无资源)} \\
\quad x \mapsto v \quad \text{(独占所有权)} \\
\quad Own(r_1) * Own(r_2) \quad \text{(分离合取)}
$$

**定理 3.1 (所有权唯一性)**

在任意程序点，若 $Own(x)$ 成立，则不存在其他活跃的 $Own'(x)$：

$$
\vdash Own(x) \Rightarrow \neg\exists Own': Own'(x) \land Own' \neq Own
$$

### 3.3 验证条件生成

**定义 3.3 (验证条件)**

对于程序 $P$ 和规范 $(Pre, Post)$，验证条件 $VC$ 定义为：

$$
VC(P, Pre, Post) := \forall \sigma: Pre(\sigma) \Rightarrow WP(P, Post)(\sigma)
$$

其中 $WP$ 是**最弱前置条件 (Weakest Precondition)** 函数。

**定理 3.2 (验证正确性)**

若 $VC(P, Pre, Post)$ 可被 SMT 求解器证明，则程序 $P$ 满足规范：

$$
\text{SMT}(VC(P, Pre, Post)) = \text{SAT} \Rightarrow \\{Pre\\}\ P\ \\{Post\\}
$$

---

## 4. 安装与配置

### 4.1 快速安装

```bash
# 克隆 Verus 仓库
git clone https://github.com/verus-lang/verus.git
cd verus

# 构建 Verus
source tools/activate
vargo build --release

# 添加到 PATH
export PATH="$PWD/source/target/release:$PATH"
```

### 4.2 项目结构

```
my-verus-project/
├── Cargo.toml          # 标准 Cargo 配置
├── rust-toolchain.toml # 指定 Rust 版本
└── src/
    └── main.rs         # 使用 verus! 宏
```

```toml
# rust-toolchain.toml
[toolchain]
channel = "1.79.0"  # 使用 Verus 支持的版本
components = ["rustc", "cargo", "rust-src", "rust-std"]
```

### 4.3 基本用法

```bash
# 验证单个文件
verus src/main.rs

# 验证包
verus --crate-type lib src/lib.rs

# 生成 SMT 日志（调试用）
verus --multiple-errors 5 src/main.rs

# 导出 SMT 查询
verus --export-smtlib queries.smt2 src/main.rs
```

---

## 5. 规范系统

### 5.1 基本规范宏

```rust
use vstd::prelude::*;

verus! {

/// 带有规范的函数
fn add(a: int, b: int) -> (result: int)
    ensures result == a + b
{
    a + b
}

/// 前置与后置条件
fn divide(numerator: int, denominator: int) -> (result: int)
    requires denominator != 0  // 前置条件
    ensures result * denominator == numerator  // 后置条件（近似）
{
    numerator / denominator
}

} // verus!
```

### 5.2 ensures、requires、invariant

```rust
verus! {

/// 数组查找
fn find(arr: &[u32], key: u32) -> (idx: usize)
    requires
        arr.len() > 0,
        exists(|i: int| 0 <= i < arr.len() && arr[i] == key),
    ensures
        idx < arr.len(),
        arr[idx as int] == key,
{
    let mut i = 0;

    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall(|j: int| 0 <= j < i ==> arr[j] != key),
    {
        if arr[i] == key {
            return i;
        }
        i += 1;
    }

    // 由于前置条件保证存在，不会执行到这里
    proof { unreachable(); }
    0
}

} // verus!
```

### 5.3 证明块（proof blocks）

```rust
verus! {

fn binary_search(v: &[u64], needle: u64) -> (result: usize)
    requires
        forall(|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]),
        v.len() > 0,
        exists(|i: int| 0 <= i < v.len() && v[i] == needle),
    ensures
        result < v.len(),
        v[result as int] == needle,
{
    let mut lo = 0usize;
    let mut hi = v.len();

    while lo < hi
        invariant
            0 <= lo <= hi <= v.len(),
            exists(|i: int| lo <= i < hi && v[i] == needle),
    {
        let mid = lo + (hi - lo) / 2;

        if v[mid] == needle {
            return mid;
        } else if v[mid] < needle {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    proof { unreachable(); }
    0
}

} // verus!
```

---

## 6. 所有权与验证

### 6.1 借用规则验证

```rust
verus! {

/// 安全的交换函数
fn swap<T>(a: &mut T, b: &mut T)
    ensures
        *a == old(*b),
        *b == old(*a),
{
    std::mem::swap(a, b);
}

/// 唯一引用保证
fn unique_borrow(arr: &mut [u32], i: usize, j: usize)
    requires
        i < arr.len(),
        j < arr.len(),
        i != j,  // 确保不重叠
    ensures
        arr[i as int] == old(arr[j as int]),
        arr[j as int] == old(arr[i as int]),
{
    let temp = arr[i];
    arr.set(i, arr[j]);
    arr.set(j, temp);
}

} // verus!
```

### 6.2 幽灵类型（Ghost Types）

```rust
use vstd::ghost::Ghost;

verus! {

/// 使用幽灵状态追踪
struct Counter {
    val: u64,
    ghost history: Seq<u64>,  // 幽灵序列，运行时擦除
}

impl Counter {
    fn new() -> (c: Self)
        ensures c.val == 0
    {
        Counter {
            val: 0,
            history: Ghost::new(Seq::empty()),
        }
    }

    fn increment(&mut self)
        ensures
            self.val == old(self.val) + 1,
            self.history == old(self.history).push(self.val as int),
    {
        self.val += 1;
        proof {
            self.history = Ghost::new(self.history@.push(self.val as int));
        }
    }
}

} // verus!
```

---

## 7. 证明技术

### 7.1 归纳证明

```rust
verus! {

/// 递归函数及其规范
proof fn factorial_spec(n: nat) -> (res: nat)
    decreases n
    ensures res == spec_factorial(n)
{
    if n == 0 {
        1
    } else {
        n * factorial_spec((n - 1) as nat)
    }
}

spec fn spec_factorial(n: nat) -> nat {
    if n == 0 { 1 } else { n * spec_factorial((n - 1) as nat) }
}

/// 循环实现的阶乘（带证明）
fn factorial_iter(n: u64) -> (res: u64)
    requires n <= 20  // 防止溢出
    ensures res == spec_factorial(n as nat)
{
    let mut i = 0u64;
    let mut acc = 1u64;

    while i < n
        invariant
            0 <= i <= n,
            acc == spec_factorial(i as nat),
    {
        i += 1;
        acc *= i;
    }

    acc
}

} // verus!
```

### 7.2 量化与 forall

```rust
verus! {

/// 数组所有元素满足性质
fn all_positive(arr: &[i32]) -> (b: bool)
    ensures b == forall(|i: int| 0 <= i < arr.len() ==> arr[i] > 0)
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall(|j: int| 0 <= j < i ==> arr[j] > 0),
    {
        if arr[i] <= 0 {
            return false;
        }
        i += 1;
    }
    true
}

/// 存在性证明
fn has_zero(arr: &[i32]) -> (b: bool)
    ensures b == exists(|i: int| 0 <= i < arr.len() && arr[i] == 0)
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall(|j: int| 0 <= j < i ==> arr[j] != 0),
    {
        if arr[i] == 0 {
            return true;
        }
        i += 1;
    }
    false
}

} // verus!
```

### 7.3 线性幽灵状态

```rust
use vstd::linear::Linear;

verus! {

/// 线性令牌模式
struct Permission {
    ghost id: int,
}

struct Resource {
    data: u64,
    ghost perm: Ghost<Permission>,
}

impl Resource {
    fn new() -> (r: Self)
        ensures r.perm@.id == r.data as int
    {
        Resource {
            data: 0,
            perm: Ghost::new(Permission { id: 0 }),
        }
    }

    fn update(&mut self, new_val: u64, Ghost(perm): Ghost<Permission>)
        requires perm.id == old(self).data as int
        ensures self.perm@.id == new_val as int
    {
        self.data = new_val;
        proof {
            self.perm = Ghost::new(Permission { id: new_val as int });
        }
    }
}

} // verus!
```

---

## 8. 实战示例

### 8.1 验证 Vec 操作

```rust
verus! {

/// 安全的 push 操作验证
proof fn vec_push_spec<T>(v: &mut Vec<T>, elem: T)
    ensures
        v.len() == old(v).len() + 1,
        v.last() == Some(elem),
{
    v.push(elem);
}

/// 过滤操作验证
fn filter_positive(v: &[i32]) -> (result: Vec<i32>)
    ensures
        result.len() <= v.len(),
        forall(|i: int| 0 <= i < result.len() ==> result[i] > 0),
        forall(|i: int| 0 <= i < result.len() ==>
            exists(|j: int| 0 <= j < v.len() && v[j] == result[i])),
{
    let mut res = Vec::new();
    let mut i = 0;

    while i < v.len()
        invariant
            0 <= i <= v.len(),
            res.len() <= i,
            forall(|k: int| 0 <= k < res.len() ==> res[k] > 0),
    {
        if v[i] > 0 {
            res.push(v[i]);
        }
        i += 1;
    }

    res
}

} // verus!
```

### 8.2 链表操作验证

```rust
verus! {

struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T> Node<T> {
    fn len(&self) -> (n: usize)
        ensures n >= 1
    {
        match &self.next {
            None => 1,
            Some(next) => 1 + next.len(),
        }
    }
}

/// 链表查找
fn list_find(head: &Node<u64>, target: u64) -> (found: bool)
    ensures found == exists(|n: &Node<u64>| n.data == target)
{
    let mut current = head;

    loop
        invariant current.data == head.data || /* ... */
    {
        if current.data == target {
            return true;
        }
        match &current.next {
            None => return false,
            Some(next) => current = next,
        }
    }
}

} // verus!
```

### 8.3 排序算法验证

```rust
verus! {

/// 插入排序验证
fn insertion_sort(arr: &mut [i32])
    ensures
        is_sorted(arr),
        permutation(old(arr), arr),
{
    let mut i = 1;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            is_sorted(&arr[0..i]),
            permutation(old(arr), arr),
    {
        let mut j = i;
        while j > 0 && arr[j-1] > arr[j]
            invariant
                0 <= j <= i,
                is_sorted(&arr[0..j]),
                is_sorted(&arr[j..i+1]),
        {
            arr.swap(j-1, j);
            j -= 1;
        }
        i += 1;
    }
}

#[pure]
fn is_sorted(arr: &[i32]) -> bool {
    forall(|i: int, j: int|
        0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    )
}

#[pure]
fn permutation(a: &[i32], b: &[i32]) -> bool {
    a.len() == b.len() &&
    forall(|x: i32| count(a, x) == count(b, x))
}

#[pure]
fn count(arr: &[i32], value: i32) -> usize {
    let mut c = 0;
    for i in 0..arr.len() {
        if arr[i] == value {
            c += 1;
        }
    }
    c
}

} // verus!
```

---

## 9. Verus 与其他工具对比

| 特性 | Verus | Miri | Kani | Prusti | Creusot |
|:---|:---|:---|:---|:---|:---|
| **验证方法** | SMT + 规范 | 解释执行 | 模型检测 | 分离逻辑 | 定理证明 |
| **自动化程度** | 高 | 全自动 | 全自动 | 中高 | 中等 |
| **规范位置** | 代码内 (宏) | N/A | 代码内 (属性) | 属性注解 | 代码内 |
| **循环处理** | 不变式 | 直接执行 | 展开 | 不变式 | 不变式 |
| **幽灵状态** | ✅ 完整支持 | ❌ | ❌ | ⚠️ 有限 | ✅ |
| **递归证明** | ✅ decreases | N/A | 展开限制 | 有限 | ✅ |
| **并发验证** | ⚠️ 基础 | ✅ 数据竞争 | ⚠️ 原子操作 | ❌ | ❌ |
| **Unsafe 支持** | ⚠️ 实验性 | ✅ 完整 | ⚠️ 部分 | ❌ | ❌ |
| **标准库** | vstd | 完整 | 部分 | 有限 | 有限 |
| **性能开销** | 零（擦除） | 10-100x | 高 | 零 | 零 |
| **学习曲线** | 中等 | 低 | 中等 | 中等 | 高 |

**选择建议：**

- **Verus**: 验证系统级代码、需要幽灵状态追踪、追求零开销
- **Miri**: 检测 unsafe 代码 UB、运行时内存问题
- **Kani**: 穷举状态空间、验证算法属性
- **Prusti**: 验证前置/后置条件合约、分离逻辑推理
- **Creusot**: 需要完整的功能正确性证明

---

## 10. 最佳实践与常见陷阱

### 10.1 最佳实践

```markdown
1. **渐进式规范**: 从简单属性开始，逐步增加复杂度
   ```rust
   // 第一步：基本类型安全
   fn step1(x: u64) -> (r: u64)
       ensures r >= 0

   // 第二步：添加功能规范
   fn step2(x: u64) -> (r: u64)
       requires x < 1000000
       ensures r * r <= x < (r+1) * (r+1)
   ```

1. **合理设计循环不变式**: 覆盖所有变化的变量

   ```rust
   while i < n
       invariant
           0 <= i <= n,           // 边界
           acc == factorial(i),   // 累加器性质
           // 确保后置条件可被推导
   ```

2. **使用 spec 函数**: 将复杂规范抽象为可重用函数

   ```rust
   spec fn is_valid_state(s: &State) -> bool { ... }
   ```

3. **分离证明代码**: 使用 proof 块组织复杂证明

   ```rust
   proof {
       // 辅助证明步骤
       assert_by(...);
   }
   ```

```

### 10.2 常见陷阱

```rust
verus! {

// 陷阱1：忘记循环不变式
fn infinite_loop() {
    let mut i = 0;
    while i < 10  // 错误：缺少不变式
    {
        i += 1;
    }
}

// 修正
fn fixed_loop() {
    let mut i = 0;
    while i < 10
        invariant 0 <= i <= 10
    {
        i += 1;
    }
}

// 陷阱2：整数溢出
fn overflow_risk(x: u64) -> u64 {
    x + 1  // 可能溢出！
}

// 修正
fn no_overflow(x: u64) -> (r: u64)
    requires x < u64::MAX
    ensures r == x + 1
{
    x + 1
}

// 陷阱3：量词触发问题
fn quantifier_issue(arr: &[i32]) -> bool {
    // 复杂量词可能使 Z3 无法求解
    forall(|i: int, j: int, k: int|
        0 <= i < j < k < arr.len() ==>
        arr[i] + arr[j] > arr[k]
    )
}

// 修正：简化量词或添加触发器
fn quantifier_fixed(arr: &[i32]) -> bool {
    forall(|i: int| 0 <= i < arr.len() ==>
        exists(|j: int| j > i && arr[j] > arr[i])
    )
}

// 陷阱4：递归无 decreases
proof fn bad_recursion(n: nat) -> nat {
    bad_recursion(n)  // 无限递归，无 decreases
}

// 修正
proof fn good_recursion(n: nat) -> nat
    decreases n  // 指定终止度量
{
    if n == 0 { 0 } else { good_recursion((n-1) as nat) }
}

} // verus!
```

---

## 11. 限制与未来发展

### 当前限制

| 限制 | 说明 | 解决方法 |
|:---|:---|:---|
| **并发验证** | 有限的并发支持 | 使用顺序化抽象 |
| **Unsafe 代码** | 实验性支持 | 封装为安全 API |
| **浮点数** | 支持有限 | 使用整数近似 |
| **外部 crate** | 需要 extern_spec | 手动添加规范 |
| **求解时间** | 复杂量词可能超时 | 简化规范 |

### 未来发展方向

1. **更好的并发支持**: 验证并发数据结构和算法
2. **完善 unsafe 支持**: 验证原始指针操作
3. **标准库扩展**: 更多 vstd 组件
4. **IDE 集成**: 更好的 VS Code 支持
5. **性能优化**: 更快的验证速度

---

## 参考

- [Verus GitHub](https://github.com/verus-lang/verus)
- [Verus 教程](https://verus-lang.github.io/verus/guide/)
- [Verus 标准库 (vstd)](https://verus-lang.github.io/verus/vstd/)
- [Z3 SMT Solver](https://github.com/Z3Prover/z3)
- [IronFleet 论文](https://www.microsoft.com/en-us/research/publication/ironfleet-proving-practical-distributed-systems-correct/)

---

*文档版本: 2.0.0* | *Verus 版本: 0.1.x* | *最后更新: 2026-03*
