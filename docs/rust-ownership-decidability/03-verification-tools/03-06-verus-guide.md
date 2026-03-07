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
  - [2. 安装与配置](#2-安装与配置)
    - [2.1 快速安装](#21-快速安装)
    - [2.2 项目结构](#22-项目结构)
    - [2.3 基本用法](#23-基本用法)
  - [3. 规范系统](#3-规范系统)
    - [3.1 基本规范宏](#31-基本规范宏)
    - [3.2 ensures、requires、invariant](#32-ensuresrequiresinvariant)
    - [3.3 证明块（proof blocks）](#33-证明块proof-blocks)
  - [4. 所有权与验证](#4-所有权与验证)
    - [4.1 借用规则验证](#41-借用规则验证)
    - [4.2 幽灵类型（Ghost Types）](#42-幽灵类型ghost-types)
  - [5. 证明技术](#5-证明技术)
    - [5.1 归纳证明](#51-归纳证明)
    - [5.2 量化与 forall](#52-量化与-forall)
    - [5.3 线性幽灵状态](#53-线性幽灵状态)
  - [6. 实战示例](#6-实战示例)
    - [6.1 验证 Vec 操作](#61-验证-vec-操作)
    - [6.2 链表操作验证](#62-链表操作验证)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 规范设计原则](#71-规范设计原则)
    - [7.2 调试验证失败](#72-调试验证失败)
    - [7.3 常见陷阱](#73-常见陷阱)
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
```

### 1.2 设计哲学

| 方面 | 说明 |
|:---|:---|
| **零开销** | 规范在编译后完全擦除 |
| **自动化** | 大部分证明自动完成 |
| **可组合** | 支持模块化验证 |
| **实用** | 针对真实系统代码设计 |

### 1.3 验证能力范围

- ✅ **算术与位运算**: 整数、位操作
- ✅ **数据结构**: 数组、向量、链表
- ✅ **指针与引用**: 所有权验证
- ✅ **循环与递归**: 自动归纳
- ✅ **不安全代码**: 实验性支持

---

## 2. 安装与配置

### 2.1 快速安装

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

### 2.2 项目结构

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

### 2.3 基本用法

```bash
# 验证单个文件
verus src/main.rs

# 验证包
verus --crate-type lib src/lib.rs

# 生成 SMT 日志（调试用）
verus --multiple-errors 5 src/main.rs
```

---

## 3. 规范系统

### 3.1 基本规范宏

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

### 3.2 ensures、requires、invariant

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

### 3.3 证明块（proof blocks）

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

## 4. 所有权与验证

### 4.1 借用规则验证

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

### 4.2 幽灵类型（Ghost Types）

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

## 5. 证明技术

### 5.1 归纳证明

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

### 5.2 量化与 forall

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

### 5.3 线性幽灵状态

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

## 6. 实战示例

### 6.1 验证 Vec 操作

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

### 6.2 链表操作验证

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

---

## 7. 最佳实践

### 7.1 规范设计原则

```rust
verus! {

// ✅ 好的规范：精确且可验证
fn well_specified_sqrt(x: u64) -> (r: u64)
    requires x < 1000000  // 明确的输入约束
    ensures
        r * r <= x,
        (r + 1) * (r + 1) > x,
{
    // 实现...
    0
}

// ❌ 差的规范：过于模糊或无法验证
fn poorly_specified(x: u64) -> u64
    requires x > 0
    ensures result > 0  // 太弱，无法捕获正确性
{
    x
}

} // verus!
```

### 7.2 调试验证失败

```bash
# 查看详细错误信息
verus --multiple-errors 10 src/main.rs

# 导出 SMT 查询（高级调试用）
verus --export-smtlib queries.smt2 src/main.rs

# 使用 recommend 模式获取建议
verus --recommend src/main.rs
```

### 7.3 常见陷阱

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

} // verus!
```

---

## 参考

- [Verus GitHub](https://github.com/verus-lang/verus)
- [Verus 教程](https://verus-lang.github.io/verus/guide/)
- [Verus 标准库 (vstd)](https://verus-lang.github.io/verus/vstd/)

---

*文档版本: 1.0.0* | *Verus 版本: 0.1.x*
