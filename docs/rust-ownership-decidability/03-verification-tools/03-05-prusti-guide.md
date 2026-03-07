# Prusti 用户指南

> **Prusti**: 基于 Viper 的 Rust 前置-后置条件验证工具
> **难度**: 🟡 中级 → 🔴 高级
> **要求**: Rust 1.70+ (Prusti 对最新 Rust 版本支持有限)

---

## 目录

- [Prusti 用户指南](#prusti-用户指南)
  - [目录](#目录)
  - [1. Prusti 简介](#1-prusti-简介)
    - [1.1 什么是 Prusti](#11-什么是-prusti)
    - [1.2 与 Miri/Kani 的区别](#12-与-mirikani-的区别)
    - [1.3 核心能力](#13-核心能力)
  - [2. 安装与配置](#2-安装与配置)
    - [2.1 VS Code 扩展（推荐）](#21-vs-code-扩展推荐)
    - [2.2 命令行安装](#22-命令行安装)
    - [2.3 Cargo 项目配置](#23-cargo-项目配置)
  - [3. 核心概念](#3-核心概念)
    - [3.1 前置条件与后置条件](#31-前置条件与后置条件)
    - [3.2 断言](#32-断言)
    - [3.3 纯函数](#33-纯函数)
  - [4. 规范注解](#4-规范注解)
    - [4.1 谓词（Predicates）](#41-谓词predicates)
    - [4.2 循环不变式](#42-循环不变式)
    - [4.3 旧值表达式](#43-旧值表达式)
  - [5. 验证示例](#5-验证示例)
    - [5.1 二分查找验证](#51-二分查找验证)
    - [5.2 栈的实现与验证](#52-栈的实现与验证)
  - [6. 高级特性](#6-高级特性)
    - [6.1 幽灵变量](#61-幽灵变量)
    - [6.2 外部函数规范](#62-外部函数规范)
    - [6.3 类型不变式](#63-类型不变式)
  - [7. 限制与解决方案](#7-限制与解决方案)
    - [7.1 已知限制](#71-已知限制)
    - [7.2 常见错误与解决](#72-常见错误与解决)
    - [7.3 调试验证失败](#73-调试验证失败)
  - [参考](#参考)

---

## 1. Prusti 简介

### 1.1 什么是 Prusti

Prusti 是一个**静态验证工具**，使用分离逻辑（Separation Logic）验证 Rust 代码的功能正确性。

```
Prusti 工作流程:
Rust 代码 + 规范注解 → Prusti → Viper → Z3 SMT → 验证结果
```

### 1.2 与 Miri/Kani 的区别

| 工具 | 验证类型 | 自动化 | 适用场景 |
|:---|:---|:---|:---|
| Miri | 运行时 UB 检测 | 全自动 | 未定义行为 |
| Kani | 模型检测 | 全自动 | 状态空间探索 |
| Creusot | 定理证明 | 半自动 | 功能正确性 |
| **Prusti** | **合约验证** | **半自动** | **前后条件** |

### 1.3 核心能力

- ✅ **前置/后置条件**: `@requires`, `@ensures`
- ✅ **循环不变式**: `@invariant`
- ✅ **断言**: `@assert`
- ✅ **纯函数**: `@pure`
- ✅ **可信函数**: `@trusted`

---

## 2. 安装与配置

### 2.1 VS Code 扩展（推荐）

```bash
# 安装 Prusti VS Code 扩展
# 1. 打开 VS Code
# 2. 进入扩展市场
# 3. 搜索 "Prusti"
# 4. 安装 "Prusti Assistant"
```

### 2.2 命令行安装

```bash
# 克隆 Prusti 仓库
git clone https://github.com/viperproject/prusti-dev.git
cd prusti-dev

# 安装（需要 Rust nightly）
rustup component add rustc-dev llvm-tools-preview
./x.py build
```

### 2.3 Cargo 项目配置

```toml
# Cargo.toml
[package]
name = "verified-project"
version = "0.1.0"
edition = "2021"

[dependencies]
# Prusti Contracts 库
prusti-contracts = { git = "https://github.com/viperproject/prusti-contracts.git" }
```

---

## 3. 核心概念

### 3.1 前置条件与后置条件

```rust
use prusti_contracts::*;

/// 计算绝对值
/// # Requires
/// 输入为 i32（自动边界）
/// # Ensures
/// 返回值 >= 0
/// 如果 x >= 0，返回 x；否则返回 -x
#[requires(x > i32::MIN)]  // 防止 -i32::MIN 溢出
#[ensures(result >= 0)]
#[ensures(if x >= 0 { result == x } else { result == -x })]
fn abs(x: i32) -> i32 {
    if x >= 0 { x } else { -x }
}
```

### 3.2 断言

```rust
#[ensures(result > 0)]
fn always_positive() -> i32 {
    let x = 42;
    prusti_assert!(x > 0);  // 编译时验证
    x
}
```

### 3.3 纯函数

```rust
/// 纯函数：无副作用，仅依赖输入
#[pure]
#[requires(x >= 0)]
#[ensures(result >= 0)]
fn sqrt_estimate(x: u32) -> u32 {
    (x as f64).sqrt() as u32
}
```

---

## 4. 规范注解

### 4.1 谓词（Predicates）

```rust
use prusti_contracts::*;

/// 定义链表节点
struct Node {
    value: i32,
    next: Option<Box<Node>>,
}

/// 递归谓词：链表已排序
#[predicate]
fn is_sorted(node: &Node) -> bool {
    match &node.next {
        None => true,
        Some(next) => node.value <= next.value && is_sorted(next),
    }
}

/// 链表长度谓词
#[predicate]
fn list_len(node: &Node, len: usize) -> bool {
    match &node.next {
        None => len == 1,
        Some(next) => list_len(next, len - 1),
    }
}
```

### 4.2 循环不变式

```rust
#[ensures(result >= 0)]
fn sum_array(arr: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    while i < arr.len() {
        body_invariant!(sum >= 0);  // 循环不变式
        body_invariant!(i <= arr.len());

        sum += arr[i];
        i += 1;
    }

    sum
}
```

### 4.3 旧值表达式

```rust
struct Counter {
    value: i32,
}

impl Counter {
    #[ensures(self.value == old(self.value) + 1)]
    fn increment(&mut self) {
        self.value += 1;
    }

    #[ensures(result == old(self.value))]
    #[ensures(self.value == 0)]
    fn reset(&mut self) -> i32 {
        let old_val = self.value;
        self.value = 0;
        old_val
    }
}
```

---

## 5. 验证示例

### 5.1 二分查找验证

```rust
use prusti_contracts::*;

/// 验证二分查找正确性
#[requires(arr.len() > 0)]
#[requires(is_sorted_slice(arr))]
#[ensures(result.map_or(true, |idx| arr[idx] == target))]
#[ensures(result.map_or(true, |idx| idx < arr.len()))]
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        body_invariant!(left <= right);
        body_invariant!(right <= arr.len());
        body_invariant!(
            forall(|i: usize| (
                i < left ==> arr[i] < target
            ) && (
                i >= right && i < arr.len() ==> arr[i] > target
            ))
        );

        let mid = left + (right - left) / 2;

        if arr[mid] == target {
            return Some(mid);
        } else if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    None
}

#[pure]
fn is_sorted_slice(arr: &[i32]) -> bool {
    forall(|i: usize, j: usize|
        i < j && j < arr.len() ==> arr[i] <= arr[j]
    )
}
```

### 5.2 栈的实现与验证

```rust
use prusti_contracts::*;

pub struct Stack<T> {
    data: Vec<T>,
}

impl<T> Stack<T> {
    #[pure]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    #[pure]
    #[ensures(result == (self.len() == 0))]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, value: T) {
        self.data.push(value);
    }

    #[requires(!self.is_empty())]
    #[ensures(self.len() == old(self.len()) - 1)]
    pub fn pop(&mut self) -> T {
        self.data.pop().unwrap()
    }

    #[requires(!self.is_empty())]
    #[ensures(result == old(self.data.last().unwrap()))]
    pub fn peek(&self) -> &T {
        self.data.last().unwrap()
    }
}
```

---

## 6. 高级特性

### 6.1 幽灵变量

```rust
use prusti_contracts::*;

/// 幽灵变量用于验证辅助
#[ensures(result.0 == a + b)]
#[ensures(result.1 == a * b)]
fn compute_with_proof(a: i32, b: i32) -> (i32, i32) {
    let sum = a + b;
    let product = a * b;

    // 幽灵块用于验证逻辑
    prusti_assert!(sum == a + b);
    prusti_assert!(product == a * b);

    (sum, product)
}
```

### 6.2 外部函数规范

```rust
use prusti_contracts::*;

// 为外部函数添加规范
#[extern_spec]
impl Vec<i32> {
    #[ensures(result.len() == 0)]
    fn new() -> Vec<i32>;

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: i32);
}
```

### 6.3 类型不变式

```rust
use prusti_contracts::*;

/// 带有不变式的类型
#[invariant(self.value >= 0)]
pub struct NonNegative {
    value: i32,
}

impl NonNegative {
    #[ensures(result.value >= 0)]
    pub fn new(v: i32) -> Self {
        assert!(v >= 0);
        Self { value: v }
    }

    #[ensures(result.value >= 0)]
    #[ensures(result.value == self.value + 1)]
    pub fn increment(&self) -> Self {
        Self { value: self.value + 1 }
    }
}
```

---

## 7. 限制与解决方案

### 7.1 已知限制

| 限制 | 说明 | 解决方案 |
|:---|:---|:---|
| Rust 版本 | 不支持最新 Rust | 使用 1.70-1.75 |
| 泛型约束 | 复杂 trait bound 受限 | 简化类型参数 |
| 循环 | 需手动指定不变式 | 仔细设计不变式 |
| 递归 | 深度受限 | 使用迭代替代 |

### 7.2 常见错误与解决

```rust
// ❌ 错误：未指定循环不变式
fn sum_wrong(arr: &[i32]) -> i32 {
    let mut sum = 0;
    for x in arr {  // Prusti 无法验证
        sum += x;
    }
    sum
}

// ✅ 正确：显式循环不变式
fn sum_correct(arr: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    while i < arr.len() {
        body_invariant!(i <= arr.len());
        sum += arr[i];
        i += 1;
    }
    sum
}
```

### 7.3 调试验证失败

```rust
#[requires(x > 0)]
#[ensures(result > x)]  // 验证失败？
fn double(x: i32) -> i32 {
    x * 2
}
// 注意：当 x = 1 时，result = 2 > 1 ✓
// 但规范可能需要调整边界条件
```

---

## 参考

- [Prusti GitHub](https://github.com/viperproject/prusti-dev)
- [Prusti 教程](https://viperproject.github.io/prusti-dev/user-guide/)
- [Viper 项目](https://www.pm.inf.ethz.ch/research/viper.html)

---

*文档版本: 1.0.0* | *Prusti 版本: 0.2.x*
