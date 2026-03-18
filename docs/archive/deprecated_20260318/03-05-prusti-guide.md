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
    - [1.2 理论基础：分离逻辑](#12-理论基础分离逻辑)
    - [1.3 与 Miri/Kani 的区别](#13-与-mirikani-的区别)
    - [1.4 核心能力](#14-核心能力)
  - [2. 安装与配置](#2-安装与配置)
    - [2.1 VS Code 扩展（推荐）](#21-vs-code-扩展推荐)
    - [2.2 命令行安装](#22-命令行安装)
    - [2.3 Cargo 项目配置](#23-cargo-项目配置)
  - [3. 形式化基础](#3-形式化基础)
    - [3.1 分离逻辑概述](#31-分离逻辑概述)
    - [3.2 Hoare 逻辑](#32-hoare-逻辑)
    - [3.3 验证条件的生成](#33-验证条件的生成)
  - [4. 核心概念](#4-核心概念)
    - [4.1 前置条件与后置条件](#41-前置条件与后置条件)
    - [4.2 断言](#42-断言)
    - [4.3 纯函数](#43-纯函数)
  - [5. 规范注解详解](#5-规范注解详解)
    - [5.1 谓词（Predicates）](#51-谓词predicates)
    - [5.2 循环不变式](#52-循环不变式)
    - [5.3 旧值表达式](#53-旧值表达式)
    - [5.4 全称与存在量词](#54-全称与存在量词)
  - [6. 验证示例](#6-验证示例)
    - [6.1 二分查找验证](#61-二分查找验证)
    - [6.2 栈的实现与验证](#62-栈的实现与验证)
    - [6.3 链表验证](#63-链表验证)
    - [6.4 排序算法验证](#64-排序算法验证)
  - [7. 高级特性](#7-高级特性)
    - [7.1 幽灵变量](#71-幽灵变量)
    - [7.2 外部函数规范](#72-外部函数规范)
    - [7.3 类型不变式](#73-类型不变式)
    - [7.4 枚举与模式匹配](#74-枚举与模式匹配)
  - [8. Prusti 与其他工具对比](#8-prusti-与其他工具对比)
  - [9. 最佳实践与常见陷阱](#9-最佳实践与常见陷阱)
    - [9.1 最佳实践](#91-最佳实践)
  - [10. 限制与解决方案](#10-限制与解决方案)
    - [已知限制](#已知限制)
    - [调试验证失败](#调试验证失败)
  - [参考](#参考)

---

## 1. Prusti 简介

### 1.1 什么是 Prusti

Prusti 是一个**静态验证工具**，使用分离逻辑（Separation Logic）和自动定理证明来验证 Rust 代码的功能正确性。

```
Prusti 工作流程:
┌──────────────┐    ┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│ Rust 代码 +  │ →  │    Prusti    │ →  │    Viper     │ →  │  Z3 SMT      │
│ 规范注解     │    │   验证器     │    │  中间语言    │    │  求解器       │
└──────────────┘    └──────────────┘    └──────────────┘    └──────────────┘
                                                                      ↓
                                                              ┌──────────────┐
                                                              │  验证结果    │
                                                              │  ✅ SUCCESS  │
                                                              │  ❌ FAILURE  │
                                                              └──────────────┘
```

**核心设计目标：**

- **模块化验证**: 每个函数独立验证
- **自动化**: 大部分证明自动生成
- **Rust 感知**: 深度集成 Rust 所有权系统

### 1.2 理论基础：分离逻辑

分离逻辑 (Separation Logic) 是 Prusti 的理论基础，专门用于推理堆内存。

**核心连接词：**

| 符号 | 名称 | 含义 |
|:---|:---|:---|
| $P * Q$ | 分离合取 | $P$ 和 $Q$ 在不相交的内存区域成立 |
| $P \wand Q$ | 分离蕴涵 | 若将满足 $P$ 的堆加到当前堆，则 $Q$ 成立 |
| $\emp$ | 空堆 | 堆为空 |

**分离逻辑推理规则：**

$$
\frac{\\{P\\}\ C\ \\{Q\\} \quad \\{Q\\}\ D\ \\{R\\}}{\\{P\\}\ C; D\ \\{R\\}} \quad \text{(顺序组合)}
$$

$$
\\{P * R\\}\ C\ \\{Q * R\\} \quad \text{(框架规则)}
$$

### 1.3 与 Miri/Kani 的区别

| 工具 | 验证类型 | 自动化 | 适用场景 | 理论基础 |
|:---|:---|:---|:---|:---|
| Miri | 运行时 UB 检测 | 全自动 | 未定义行为 | 操作语义 |
| Kani | 模型检测 | 全自动 | 状态空间探索 | 有界模型检测 |
| Creusot | 定理证明 | 半自动 | 功能正确性 | Why3 |
| **Prusti** | **合约验证** | **半自动** | **前后条件** | **分离逻辑** |

**关键区别：**

- **Miri**: 运行代码，检测实际的 UB
- **Kani**: 符号执行，穷举状态空间
- **Prusti**: 静态分析，验证逻辑合约

### 1.4 核心能力

- ✅ **前置/后置条件**: `@requires`, `@ensures`
- ✅ **循环不变式**: `@invariant`, `body_invariant!`
- ✅ **断言**: `@assert`, `prusti_assert!`
- ✅ **纯函数**: `@pure`
- ✅ **可信函数**: `@trusted`
- ✅ **谓词定义**: `@predicate`
- ✅ **类型不变式**: `@invariant`
- ✅ **量词**: `forall`, `exists`

---

## 2. 安装与配置

### 2.1 VS Code 扩展（推荐）

```bash
# 安装 Prusti VS Code 扩展
# 1. 打开 VS Code
# 2. 进入扩展市场 (Ctrl+Shift+X)
# 3. 搜索 "Prusti Assistant"
# 4. 安装并重启
```

**VS Code 扩展功能：**

- 实时验证反馈
- 错误高亮
- 验证状态指示器

### 2.2 命令行安装

```bash
# 克隆 Prusti 仓库
git clone https://github.com/viperproject/prusti-dev.git
cd prusti-dev

# 安装（需要 Rust nightly）
rustup component add rustc-dev llvm-tools-preview
./x.py build

# 设置环境变量
export PRUSTI_PATH="$PWD/target/release"
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

```rust
// src/lib.rs
use prusti_contracts::*;

// 你的验证代码
```

---

## 3. 形式化基础

### 3.1 分离逻辑概述

分离逻辑扩展了 Hoare 逻辑，支持对堆内存的推理。

**基本断言：**

- $x \mapsto v$: 地址 $x$ 存储值 $v$
- $\textbf{ls}(x, y)$: 从 $x$ 到 $y$ 的链表
- $\textbf{tree}(t)$: 树结构 $t$ 有效

**分离合取 ($*$)：**

$$
(x \mapsto 5) * (y \mapsto 10)
$$

表示 $x$ 和 $y$ 指向不相交的内存位置。

### 3.2 Hoare 逻辑

Hoare 三元组 ${P}\ C\ {Q}$ 表示：

- 若前置条件 $P$ 成立，执行命令 $C$
- 则后置条件 $Q$ 成立

**推理规则：**

$$
\\{\textbf{true}\\}\ x := 5\ \\{x = 5\\}
$$

$$
\\{P[x := E]\\}\ x := E\ \\{P\\}
$$

### 3.3 验证条件的生成

Prusti 将 Rust 代码转换为验证条件 (Verification Conditions, VC)：

```
Rust 代码
    ↓
[Prusti] → Viper 中间表示
    ↓
[Viper] → SMT-LIB 公式
    ↓
[Z3] → SAT/UNSAT
```

---

## 4. 核心概念

### 4.1 前置条件与后置条件

**前置条件 (@requires):** 函数调用前必须满足的条件

**后置条件 (@ensures):** 函数返回时必须满足的条件

```rust
use prusti_contracts::*;

/// 计算绝对值
/// # Requires
/// 输入不为 i32::MIN（防止溢出）
/// # Ensures
/// 返回值 >= 0
/// 如果 x >= 0，返回 x；否则返回 -x
#[requires(x > i32::MIN)]  // 前置条件
#[ensures(result >= 0)]     // 后置条件 1
#[ensures(if x >= 0 { result == x } else { result == -x })]  // 后置条件 2
fn abs(x: i32) -> i32 {
    if x >= 0 { x } else { -x }
}
```

**形式化表示：**

$$
\\{x > \text{i32::MIN}\\}\ \text{abs}(x)\ \\{
  \text{result} \geq 0 \land
  (x \geq 0 \Rightarrow \text{result} = x) \land
  (x < 0 \Rightarrow \text{result} = -x)
\\}
$$

### 4.2 断言

```rust
#[ensures(result > 0)]
fn always_positive() -> i32 {
    let x = 42;
    prusti_assert!(x > 0);  // 编译时验证
    x
}
```

### 4.3 纯函数

纯函数是无副作用、仅依赖输入的函数：

```rust
/// 纯函数：无副作用，仅依赖输入
#[pure]
#[requires(x >= 0)]
#[ensures(result >= 0)]
#[ensures(result * result <= x)]
#[ensures((result + 1) * (result + 1) > x)]
fn sqrt_estimate(x: u32) -> u32 {
    (x as f64).sqrt() as u32
}
```

---

## 5. 规范注解详解

### 5.1 谓词（Predicates）

谓词是可重用的规范函数：

```rust
use prusti_contracts::*;

/// 链表节点
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

/// 使用谓词
#[requires(is_sorted(head))]
#[ensures(result.map_or(true, |idx| idx < list_len(head)))]
fn find_in_sorted(head: &Node, target: i32) -> Option<usize> {
    // ...
    None
}
```

### 5.2 循环不变式

循环不变式是在每次迭代前后都保持成立的条件：

```rust
#[ensures(result >= 0)]
fn sum_array(arr: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    while i < arr.len() {
        body_invariant!(sum >= 0);  // 循环不变式 1
        body_invariant!(i <= arr.len());  // 循环不变式 2
        body_invariant!(sum == sum_of(&arr[0..i]));  // 循环不变式 3

        sum += arr[i];
        i += 1;
    }

    sum
}

#[pure]
fn sum_of(arr: &[i32]) -> i32 {
    let mut s = 0;
    for x in arr {
        s += x;
    }
    s
}
```

**循环不变式的设计原则：**

1. **初始化**: 循环开始前成立
2. **保持**: 每次迭代后保持
3. **终止**: 循环结束时蕴含后置条件

### 5.3 旧值表达式

`old(expr)` 表示函数执行前的值：

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

### 5.4 全称与存在量词

```rust
use prusti_contracts::*;

/// 全称量词：所有元素满足条件
#[pure]
#[ensures(result == forall(|i: usize|
    i < arr.len() ==> arr[i] >= 0
))]
fn all_non_negative(arr: &[i32]) -> bool {
    for i in 0..arr.len() {
        if arr[i] < 0 {
            return false;
        }
    }
    true
}

/// 存在量词：存在满足条件的元素
#[pure]
#[ensures(result == exists(|i: usize|
    i < arr.len() && arr[i] == target
))]
fn contains(arr: &[i32], target: i32) -> bool {
    for i in 0..arr.len() {
        if arr[i] == target {
            return true;
        }
    }
    false
}

/// 使用量词
#[requires(arr.len() > 0)]
#[requires(forall(|i: usize| i < arr.len() ==> arr[i] >= 0))]
#[ensures(result >= 0)]
fn sum_positive_only(arr: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;

    while i < arr.len() {
        body_invariant!(i <= arr.len());
        body_invariant!(sum >= 0);
        body_invariant!(forall(|j: usize| j < i ==> arr[j] >= 0));

        sum += arr[i];
        i += 1;
    }

    sum
}
```

---

## 6. 验证示例

### 6.1 二分查找验证

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

### 6.2 栈的实现与验证

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
    #[ensures(self.peek() == &value)]
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

/// 使用示例和验证
#[requires(stack.len() < 100)]
#[ensures(result == old(stack.len()) + 1)]
fn push_and_count<T>(stack: &mut Stack<T>, value: T) -> usize
where
    T: Clone,
{
    stack.push(value);
    stack.len()
}
```

### 6.3 链表验证

```rust
use prusti_contracts::*;

pub struct ListNode {
    value: i32,
    next: Option<Box<ListNode>>,
}

impl ListNode {
    /// 计算链表长度
    #[pure]
    #[ensures(result > 0)]
    pub fn len(&self) -> usize {
        match &self.next {
            None => 1,
            Some(next) => 1 + next.len(),
        }
    }

    /// 获取第 n 个元素
    #[pure]
    #[requires(n < self.len())]
    pub fn get(&self, n: usize) -> i32 {
        if n == 0 {
            self.value
        } else {
            match &self.next {
                None => unreachable!(),
                Some(next) => next.get(n - 1),
            }
        }
    }

    /// 链表已排序
    #[pure]
    pub fn is_sorted(&self) -> bool {
        match &self.next {
            None => true,
            Some(next) => {
                self.value <= next.value && next.is_sorted()
            }
        }
    }
}

/// 在已排序链表中插入
#[requires(list.is_sorted())]
#[ensures(result.is_sorted())]
#[ensures(result.len() == old(list.len()) + 1)]
pub fn insert_sorted(list: ListNode, value: i32) -> ListNode {
    if value <= list.value {
        ListNode {
            value,
            next: Some(Box::new(list)),
        }
    } else {
        match list.next {
            None => ListNode {
                value: list.value,
                next: Some(Box::new(ListNode {
                    value,
                    next: None,
                })),
            },
            Some(next) => ListNode {
                value: list.value,
                next: Some(Box::new(insert_sorted(*next, value))),
            },
        }
    }
}
```

### 6.4 排序算法验证

```rust
use prusti_contracts::*;

/// 选择排序验证
#[ensures(is_sorted(result.as_slice()))]
#[ensures(result.len() == old(arr.len()))]
#[ensures(permutation(result.as_slice(), old(arr)))]
fn selection_sort(mut arr: Vec<i32>) -> Vec<i32> {
    let len = arr.len();
    let mut i = 0;

    while i < len {
        body_invariant!(i <= len);
        body_invariant!(is_sorted(&arr[0..i]));
        body_invariant!(forall(|j: usize, k: usize|
            j < i && k >= i && k < len ==> arr[j] <= arr[k]
        ));

        let mut min_idx = i;
        let mut j = i + 1;

        while j < len {
            body_invariant!(j <= len);
            body_invariant!(min_idx >= i && min_idx < len);
            body_invariant!(forall(|k: usize|
                k >= i && k < j ==> arr[min_idx] <= arr[k]
            ));

            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
            j += 1;
        }

        arr.swap(i, min_idx);
        i += 1;
    }

    arr
}

#[pure]
fn is_sorted(arr: &[i32]) -> bool {
    forall(|i: usize, j: usize|
        i < j && j < arr.len() ==> arr[i] <= arr[j]
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
```

---

## 7. 高级特性

### 7.1 幽灵变量

幽灵变量用于验证辅助，不生成运行时代码：

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

### 7.2 外部函数规范

```rust
use prusti_contracts::*;

// 为外部函数添加规范
#[extern_spec]
impl Vec<i32> {
    #[ensures(result.len() == 0)]
    fn new() -> Vec<i32>;

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: i32);

    #[requires(!self.is_empty())]
    #[ensures(self.len() == old(self.len()) - 1)]
    fn pop(&mut self) -> Option<i32>;
}
```

### 7.3 类型不变式

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
        Self::new(self.value + 1)
    }

    #[pure]
    pub fn value(&self) -> i32 {
        self.value
    }
}
```

### 7.4 枚举与模式匹配

```rust
use prusti_contracts::*;

enum Option<T> {
    Some(T),
    None,
}

impl<T> Option<T> {
    #[pure]
    pub fn is_some(&self) -> bool {
        matches!(self, Option::Some(_))
    }

    #[pure]
    pub fn is_none(&self) -> bool {
        !self.is_some()
    }

    #[requires(self.is_some())]
    pub fn unwrap(self) -> T {
        match self {
            Option::Some(v) => v,
            Option::None => panic!("called `Option::unwrap()` on a `None` value"),
        }
    }

    #[ensures(result.is_some())]
    #[ensures(result.unwrap() == value)]
    pub fn new(value: T) -> Self {
        Option::Some(value)
    }
}
```

---

## 8. Prusti 与其他工具对比

| 特性 | Prusti | Miri | Kani | Creusot |
|:---|:---|:---|:---|:---|
| **验证方法** | 分离逻辑 | 解释执行 | 模型检测 | 定理证明 |
| **前置/后置** | ✅ 原生支持 | ❌ | ⚠️ assume/ensure | ✅ 原生支持 |
| **循环不变式** | ✅ 支持 | N/A | N/A | ✅ 支持 |
| **纯函数** | ✅ @pure | N/A | N/A | ✅ 逻辑函数 |
| **自动化** | 高 | 全自动 | 全自动 | 中等 |
| **量词支持** | ✅ forall/exists | N/A | N/A | ✅ |
| **学习曲线** | 中等 | 低 | 中等 | 高 |
| **Rust 版本** | 1.70-1.75 | 最新 | 最新 | 最新 |

**选择建议：**

- **Prusti**: 需要验证复杂的前置/后置条件，特别是数据结构
- **Miri**: 检查 unsafe 代码和运行时 UB
- **Kani**: 穷举状态空间，验证算法属性
- **Creusot**: 需要完整的程序正确性证明

---

## 9. 最佳实践与常见陷阱

### 9.1 最佳实践

```markdown
1. **增量式验证**: 从简单规范开始，逐步完善
   ```rust
   // 第一步：基本后置条件
   #[ensures(result >= 0)]

   // 第二步：添加前置条件
   #[requires(x >= 0)]

   // 第三步：完整规范
   #[ensures(result * result <= x)]
   ```

1. **纯函数优先**: 尽可能将辅助逻辑声明为 pure

   ```rust
   #[pure]
   fn helper(x: i32) -> bool { ... }
   ```

2. **循环不变式设计**: 确保覆盖所有变量

   ```rust
   while i < n {
       body_invariant!(i <= n);
       body_invariant!(sum == sum_of(&arr[0..i]));
       // ...
   }
   ```

3. **使用谓词复用**: 将复杂规范抽象为谓词

   ```rust
   #[predicate]
   fn is_valid_state(s: &State) -> bool { ... }
   ```

```

### 9.2 常见陷阱

**陷阱 1: 忘记循环不变式**

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
        body_invariant!(sum == sum_of(&arr[0..i]));
        sum += arr[i];
        i += 1;
    }
    sum
}
```

**陷阱 2: 量词使用不当**

```rust
// ❌ 错误：量词范围不明确
#[ensures(forall(|i| arr[i] > 0))]  // i 的范围？

// ✅ 正确：明确范围
#[ensures(forall(|i: usize| i < arr.len() ==> arr[i] > 0))]
```

**陷阱 3: 递归谓词无终止**

```rust
// ❌ 错误：递归可能不终止
#[predicate]
fn bad_recursive(node: &Node) -> bool {
    bad_recursive(node)  // 无限递归！
}

// ✅ 正确：递归往基例靠近
#[predicate]
fn good_recursive(node: &Node) -> bool {
    match &node.next {
        None => true,
        Some(next) => node.value <= next.value && good_recursive(next),
    }
}
```

**陷阱 4: 忽略溢出**

```rust
// ❌ 错误：未考虑溢出
#[ensures(result > x)]
fn double(x: i32) -> i32 {
    x * 2  // 当 x 很大时可能溢出
}

// ✅ 正确：添加前置条件
#[requires(x <= i32::MAX / 2)]
#[ensures(result == x * 2)]
fn double_safe(x: i32) -> i32 {
    x * 2
}
```

---

## 10. 限制与解决方案

### 已知限制

| 限制 | 说明 | 解决方案 |
|:---|:---|:---|
| Rust 版本 | 不支持最新 Rust | 使用 1.70-1.75 |
| 泛型约束 | 复杂 trait bound 受限 | 简化类型参数 |
| 循环 | 需手动指定不变式 | 仔细设计不变式 |
| 递归 | 深度受限 | 使用迭代替代 |
| Unsafe | 支持有限 | 封装为安全抽象 |
| 并发 | 基础支持 | 顺序化验证 |

### 调试验证失败

```rust
#[requires(x > 0)]
#[ensures(result > x)]  // 验证失败？
fn double(x: i32) -> i32 {
    x * 2
}
// 注意：规范可能需要调整边界条件
```

**调试技巧：**

1. 使用 `prusti_assert!` 添加中间断言
2. 简化规范，逐步增加复杂度
3. 检查循环不变式是否充分
4. 使用 VS Code 扩展查看具体错误位置

---

## 参考

- [Prusti GitHub](https://github.com/viperproject/prusti-dev)
- [Prusti 教程](https://viperproject.github.io/prusti-dev/user-guide/)
- [Viper 项目](https://www.pm.inf.ethz.ch/research/viper.html)
- [分离逻辑简介](https://en.wikipedia.org/wiki/Separation_logic)
- [Hoare 逻辑](https://en.wikipedia.org/wiki/Hoare_logic)

---

*文档版本: 2.0.0* | *Prusti 版本: 0.2.x* | *最后更新: 2026-03*
