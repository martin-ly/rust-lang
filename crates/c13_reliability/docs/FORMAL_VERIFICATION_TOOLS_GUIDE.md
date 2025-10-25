# 🔬 Rust形式化验证工具实践指南

> **创建日期**: 2025-10-20  
> **版本**: v1.0  
> **目标**: 提供Prusti、Kani、Creusot三大形式化验证工具的完整实践教程

---

## 📊 目录

- [🔬 Rust形式化验证工具实践指南](#-rust形式化验证工具实践指南)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [简介](#简介)
  - [工具概览](#工具概览)
    - [对比矩阵](#对比矩阵)
    - [选择建议](#选择建议)
  - [Prusti实践](#prusti实践)
    - [1. 安装Prusti](#1-安装prusti)
    - [2. 基础示例：验证Vec的不变量](#2-基础示例验证vec的不变量)
    - [3. 所有权验证](#3-所有权验证)
    - [4. 运行Prusti验证](#4-运行prusti验证)
  - [Kani实践](#kani实践)
    - [1. 安装Kani](#1-安装kani)
    - [2. 基础示例：有界模型检查](#2-基础示例有界模型检查)
    - [3. 并发程序验证](#3-并发程序验证)
    - [4. 自定义属性验证](#4-自定义属性验证)
    - [5. 运行Kani验证](#5-运行kani验证)
  - [Creusot实践](#creusot实践)
    - [1. 安装Creusot](#1-安装creusot)
    - [2. 基础示例：函数式规约](#2-基础示例函数式规约)
    - [3. 高级示例：数据结构验证](#3-高级示例数据结构验证)
    - [4. 循环不变量](#4-循环不变量)
    - [5. 运行Creusot验证](#5-运行creusot验证)
  - [工具对比](#工具对比)
    - [实际项目场景](#实际项目场景)
    - [性能对比](#性能对比)
  - [最佳实践](#最佳实践)
    - [1. 渐进式验证策略](#1-渐进式验证策略)
    - [2. 分层验证](#2-分层验证)
    - [3. CI/CD集成](#3-cicd集成)
    - [4. 文档化规约](#4-文档化规约)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [学术论文](#学术论文)
    - [社区资源](#社区资源)
    - [示例项目](#示例项目)
  - [练习题](#练习题)
    - [初级练习](#初级练习)
    - [中级练习](#中级练习)
    - [高级练习](#高级练习)

## 📋 目录

- [简介](#简介)
- [工具概览](#工具概览)
- [Prusti实践](#prusti实践)
- [Kani实践](#kani实践)
- [Creusot实践](#creusot实践)
- [工具对比](#工具对比)
- [最佳实践](#最佳实践)
- [参考资源](#参考资源)

---

## 简介

形式化验证是一种使用数学方法证明程序正确性的技术。在Rust生态系统中，有三个主要的形式化验证工具：

1. **Prusti** - 基于Viper的所有权和借用验证器
2. **Kani** - 基于模型检查的有界验证器
3. **Creusot** - 基于Why3的演绎验证工具

本指南将详细介绍这三个工具的安装、使用和最佳实践。

---

## 工具概览

### 对比矩阵

| 特性 | Prusti | Kani | Creusot |
|------|--------|------|---------|
| **验证方法** | 演绎验证（Viper后端） | 有界模型检查（CBMC后端） | 演绎验证（Why3后端） |
| **表达能力** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| **自动化程度** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |
| **性能** | 中等 | 快速（有界） | 较慢 |
| **学习曲线** | 中等 | 较低 | 较高 |
| **成熟度** | 研究工具 | 积极开发 | 研究工具 |
| **所有权支持** | ✅ 原生支持 | ✅ 部分支持 | ✅ 完整支持 |
| **并发验证** | ❌ 有限 | ✅ 支持 | ✅ 支持 |
| **循环不变量** | ✅ 需要标注 | ✅ 自动展开 | ✅ 需要标注 |

### 选择建议

```text
┌─────────────────────────────────────────────────┐
│ 使用场景决策树                                  │
├─────────────────────────────────────────────────┤
│                                                 │
│  需要验证什么？                                 │
│                                                 │
│  ┌───────────────┐     ┌─────────────────┐    │
│  │ 内存安全性    │ --> │ Prusti          │    │
│  │ 所有权规则    │     │ (最适合)        │    │
│  └───────────────┘     └─────────────────┘    │
│                                                 │
│  ┌───────────────┐     ┌─────────────────┐    │
│  │ 快速查找bug   │ --> │ Kani            │    │
│  │ 边界条件      │     │ (推荐)          │    │
│  └───────────────┘     └─────────────────┘    │
│                                                 │
│  ┌───────────────┐     ┌─────────────────┐    │
│  │ 复杂算法证明  │ --> │ Creusot         │    │
│  │ 函数式规约    │     │ (最强大)        │    │
│  └───────────────┘     └─────────────────┘    │
│                                                 │
└─────────────────────────────────────────────────┘
```

---

## Prusti实践

### 1. 安装Prusti

```bash
# 方式1：使用rustup（推荐）
rustup component add rust-src
cargo install prusti-cli

# 方式2：从源码构建
git clone https://github.com/viperproject/prusti-dev.git
cd prusti-dev
./x.py setup
./x.py build
```

### 2. 基础示例：验证Vec的不变量

```rust
// examples/prusti_basic.rs

use prusti_contracts::*;

/// 验证：向量总是非空的
#[requires(v.len() > 0)]
#[ensures(v.len() > 0)]
fn keep_non_empty(v: &mut Vec<i32>) {
    if v.is_empty() {
        v.push(0);
    }
}

/// 验证：数组访问安全
#[requires(index < v.len())]
#[ensures(result == old(v[index]))]
fn safe_get(v: &Vec<i32>, index: usize) -> i32 {
    v[index]
}

/// 验证：二分查找的正确性
#[requires(forall(|i: usize, j: usize| (i < j && j < arr.len()) ==> arr[i] <= arr[j]))]
#[ensures(
    match result {
        Some(idx) => idx < arr.len() && arr[idx] == target,
        None => forall(|i: usize| i < arr.len() ==> arr[i] != target),
    }
)]
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    #[invariant(left <= right)]
    #[invariant(right <= arr.len())]
    #[invariant(forall(|i: usize| i < left ==> arr[i] < target))]
    #[invariant(forall(|i: usize| i >= right && i < arr.len() ==> arr[i] > target))]
    while left < right {
        let mid = left + (right - left) / 2;

        if arr[mid] < target {
            left = mid + 1;
        } else if arr[mid] > target {
            right = mid;
        } else {
            return Some(mid);
        }
    }

    None
}

fn main() {
    let mut v = vec![1, 2, 3];
    keep_non_empty(&mut v);
    
    let sorted = vec![1, 3, 5, 7, 9];
    assert_eq!(binary_search(&sorted, 5), Some(2));
}
```

### 3. 所有权验证

```rust
// examples/prusti_ownership.rs

use prusti_contracts::*;

/// 验证：所有权转移
#[ensures(result.len() == old(v.len()))]
fn take_ownership(v: Vec<i32>) -> Vec<i32> {
    v
}

/// 验证：可变借用不重叠
#[requires(a.len() > 0)]
#[requires(b.len() > 0)]
#[ensures(a[0] == old(b[0]))]
#[ensures(b[0] == old(a[0]))]
fn swap_first(a: &mut Vec<i32>, b: &mut Vec<i32>) {
    let temp = a[0];
    a[0] = b[0];
    b[0] = temp;
}

/// 验证：生命周期约束
#[requires(v.len() > 0)]
#[ensures(result <= v.len())]
fn longest_prefix<'a>(v: &'a Vec<i32>, predicate: impl Fn(&i32) -> bool) -> usize {
    let mut count = 0;
    
    #[invariant(count <= v.len())]
    for item in v {
        if predicate(item) {
            count += 1;
        } else {
            break;
        }
    }
    
    count
}

fn main() {
    let v = vec![1, 2, 3];
    let v2 = take_ownership(v);
    assert_eq!(v2.len(), 3);
}
```

### 4. 运行Prusti验证

```bash
# 验证单个文件
cargo prusti --features prusti examples/prusti_basic.rs

# 验证整个项目
cargo prusti

# 查看详细输出
cargo prusti -- --verbose

# 生成验证报告
cargo prusti -- --json > verification_report.json
```

---

## Kani实践

### 1. 安装Kani

```bash
# 使用cargo安装
cargo install --locked kani-verifier

# 或者下载预编译版本
# https://github.com/model-checking/kani/releases

# 设置Kani
cargo kani setup
```

### 2. 基础示例：有界模型检查

```rust
// examples/kani_basic.rs

/// 验证：整数除法不会溢出
#[cfg(kani)]
#[kani::proof]
fn verify_div() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();
    
    kani::assume(b != 0);
    kani::assume(!(a == i32::MIN && b == -1));
    
    let result = a / b;
    assert!(result >= i32::MIN && result <= i32::MAX);
}

/// 验证：数组边界检查
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(10)]
fn verify_array_access() {
    let arr = [1, 2, 3, 4, 5];
    let index: usize = kani::any();
    
    kani::assume(index < arr.len());
    let _ = arr[index];
}

/// 验证：无符号整数加法不会溢出
#[cfg(kani)]
#[kani::proof]
fn verify_addition() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    
    if let Some(result) = a.checked_add(b) {
        assert!(result >= a);
        assert!(result >= b);
    }
}

fn main() {
    println!("使用 'cargo kani' 运行验证");
}
```

### 3. 并发程序验证

```rust
// examples/kani_concurrency.rs

use std::sync::{Arc, Mutex};
use std::thread;

/// 验证：互斥锁保护共享数据
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(3)]
fn verify_mutex() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..2 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let final_count = *counter.lock().unwrap();
    assert!(final_count == 2);
}

/// 验证：原子操作的顺序性
#[cfg(kani)]
#[kani::proof]
fn verify_atomic_ordering() {
    use std::sync::atomic::{AtomicBool, Ordering};
    
    let flag = AtomicBool::new(false);
    
    // 验证：store后load必然返回true
    flag.store(true, Ordering::SeqCst);
    let value = flag.load(Ordering::SeqCst);
    assert!(value);
}

fn main() {
    println!("并发验证示例");
}
```

### 4. 自定义属性验证

```rust
// examples/kani_properties.rs

/// 验证：自定义排序算法的正确性
fn bubble_sort(arr: &mut [i32]) {
    let n = arr.len();
    for i in 0..n {
        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
            }
        }
    }
}

fn is_sorted(arr: &[i32]) -> bool {
    for i in 0..arr.len() - 1 {
        if arr[i] > arr[i + 1] {
            return false;
        }
    }
    true
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(11)]
fn verify_bubble_sort() {
    let mut arr: [i32; 5] = kani::any();
    
    bubble_sort(&mut arr);
    
    // 性质1：结果必须是有序的
    assert!(is_sorted(&arr));
}

fn main() {}
```

### 5. 运行Kani验证

```bash
# 验证所有proof函数
cargo kani

# 验证特定函数
cargo kani --harness verify_div

# 显示详细输出
cargo kani --verbose

# 设置展开次数
cargo kani --default-unwind 100

# 生成可视化追踪
cargo kani --visualize
```

---

## Creusot实践

### 1. 安装Creusot

```bash
# 安装Why3（Creusot的后端）
sudo apt-get install why3

# 安装自动定理证明器
sudo apt-get install z3 cvc4 alt-ergo

# 从源码构建Creusot
git clone https://github.com/creusot-rs/creusot.git
cd creusot
cargo build --release
cargo install --path cargo-creusot
```

### 2. 基础示例：函数式规约

```rust
// examples/creusot_basic.rs

use creusot_contracts::*;

/// 验证：阶乘函数的正确性
#[requires(n <= 12)] // 防止溢出
#[ensures(result > 0)]
#[ensures(n == 0 ==> result == 1)]
#[ensures(n > 0 ==> result == n * factorial(n - 1))]
fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

/// 验证：斐波那契数列
#[requires(n <= 20)]
#[ensures(n == 0 ==> result == 0)]
#[ensures(n == 1 ==> result == 1)]
#[ensures(n >= 2 ==> result == fibonacci(n - 1) + fibonacci(n - 2))]
fn fibonacci(n: u32) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

/// 验证：最大公约数（欧几里得算法）
#[requires(b != 0)]
#[ensures(result > 0)]
#[ensures(a % result == 0 && b % result == 0)]
#[variant(b)]
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

fn main() {}
```

### 3. 高级示例：数据结构验证

```rust
// examples/creusot_datastructures.rs

use creusot_contracts::*;

/// 验证链表的不变量
#[derive(Clone)]
pub struct List<T> {
    head: Option<Box<Node<T>>>,
}

#[derive(Clone)]
struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

impl<T: Clone> List<T> {
    #[ensures(result.len() == 0)]
    pub fn new() -> Self {
        List { head: None }
    }
    
    #[ensures(result.len() == old(self.len()) + 1)]
    pub fn push(&mut self, value: T) {
        let new_node = Box::new(Node {
            value,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
    
    #[requires(self.len() > 0)]
    #[ensures(old(self.len()) == result.len() + 1)]
    pub fn pop(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;
            node.value
        })
    }
    
    #[pure]
    pub fn len(&self) -> usize {
        self.len_helper(&self.head)
    }
    
    #[pure]
    fn len_helper(&self, node: &Option<Box<Node<T>>>) -> usize {
        match node {
            None => 0,
            Some(n) => 1 + self.len_helper(&n.next),
        }
    }
}

fn main() {}
```

### 4. 循环不变量

```rust
// examples/creusot_loops.rs

use creusot_contracts::*;

/// 验证：数组求和
#[ensures(result == sum_spec(arr))]
fn array_sum(arr: &[i32]) -> i32 {
    let mut sum = 0;
    let mut i = 0;
    
    #[invariant(i <= arr.len())]
    #[invariant(sum == sum_spec(&arr[0..i]))]
    while i < arr.len() {
        sum += arr[i];
        i += 1;
    }
    
    sum
}

/// 规约函数：定义数组求和的语义
#[logic]
#[variant(arr.len())]
fn sum_spec(arr: &[i32]) -> i32 {
    if arr.is_empty() {
        0
    } else {
        arr[0] + sum_spec(&arr[1..])
    }
}

/// 验证：线性查找
#[ensures(match result {
    Some(idx) => idx < arr.len() && arr[idx] == target,
    None => !contains(arr, target),
})]
fn linear_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut i = 0;
    
    #[invariant(i <= arr.len())]
    #[invariant(!contains(&arr[0..i], target))]
    while i < arr.len() {
        if arr[i] == target {
            return Some(i);
        }
        i += 1;
    }
    
    None
}

#[logic]
fn contains(arr: &[i32], target: i32) -> bool {
    exists(|i: usize| i < arr.len() && arr[i] == target)
}

fn main() {}
```

### 5. 运行Creusot验证

```bash
# 验证单个文件
cargo creusot verify examples/creusot_basic.rs

# 验证整个项目
cargo creusot verify

# 使用特定证明器
cargo creusot verify --prover z3

# 生成Why3会话
cargo creusot why3 session

# 交互式证明
why3 ide session.why
```

---

## 工具对比

### 实际项目场景

| 场景 | Prusti | Kani | Creusot | 推荐 |
|------|--------|------|---------|------|
| **内核驱动开发** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐ | Prusti |
| **密码学算法** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | Kani |
| **编译器优化** | ⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Creusot |
| **Web服务** | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐ | Kani |
| **数据结构库** | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Creusot |
| **嵌入式系统** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐ | Kani |

### 性能对比

```text
验证时间对比（基于1000行代码）:
┌─────────────────────────────────────────┐
│ Prusti:  ████████░░░░░░░░░░ 5-10 分钟  │
│ Kani:    ███░░░░░░░░░░░░░░░ 1-2 分钟   │
│ Creusot: █████████████░░░░░ 15-30 分钟 │
└─────────────────────────────────────────┘

表达能力对比:
┌─────────────────────────────────────────┐
│ Prusti:  ████████░░░░░░░░░░ 80%        │
│ Kani:    ██████░░░░░░░░░░░░ 60%        │
│ Creusot: ██████████████████ 100%       │
└─────────────────────────────────────────┘
```

---

## 最佳实践

### 1. 渐进式验证策略

```rust
// 步骤1：从简单的前置/后置条件开始
#[requires(x > 0)]
#[ensures(result > x)]
fn increment(x: i32) -> i32 {
    x + 1
}

// 步骤2：添加复杂的不变量
#[requires(arr.len() > 0)]
#[ensures(result >= 0 && result < arr.len())]
#[ensures(forall(|i: usize| i < arr.len() ==> arr[i] <= arr[result]))]
fn find_max_index(arr: &[i32]) -> usize {
    // 实现...
}

// 步骤3：完整的形式化规约
#[ensures(result.len() == old(v1.len() + v2.len()))]
#[ensures(forall(|i: usize| i < v1.len() ==> result[i] == old(v1[i])))]
#[ensures(forall(|i: usize| 
    i >= v1.len() && i < result.len() ==> result[i] == old(v2[i - v1.len()])
))]
fn concatenate<T: Clone>(v1: Vec<T>, v2: Vec<T>) -> Vec<T> {
    // 实现...
}
```

### 2. 分层验证

```text
┌─────────────────────────────────────────┐
│         应用层验证                      │
│  (业务逻辑、算法正确性)                │
│         [Creusot]                       │
├─────────────────────────────────────────┤
│         中间层验证                      │
│  (数据结构、内存安全)                  │
│         [Prusti]                        │
├─────────────────────────────────────────┤
│         底层验证                        │
│  (边界条件、并发bug)                   │
│         [Kani]                          │
└─────────────────────────────────────────┘
```

### 3. CI/CD集成

```yaml
# .github/workflows/verification.yml
name: Formal Verification

on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      
      - name: Setup Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: nightly
          
      - name: Install Kani
        run: cargo install --locked kani-verifier
        
      - name: Run Kani Verification
        run: cargo kani
        
      - name: Install Prusti
        run: cargo install prusti-cli
        
      - name: Run Prusti Verification
        run: cargo prusti
```

### 4. 文档化规约

```rust
/// # 规约
///
/// ## 前置条件
/// - `arr` 必须非空
/// - `arr` 必须已排序
///
/// ## 后置条件
/// - 返回值在 `[0, arr.len())` 范围内
/// - `arr[result]` 是数组中的最大值
///
/// ## 不变量
/// - 数组内容不变
/// - 时间复杂度：O(n)
///
/// ## 形式化规约
/// ```text
/// requires: arr.len() > 0
/// requires: forall i, j. i < j < arr.len() => arr[i] <= arr[j]
/// ensures: result < arr.len()
/// ensures: forall i. i < arr.len() => arr[i] <= arr[result]
/// ```
#[requires(arr.len() > 0)]
#[ensures(result < arr.len())]
fn find_maximum(arr: &[i32]) -> usize {
    // 实现
}
```

---

## 参考资源

### 官方文档

- **Prusti**: <https://viperproject.github.io/prusti-dev/>
- **Kani**: <https://model-checking.github.io/kani/>
- **Creusot**: <https://creusot-rs.github.io/>

### 学术论文

1. **Prusti**: "Leveraging Rust Types for Modular Specification and Verification" (OOPSLA 2019)
2. **Kani**: "Model Checking Rust with Kani" (2022)
3. **Creusot**: "Creusot: A Foundry for the Deductive Verification of Rust Programs" (ICFEM 2022)

### 社区资源

- Rust Formal Methods Interest Group: <https://rust-formal-methods.github.io/>
- Rust Verification Workshop: <https://sites.google.com/view/rustverify/>
- Prusti Discord: <https://discord.gg/viper>

### 示例项目

- `prusti-dev/prusti-tests`: Prusti官方测试套件
- `model-checking/kani/tests`: Kani测试示例
- `creusot-rs/creusot/examples`: Creusot示例集

---

## 练习题

### 初级练习

1. **验证安全的除法**：使用Kani验证除法操作不会panic
2. **验证数组边界**：使用Prusti验证数组访问始终在界内
3. **验证简单排序**：使用Creusot验证选择排序的正确性

### 中级练习

1. **验证二叉搜索树**：验证BST的插入和删除操作保持不变量
2. **验证LRU缓存**：验证缓存大小限制和访问顺序
3. **验证并发计数器**：验证原子操作的正确性

### 高级练习

1. **验证红黑树**：完整验证红黑树的所有操作
2. **验证内存分配器**：验证自定义分配器的安全性
3. **验证并发哈希表**：验证无锁哈希表的线程安全性

---

**文档版本**: v1.0  
**最后更新**: 2025-10-20  
**维护者**: Rust Learning Community

🔬 **开始你的形式化验证之旅！** ✨
