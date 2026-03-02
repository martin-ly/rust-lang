# Prusti 使用教程：分离逻辑验证Rust程序

> Prusti是Rust的形式化验证工具，基于Viper验证基础设施，使用分离逻辑验证Rust程序。

---

## 目录

- [Prusti 使用教程：分离逻辑验证Rust程序](#prusti-使用教程分离逻辑验证rust程序)
  - [目录](#目录)
  - [安装与配置](#安装与配置)
    - [系统要求](#系统要求)
    - [安装步骤](#安装步骤)
    - [VS Code 扩展](#vs-code-扩展)
  - [基础概念](#基础概念)
    - [什么是Prusti？](#什么是prusti)
    - [基本注解](#基本注解)
  - [前置条件与后置条件](#前置条件与后置条件)
    - [简单示例](#简单示例)
    - [old表达式](#old表达式)
    - [结果引用](#结果引用)
  - [循环不变量](#循环不变量)
    - [基本循环](#基本循环)
    - [循环不变量的作用](#循环不变量的作用)
    - [复杂循环](#复杂循环)
  - [所有权与借用](#所有权与借用)
    - [所有权转移](#所有权转移)
    - [借用验证](#借用验证)
    - [结构体验证](#结构体验证)
  - [高级特性](#高级特性)
    - [forall量化](#forall量化)
    - [exists量化](#exists量化)
    - [纯函数](#纯函数)
    - [谓词（Predicates）](#谓词predicates)
  - [实际案例](#实际案例)
    - [案例1: 向量操作](#案例1-向量操作)
    - [案例2: 链表操作](#案例2-链表操作)
    - [案例3: 银行账户](#案例3-银行账户)
  - [故障排除](#故障排除)
    - [常见问题](#常见问题)
    - [调试技巧](#调试技巧)
  - [参考资源](#参考资源)

---

## 安装与配置

### 系统要求

- Rust 1.65+
- Java 11+
- Python 3.8+

### 安装步骤

```bash
# 1. 安装Rust（如果尚未安装）
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# 2. 安装Prusti
rustup component add prusti

# 或者使用cargo-prusti
cargo install cargo-prusti

# 3. 验证安装
prusti --version
```

### VS Code 扩展

```bash
# 安装Prusti Assistant扩展
# 在VS Code中搜索 "Prusti Assistant"
```

---

## 基础概念

### 什么是Prusti？

Prusti使用**分离逻辑（Separation Logic）**验证Rust程序：

```text
程序验证流程：

Rust源代码
    ↓
Prusti解析器
    ↓
中间表示（Viper）
    ↓
分离逻辑验证器
    ↓
验证结果（通过/失败）
```

### 基本注解

| 注解 | 含义 |
|------|------|
| `#[requires(...)]` | 前置条件 |
| `#[ensures(...)]` | 后置条件 |
| `#[invariant(...)]` | 循环不变量 |
| `#[pure]` | 纯函数（无副作用） |
| `#[trusted]` | 信任此函数（不验证） |

---

## 前置条件与后置条件

### 简单示例

```rust
use prusti_contracts::*;

/// 计算绝对值
#[requires(n > i32::MIN)]  // 前置：避免溢出
#[ensures(result >= 0)]     // 后置：结果非负
#[ensures(result == n || result == -n)]  // 后置：结果是n或-n
fn abs(n: i32) -> i32 {
    if n < 0 {
        -n
    } else {
        n
    }
}
```

### old表达式

```rust
#[requires(x > 0)]
#[ensures(result == x + y)]
#[ensures(*x == old(*x) + 1)]  // 验证x增加了1
fn increment_and_add(x: &mut i32, y: i32) -> i32 {
    *x += 1;
    *x + y
}
```

### 结果引用

```rust
#[ensures(result == n * (n + 1) / 2)]
fn sum_formula(n: i32) -> i32 {
    n * (n + 1) / 2
}
```

---

## 循环不变量

### 基本循环

```rust
#[requires(n >= 0)]
#[ensures(result == n * (n + 1) / 2)]
fn sum_loop(n: i32) -> i32 {
    let mut i = 0;
    let mut sum = 0;

    while i < n {
        // 循环不变量
        body_invariant!(i >= 0 && i <= n);
        body_invariant!(sum == i * (i + 1) / 2);

        sum += i + 1;
        i += 1;
    }

    sum
}
```

### 循环不变量的作用

```text
循环不变量：在每次迭代前后都成立的断言

初始化：在进入循环前成立
保持：如果一次迭代前成立，则迭代后仍成立
终止：当循环结束时，结合条件推出后置条件
```

### 复杂循环

```rust
#[requires(arr.len() >= 1)]
#[ensures(result >= 0 && (result as usize) < arr.len())]
#[ensures(forall(|i: usize| i < arr.len() ==> arr[i] <= arr[result as usize]))]
fn find_max(arr: &[i32]) -> usize {
    let mut max_idx = 0;
    let mut i = 1;

    while i < arr.len() {
        body_invariant!(max_idx < arr.len());
        body_invariant!(i >= 1 && i <= arr.len());
        body_invariant!(forall(|j: usize| j < i ==> arr[j] <= arr[max_idx]));

        if arr[i] > arr[max_idx] {
            max_idx = i;
        }
        i += 1;
    }

    max_idx
}
```

---

## 所有权与借用

### 所有权转移

```rust
#[ensures(result.len() == 0)]
fn empty_vec() -> Vec<i32> {
    vec![]
}

#[requires(v.len() > 0)]
#[ensures(result == v[0])]
#[ensures(v.len() == old(v.len()) - 1)]  // v的长度减1
fn pop_first(v: &mut Vec<i32>) -> i32 {
    v.remove(0)
}
```

### 借用验证

```rust
#[requires(index < slice.len())]
#[ensures(result == slice[index])]
fn get(slice: &[i32], index: usize) -> i32 {
    slice[index]
}

#[requires(index < slice.len())]
#[ensures(slice[index] == value)]
#[ensures(forall(|i: usize| i < slice.len() && i != index ==>
    slice[i] == old(slice[i])))]
fn set(slice: &mut [i32], index: usize, value: i32) {
    slice[index] = value;
}
```

### 结构体验证

```rust
struct Account {
    balance: i32,
}

impl Account {
    #[ensures(result.balance == 0)]
    fn new() -> Self {
        Account { balance: 0 }
    }

    #[requires(amount >= 0)]
    #[ensures(self.balance == old(self.balance) + amount)]
    fn deposit(&mut self, amount: i32) {
        self.balance += amount;
    }

    #[requires(amount >= 0)]
    #[requires(self.balance >= amount)]
    #[ensures(self.balance == old(self.balance) - amount)]
    fn withdraw(&mut self, amount: i32) {
        self.balance -= amount;
    }
}
```

---

## 高级特性

### forall量化

```rust
#[ensures(forall(|i: usize| i < arr.len() ==> arr[i] >= 0))]
fn all_non_negative(arr: &[i32]) -> bool {
    for i in 0..arr.len() {
        body_invariant!(forall(|j: usize| j < i ==> arr[j] >= 0));
        if arr[i] < 0 {
            return false;
        }
    }
    true
}
```

### exists量化

```rust
#[requires(arr.len() > 0)]
#[ensures(exists(|i: usize| i < arr.len() && result == arr[i]))]
fn pick_one(arr: &[i32]) -> i32 {
    arr[0]
}
```

### 纯函数

```rust
#[pure]
#[ensures(result == a + b)]
fn add(a: i32, b: i32) -> i32 {
    a + b
}

// 纯函数可以在规范中使用
#[requires(n >= 0)]
#[ensures(result == add(n, n))]
fn double(n: i32) -> i32 {
    add(n, n)
}
```

### 谓词（Predicates）

```rust
#[predicate]
fn sorted(arr: &[i32]) -> bool {
    forall(|i: usize, j: usize|
        i < j && j < arr.len() ==> arr[i] <= arr[j])
}

#[requires(sorted(arr))]
#[ensures(sorted(arr))]
#[ensures(result ==> exists(|i: usize| i < arr.len() && arr[i] == key))]
fn binary_search(arr: &[i32], key: i32) -> bool {
    // 二分查找实现
    unimplemented!()
}
```

---

## 实际案例

### 案例1: 向量操作

```rust
use prusti_contracts::*;

struct MyVec<T> {
    data: Vec<T>,
}

impl<T: Copy> MyVec<T> {
    #[ensures(result.len() == 0)]
    fn new() -> Self {
        MyVec { data: vec![] }
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push(&mut self, value: T) {
        self.data.push(value);
    }

    #[requires(self.len() > 0)]
    #[ensures(self.len() == old(self.len()) - 1)]
    #[ensures(result == old(self.data[self.len() - 1]))]
    fn pop(&mut self) -> T {
        self.data.pop().unwrap()
    }

    #[pure]
    fn len(&self) -> usize {
        self.data.len()
    }
}
```

### 案例2: 链表操作

```rust
struct Node {
    value: i32,
    next: Option<Box<Node>>,
}

impl Node {
    #[ensures(result.len() == 0)]
    fn new() -> Self {
        Node { value: 0, next: None }
    }

    #[ensures(self.len() == old(self.len()) + 1)]
    fn push_front(&mut self, value: i32) {
        let new_node = Box::new(Node {
            value,
            next: self.next.take(),
        });
        self.next = Some(new_node);
    }

    #[pure]
    fn len(&self) -> usize {
        match &self.next {
            None => 0,
            Some(n) => 1 + n.len(),
        }
    }
}
```

### 案例3: 银行账户

```rust
struct BankAccount {
    id: u64,
    balance: i64,
    frozen: bool,
}

impl BankAccount {
    #[ensures(result.balance == 0)]
    #[ensures(!result.frozen)]
    fn new(id: u64) -> Self {
        BankAccount { id, balance: 0, frozen: false }
    }

    #[requires(!self.frozen)]
    #[requires(amount >= 0)]
    #[ensures(self.balance == old(self.balance) + amount)]
    fn deposit(&mut self, amount: i64) {
        self.balance += amount;
    }

    #[requires(!self.frozen)]
    #[requires(amount >= 0)]
    #[requires(self.balance >= amount)]
    #[ensures(self.balance == old(self.balance) - amount)]
    fn withdraw(&mut self, amount: i64) {
        self.balance -= amount;
    }

    #[ensures(self.frozen)]
    fn freeze(&mut self) {
        self.frozen = true;
    }
}
```

---

## 故障排除

### 常见问题

**问题1：验证超时**

```rust
// ❌ 复杂循环可能导致超时
#[requires(n < 1000)]  // 添加约束
fn complex_loop(n: i32) { ... }
```

**问题2：量化器实例化失败**

```rust
// ❌ forall可能导致问题
#[ensures(forall(|i: usize| ...))]

// ✅ 使用具体化策略
#[ensures(arr.len() == old(arr.len()))]
#[ensures(forall(|i: usize| i < arr.len() ==> ...))]
```

**问题3：递归终止**

```rust
#[requires(n >= 0)]
#[requires(n < 100)]  // 添加递归深度限制
fn recursive(n: i32) -> i32 { ... }
```

### 调试技巧

```bash
# 详细输出
prusti --verbose file.rs

# 仅验证特定函数
prusti --function my_function file.rs

# 生成Viper代码
prusti --print-viper file.rs
```

---

## 参考资源

- [Prusti GitHub](https://github.com/viperproject/prusti)
- [Prusti用户指南](https://viperproject.github.io/prusti-dev/user-guide/)
- [分离逻辑简介](https://en.wikipedia.org/wiki/Separation_logic)

---

*Prusti为Rust程序提供了强大的形式化验证能力，特别适用于验证安全关键代码的正确性。*
