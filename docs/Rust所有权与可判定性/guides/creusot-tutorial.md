# Creusot 形式化验证教程

> 基于预言逻辑(Prophecy Logic)的Rust程序验证工具

---

## 目录

1. [Creusot 简介](#1-creusot-简介)
2. [安装与配置](#2-安装与配置)
3. [预言逻辑基础](#3-预言逻辑基础)
4. [规范注解](#4-规范注解)
5. [核心验证模式](#5-核心验证模式)
6. [高级主题](#6-高级主题)
7. [完整示例](#7-完整示例)
8. [与 Prusti 对比](#8-与-prusti-对比)
9. [常见问题](#9-常见问题)
10. [参考资源](#10-参考资源)

---

## 1. Creusot 简介

### 1.1 什么是 Creusot

Creusot 是一个基于 **MLCFG** (ML-like Control Flow Graph) 中间表示的 Rust 形式化验证工具，它将 Rust 代码翻译成 Why3 验证平台的输入，利用自动定理证明器（如 Alt-Ergo、CVC5、Z3）进行验证。

### 1.2 核心特点

| 特性 | 说明 |
|------|------|
| **预言逻辑** | 支持对可变引用的强大推理 |
| **模块化验证** | 基于契约的规范，支持抽象规约 |
| **自动化** | 大部分证明自动完成 |
| **Rust 原生** | 深度集成 Rust 语义，支持所有权、生命周期 |

### 1.3 验证流程

```
Rust 源代码
    ↓
MLCFG 中间表示
    ↓
Why3 理论文件 (.mlw)
    ↓
自动定理证明器
    ↓
✓ 验证通过 / ✗ 验证失败
```

---

## 2. 安装与配置

### 2.1 系统要求

- Rust 1.70+ (建议使用 rustup 安装)
- Why3 1.6.0+
- OPAM (OCaml 包管理器)
- 自动定理证明器 (Alt-Ergo, CVC5, Z3)

### 2.2 安装步骤

```bash
# 1. 安装 Why3 和证明器
opam install why3
opam install alt-ergo

# 2. 配置 Why3
why3 config detect

# 3. 安装 Creusot
cargo install cargo-creusot

# 4. 验证安装
cargo creusot --version
```

### 2.3 项目配置

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
creusot-contracts = "0.3"

[dev-dependencies]
# 测试依赖
```

---

## 3. 预言逻辑基础

### 3.1 核心概念

预言逻辑(Prophecy Logic)是 Creusot 的核心创新，它允许对可变引用进行精确的推理。

#### 3.1.1 最终值 (Final Value)

```rust
use creusot_contracts::*;

#[ensures(*x == 5)]  // 确保 *x 的最终值是 5
fn set_to_five(x: &mut i32) {
    *x = 5;
}
```

#### 3.1.2 两状态规范 (Two-state Specifications)

```rust
#[ensures(*result == **x)]      // 返回值等于 x 的旧值
#[ensures(**x == ^*x)]          // x 的新值等于 x 的旧值（未改变）
fn take_and_return<'a>(x: &mut &'a mut i32) -> &'a mut i32 {
    std::mem::replace(x, x)  // 交换并返回
}
```

符号说明：
- `*x` - x 的最终值
- `^x` - x 的旧值（pre-state）
- `**x` - 双重解引用

### 3.2 快照 (Snapshot)

快照捕获值在特定时间点的状态：

```rust
#[ensures(@result == @x + @y)]  // @ 表示快照
defn add(x: i32, y: i32) -> i32 {
    x + y
}
```

---

## 4. 规范注解

### 4.1 基本注解

| 注解 | 含义 | 位置 |
|------|------|------|
| `#[requires(...)]` | 前置条件 | 函数前 |
| `#[ensures(...)]` | 后置条件 | 函数前 |
| `#[invariant(...)]` | 循环不变量 | 循环前 |
| `#[variant(...)]` | 变体（终止性） | 循环/递归前 |
| `#[trusted]` | 信任此函数 | 函数前 |

### 4.2 前置与后置条件

```rust
use creusot_contracts::*;

// 整数除法
#[requires(divisor != 0)]           // 前置：除数不为零
#[requires(divisor > 0)]            // 前置：除数为正
#[requires(dividend >= 0)]          // 前置：被除数非负
#[ensures(result * divisor <= dividend)]  // 后置：结果约束
#[ensures(dividend < (result + 1) * divisor)]
pub fn safe_div(dividend: i32, divisor: i32) -> i32 {
    dividend / divisor
}
```

### 4.3 循环规范

```rust
#[requires(n >= 0)]
#[ensures(result == n * (n + 1) / 2)]
pub fn sum(n: i32) -> i32 {
    let mut i = 0;
    let mut sum = 0;
    
    #[invariant(i >= 0)]
    #[invariant(i <= n)]
    #[invariant(sum == i * (i - 1) / 2)]  // 不变量：sum 是 0 到 i-1 的和
    while i < n {
        sum += i;
        i += 1;
    }
    
    sum
}
```

### 4.4 变体与终止性

```rust
#[requires(n >= 0)]
#[variant(n)]  // 变体：每次递归 n 减小，确保终止
fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}
```

---

## 5. 核心验证模式

### 5.1 所有权转移验证

```rust
use creusot_contracts::*;

pub struct Account {
    balance: i32,
}

impl Account {
    #[ensures(result.balance == 0)]
    pub fn new() -> Self {
        Account { balance: 0 }
    }
    
    #[requires(amount >= 0)]
    #[ensures(self.balance == old(self.balance) + amount)]
    pub fn deposit(&mut self, amount: i32) {
        self.balance += amount;
    }
    
    #[requires(amount >= 0)]
    #[requires(self.balance >= amount)]  // 账户余额充足
    #[ensures(self.balance == old(self.balance) - amount)]
    pub fn withdraw(&mut self, amount: i32) {
        self.balance -= amount;
    }
}
```

### 5.2 不变量维护

```rust
pub struct Vector<T> {
    data: Vec<T>,
}

impl<T> Vector<T> {
    // 类型不变量：len >= 0（自动满足）
    
    #[ensures(self.len() == 0)]
    pub fn new() -> Self {
        Vector { data: Vec::new() }
    }
    
    #[pure]  // 纯函数，无副作用
    #[ensures(result == self.data.len())]
    pub fn len(&self) -> usize {
        self.data.len()
    }
    
    #[ensures(self.len() == old(self.len()) + 1)]
    pub fn push(&mut self, value: T) {
        self.data.push(value);
    }
}
```

### 5.3 数组与切片操作

```rust
#[requires(arr.len() > 0)]
#[ensures(result >= 0)]
#[ensures((@arr).contains(result))]  // 结果在数组中
#[ensures(forall<i: Int> 0 <= i && i < @arr ==> @arr[i] <= result)]  // 是最大值
pub fn find_max(arr: &[i32]) -> i32 {
    let mut max = arr[0];
    let mut i = 1;
    
    #[invariant(i >= 1)]
    #[invariant(i <= arr.len())]
    #[invariant(forall<j: Int> 0 <= j && j < i ==> @arr[j] <= max)]
    while i < arr.len() {
        if arr[i] > max {
            max = arr[i];
        }
        i += 1;
    }
    
    max
}
```

### 5.4 递归数据结构

```rust
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    #[pure]
    #[variant(self)]
    #[ensures(result >= 0)]
    pub fn len(&self) -> usize {
        match self {
            List::Nil => 0,
            List::Cons(_, tail) => 1 + tail.len(),
        }
    }
    
    #[pure]
    #[variant(self)]
    #[ensures(result ==> self.len() == 0)]
    pub fn is_empty(&self) -> bool {
        matches!(self, List::Nil)
    }
}
```

---

## 6. 高级主题

### 6.1 幽灵状态 (Ghost State)

幽灵状态用于验证但不影响运行时：

```rust
use creusot_contracts::ghost::*;

#[ensures(result.0 == x + y)]
#[ensures(result.1 == x * y)]
pub fn compute_with_ghost(x: i32, y: i32) -> (i32, i32) {
    ghost! {
        // 幽灵代码块，仅在验证时执行
        let sum = x + y;
        let product = x * y;
        // 可以用于复杂的中间断言
    };
    
    (x + y, x * y)
}
```

### 6.2  traits 规范

```rust
#[allow(unused)]
pub trait Equals {
    #[predicate]
    fn equals(&self, other: &Self) -> bool;
}

impl<T: Eq> Equals for T {
    #[predicate]
    fn equals(&self, other: &Self) -> bool {
        *self == *other
    }
}
```

### 6.3 外部函数契约

对于无法验证的代码，使用 `#[trusted]`：

```rust
#[trusted]  // 信任此函数满足规范
#[ensures(result >= 0)]
#[ensures(result * result <= n)]
#[ensures((result + 1) * (result + 1) > n || result == 46340)]
pub fn isqrt(n: i32) -> i32 {
    (n as f64).sqrt() as i32
}
```

---

## 7. 完整示例

### 7.1 验证二分查找

```rust
use creusot_contracts::*;

#[requires(arr.len() > 0)]
#[requires(is_sorted(arr))]  // 数组已排序
#[ensures(result == true ==> exists<i: Int> 0 <= i && i < @arr && @arr[i] == target)]
#[ensures(result == false ==> forall<i: Int> 0 <= i && i < @arr ==> @arr[i] != target)]
pub fn binary_search(arr: &[i32], target: i32) -> bool {
    let mut low = 0;
    let mut high = arr.len();
    
    #[invariant(low <= high)]
    #[invariant(high <= arr.len())]
    #[invariant(forall<i: Int> 0 <= i && i < low ==> @arr[i] < target)]
    #[invariant(forall<i: Int> high <= i && i < @arr ==> @arr[i] > target)]
    while low < high {
        let mid = low + (high - low) / 2;
        
        if arr[mid] == target {
            return true;
        } else if arr[mid] < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    
    false
}

// 辅助谓词：数组已排序
#[predicate]
fn is_sorted(arr: &[i32]) -> bool {
    forall<i: Int, j: Int> 0 <= i && i < j && j < @arr ==> @arr[i] <= @arr[j]
}
```

### 7.2 验证栈实现

```rust
pub struct Stack<T> {
    data: Vec<T>,
}

impl<T> Stack<T> {
    #[ensures(result.is_empty())]
    pub fn new() -> Self {
        Stack { data: Vec::new() }
    }
    
    #[pure]
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    
    #[pure]
    pub fn len(&self) -> usize {
        self.data.len()
    }
    
    #[ensures(!result.is_empty())]
    #[ensures(result.len() == old(self.len()) + 1)]
    #[ensures(result.peek() == Some(item))]
    pub fn push(mut self, item: T) -> Self {
        self.data.push(item);
        self
    }
    
    #[requires(!self.is_empty())]
    #[ensures(result.0 == old(self.peek().unwrap()))]
    #[ensures(result.1.len() == old(self.len()) - 1)]
    pub fn pop(mut self) -> (T, Self) {
        let item = self.data.pop().unwrap();
        (item, self)
    }
    
    #[pure]
    pub fn peek(&self) -> Option<&T> {
        self.data.last()
    }
}
```

---

## 8. 与 Prusti 对比

| 特性 | Creusot | Prusti |
|------|---------|--------|
| **中间表示** | MLCFG | Viper (Silver) |
| **可变引用** | 预言逻辑 | 权限系统 |
| **终止性** | 显式变体 | 自动推断 |
| **证明器** | Why3 + SMT | Viper + SMT |
| **Rust 版本** | 较新 | 较旧 |
| **学习曲线** | 中等 | 较低 |

### 选择建议

- **选择 Creusot**：需要验证复杂可变引用模式、使用较新 Rust 特性
- **选择 Prusti**：快速上手、更成熟的外部工具支持

---

## 9. 常见问题

### Q1: 验证超时怎么办？

```bash
# 增加超时时间
cargo creusot -- --prover-timeout=60
```

### Q2: 如何调试失败的验证？

```rust
// 添加中间断言
#[assert(i < arr.len())]
let mid = arr[i];
```

### Q3: 支持哪些 Rust 特性？

当前支持：
- 基本类型、结构体、枚举
- 泛型、trait
- 模式匹配
- 基础生命周期

限制：
- 异步/await
- 部分 unsafe 代码
- 复杂闭包

### Q4: 如何处理循环引用？

使用 `#[trusted]` 或提供抽象规范：

```rust
#[trusted]
#[ensences(result.is_valid())]
pub fn create_cyclic() -> Node { ... }
```

---

## 10. 参考资源

### 10.1 官方资源

- [Creusot GitHub](https://github.com/creusot-rs/creusot)
- [用户手册](https://creusot-rs.github.io/creusot/)
- [论文: Prophecy Logic](https://arxiv.org/abs/2306.08903)

### 10.2 相关工具

- [Why3 平台](http://why3.lri.fr/)
- [Alt-Ergo 证明器](https://alt-ergo.ocamlpro.com/)
- [Z3 证明器](https://github.com/Z3Prover/z3)

### 10.3 学术论文

1. **Denes & Pichardie (2022)** - Creusot 原始论文
2. ** prophecy variables ( prophecy 变量)** - 理论基础
3. **RustBelt** - Rust 形式化基础

---

## 总结

Creusot 提供了强大的 Rust 程序验证能力，特别是其预言逻辑对可变引用的支持。关键要点：

1. ✓ 使用 `#[requires]` 和 `#[ensures]` 定义契约
2. ✓ 用 `#[invariant]` 标注循环不变量
3. ✓ 用 `#[variant]` 证明终止性
4. ✓ 利用快照 `@` 进行值比较
5. ✓ 对无法验证的代码使用 `#[trusted]`

---

*最后更新: 2026-03-04*
