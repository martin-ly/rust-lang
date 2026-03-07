# Kani 模型检测指南

> **工具类型**: 模型检测 (Model Checking)
> **难度**: 🔴 高级
> **应用场景**: 穷举状态空间、验证程序属性、证明功能正确性

---

## 目录

- [Kani 模型检测指南](#kani-模型检测指南)
  - [目录](#目录)
  - [1. 引言与概述](#1-引言与概述)
  - [2. Kani 的工作原理](#2-kani-的工作原理)
    - [2.1 符号执行基础](#21-符号执行基础)
    - [2.2 CBMC 集成](#22-cbmc-集成)
    - [2.3 有界验证](#23-有界验证)
  - [3. 形式化定义](#3-形式化定义)
    - [3.1 符号执行的数学模型](#31-符号执行的数学模型)
    - [3.2 路径完备性定理](#32-路径完备性定理)
    - [3.3 属性验证的形式化](#33-属性验证的形式化)
  - [4. 安装与配置](#4-安装与配置)
    - [4.1 安装 Kani](#41-安装-kani)
    - [4.2 项目配置](#42-项目配置)
  - [5. 核心功能详解](#5-核心功能详解)
    - [5.1 基础证明函数](#51-基础证明函数)
    - [5.2 任意值生成 (kani::any)](#52-任意值生成-kaniany)
    - [5.3 假设与断言](#53-假设与断言)
    - [5.4 循环展开](#54-循环展开)
  - [6. 验证示例](#6-验证示例)
    - [6.1 算术运算验证](#61-算术运算验证)
    - [6.2 二分查找验证](#62-二分查找验证)
    - [6.3 Unsafe 代码验证](#63-unsafe-代码验证)
    - [6.4 状态机验证](#64-状态机验证)
  - [7. 高级特性](#7-高级特性)
    - [7.1 覆盖率分析](#71-覆盖率分析)
    - [7.2 假设契约](#72-假设契约)
    - [7.3 多线程支持](#73-多线程支持)
  - [8. Kani 与其他工具对比](#8-kani-与其他工具对比)
  - [9. 最佳实践与常见陷阱](#9-最佳实践与常见陷阱)
    - [9.1 最佳实践](#91-最佳实践)
  - [10. 限制与解决方案](#10-限制与解决方案)
    - [当前限制](#当前限制)
    - [性能优化建议](#性能优化建议)
  - [参考](#参考)

---

## 1. 引言与概述

Kani 是一个 Rust 的**模型检测器 (Model Checker)**，基于 CBMC (C Bounded Model Checker) 构建。它能够穷举程序的所有可能执行路径，验证给定的属性是否在所有情况下都成立。

```
┌─────────────────────────────────────────────────────────────┐
│                    Kani 验证流程                            │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│   Rust 代码 + 规范  →  Kani  →  CBMC  →  SMT Solver         │
│        ↓                                               ↓    │
│   #[kani::proof]                              验证结果     │
│   #[kani::assume]                             ✅ SUCCESS   │
│   assert!()                                   ❌ FAILURE   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**核心特点:**

- ✅ **自动化验证**: 无需手动编写证明脚本
- ✅ **符号执行**: 使用符号值而非具体值进行验证
- ✅ **有界完备性**: 在设定的界限内提供完备性保证
- ✅ **Rust 原生**: 直接验证 Rust 代码，无需转换

---

## 2. Kani 的工作原理

### 2.1 符号执行基础

符号执行使用**符号变量**代替具体值进行程序分析：

```
┌─────────────────────────────────────────────────────────────┐
│                    符号执行 vs 常规执行                      │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  常规执行:                    符号执行:                      │
│  ─────────                    ─────────                     │
│                                                             │
│  x = 5;                      x = α (符号)                   │
│  y = x + 3;                  y = α + 3 (符号表达式)          │
│  if x > 0:                   if α > 0:                       │
│      z = y * 2;                  z = (α + 3) * 2            │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

**关键概念：**

1. **符号状态**: 程序状态由符号表达式表示
2. **路径条件 (Path Condition)**: 到达某条路径需要满足的条件
3. **约束求解**: 使用 SMT Solver 检查条件的可满足性

### 2.2 CBMC 集成

Kani 使用 CBMC 作为后端验证引擎：

```
┌──────────────┐    ┌──────────────┐    ┌──────────────┐
│   Rust 源码   │ → │  Goto-C 中间  │ → │    CBMC      │
└──────────────┘    │  表示 (CIR)   │    └──────────────┘
                    └──────────────┘           ↓
                    ┌──────────────┐    ┌──────────────┐
                    │  验证结果    │ ← │  SMT Solver  │
                    └──────────────┘    └──────────────┘
```

CBMC 的处理流程：

1. 将 Rust MIR 转换为 Goto-C 中间表示
2. 对循环进行展开 (unrolling)
3. 生成逻辑公式编码程序语义
4. 调用 SMT Solver 验证属性

### 2.3 有界验证

Kani 采用**有界模型检测 (Bounded Model Checking)**，对循环和递归设置界限：

```rust
// Kani 会展开循环最多 10 次
cargo kani --unwind 10

// 自动计算所需的展开次数
cargo kani --unwind auto
```

**完备性边界 (Completeness Threshold):**

对于循环，完备性边界是确保找到所有错误所需的最小展开次数：

```
循环: for i in 0..n { ... }

完备性边界 = n (当 n 为常数时)
完备性边界 = k (用户指定的界限)
```

---

## 3. 形式化定义

### 3.1 符号执行的数学模型

**定义 3.1 (符号状态)**

符号状态 $σ$ 是一个映射：

$$σ: Var \rightarrow SymExpr$$

其中 $Var$ 是程序变量集合，$SymExpr$ 是符号表达式集合。

**定义 3.2 (路径条件)**

路径条件 $PC$ 是到达特定程序点所需满足的布尔约束：

$$PC = \bigwedge_{i=1}^{n} c_i$$

其中 $c_i$ 是分支条件。

**定义 3.3 (符号执行转换)**

语句的符号执行定义为转换函数：

$$\llbracket stmt \rrbracket: (σ, PC) \rightarrow (σ', PC')$$

### 3.2 路径完备性定理

**定理 3.1 (有界完备性)**

设程序 $P$ 的所有循环展开界限为 $k$，若 Kani 报告 SUCCESS，则：

$$\forall π \in Paths_k(P): \forall s \in States(π): Property(s) = true$$

其中 $Paths_k(P)$ 是展开界限为 $k$ 的所有路径集合。

**定理 3.2 (反例完备性)**

若存在违反属性的执行路径，且该路径在展开界限内，Kani 必定能找到反例：

$$\exists π: Violates(π) \land Length(π) \leq k \Rightarrow Kani\ reports\ FAILURE$$

### 3.3 属性验证的形式化

**定义 3.4 (Hoare 三元组)**

Kani 验证的属性可以表示为 Hoare 三元组：

$${P}\ C\ {Q}$$

其中：

- $P$: 前置条件 (assume)
- $C$: 程序代码
- $Q$: 后置条件 (assert)

**定理 3.3 (验证正确性)**

Kani 报告 SUCCESS 当且仅当：

$$\forall σ: P(σ) \Rightarrow Q(\llbracket C \rrbracket(σ))$$

---

## 4. 安装与配置

### 4.1 安装 Kani

```bash
# 安装 Kani 工具链
cargo install --locked kani-verifier

# 设置 Kani 和依赖
cargo kani setup

# 验证安装
cargo kani --version
```

### 4.2 项目配置

```toml
# Cargo.toml
[package]
name = "verified-project"
version = "0.1.0"
edition = "2021"

[dependencies]
# Kani 验证时不需要特殊依赖

[dev-dependencies]
# 测试依赖
```

---

## 5. 核心功能详解

### 5.1 基础证明函数

```rust
// 最简单的证明函数
#[kani::proof]
fn test_addition() {
    let a: u32 = kani::any();  // 符号变量
    let b: u32 = kani::any();

    // 基本加法性质
    let result = a + b;
    assert!(result >= a || result >= b);  // 溢出时可能不成立
}
```

### 5.2 任意值生成 (kani::any)

`kani::any()` 生成符号值，代表所有可能的输入：

```rust
use kani::Arbitrary;

#[derive(Arbitrary)]  // 自动生成任意值
struct Point {
    x: i32,
    y: i32,
}

#[kani::proof]
fn test_struct() {
    let p: Point = kani::any();

    // 验证所有可能的 Point 值
    assert!(p.x >= i32::MIN && p.x <= i32::MAX);
}
```

**任意值类型支持：**

| 类型 | 支持 | 说明 |
|:---|:---:|:---|
| 整数 (i32, u64等) | ✅ | 全范围 |
| 布尔 | ✅ | true/false |
| 元组 | ✅ | 组合类型 |
| 数组 | ✅ | 固定大小 |
| 结构体 | ✅ | 需实现 Arbitrary |
| 枚举 | ✅ | 自动派生 |
| 浮点数 | ⚠️ | 有限支持 |
| 指针 | ⚠️ | 需要额外处理 |

### 5.3 假设与断言

**假设 (Assume) - 前置条件：**

```rust
#[kani::proof]
fn test_division() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();

    // 假设前提：除数不为零
    kani::assume(y != 0);

    let result = x / y;

    // 验证除法基本性质
    assert_eq!(x, result * y + x % y);
}
```

**断言 (Assert) - 后置条件：**

```rust
#[kani::proof]
fn test_abs() {
    let x: i32 = kani::any();

    kani::assume(x != i32::MIN);  // 防止溢出

    let result = x.abs();

    // 多个后置条件
    assert!(result >= 0, "绝对值非负");
    assert!(result == x || result == -x, "绝对值定义");
    assert!(if x >= 0 { result == x } else { result == -x });
}
```

### 5.4 循环展开

```rust
// 需要指定循环展开次数
#[kani::proof]
#[kani::unwind(10)]  // 展开循环最多 10 次
fn test_loop() {
    let n: usize = kani::any();
    kani::assume(n < 10);

    let mut sum = 0;
    for i in 0..n {
        sum += i;
    }

    // 验证求和公式
    assert_eq!(sum, n * (n - 1) / 2);
}
```

---

## 6. 验证示例

### 6.1 算术运算验证

```rust
/// 安全加法函数
fn saturating_add(a: u32, b: u32) -> u32 {
    a.saturating_add(b)
}

#[kani::proof]
fn verify_saturating_add() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();

    let result = saturating_add(a, b);

    // 属性 1: 结果不小于任一操作数（除非溢出）
    if a <= u32::MAX - b {
        assert_eq!(result, a + b);
    } else {
        assert_eq!(result, u32::MAX);
    }

    // 属性 2: 结果不会溢出
    assert!(result >= a || result >= b || result == u32::MAX);
}

/// 乘法函数验证
fn checked_mul(a: i32, b: i32) -> Option<i32> {
    a.checked_mul(b)
}

#[kani::proof]
fn verify_checked_mul() {
    let a: i32 = kani::any();
    let b: i32 = kani::any();

    match checked_mul(a, b) {
        Some(result) => {
            // 乘法成功，验证结果
            assert_eq!(result, a * b);
            assert!(result / b == a || b == 0);
        }
        None => {
            // 乘法溢出
            let a_i64 = a as i64;
            let b_i64 = b as i64;
            let product = a_i64 * b_i64;
            assert!(product < i32::MIN as i64 || product > i32::MAX as i64);
        }
    }
}
```

### 6.2 二分查找验证

```rust
/// 二分查找实现
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    None
}

#[kani::proof]
#[kani::unwind(5)]
fn verify_binary_search_found() {
    // 固定大小数组进行验证
    let arr: [i32; 5] = kani::any();
    let target: i32 = kani::any();

    // 假设数组已排序
    kani::assume(arr[0] <= arr[1]);
    kani::assume(arr[1] <= arr[2]);
    kani::assume(arr[2] <= arr[3]);
    kani::assume(arr[3] <= arr[4]);

    if let Some(idx) = binary_search(&arr, target) {
        // 验证：如果返回 Some(idx)，则 arr[idx] == target
        assert!(idx < arr.len(), "索引在范围内");
        assert_eq!(arr[idx], target, "找到的元素等于目标");
    }
}

#[kani::proof]
#[kani::unwind(5)]
fn verify_binary_search_not_found() {
    let arr: [i32; 5] = kani::any();
    let target: i32 = kani::any();

    kani::assume(arr[0] <= arr[1]);
    kani::assume(arr[1] <= arr[2]);
    kani::assume(arr[2] <= arr[3]);
    kani::assume(arr[3] <= arr[4]);

    // 假设目标不在数组中
    kani::assume(arr[0] != target);
    kani::assume(arr[1] != target);
    kani::assume(arr[2] != target);
    kani::assume(arr[3] != target);
    kani::assume(arr[4] != target);

    let result = binary_search(&arr, target);

    // 验证：找不到时返回 None
    assert!(result.is_none(), "目标不在数组中时应返回 None");
}
```

### 6.3 Unsafe 代码验证

```rust
/// 安全的内存复制
unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize) {
    std::ptr::copy_nonoverlapping(src, dst, count);
}

#[kani::proof]
#[kani::unwind(10)]
fn verify_copy_nonoverlapping() {
    const SIZE: usize = 5;
    let mut src: [u8; SIZE] = kani::any();
    let mut dst: [u8; SIZE] = kani::any();

    // 保存原始 src 值用于验证
    let src_backup = src;

    unsafe {
        copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), SIZE);
    }

    // 验证复制正确性
    for i in 0..SIZE {
        assert_eq!(dst[i], src_backup[i], "元素 {} 应正确复制", i);
    }
}

/// 原始指针操作验证
#[kani::proof]
fn verify_raw_pointer() {
    let mut x: i32 = kani::any();
    let original = x;

    let ptr: *mut i32 = &mut x;

    unsafe {
        *ptr = 42;
        assert_eq!(*ptr, 42);
    }

    // 验证通过指针修改成功
    assert_eq!(x, 42);
}
```

### 6.4 状态机验证

```rust
/// 简单的状态机
#[derive(Clone, Copy, PartialEq)]
enum State {
    Idle,
    Running,
    Stopped,
}

struct StateMachine {
    state: State,
    count: u32,
}

impl StateMachine {
    fn new() -> Self {
        StateMachine {
            state: State::Idle,
            count: 0,
        }
    }

    fn start(&mut self) -> bool {
        if self.state == State::Idle {
            self.state = State::Running;
            true
        } else {
            false
        }
    }

    fn tick(&mut self) {
        if self.state == State::Running {
            self.count += 1;
        }
    }

    fn stop(&mut self) {
        self.state = State::Stopped;
    }
}

#[kani::proof]
#[kani::unwind(10)]
fn verify_state_machine() {
    let mut sm = StateMachine::new();

    // 初始状态验证
    assert_eq!(sm.state, State::Idle);
    assert_eq!(sm.count, 0);

    // 启动
    assert!(sm.start());
    assert_eq!(sm.state, State::Running);

    // 执行若干 tick
    let ticks: u8 = kani::any();
    kani::assume(ticks < 10);

    for _ in 0..ticks {
        sm.tick();
    }

    // 验证计数器
    assert_eq!(sm.count, ticks as u32);

    // 停止
    sm.stop();
    assert_eq!(sm.state, State::Stopped);
}
```

---

## 7. 高级特性

### 7.1 覆盖率分析

```bash
# 生成覆盖率报告
cargo kani --coverage

# 查看未覆盖的代码路径
cargo kani --coverage --visualize
```

### 7.2 假设契约

```rust
/// 契约：函数的前置条件
struct Contract<T> {
    value: T,
}

impl Contract<i32> {
    fn new(x: i32) -> Option<Self> {
        if x > 0 {
            Some(Contract { value: x })
        } else {
            None
        }
    }

    fn double(&self) -> i32 {
        self.value * 2
    }
}

#[kani::proof]
fn verify_contract() {
    let x: i32 = kani::any();
    kani::assume(x > 0);

    let c = Contract::new(x).unwrap();
    let result = c.double();

    assert!(result > x);  // 2x > x 当 x > 0
    assert_eq!(result, x * 2);
}
```

### 7.3 多线程支持

Kani 对多线程的支持有限，主要用于验证同步原语：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

#[kani::proof]
fn verify_atomic_operations() {
    let counter = AtomicUsize::new(0);

    counter.fetch_add(1, Ordering::SeqCst);
    counter.fetch_add(1, Ordering::SeqCst);

    let final_value = counter.load(Ordering::SeqCst);
    assert_eq!(final_value, 2);
}
```

---

## 8. Kani 与其他工具对比

| 特性 | Kani | Miri | Prusti | Creusot |
|:---|:---|:---|:---|:---|
| **验证方法** | 模型检测 | 解释执行 | 合约验证 | 定理证明 |
| **完备性** | 有界完备 | 运行时 | 依赖证明 | 完整 |
| **自动化** | 全自动 | 全自动 | 半自动 | 半自动 |
| **循环处理** | 展开 | 直接执行 | 不变式 | 归纳 |
| **内存模型** | 基础 | Stacked Borrows | 分离逻辑 | Why3 |
| **性能** | 高消耗 | 慢 (10-100x) | 中等 | 中等 |
| **浮点支持** | 有限 | 完整 | 有限 | 有限 |
| **Unsafe 支持** | 部分 | 完整 | 有限 | 有限 |

**选择建议：**

- **Kani**: 需要穷举状态空间、验证算法属性
- **Miri**: 检查运行时 UB、unsafe 代码
- **Prusti**: 验证复杂的前置/后置条件合约
- **Creusot**: 需要完整功能正确性证明

---

## 9. 最佳实践与常见陷阱

### 9.1 最佳实践

```markdown
1. **渐进式验证**: 从简单属性开始，逐步增加复杂度
   ```rust
   // 第一步：验证基本属性
   #[kani::proof]
   fn test_basic() { ... }

   // 第二步：添加边界条件
   #[kani::proof]
   fn test_edge_cases() { ... }
   ```

1. **合理设置展开界限**: 根据算法复杂度设置

   ```rust
   // 对于 O(n) 算法，界限设为 n 的最大值
   #[kani::unwind(100)]
   fn test_linear_algorithm() {
       let n: usize = kani::any();
       kani::assume(n < 100);
       // ...
   }
   ```

2. **分离复杂验证**: 将大函数拆分为可验证单元

3. **使用覆盖率指导**: 检查哪些代码未被验证覆盖

```

### 9.2 常见陷阱

**陷阱 1: 循环界限不足**

```rust
#[kani::proof]
#[kani::unwind(5)]  // 界限太小！
fn test_loop() {
    let n: usize = kani::any();
    kani::assume(n < 10);  // n 可能为 9

    for i in 0..n {
        // ...
    }
}
// 错误: unwind bound (5) 小于最大迭代次数
```

**陷阱 2: 忘记假设约束**

```rust
#[kani::proof]
fn test_division_unconstrained() {
    let x: i32 = kani::any();
    let y: i32 = kani::any();
    // 缺少: kani::assume(y != 0);

    let _ = x / y;  // 可能除以零！
}
```

**陷阱 3: 状态空间爆炸**

```rust
// ❌ 错误：状态空间太大
#[kani::proof]
fn test_explosion() {
    let a: u64 = kani::any();
    let b: u64 = kani::any();
    let c: u64 = kani::any();
    // 状态空间: 2^192，无法验证
}

// ✅ 正确：限制范围
#[kani::proof]
fn test_constrained() {
    let a: u8 = kani::any();  // 限制为 u8
    kani::assume(a < 10);      // 进一步限制
    // 状态空间: 10，可验证
}
```

---

## 10. 限制与解决方案

### 当前限制

| 限制 | 说明 | 解决方案 |
|:---|:---|:---|
| 状态空间爆炸 | 复杂函数验证不可行 | 限制输入范围、使用 assume |
| 循环展开 | 需要手动指定界限 | 使用 `#[kani::unwind]` |
| 递归限制 | 深度受限 | 限制递归深度或改用迭代 |
| 浮点数 | 支持有限 | 使用整数近似或缩放 |
| 堆分配 | 支持有限 | 优先使用栈分配 |
| 并发 | 基本支持 | 使用原子操作验证 |

### 性能优化建议

```rust
// 1. 使用较小的数据类型
let x: u8 = kani::any();  // 比 u64 更快

// 2. 添加合理的约束
kani::assume(x < 100);  // 大幅减少状态空间

// 3. 模块化验证
// 将大函数拆分为小函数分别验证
```

---

## 参考

- [Kani GitHub](https://github.com/model-checking/kani)
- [Kani 教程](https://model-checking.github.io/kani/)
- [CBMC 文档](http://www.cprover.org/cbmc/)
- [Bounded Model Checking 论文](https://en.wikipedia.org/wiki/Bounded_model_checking)

---

*文档版本: 2.0.0* | *最后更新: 2026-03*
