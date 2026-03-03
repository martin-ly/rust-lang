# Aeneas：Rust到函数式语言的翻译

## 目录

- [Aeneas：Rust到函数式语言的翻译](#aeneasrust到函数式语言的翻译)
  - [目录](#目录)
  - [概述](#概述)
  - [1. 项目目标](#1-项目目标)
    - [1.1 核心挑战](#11-核心挑战)
    - [1.2 翻译策略](#12-翻译策略)
  - [2. LLBC核心概念](#2-llbc核心概念)
    - [2.1 LLBC语法](#21-llbc语法)
    - [2.2 所有权翻译示例](#22-所有权翻译示例)
    - [2.3 借用翻译](#23-借用翻译)
  - [3. 复杂模式翻译](#3-复杂模式翻译)
    - [3.1 结构体借用](#31-结构体借用)
    - [3.2 循环和迭代器](#32-循环和迭代器)
    - [3.3 条件借用](#33-条件借用)
  - [4. 形式化属性](#4-形式化属性)
    - [4.1 类型安全定理](#41-类型安全定理)
    - [4.2 语义保持](#42-语义保持)
    - [4.3 所有权正确性](#43-所有权正确性)
  - [5. 处理局限性](#5-处理局限性)
    - [5.1 不支持的模式](#51-不支持的模式)
    - [5.2 当前限制示例](#52-当前限制示例)
  - [6. 验证工作流](#6-验证工作流)
    - [6.1 典型验证流程](#61-典型验证流程)
    - [6.2 支持的后端](#62-支持的后端)
  - [7. 与RustBelt的关系](#7-与rustbelt的关系)
    - [7.1 互补使用](#71-互补使用)
  - [8. 实际应用案例](#8-实际应用案例)
    - [8.1 验证数据结构](#81-验证数据结构)
    - [8.2 验证算法](#82-验证算法)
  - [9. 使用Aeneas](#9-使用aeneas)
    - [9.1 安装](#91-安装)
    - [9.2 命令行使用](#92-命令行使用)
  - [10. 总结](#10-总结)
  - [参考](#参考)

## 概述

Aeneas是一个将Rust的MIR（中级中间表示）翻译为函数式语言（如Lean、Coq、F*）的工具。它基于**LLBC（Low-Level Borrow Calculus）**形式化，处理Rust的所有权和借用语义。

---

## 1. 项目目标

### 1.1 核心挑战

Rust的所有权和借用系统使得传统的程序验证工具难以直接应用：

```rust
fn swap<T>(x: &mut T, y: &mut T) {
    std::mem::swap(x, y);
}
```

传统的命令式程序验证需要复杂的分离逻辑来处理这种代码。Aeneas通过**将所有权和借用转化为函数式风格**来解决这个问题。

### 1.2 翻译策略

| Rust概念 | LLBC翻译 | 目标语言 |
|---------|----------|---------|
| 所有权转移 | 线性类型 | 线性函数 |
| 借用 | 索引/投影 | 纯函数 |
| 可变引用 | 状态传递 | 状态单子 |
| 生命周期 | 类型推导 | 隐式处理 |

---

## 2. LLBC核心概念

### 2.1 LLBC语法

```text
Type:
  | T                    // 基础类型
  | &mut T               // 可变引用（被翻译）
  | Box<T>               // 堆分配

Expr:
  | let x = e1 in e2     // 绑定
  | x <- e               // 赋值（状态更新）
  | borrow x as y in e   // 借用翻译
  | *x                   // 解引用（投影）
```

### 2.2 所有权翻译示例

```rust
// Rust源代码
fn take_ownership(s: String) -> usize {
    s.len()
}

fn caller() {
    let s = String::from("hello");
    let len = take_ownership(s);
    // s 不再可用
}
```

```lean
-- LLBC翻译到Lean
structure String where
  data : List Char

def take_ownership (s : String) : Nat × Unit :=
  (s.data.length, ())  -- 返回长度和单位

def caller : Nat :=
  let s := { data := ['h','e','l','l','o'] }
  let (len, _) := take_ownership s
  len  -- s 被消费，无法再次使用
```

### 2.3 借用翻译

```rust
// 可变借用
fn increment(x: &mut i32) {
    *x += 1;
}

fn main() {
    let mut n = 5;
    increment(&mut n);
    println!("{}", n); // 6
}
```

```lean
-- LLBC：借用变为状态传递
def increment (x : Int) : Int :=
  x + 1

def main : Int :=
  let n := 5
  let n' := increment n  -- 借用变为函数调用
  n'  -- 更新后的值
```

---

## 3. 复杂模式翻译

### 3.1 结构体借用

```rust
struct Point { x: i32, y: i32 }

fn swap_x(p1: &mut Point, p2: &mut Point) {
    std::mem::swap(&mut p1.x, &mut p2.x);
}
```

```lean
-- LLBC：结构体投影
structure Point where
  x : Int
  y : Int

def swap_x (p1 : Point) (p2 : Point) : Point × Point :=
  -- 借用翻译为返回更新后的结构
  let p1' := { p1 with x := p2.x }
  let p2' := { p2 with x := p1.x }
  (p1', p2')
```

### 3.2 循环和迭代器

```rust
fn sum(vec: &Vec<i32>) -> i32 {
    let mut total = 0;
    for x in vec {
        total += x;
    }
    total
}
```

```lean
-- LLBC：循环翻译为递归
def sum (vec : List Int) : Int :=
  let rec loop (remaining : List Int) (acc : Int) : Int :=
    match remaining with
    | [] => acc
    | x :: xs => loop xs (acc + x)
  loop vec 0
```

### 3.3 条件借用

```rust
fn get_or_default(v: &mut Vec<i32>, idx: usize) -> &mut i32 {
    if idx < v.len() {
        &mut v[idx]
    } else {
        v.push(0);
        &mut v[v.len() - 1]
    }
}
```

```lean
-- LLBC：条件表达式需要统一返回类型
def get_or_default (v : List Int) (idx : Nat) : Int × List Int :=
  if idx < v.length then
    (v.get! idx, v)  -- 借用元素并返回整个结构
  else
    (0, v ++ [0])    -- 添加默认值
```

---

## 4. 形式化属性

### 4.1 类型安全定理

**定理（类型保持）**：如果Rust程序e在Rust类型系统中类型良好，则其LLBC翻译[e]也在LLBC类型系统中类型良好。

```text
Γ ⊢_Rust e : T  =>  [Γ] ⊢_LLBC [e] : [T]
```

### 4.2 语义保持

**定理（语义等价）**：Rust程序和其LLBC翻译在观察等价意义下具有相同的行为。

```text
e ↓_Rust v  <=>  [e] ↓_LLBC [v]
```

### 4.3 所有权正确性

**定理（线性性）**：翻译后的LLBC程序满足线性类型规则，没有资源泄漏或双重释放。

---

## 5. 处理局限性

### 5.1 不支持的模式

| 模式 | 原因 | 替代方案 |
|------|------|---------|
| 原始指针算术 | 无法跟踪别名 | 使用安全抽象 |
| 联合体(union) | 类型不安全 | 使用enum |
| 外部函数(FFI) | 未知行为 | 建模为假设 |
| 自引用结构 | 复杂生命周期 | Pin抽象 |

### 5.2 当前限制示例

```rust
// Aeneas目前不支持
unsafe fn raw_pointer_arithmetic() {
    let mut x = [1, 2, 3];
    let ptr = x.as_mut_ptr();
    *ptr.add(1) = 5;  // 算术太复杂
}

// 替代方案：使用安全索引
fn safe_alternative(arr: &mut [i32]) {
    arr[1] = 5;  // Aeneas支持
}
```

---

## 6. 验证工作流

### 6.1 典型验证流程

```rust
// 1. 编写Rust代码
fn binary_search(arr: &[u32], target: u32) -> Option<usize> {
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
```

```lean
-- 2. Aeneas翻译到Lean
-- 3. 添加规范
def binary_search_spec (arr : List Nat) (target : Nat) : Option Nat :=
  -- 功能规范
  arr.index_of? target

-- 4. 证明等价性
theorem binary_search_correct :
  ∀ arr target, binary_search arr target = binary_search_spec arr target :=
by
  -- 归纳证明
  sorry
```

### 6.2 支持的后端

| 后端 | 用途 | 状态 |
|------|------|------|
| Lean 4 | 交互式证明 | ✅ 完整 |
| Coq | 形式验证 | ✅ 完整 |
| F* | 自动化验证 | ✅ 完整 |
| HOL4 | 定理证明 | 🔄 开发中 |

---

## 7. 与RustBelt的关系

| 特性 | RustBelt | Aeneas |
|------|----------|--------|
| 目标 | 验证unsafe代码 | 验证safe代码 |
| 方法 | 分离逻辑 | 函数式翻译 |
| 范围 | 全语言 | safe子集 |
| 工具 | Coq | Lean/Coq/F* |
| 使用难度 | 高 | 中 |

### 7.1 互补使用

```text
Rust程序
    │
    ├─ Safe部分 ──> Aeneas ──> 功能验证
    │
    └─ Unsafe部分 ──> RustBelt ──> 内存安全验证
```

---

## 8. 实际应用案例

### 8.1 验证数据结构

```rust
// 已验证：链表
pub struct List<T> {
    head: Link<T>,
}

type Link<T> = Option<Box<Node<T>>>;

struct Node<T> {
    elem: T,
    next: Link<T>,
}

impl<T> List<T> {
    pub fn push(&mut self, elem: T) {
        let new_node = Box::new(Node {
            elem,
            next: self.head.take(),
        });
        self.head = Some(new_node);
    }
}
```

Aeneas可以证明：

- 无内存泄漏
- push后长度+1
- 元素保持顺序

### 8.2 验证算法

```rust
// 已验证：快速排序分区
fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_index = len / 2;
    arr.swap(pivot_index, len - 1);

    let mut store_index = 0;
    for i in 0..len-1 {
        if arr[i] <= arr[len-1] {
            arr.swap(i, store_index);
            store_index += 1;
        }
    }
    arr.swap(store_index, len - 1);
    store_index
}
```

可证明：

- 分区后枢轴在正确位置
- 左侧都≤枢轴，右侧都≥枢轴
- 排列是原元素的重新排列

---

## 9. 使用Aeneas

### 9.1 安装

```bash
# 克隆仓库
git clone https://github.com/AeneasVerif/aeneas.git
cd aeneas

# 构建
make build

# 验证示例
aeneas lean tests/test_array.rs
```

### 9.2 命令行使用

```bash
# 翻译到Lean
aeneas lean input.rs -o output.lean

# 翻译到Coq
aeneas coq input.rs -o output.v

# 翻译到F*
aeneas fstar input.rs -o output.fst
```

---

## 10. 总结

Aeneas为Rust safe代码的形式验证提供了实用路径：

1. **自动化**：自动处理所有权和借用
2. **可读性**：生成的代码接近原始Rust
3. **实用性**：支持真实Rust代码的子集
4. **集成**：与主流证明助手集成

局限性：

- 不支持unsafe代码（使用RustBelt）
- 某些模式需要重写
- 复杂循环可能需要手动不变量

---

## 参考

1. [Aeneas GitHub](https://github.com/AeneasVerif/aeneas)
2. [Aeneas Paper: ICFP 2022](https://arxiv.org/abs/2206.07185)
3. [LLBC Formalization](https://github.com/AeneasVerif/aeneas/blob/main/doc/llbc.md)
4. [Companion Tutorial](https://github.com/AeneasVerif/aeneas-tutorial)
