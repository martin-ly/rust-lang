# 借用深入分析

> **目标**: 全面理解 Rust 借用系统的深层机制，包括共享与可变借用、Non-Lexical Lifetimes (NLL)、以及重新借用等高级概念。

---

## 目录

- [借用深入分析](#借用深入分析)
  - [目录](#目录)
  - [1. 形式化定义](#1-形式化定义)
    - [1.1 借用的形式化模型](#11-借用的形式化模型)
    - [1.2 生命周期与借用的关系](#12-生命周期与借用的关系)
    - [1.3 借用的状态转换](#13-借用的状态转换)
  - [2. 共享借用 vs 可变借用](#2-共享借用-vs-可变借用)
    - [2.1 共享借用的本质](#21-共享借用的本质)
    - [2.2 可变借用的独占性](#22-可变借用的独占性)
    - [2.3 共享与可变借用的交互](#23-共享与可变借用的交互)
    - [2.4 可变借用的"降级"](#24-可变借用的降级)
  - [3. Non-Lexical Lifetimes (NLL)](#3-non-lexical-lifetimes-nll)
    - [3.1 NLL 的引入背景](#31-nll-的引入背景)
    - [3.2 NLL 的工作原理](#32-nll-的工作原理)
    - [3.3 NLL 的限制](#33-nll-的限制)
    - [3.4 NLL 与 Two-Phase Borrows](#34-nll-与-two-phase-borrows)
  - [4. 重新借用 (Reborrowing)](#4-重新借用-reborrowing)
    - [4.1 什么是重新借用](#41-什么是重新借用)
    - [4.2 重新借用的形式化定义](#42-重新借用的形式化定义)
    - [4.3 函数参数中的重新借用](#43-函数参数中的重新借用)
    - [4.4 显式与隐式重新借用](#44-显式与隐式重新借用)
    - [4.5 重新借用与模式匹配](#45-重新借用与模式匹配)
  - [5. 常见陷阱与解决方案](#5-常见陷阱与解决方案)
    - [陷阱 1: 迭代器失效](#陷阱-1-迭代器失效)
    - [陷阱 2: 自引用结构体](#陷阱-2-自引用结构体)
    - [陷阱 3: 生命周期标注遗漏](#陷阱-3-生命周期标注遗漏)
    - [陷阱 4: 借用与线程](#陷阱-4-借用与线程)
    - [陷阱 5: 可变借用与条件编译](#陷阱-5-可变借用与条件编译)
  - [6. 与其他语言对比](#6-与其他语言对比)
    - [6.1 C/C++: 裸指针](#61-cc-裸指针)
    - [6.2 Java: 引用与 GC](#62-java-引用与-gc)
    - [6.3 Swift: 值类型与引用类型](#63-swift-值类型与引用类型)
    - [6.4 Go: 指针与 GC](#64-go-指针与-gc)
  - [7. 性能影响分析](#7-性能影响分析)
    - [7.1 借用与复制的性能对比](#71-借用与复制的性能对比)
    - [7.2 可变借用的优化机会](#72-可变借用的优化机会)
    - [7.3 共享借用的缓存友好性](#73-共享借用的缓存友好性)
    - [7.4 借用检查器的编译时间影响](#74-借用检查器的编译时间影响)
  - [8. 高级借用模式](#8-高级借用模式)
    - [8.1 分离借用（Splitting Borrows）](#81-分离借用splitting-borrows)
    - [8.2 结构体字段的独立借用](#82-结构体字段的独立借用)
    - [8.3 切片模式](#83-切片模式)
    - [8.4 泛型与借用](#84-泛型与借用)
    - [8.5 闭包与借用](#85-闭包与借用)
  - [总结](#总结)

---

## 1. 形式化定义

### 1.1 借用的形式化模型

**定义 1.1** (借用): 借用是临时获取对值的引用的操作，不转移所有权。借用分为两类：

- **共享借用** (`&T`): 允许多个，不可变
- **可变借用** (`&mut T`): 唯一一个，可变

**定义 1.2** (借用规则): 对于任意作用域内的值 `v`，以下规则必须同时满足：

```
规则 1: borrow(v, imm, n) → n ≥ 0 ∧ ¬borrow(v, mut, 1)
规则 2: borrow(v, mut, 1) → ¬borrow(v, imm, n) ∧ ¬borrow(v, mut, 1)
```

即：要么有多个不可变引用，要么有一个可变引用，不能同时存在。

### 1.2 生命周期与借用的关系

**定义 1.3** (借用的生命周期): 如果 `r: &'a T`，则引用 `r` 的生命周期 `'a` 必须满足：

```
∀'a: 'a ⊆ lifetime(T) ∧ 'a: valid
```

即：借用的生命周期不能超过被引用值的生命周期。

### 1.3 借用的状态转换

```
         ┌─────────────────────────────────────────┐
         │            owned(T)                      │
         │           拥有状态                       │
         └───────────────┬─────────────────────────┘
                         │
            ┌────────────┼────────────┐
            ▼            ▼            ▼
    ┌───────────┐ ┌───────────┐ ┌───────────┐
    │  &T       │ │  &mut T   │ │  move     │
    │共享借用    │ │可变借用    │ │所有权转移  │
    └─────┬─────┘ └─────┬─────┘ └─────┬─────┘
          │             │             │
          └─────────────┴─────────────┘
                          │
                          ▼
                ┌─────────────────┐
                │    dropped(T)   │
                │     释放状态      │
                └─────────────────┘
```

---

## 2. 共享借用 vs 可变借用

### 2.1 共享借用的本质

共享借用（`&T`）提供对数据的只读访问，关键特性是**可共存**。

```rust
fn main() {
    let data = vec![1, 2, 3, 4, 5];

    // 多个共享借用可以共存
    let ref1: &Vec<i32> = &data;
    let ref2: &Vec<i32> = &data;
    let ref3: &Vec<i32> = &data;

    println!("ref1: {:?}", ref1);
    println!("ref2: {:?}", ref2);
    println!("ref3: {:?}", ref3);
}
```

**为什么多个共享借用是安全的？**

```rust
// 形式化证明
// 前提: data: Vec<i32>
// 操作: let r1 = &data; let r2 = &data;

// 1. 共享借用不修改数据
//    ∀r: &T, ∀op ∈ operations(r), op 是只读的

// 2. 数据竞争条件不满足
//    ¬∃write(r1) ∧ ¬∃write(r2)
//    因此无数据竞争

// 3. 别名安全
//    多个只读别名不会破坏不变量
```

### 2.2 可变借用的独占性

可变借用（`&mut T`）提供独占的写访问，关键特性是**排他性**。

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    // 只能有一个可变借用
    let ref1: &mut Vec<i32> = &mut data;
    // let ref2: &mut Vec<i32> = &mut data;  // ❌ 编译错误

    ref1.push(4);
    println!("{:?}", ref1);
}
```

**为什么可变借用必须是唯一的？**

```rust
// 假设允许多个可变借用（危险！）
fn dangerous_scenario() {
    let mut v = vec![1, 2, 3];
    let r1 = &mut v;
    let r2 = &mut v;  // 假设这是允许的

    r1.push(4);  // 可能导致重新分配
    // 如果 v 重新分配了内存
    // r2 现在指向已释放的内存！
    println!("{}", r2[0]);  // 悬垂指针访问！
}
```

### 2.3 共享与可变借用的交互

```rust
fn main() {
    let mut data = String::from("hello");

    // 阶段 1: 共享借用
    let r1 = &data;
    let r2 = &data;
    println!("{} {}", r1, r2);

    // 阶段 2: 共享借用结束，可变借用开始
    let r3 = &mut data;  // ✅ 可以，因为 r1, r2 不再使用
    r3.push_str(" world");
    println!("{}", r3);

    // 阶段 3: 不能再使用 r1, r2
    // println!("{}", r1);  // ❌ 编译错误
}
```

**编译器的生命周期分析**:

```
let mut data = String::from("hello");
let r1 = &data;     ──────────────────┐
let r2 = &data;     ──────────────┐   │
println!(...);                        │   │
                                      │   │
let r3 = &mut data;  ────────────────────┤   │  ← 错误！r1, r2 仍然有效
                                       │   │
// 修正后：                              │   │
let r1 = &data;     ──────────────┐       │
let r2 = &data;     ──────────┐   │       │
println!(...);                 │   │       │
// r1, r2 的生命周期在这里结束   ──┴───┘       │
let r3 = &mut data;  ────────────────────────┘  ← 正确！
```

### 2.4 可变借用的"降级"

可变借用可以"降级"为共享借用：

```rust
fn main() {
    let mut data = vec![1, 2, 3];

    // 获取可变借用
    let mut_ref = &mut data;
    mut_ref.push(4);

    // 可变借用重新借用为共享借用
    let shared_ref: &&Vec<i32> = &&*mut_ref;  // 解引用再引用
    println!("{:?}", shared_ref);

    // 或者更常见的模式
    let shared = &*mut_ref;  // 可变借用 → 共享借用
    println!("{:?}", shared);

    // 但反向不行：
    // let mut_again = &mut *shared;  // ❌ 不能从共享升级到可变
}
```

---

## 3. Non-Lexical Lifetimes (NLL)

### 3.1 NLL 的引入背景

在 NLL 之前，引用的生命周期与词法作用域绑定：

```rust
// 旧版 Rust（2015 edition，无 NLL）
fn old_style() {
    let mut x = 5;
    let y = &x;     // y 的生命周期开始
    let z = &mut x; // ❌ 错误！y 仍然"存活"（词法上）
    println!("{}", y);
}
```

NLL（非词法生命周期）基于实际使用位置而非词法作用域计算生命周期：

```rust
// 现代 Rust（2018+ edition，有 NLL）
fn nll_style() {
    let mut x = 5;
    let y = &x;     // y 借用 x
    println!("{}", y);  // y 最后一次使用
    // y 的生命周期实际上在这里结束

    let z = &mut x; // ✅ 正确！y 已不再需要
    *z += 1;
}
```

### 3.2 NLL 的工作原理

NLL 使用**数据流分析**而非简单的词法作用域：

```rust
fn nll_analysis() {
    let mut data = String::from("hello");

    let r1 = &data;     // 借用开始
    println!("{}", r1); // 最后一次使用 r1
    // ← NLL: r1 的借用在这里结束

    let r2 = &data;     // ✅ 新的借用，r1 已结束
    println!("{}", r2);
    // ← NLL: r2 的借用在这里结束

    let r3 = &mut data; // ✅ 可变借用，之前的借用都已结束
    r3.push_str(" world");
}
```

**控制流感知**: NLL 理解控制流结构：

```rust
fn control_flow_nll() {
    let mut x = 5;

    if condition {
        let r = &x;
        println!("{}", r);
        // r 在这个分支结束时就不再需要
    } else {
        // r 在这个分支中从未存在
    }

    // ✅ 可以获取可变借用，因为所有可能的 r 都已经结束
    let m = &mut x;
    *m = 10;
}
```

### 3.3 NLL 的限制

NLL 虽然强大，但仍有无法处理的情况：

```rust
fn nll_limitation() {
    let mut x = 5;
    let y = &x;

    if condition {
        println!("{}", y);
    }

    // ❌ 即使 condition 为 false，编译器也保守地认为 y 可能还需要
    let z = &mut x;
}
```

解决方案：缩小 y 的作用域：

```rust
fn nll_workaround() {
    let mut x = 5;

    if condition {
        let y = &x;
        println!("{}", y);
        // y 在这里结束
    }

    // ✅ 现在可以获取可变借用
    let z = &mut x;
}
```

### 3.4 NLL 与 Two-Phase Borrows

Two-Phase Borrows 是 NLL 的扩展，允许某些特定的借用模式：

```rust
fn two_phase_borrow() {
    let mut v = vec![1, 2, 3];

    // 在方法调用中，可变借用可以"延迟"到参数评估完成后
    v.push(v.len());  // ✅ 允许！

    // 等价于：
    // let len = v.len();  // 共享借用
    // v.push(len);        // 可变借用
}
```

**工作原理**:

```
1. 方法调用 v.push(v.len()) 开始
2. 评估参数 v.len()
   - 这需要 &v（共享借用）
   - Two-Phase: 暂时允许，标记为"保留"
3. 评估完成后
   - 共享借用结束
   - 激活可变借用 &mut v
4. 执行 push
```

---

## 4. 重新借用 (Reborrowing)

### 4.1 什么是重新借用

重新借用是指从现有引用创建新引用的过程：

```rust
fn main() {
    let mut x = 5;
    let r1 = &mut x;  // 第一次借用

    // 重新借用 r1
    let r2 = &mut *r1;  // 从 &mut x 重新借用
    *r2 = 10;

    // r2 结束后，r1 恢复有效
    println!("{}", r1);  // ✅
}
```

**关键特性**: 重新借用期间，原引用被"冻结"，新引用结束后原引用恢复。

### 4.2 重新借用的形式化定义

**定义 4.1** (重新借用): 对于引用 `r: &'a mut T`，重新借用 `&mut *r` 创建一个新的引用 `r': &'b mut T`，其中 `'b ⊆ 'a`。

**约束**:

```
reborrow(r) → r' 期间:
- r 被冻结（不可用）
- r' 独占访问 T
- r' 结束后，r 恢复有效
```

### 4.3 函数参数中的重新借用

```rust
fn process(data: &mut Vec<i32>) {
    // 这里 data 被重新借用
    push_elements(data);
    // data 恢复有效
    println!("Length: {}", data.len());
}

fn push_elements(data: &mut Vec<i32>) {
    data.push(1);
    data.push(2);
}

fn main() {
    let mut v = vec![0];
    process(&mut v);  // 重新借用 &mut v
    println!("{:?}", v);  // ✅ v 仍然有效
}
```

### 4.4 显式与隐式重新借用

**显式重新借用**:

```rust
let r1 = &mut x;
let r2: &mut i32 = &mut *r1;  // 显式重新借用
```

**隐式重新借用** (自动解引用):

```rust
fn foo(s: &mut String) {
    s.push_str("hello");  // 隐式重新借用
}

let mut s = String::new();
let r = &mut s;
foo(r);      // r 被隐式重新借用为 &mut *r
foo(r);      // ✅ 可以再次调用，因为上次重新借用已结束
```

### 4.5 重新借用与模式匹配

```rust
fn reborrow_in_match() {
    let mut x = Some(String::from("hello"));

    // 重新借用 Option 内部的可变引用
    if let Some(ref mut inner) = x {
        inner.push_str(" world");
    }

    // x 仍然有效
    println!("{:?}", x);  // Some("hello world")
}
```

**模式中的重新借用关键字**:

- `ref` - 创建共享引用
- `ref mut` - 创建可变引用

```rust
fn pattern_reborrow() {
    let mut point = (1, 2);

    // 解构并重新借用
    let (ref x, ref mut y) = point;
    println!("x = {}", x);  // 共享借用
    *y = 10;                 // 可变借用

    // 借用结束后
    println!("{:?}", point);  // (1, 10)
}
```

---

## 5. 常见陷阱与解决方案

### 陷阱 1: 迭代器失效

```rust
fn iterator_invalidation() {
    let mut v = vec![1, 2, 3];

    // ❌ 错误：在迭代时修改集合
    for x in &v {
        v.push(*x);  // 编译错误：不能借入 `v` 作为可变，因为它也被借为不可变
    }
}
```

**解决方案**:

```rust
// 方案 1: 克隆数据
fn solution_clone() {
    let mut v = vec![1, 2, 3];
    let to_add: Vec<_> = v.clone();
    for x in to_add {
        v.push(x);
    }
}

// 方案 2: 收集索引
fn solution_indices() {
    let mut v = vec![1, 2, 3];
    let indices: Vec<_> = (0..v.len()).collect();
    for i in indices {
        let x = v[i];
        v.push(x);
    }
}

// 方案 3: 使用迭代器方法
fn solution_iterator() {
    let v = vec![1, 2, 3];
    let v: Vec<_> = v.iter()
        .cycle()
        .take(v.len() * 2)
        .cloned()
        .collect();
}
```

### 陷阱 2: 自引用结构体

```rust
// ❌ 危险的设计
struct Parser {
    text: String,
    current_token: &str,  // 指向 text 内部
}

impl Parser {
    fn new(text: String) -> Self {
        Parser {
            text,
            current_token: &text[0..5],  // 不能这样做！
        }
    }
}
```

**解决方案**:

```rust
// 方案 1: 存储索引
struct SafeParser {
    text: String,
    token_start: usize,
    token_end: usize,
}

impl SafeParser {
    fn current_token(&self) -> &str {
        &self.text[self.token_start..self.token_end]
    }
}

// 方案 2: 使用 Pin（高级）
use std::pin::Pin;
use std::marker::PhantomPinned;

struct PinnedParser {
    text: String,
    current_token: *const str,
    _pin: PhantomPinned,
}
```

### 陷阱 3: 生命周期标注遗漏

```rust
// ❌ 编译错误：返回的引用生命周期不明确
fn first_word(s: &str) -> &str {
    &s[0..s.find(' ').unwrap_or(s.len())]
}
```

**解决方案**:

```rust
// ✅ 显式生命周期标注
fn first_word<'a>(s: &'a str) -> &'a str {
    &s[0..s.find(' ').unwrap_or(s.len())]
}

// 或使用生命周期省略规则（Elision）
fn first_word(s: &str) -> &str {  // 编译器自动推断
    &s[0..s.find(' ').unwrap_or(s.len())]
}
```

### 陷阱 4: 借用与线程

```rust
use std::thread;

// ❌ 错误：引用不能跨越线程边界
fn thread_borrow() {
    let data = vec![1, 2, 3];
    let handle = thread::spawn(|| {
        println!("{:?}", &data);  // 编译错误：不能捕获引用
    });
    handle.join().unwrap();
}
```

**解决方案**:

```rust
use std::thread;
use std::sync::Arc;

fn thread_ownership() {
    let data = Arc::new(vec![1, 2, 3]);
    let data_clone = Arc::clone(&data);

    let handle = thread::spawn(move || {
        println!("{:?}", data_clone);
    });

    println!("{:?}", data);
    handle.join().unwrap();
}
```

### 陷阱 5: 可变借用与条件编译

```rust
fn conditional_borrow() {
    let mut x = 5;
    let y = &mut x;

    #[cfg(feature = "debug")]
    println!("Debug: {}", y);

    // 在非 debug 构建中，y 实际上不再使用
    // 但编译器保守地认为 y 可能还需要
    let z = &mut x;  // ❌ 可能编译错误
}
```

**解决方案**:

```rust
fn conditional_borrow_fixed() {
    let mut x = 5;

    {
        let y = &mut x;
        #[cfg(feature = "debug")]
        println!("Debug: {}", y);
    }  // y 在这里结束

    let z = &mut x;  // ✅
}
```

---

## 6. 与其他语言对比

### 6.1 C/C++: 裸指针

**C++ 版本**:

```cpp
#include <vector>
#include <iostream>

void dangerous() {
    std::vector<int> v = {1, 2, 3};
    int* ptr = &v[0];

    v.push_back(4);  // 可能导致重新分配

    // ptr 现在可能悬垂！
    std::cout << *ptr << std::endl;  // 未定义行为
}
```

**对比分析**:

| 特性 | Rust | C++ |
|------|------|-----|
| 安全检查 | 编译期 | 无（程序员责任）|
| 悬垂指针 | 编译错误 | 运行时未定义行为 |
| 迭代器失效 | 编译期检测 | 运行时崩溃/UB |
| 性能 | 零成本 | 同等 |

### 6.2 Java: 引用与 GC

**Java 版本**:

```java
import java.util.ArrayList;
import java.util.Iterator;

public class IteratorExample {
    public static void main(String[] args) {
        ArrayList<Integer> list = new ArrayList<>();
        list.add(1);
        list.add(2);
        list.add(3);

        // 快速失败迭代器
        for (Integer x : list) {
            list.add(x);  // 运行时抛出 ConcurrentModificationException
        }
    }
}
```

**对比分析**:

| 特性 | Rust | Java |
|------|------|------|
| 修改检测 | 编译期 | 运行时异常 |
| 内存安全 | 编译期 | GC |
| 性能 | 零运行时检查 | 迭代器状态检查 |

### 6.3 Swift: 值类型与引用类型

**Swift 版本**:

```swift
struct ValueType {
    var data: [Int]
}

class ReferenceType {
    var data: [Int]
    init(_ data: [Int]) { self.data = data }
}

// 值类型：隐式复制
var v1 = ValueType(data: [1, 2, 3])
var v2 = v1  // 复制
v2.data.append(4)
print(v1.data.count)  // 3，v1 未改变

// 引用类型：共享
var r1 = ReferenceType([1, 2, 3])
var r2 = r1  // 共享引用
r2.data.append(4)
print(r1.data.count)  // 4，r1 也改变了
```

**对比分析**:

| 特性 | Rust | Swift |
|------|------|-------|
| 所有权模型 | 显式所有权 + 借用 | ARC + 值/引用类型 |
| 编译期检查 | 完整借用检查 | 有限的逃逸分析 |
| 多线程安全 | 编译期保证 | 需要显式同步 |

### 6.4 Go: 指针与 GC

**Go 版本**:

```go
package main

import "fmt"

func modifySlice(s []int) {
    s[0] = 100  // 修改会影响原切片
    s = append(s, 4)  // 可能重新分配，不影响原切片
}

func main() {
    data := []int{1, 2, 3}
    modifySlice(data)
    fmt.Println(data)  // [100 2 3]
}
```

**对比分析**:

| 特性 | Rust | Go |
|------|------|-----|
| 切片语义 | 显式（&[] vs Vec） | 隐式（切片 vs 数组）|
| 重新分配安全 | 编译期 | 运行时 |
| 并发安全 | 编译期 | 运行时竞争检测（可选）|

---

## 7. 性能影响分析

### 7.1 借用与复制的性能对比

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

// 测试数据
const DATA_SIZE: usize = 1000;

fn bench_borrow(c: &mut Criterion) {
    let data: Vec<u8> = vec![0; DATA_SIZE];

    c.bench_function("borrow", |b| {
        b.iter(|| {
            let sum: u8 = data.iter().sum();  // 借用
            black_box(sum);
        });
    });
}

fn bench_clone(c: &mut Criterion) {
    let data: Vec<u8> = vec![0; DATA_SIZE];

    c.bench_function("clone", |b| {
        b.iter(|| {
            let cloned = data.clone();  // 完整复制
            let sum: u8 = cloned.iter().sum();
            black_box(sum);
        });
    });
}

criterion_group!(benches, bench_borrow, bench_clone);
criterion_main!(benches);
```

**预期结果**:

```
borrow   time:   [50 ns]     # 零成本抽象
clone    time:   [450 ns]    # 内存分配 + 复制
```

### 7.2 可变借用的优化机会

```rust
// 未优化：多次获取可变借用
fn unoptimized(data: &mut Vec<i32>) {
    for i in 0..data.len() {
        data[i] *= 2;  // 每次循环都重新借用
    }
}

// 优化：使用迭代器方法
fn optimized(data: &mut Vec<i32>) {
    for x in data.iter_mut() {
        *x *= 2;  // 单次可变借用，遍历期间保持
    }
}

// 进一步优化：可能使用 SIMD
fn further_optimized(data: &mut [i32]) {
    for chunk in data.chunks_mut(4) {
        for x in chunk {
            *x *= 2;
        }
    }
}
```

### 7.3 共享借用的缓存友好性

```rust
// 场景：并行读取大量数据
fn parallel_read(data: &[f64]) -> f64 {
    use rayon::prelude::*;

    // 多个线程同时共享读取同一数据
    // 数据只读，无缓存一致性开销
    data.par_iter().sum()
}

// 对比：需要锁的读写
fn locked_access(data: &Arc<Mutex<Vec<f64>>>) -> f64 {
    let data = data.lock().unwrap();
    data.iter().sum()  // 缓存行在核间来回传递
}
```

### 7.4 借用检查器的编译时间影响

借用检查是 Rust 编译时间的重要组成部分：

| 代码复杂度 | 借用检查时间占比 | 优化建议 |
|------------|------------------|----------|
| 简单 | 10-20% | 无需优化 |
| 中等 | 20-30% | 适当拆分函数 |
| 复杂（大量泛型） | 30-50% | 使用显式生命周期，减少类型推导 |

---

## 8. 高级借用模式

### 8.1 分离借用（Splitting Borrows）

```rust
fn split_borrow() {
    let mut pair = (String::from("hello"), String::from("world"));

    // 同时借用元组的不同元素
    let first = &mut pair.0;
    let second = &mut pair.1;

    first.push_str("!");
    second.push_str("!");

    println!("({}, {})", pair.0, pair.1);
}
```

### 8.2 结构体字段的独立借用

```rust
struct Point3D {
    x: f64,
    y: f64,
    z: f64,
}

fn borrow_fields() {
    let mut point = Point3D { x: 1.0, y: 2.0, z: 3.0 };

    // 同时可变借用不同字段
    let x = &mut point.x;
    let y = &mut point.y;

    *x += 1.0;
    *y += 2.0;

    // point.z 仍然可以访问
    println!("z = {}", point.z);
}
```

### 8.3 切片模式

```rust
fn slice_patterns(data: &mut [i32]) {
    // 可变切片的拆分
    let (first, rest) = data.split_first_mut().unwrap();
    let (second, rest) = rest.split_first_mut().unwrap();

    *first = 100;
    *second = 200;

    // rest 仍然可用
    for x in rest {
        *x *= 2;
    }
}
```

### 8.4 泛型与借用

```rust
// 使用 Borrow trait 抽象借用
use std::borrow::Borrow;

fn get_value<Q: ?Sized>(map: &HashMap<String, i32>, key: &Q) -> Option<&i32>
where
    String: Borrow<Q>,
    Q: Hash + Eq,
{
    map.get(key)
}

// 可以传入 &String 或 &str
let map: HashMap<String, i32> = ...;
get_value(&map, "key");      // &str
get_value(&map, &String::from("key"));  // &String
```

### 8.5 闭包与借用

```rust
fn closure_borrowing() {
    let mut data = vec![1, 2, 3];

    // FnOnce：获取所有权
    let consume = || {
        let _ = data;  // 移动
    };
    consume();
    // data 不再可用

    let mut data = vec![1, 2, 3];

    // FnMut：可变借用
    let mut modify = || {
        data.push(4);  // 可变借用
    };
    modify();
    modify();  // 可以多次调用

    // Fn：共享借用
    let data = vec![1, 2, 3];
    let read = || {
        println!("{:?}", data);  // 共享借用
    };
    read();
    read();
    println!("{:?}", data);  // data 仍然可用
}
```

---

## 总结

借用是 Rust 所有权系统的核心机制，它提供了：

1. **零成本抽象** - 借用检查在编译期完成，无运行时开销
2. **内存安全** - 编译期防止悬垂指针和数据竞争
3. **灵活性** - 支持复杂的借用模式（重新借用、分离借用等）
4. **NLL 优化** - 基于实际使用情况的生命周期分析

掌握借用的各种模式是编写高效、安全 Rust 代码的关键。

---

*继续学习: [lifetimes-mastery.md](./lifetimes-mastery.md)*
