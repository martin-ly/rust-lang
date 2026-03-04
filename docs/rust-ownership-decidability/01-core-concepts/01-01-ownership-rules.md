# Rust所有权三大规则

> **权威来源**: The Rust Programming Language (Book), Chapter 4
> **形式化参考**: Jung et al. (2018). RustBelt: Securing the Foundations of the Rust Programming Language. POPL

---

## 目录

- [Rust所有权三大规则](#rust所有权三大规则)
  - [目录](#目录)
  - [1. 核心规则体系](#1-核心规则体系)
    - [1.1 三大规则概述](#11-三大规则概述)
    - [1.2 形式化表示](#12-形式化表示)
  - [2. 规则1：每个值都有一个所有者](#2-规则1每个值都有一个所有者)
    - [2.1 所有权建立](#21-所有权建立)
    - [2.2 形式化解释](#22-形式化解释)
  - [3. 规则2：所有者唯一性](#3-规则2所有者唯一性)
    - [3.1 Move语义](#31-move语义)
    - [3.2 形式化：Move as Linear Implication](#32-形式化move-as-linear-implication)
    - [3.3 Copy vs Move](#33-copy-vs-move)
    - [3.4 反例：使用已Move的值](#34-反例使用已move的值)
  - [4. 规则3：作用域与Drop](#4-规则3作用域与drop)
    - [4.1 RAII模式](#41-raii模式)
    - [4.2 形式化：生命周期与作用域](#42-形式化生命周期与作用域)
    - [4.3 Drop trait的形式语义](#43-drop-trait的形式语义)
    - [4.4 反例：忘记释放资源](#44-反例忘记释放资源)
  - [5. 所有权的函数语义](#5-所有权的函数语义)
    - [5.1 函数参数传递](#51-函数参数传递)
    - [5.2 返回值与所有权](#52-返回值与所有权)
  - [6. 所有权与内存模型](#6-所有权与内存模型)
    - [6.1 栈与堆](#61-栈与堆)
    - [6.2 内存安全保证](#62-内存安全保证)
  - [7. 概念矩阵：所有权的多维视角](#7-概念矩阵所有权的多维视角)
  - [8. 常见模式与反例](#8-常见模式与反例)
    - [8.1 模式：使用Clone显式复制](#81-模式使用clone显式复制)
    - [8.2 反例：使用已Move的值](#82-反例使用已move的值)
    - [8.3 模式：函数式更新](#83-模式函数式更新)
  - [9. 与形式化验证的接口](#9-与形式化验证的接口)
  - [10. 参考文献](#10-参考文献)

---

## 1. 核心规则体系

### 1.1 三大规则概述

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Rust所有权三大规则                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  规则1: 每个值都有一个所有者                                          │
│  ────────────────────────────                                        │
│  Each value in Rust has a variable that's called its owner.         │
│                                                                     │
│  规则2: 所有者唯一性                                                  │
│  ────────────────────                                                │
│  There can only be one owner at a time.                             │
│                                                                     │
│  规则3: 所有者离开作用域时值被丢弃                                      │
│  ──────────────────────────────────                                  │
│  When the owner goes out of scope, the value will be dropped.       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 形式化表示

```
基于RustBelt的逻辑关系语义:

所有权谓词: [T].own(t, v) ∈ iProp
- T: 类型
- t: 线程标识
- v: 值列表

规则1 (存在性): ∀v: T. ∃!owner. [T].own(t, v)
规则2 (唯一性): [T].own(t, v) * [T].own(t', v) ⊢ False  (当 t ≠ t')
规则3 (作用域): 当owner scope结束时，自动调用Drop
```

---

## 2. 规则1：每个值都有一个所有者

### 2.1 所有权建立

```rust
fn main() {
    let s = String::from("hello");  // s 是 String值的所有者
    let x = 5;                       // x 是 i32值的所有者
    let v = vec![1, 2, 3];          // v 是 Vec的所有者
}
```

### 2.2 形式化解释

```
仿射类型系统视角:

let s: String = String::from("hello");
─────────────────────────────────────
Γ, s: String ⊢ ...

其中 s 是唯一的所有者，类型 String 是非Copy的(非!A)
```

---

## 3. 规则2：所有者唯一性

### 3.1 Move语义

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // 所有权从s1 MOVE到s2

    // println!("{}", s1);  // 错误! s1不再有效
    println!("{}", s2);      // OK, s2是现在的所有者
}
```

### 3.2 形式化：Move as Linear Implication

```
Move操作的类型理论:

let s1: String = ...;
let s2 = s1;
──────────────────────
Γ, s1: String ⊢ let s2 = s1; ...
───────────────────────────────
Γ ⊢ s2: String, s1: ⊥ (无效)

这对应于线性逻辑的:
String ⊸ String  (消耗一个String产生一个String)
```

### 3.3 Copy vs Move

```rust
// Copy类型 (标量类型, 实现Copy trait)
let a: i32 = 5;
let b = a;  // 复制值，a仍然有效
println!("{}", a);  // OK

// Move类型 (堆分配类型)
let s1 = String::from("hello");
let s2 = s1;  // 转移所有权
// println!("{}", s1);  // 错误!
```

| 类型类别 | 例子 | 行为 | 类型理论 |
|---------|------|------|---------|
| Copy | i32, bool, char, f64 | 复制 | !A (指数) |
| Move | String, Vec, Box | 转移 | A (线性) |

### 3.4 反例：使用已Move的值

```rust
fn use_after_move() {
    let s = String::from("hello");
    let t = s;  // s 被移动到 t

    // 编译错误！
    println!("{}", s);  // error[E0382]: borrow of moved value: `s`
}

// 错误解释:
// s 的所有权已经转移给 t
// s 不再拥有任何值
// 访问 s 是未定义行为
```

---

## 4. 规则3：作用域与Drop

### 4.1 RAII模式

```rust
{
    let s = String::from("hello");  // s进入作用域，分配内存
    // 使用s
}  // s离开作用域，自动调用drop(s)，释放内存
```

### 4.2 形式化：生命周期与作用域

```
基于区域的生命周期:

{                     // 区域 'a 开始
    let s: String;    // s 绑定到 'a
    ...
}                     // 'a 结束，s被drop

类型: s: String^{'a}  (String在区域'a内有效)
```

### 4.3 Drop trait的形式语义

```rust
trait Drop {
    fn drop(&mut self);
}
```

```
在分离逻辑中:

Drop谓词: Drop(T) ≡ ∀v. [T].own(t, v) ⊢ ∃w. v ↦ w * Dealloc(v)

含义: 当T类型的值被drop时，其拥有的资源被释放
```

### 4.4 反例：忘记释放资源

```rust
// 在其他语言中可能发生的情况
// Rust通过Drop trait自动防止

// 假设没有Drop，可能泄漏内存:
fn potential_leak() {
    let _data = vec![0; 1000000];  // 分配大量内存
    // 如果忘记释放，内存泄漏
}  // Rust自动调用drop，释放内存

// 显式泄漏（需要unsafe或Box::leak）
fn explicit_leak() -> &'static i32 {
    let b = Box::new(42);
    Box::leak(b)  // 显式放弃所有权，返回'static引用
}
```

---

## 5. 所有权的函数语义

### 5.1 函数参数传递

```rust
fn takes_ownership(s: String) {  // s进入作用域
    println!("{}", s);
}  // s离开作用域，drop被调用

fn makes_copy(i: i32) {  // i是Copy类型
    println!("{}", i);
}  // i离开作用域，无特殊操作

fn main() {
    let s = String::from("hello");
    takes_ownership(s);  // s移动到函数
    // s不再可用

    let x = 5;
    makes_copy(x);  // x被复制
    // x仍然可用
}
```

### 5.2 返回值与所有权

```rust
fn gives_ownership() -> String {
    let s = String::from("hello");
    s  // s被返回，所有权转移给调用者
}

fn takes_and_gives_back(s: String) -> String {
    s  // 接收并返回s，所有权转移
}
```

---

## 6. 所有权与内存模型

### 6.1 栈与堆

```
┌─────────────────────────────────────────────────────────────┐
│                      内存布局                                │
├─────────────────────────────────────────────────────────────┤
│                                                             │
│  栈 (Stack)                    堆 (Heap)                    │
│  ─────────                     ─────────                     │
│                                                             │
│  let x = 5;                   let s = String::from("hi");   │
│  ┌───────┐                    ┌───────┐     ┌───────────┐   │
│  │ x: 5  │                    │ ptr   │────▶│ "hi"      │   │
│  └───────┘                    │ len   │     │ (堆分配)   │   │
│                               │ cap   │     └───────────┘   │
│                               └───────┘                     │
│                                                             │
│  - 快速分配/释放              - 动态大小                      │
│  - 自动管理                   - 通过所有权管理                │
│  - 固定大小                   - Drop时释放                    │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### 6.2 内存安全保证

Rust所有权系统保证的内存安全：

1. **无悬挂指针**: 所有权转移后原变量无效
2. **无双重释放**: 每个值只有一个所有者，只有一个drop
3. **无内存泄漏**: 作用域结束自动drop (除非显式泄漏)

---

## 7. 概念矩阵：所有权的多维视角

| 视角 | 概念 | Rust语法 | 类型理论 |
|------|------|----------|----------|
| 内存管理 | 所有权 | `let s = String::from("x")` | 线性/仿射类型 |
| 转移 | Move | `let s2 = s1` | 线性蕴含 ⊸ |
| 复制 | Copy | `let y = x` (i32) | 指数 !A |
| 释放 | Drop | 作用域结束 | 资源释放 |
| 借用 | Borrow | `&s`, `&mut s` | 能力类型 |
| 生命周期 | Lifetime | `'a` | 区域类型 |

---

## 8. 常见模式与反例

### 8.1 模式：使用Clone显式复制

```rust
let s1 = String::from("hello");
let s2 = s1.clone();  // 显式深拷贝
// s1和s2都有效
```

### 8.2 反例：使用已Move的值

```rust
let s = String::from("hello");
let t = s;
println!("{}", s);  // 编译错误: use of moved value
```

### 8.3 模式：函数式更新

```rust
fn update(mut s: String) -> String {
    s.push_str(" world");
    s  // 返回所有权
}
```

---

## 9. 与形式化验证的接口

```
RustBelt中的所有权的语义模型:

类型解释:
[[String]].own(t, v) ≡ ∃ℓ. v = [ℓ] * ℓ ↦ "..." * Dealloc(ℓ)

其中:
- ℓ: 堆位置
- ℓ ↦ "...": 该位置的值
- Dealloc(ℓ): 释放权限

所有权的转移对应于分离逻辑中的资源转移:
[T].own(t, v) ──转移──▶ [T].own(t', v)
```

---

## 10. 参考文献

1. Klabnik, S., & Nichols, C. (2018). *The Rust Programming Language*. No Starch Press.
2. Jung, R., et al. (2018). RustBelt: Securing the Foundations of the Rust Programming Language. *POPL*.
3. Weiss, A., Patterson, D., & Ahmed, A. (2020). Oxide: The Essence of Rust. *arXiv:1903.00982*.
