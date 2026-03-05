# Rust借用系统深度分析

> **权威来源**: The Rust Programming Language, Chapter 4.2
> **形式化参考**: Weiss et al. (2020). Oxide: The Essence of Rust

---

## 目录

- [Rust借用系统深度分析](#rust借用系统深度分析)
  - [目录](#目录)
  - [1. 借用系统的核心原则](#1-借用系统的核心原则)
    - [1.1 借用的动机](#11-借用的动机)
    - [1.2 借用规则](#12-借用规则)
  - [2. 不可变借用 (\&T)](#2-不可变借用-t)
    - [2.1 基本语法](#21-基本语法)
    - [2.2 形式化：共享借用](#22-形式化共享借用)
    - [2.3 示例：多读者模式](#23-示例多读者模式)
  - [3. 可变借用 (\&mut T)](#3-可变借用-mut-t)
    - [3.1 独占访问](#31-独占访问)
    - [3.2 形式化：可变借用](#32-形式化可变借用)
    - [3.3 反例：同时多个可变借用](#33-反例同时多个可变借用)
  - [4. 借用规则的形式化](#4-借用规则的形式化)
    - [4.1 别名互斥规则](#41-别名互斥规则)
    - [4.2 借用检查器的判断](#42-借用检查器的判断)
  - [5. 悬挂引用预防](#5-悬挂引用预防)
    - [5.1 编译时检查](#51-编译时检查)
    - [5.2 反例：返回局部引用](#52-反例返回局部引用)
    - [5.3 解决方案](#53-解决方案)
  - [6. 重新借用 (Reborrowing)](#6-重新借用-reborrowing)
    - [6.1 概念](#61-概念)
    - [6.2 形式化](#62-形式化)
  - [7. 借用与模式匹配](#7-借用与模式匹配)
    - [7.1 解构借用](#71-解构借用)
    - [7.2 部分借用](#72-部分借用)
  - [8. 借用检查算法的演进](#8-借用检查算法的演进)
    - [8.1 词法生命周期](#81-词法生命周期)
    - [8.2 非词法生命周期 (NLL)](#82-非词法生命周期-nll)
  - [9. 借用系统的类型理论总结](#9-借用系统的类型理论总结)
  - [10. 实例与案例分析](#10-实例与案例分析)
    - [10.1 链表迭代](#101-链表迭代)
    - [10.2 树遍历](#102-树遍历)
    - [10.3 并发读取](#103-并发读取)
  - [11. 与其他理论的联系](#11-与其他理论的联系)
  - [12. 参考文献](#12-参考文献)

---

## 1. 借用系统的核心原则

### 1.1 借用的动机

所有权系统的一个问题：严格的Move语义导致频繁的所有权转移。

```rust
fn main() {
    let s = String::from("hello");
    let len = calculate_length(s);  // s被move到函数
    // println!("{}", s);  // 错误! s已被move
    println!("length: {}", len);
}

fn calculate_length(s: String) -> (String, usize) {
    let len = s.len();
    (s, len)  // 必须返回s才能继续使用
}
```

借用允许临时访问而不转移所有权：

```rust
fn main() {
    let s = String::from("hello");
    let len = calculate_length(&s);  // 借用s
    println!("{}'s length is {}", s, len);  // s仍然可用
}

fn calculate_length(s: &String) -> usize {
    s.len()  // 只读访问
}
```

### 1.2 借用规则

```text
┌─────────────────────────────────────────────────────────────────────┐
│                    借用规则 (Borrowing Rules)                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  在任意给定时刻，只能满足以下之一:                                     │
│                                                                     │
│  1. 一个可变引用 (&mut T)                                            │
│  2. 任意数量的不可变引用 (&T)                                         │
│                                                                     │
│  但不能同时满足两者!                                                │
│                                                                     │
│  附加规则: 引用必须始终有效 (引用的值不能在其生命周期结束前被释放)      │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## 2. 不可变借用 (&T)

### 2.1 基本语法

```rust
fn main() {
    let s = String::from("hello");

    let r1 = &s;  // 不可变借用1
    let r2 = &s;  // 不可变借用2 - 允许！
    let r3 = &s;  // 不可变借用3 - 允许！

    println!("{}, {}, {}", r1, r2, r3);
}  // 所有借用在这里结束
```

### 2.2 形式化：共享借用

```text
在分离逻辑中的表示:

[&T].share(t, v) ≡ ∃ℓ. v = [ℓ] * readonly(ℓ, T)

其中:
- readonly(ℓ, T): 位置ℓ的只读权限
- 多个线程/变量可以同时持有share权限
```

### 2.3 示例：多读者模式

```rust
// 多读者场景：配置读取
struct Config {
    settings: HashMap<String, String>,
}

fn read_config(config: &Config) {
    // 多个函数可以同时读取配置
    let reader1 = &config.settings;
    let reader2 = &config.settings;
    let reader3 = &config.settings;

    // 所有读者同时存在是安全的
    println!("{:?}", reader1.get("key1"));
    println!("{:?}", reader2.get("key2"));
    println!("{:?}", reader3.get("key3"));
}
```

---

## 3. 可变借用 (&mut T)

### 3.1 独占访问

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;  // 可变借用
    // let r2 = &mut s;  // 错误! 不能同时有两个可变借用

    r1.push_str(" world");
    println!("{}", r1);
}
```

### 3.2 形式化：可变借用

```text
基于RustBelt的生命周期逻辑:

[&mut T].own(t, [ℓ]) ≡ ∃α. &^α(∃v. ℓ ↦ v * ▷[[T]].own(t, v))

其中:
- α: 生命周期变量
- &^α: 区域α上的借用
- ▷: later modality (用于递归类型)
- ℓ ↦ v: 堆位置ℓ包含值v
```

### 3.3 反例：同时多个可变借用

```rust
fn multiple_mut_borrows() {
    let mut data = vec![1, 2, 3];

    let r1 = &mut data;
    let r2 = &mut data;  // 编译错误！

    r1.push(4);
    r2.push(5);
}

// 错误: cannot borrow `data` as mutable more than once at a time
// 原因: r1 和 r2 可能同时修改 data，导致数据竞争
```

---

## 4. 借用规则的形式化

### 4.1 别名互斥规则

```text
读写互斥规则的形式化:

Γ ⊢ e: &mut T    Γ, x: T ⊢ e': T'
──────────────────────────────────── (使用可变借用)
Γ ⊢ let x = *e in e': T'

约束: 在e'中，不能同时出现:
- 对*e的读取
- 对*e的写入 (通过其他引用)
```

### 4.2 借用检查器的判断

```text
借用检查器维护的上下文:

Loan Context L ::= · | L, loan(ℓ, kind, region)

其中:
- ℓ: 借用的路径
- kind: Shared | Mut
- region: 生命周期

冲突检测:
loan(ℓ, Mut, r) ∈ L  ∧  loan(ℓ', _, r') ∈ L
⊢ conflict 如果 paths_conflict(ℓ, ℓ') ∧ regions_overlap(r, r')
```

---

## 5. 悬挂引用预防

### 5.1 编译时检查

```rust
fn dangle() -> &String {  // 错误!
    let s = String::from("hello");
    &s  // s在函数结束时被drop
}  // 返回的引用指向无效内存
```

错误信息：

```text
error[E0106]: missing lifetime specifier
 --> src/main.rs:1:16
  |
1 | fn dangle() -> &String {
  |                ^ expected named lifetime parameter
```

### 5.2 反例：返回局部引用

```rust
fn dangling_reference() -> &i32 {
    let x = 5;
    &x  // x 在这里离开作用域被释放
}

// 编译错误: `x` does not live long enough
// returned reference points to `x`, which is dropped
```

### 5.3 解决方案

```rust
fn no_dangle() -> String {
    let s = String::from("hello");
    s  // 转移所有权，而非返回引用
}

// 或者使用 'static
fn get_static() -> &'static str {
    "always valid"
}
```

---

## 6. 重新借用 (Reborrowing)

### 6.1 概念

```rust
fn main() {
    let mut s = String::from("hello");
    let r1 = &mut s;
    let r2 = &mut *r1;  // 从r1重新借用

    // r1在这里被"冻结"，直到r2不再使用
    println!("{}", r2);
    // r2作用域结束，r1重新激活
    println!("{}", r1);
}
```

### 6.2 形式化

```text
重新借用的类型规则:

Γ ⊢ r: &mut^{α} T    α' ⊆ α
────────────────────────────
Γ ⊢ &mut^{α'} *r: &mut^{α'} T

原借用r在α'期间被冻结
```

---

## 7. 借用与模式匹配

### 7.1 解构借用

```rust
fn main() {
    let mut v = vec![1, 2, 3];

    match &mut v {
        // 借用整个vec
        vec => vec.push(4),
    }

    // 部分借用
    if let Some(first) = v.first_mut() {
        *first = 10;  // 只修改第一个元素
    }
    // v仍然可用
    println!("{:?}", v);
}
```

### 7.2 部分借用

```rust
struct Point { x: i32, y: i32 }

fn main() {
    let mut p = Point { x: 0, y: 0 };

    let x = &mut p.x;  // 借用x字段
    let y = &mut p.y;  // 借用y字段 - 允许！

    *x = 5;
    *y = 10;
}
```

---

## 8. 借用检查算法的演进

### 8.1 词法生命周期

```rust
// Rust 1.0 - 基于词法作用域
fn lexical_example() {
    let mut data = vec![1, 2, 3];
    let slice = &data[0];  // 借用开始

    // 即使这里不再使用slice，借用仍持续到作用域结束
    // data.push(4);  // 错误! slice仍然"活"着

    println!("{}", slice);  // 最后使用
}  // 借用结束
```

### 8.2 非词法生命周期 (NLL)

```rust
// Rust 2018+ - 基于控制流
fn nll_example() {
    let mut data = vec![1, 2, 3];
    let slice = &data[0];

    println!("{}", slice);  // 最后一次使用

    // slice的借用在这里结束！
    data.push(4);  // OK!
}
```

NLL的关键：生命周期基于**使用位置**而非**作用域范围**。

---

## 9. 借用系统的类型理论总结

| Rust概念 | 类型理论对应 | 形式化表示 |
|---------|-------------|-----------|
| &T | 共享借用 | share(ℓ, T) |
| &mut T | 独占借用 | &^α(exists v. ℓ ↦ v * T(v)) |
| 借用冲突 | 资源冲突 | loan_conflict |
| 生命周期 | 区域 | region α |
| 重新借用 | 子借用 | reborrow ⊆ |

---

## 10. 实例与案例分析

### 10.1 链表迭代

```rust
struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

// 使用借用安全地迭代
fn iterate_list<T>(head: &Node<T>) {
    let mut current = Some(head);

    while let Some(node) = current {
        println!("{}", node.value);
        current = node.next.as_deref();  // 借用next
    }
}
```

### 10.2 树遍历

```rust
struct TreeNode<T> {
    value: T,
    left: Option<Box<TreeNode<T>>>,
    right: Option<Box<TreeNode<T>>>,
}

// 中序遍历 - 使用借用
fn inorder_traversal<T>(root: &TreeNode<T>) {
    if let Some(ref left) = root.left {
        inorder_traversal(left);
    }
    println!("{}", root.value);
    if let Some(ref right) = root.right {
        inorder_traversal(right);
    }
}
```

### 10.3 并发读取

```rust
use std::thread;

fn concurrent_reads() {
    let data = vec![1, 2, 3, 4, 5];

    // 多个线程可以同时读取
    let handles: Vec<_> = (0..3)
        .map(|i| {
            let slice = &data[i..i+2];
            thread::spawn(move || {
                println!("Thread {:?}", slice);
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
```

---

## 11. 与其他理论的联系

```text
借用系统 ←→ 其他理论

分离逻辑:
- &T 对应 readonly(ℓ)
- &mut T 对应 ℓ ↦ v

线性逻辑:
- 借用对应于 "!" 和 "?" 模态

区域类型:
- 生命周期对应于区域变量

能力类型系统:
- 借用是一种能力 (capability)
```

---

## 12. 参考文献

1. Weiss, A., Patterson, D., & Ahmed, A. (2020). Oxide: The Essence of Rust. *arXiv:1903.00982*.
2. Jung, R., et al. (2017). RustBelt: Securing the Foundations of the Rust Programming Language. *POPL*.
3. Rust RFC 2094: Non-Lexical Lifetimes.
