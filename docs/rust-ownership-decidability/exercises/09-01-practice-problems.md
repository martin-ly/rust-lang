# 实践练习与问题

## 目录

- [实践练习与问题](#实践练习与问题)
  - [目录](#目录)
  - [1. 所有权基础练习](#1-所有权基础练习)
    - [练习 1.1: 修复借用错误](#练习-11-修复借用错误)
    - [练习 1.2: 实现自定义智能指针](#练习-12-实现自定义智能指针)
    - [练习 1.3: 所有权转移链](#练习-13-所有权转移链)
  - [2. 借用与生命周期练习](#2-借用与生命周期练习)
    - [练习 2.1: 标注生命周期](#练习-21-标注生命周期)
    - [练习 2.2: 结构体生命周期](#练习-22-结构体生命周期)
    - [练习 2.3: 修复生命周期错误](#练习-23-修复生命周期错误)
  - [3. 形式化验证练习](#3-形式化验证练习)
    - [练习 3.1: Creusot 规范](#练习-31-creusot-规范)
    - [练习 3.2: 分离逻辑推理](#练习-32-分离逻辑推理)
  - [4. 综合案例练习](#4-综合案例练习)
    - [练习 4.1: 实现线程安全的引用计数](#练习-41-实现线程安全的引用计数)
    - [练习 4.2: 实现安全的双向链表](#练习-42-实现安全的双向链表)
  - [5. 思考题与讨论](#5-思考题与讨论)
    - [思考题 1: 为什么 Rust 选择仿射类型而非线性类型？](#思考题-1-为什么-rust-选择仿射类型而非线性类型)
    - [思考题 2: NLL 与词法生命周期的本质区别是什么？](#思考题-2-nll-与词法生命周期的本质区别是什么)
    - [思考题 3: 分离逻辑的帧规则有什么意义？](#思考题-3-分离逻辑的帧规则有什么意义)
    - [思考题 4: 为什么 Rust 的泛型约束求解是不可判定的？](#思考题-4-为什么-rust-的泛型约束求解是不可判定的)
  - [6. 参考答案](#6-参考答案)
    - [学习建议](#学习建议)
    - [进一步学习资源](#进一步学习资源)

---

## 1. 所有权基础练习

### 练习 1.1: 修复借用错误

**题目**: 修复以下代码中的借用错误

```rust
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;
    let r2 = &mut s;
    println!("{}", r1);
}
```

<details>
<summary>点击查看答案</summary>

```rust
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;
    println!("{}", r1);  // r1 最后一次使用
    let r2 = &mut s;      // 现在可以创建可变借用
    println!("{}", r2);
}
```

**解释**: 在NLL（非词法生命周期）下，r1 在 println 后就不再使用，因此可以创建 r2。
</details>

### 练习 1.2: 实现自定义智能指针

**题目**: 实现一个简单的智能指针 MyBox，包含 Deref 和 Drop

```rust
struct MyBox<T> {
    // 你的实现
}

// 实现 Deref
// 实现 Drop

fn main() {
    let b = MyBox::new(5);
    assert_eq!(*b, 5);
}  // 应该打印 "Dropping MyBox!"
```

<details>
<summary>点击查看答案</summary>

```rust
use std::ops::Deref;

struct MyBox<T> {
    data: T,
}

impl<T> MyBox<T> {
    fn new(x: T) -> MyBox<T> {
        MyBox { data: x }
    }
}

impl<T> Deref for MyBox<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.data
    }
}

impl<T> Drop for MyBox<T> {
    fn drop(&mut self) {
        println!("Dropping MyBox!");
    }
}

fn main() {
    let b = MyBox::new(5);
    assert_eq!(*b, 5);
}
```

</details>

### 练习 1.3: 所有权转移链

**题目**: 追踪以下代码的所有权转移

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = take_ownership(s1);
    let s3 = give_back(s2);
    println!("{}", s3);
}

fn take_ownership(s: String) -> String {
    s.push_str(" world");
    s
}

fn give_back(s: String) -> String {
    s
}
```

<details>
<summary>点击查看答案</summary>

所有权转移链:

1. `s1` 创建，拥有 "hello"
2. `s1` 移动到 `take_ownership` 的 `s`
3. `s` 在函数内修改，返回后移动到 `s2`
4. `s2` 移动到 `give_back` 的 `s`
5. `s` 返回，移动到 `s3`
6. `s3` 被打印

关键点:

- s1 在调用 take_ownership 后不再有效
- s2 在调用 give_back 后不再有效

</details>

---

## 2. 借用与生命周期练习

### 练习 2.1: 标注生命周期

**题目**: 为以下函数标注正确的生命周期

```rust
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}
```

<details>
<summary>点击查看答案</summary>

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

**解释**: 返回值可能引用 x 或 y，因此必须至少和两者中活得较短的一样长。使用相同的生命周期参数 'a 表示这种关系。
</details>

### 练习 2.2: 结构体生命周期

**题目**: 为以下结构体添加生命周期标注

```rust
struct Parser {
    text: &str,
}

impl Parser {
    fn new(text: &str) -> Parser {
        Parser { text }
    }

    fn first_word(&self) -> &str {
        self.text.split_whitespace().next().unwrap_or(""
    }
}
```

<details>
<summary>点击查看答案</summary>

```rust
struct Parser<'a> {
    text: &'a str,
}

impl<'a> Parser<'a> {
    fn new(text: &'a str) -> Parser<'a> {
        Parser { text }
    }

    fn first_word(&self) -> &'a str {
        self.text.split_whitespace().next().unwrap_or(""
    }
}
```

**解释**:

- Parser 保存引用 text，因此需要生命周期参数
- first_word 返回的字符串切片来自 text，因此也是 'a

</details>

### 练习 2.3: 修复生命周期错误

**题目**: 修复以下生命周期错误

```rust
fn make_string() -> &String {
    let s = String::from("hello");
    &s
}
```

<details>
<summary>点击查看答案</summary>

方案1: 返回拥有所有权的值

```rust
fn make_string() -> String {
    let s = String::from("hello");
    s  // 转移所有权
}
```

方案2: 返回 'static 字符串

```rust
fn make_string() -> &'static str {
    "hello"
}
```

**解释**:

- 原代码中 s 在函数结束时被释放
- 返回的引用指向已释放的内存
- 解决方案是转移所有权或返回 'static 数据

</details>

---

## 3. 形式化验证练习

### 练习 3.1: Creusot 规范

**题目**: 为以下函数编写 Creusot 规范

```rust
fn factorial(n: u64) -> u64 {
    let mut result = 1;
    let mut i = 1;
    while i <= n {
        result *= i;
        i += 1;
    }
    result
}
```

<details>
<summary>点击查看答案</summary>

```rust
use creusot_contracts::*;

#[logic]
fn factorial_spec(n: u64) -> u64 {
    if n == 0 { 1 } else { n * factorial_spec(n - 1) }
}

#[requires(n <= 20)]  // 防止溢出
#[ensures(result == factorial_spec(n))]
fn factorial(n: u64) -> u64 {
    let mut result = 1;
    let mut i = 1;

    #[invariant(i <= n + 1)]
    #[invariant(result == factorial_spec(i - 1))]
    while i <= n {
        result *= i;
        i += 1;
    }

    result
}
```

**解释**:

- `factorial_spec` 是逻辑函数，定义阶乘的规范
- `requires` 前置条件：防止整数溢出
- `ensures` 后置条件：结果等于阶乘
- `invariant` 循环不变量：保持正确的中间状态

</details>

### 练习 3.2: 分离逻辑推理

**题目**: 使用分离逻辑推导以下程序的断言

```rust
let mut x = Box::new(5);
*x = 10;
let y = *x;
```

<details>
<summary>点击查看答案</summary>

分离逻辑推导:

```
{ emp }
let mut x = Box::new(5);
{ x ↦ 5 }

*x = 10;
{ x ↦ 10 }

let y = *x;
{ x ↦ 10 * y = 10 }
```

**解释**:

- Box::new 创建堆分配，对应 points-to 断言
- 赋值改变堆值
- 读取创建新变量，保留原有断言

</details>

---

## 4. 综合案例练习

### 练习 4.1: 实现线程安全的引用计数

**题目**: 实现一个简单的 Arc (原子引用计数)

要求:

- 使用 AtomicUsize 进行引用计数
- 实现 Send 和 Sync
- 实现 Clone 和 Drop

<details>
<summary>点击查看答案</summary>

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

struct ArcData<T> {
    ref_count: AtomicUsize,
    data: T,
}

pub struct MyArc<T> {
    ptr: *mut ArcData<T>,
}

unsafe impl<T: Send + Sync> Send for MyArc<T> {}
unsafe impl<T: Send + Sync> Sync for MyArc<T> {}

impl<T> MyArc<T> {
    pub fn new(data: T) -> MyArc<T> {
        let boxed = Box::new(ArcData {
            ref_count: AtomicUsize::new(1),
            data,
        });
        MyArc {
            ptr: Box::into_raw(boxed),
        }
    }

    pub fn clone(&self) -> MyArc<T> {
        unsafe {
            (*self.ptr).ref_count.fetch_add(1, Ordering::Relaxed);
        }
        MyArc { ptr: self.ptr }
    }
}

impl<T> Drop for MyArc<T> {
    fn drop(&mut self) {
        unsafe {
            if (*self.ptr).ref_count.fetch_sub(1, Ordering::Release) == 1 {
                std::sync::atomic::fence(Ordering::Acquire);
                drop(Box::from_raw(self.ptr));
            }
        }
    }
}
```

**关键概念**:

- 原子操作保证线程安全
- Send/Sync 标记表示可以跨线程
- Drop 中需要内存屏障保证正确性

</details>

### 练习 4.2: 实现安全的双向链表

**题目**: 实现一个使用 Box 和裸指针的安全双向链表

<details>
<summary>点击查看答案</summary>

```rust
struct Node<T> {
    data: T,
    next: Option<Box<Node<T>>>,
    prev: *mut Node<T>,
}

pub struct LinkedList<T> {
    head: Option<Box<Node<T>>>,
    tail: *mut Node<T>,
}

impl<T> LinkedList<T> {
    pub fn new() -> Self {
        LinkedList {
            head: None,
            tail: std::ptr::null_mut(),
        }
    }

    pub fn push_front(&mut self, data: T) {
        let mut new_node = Box::new(Node {
            data,
            next: self.head.take(),
            prev: std::ptr::null_mut(),
        });

        let raw_node: *mut _ = &mut *new_node;

        if let Some(ref mut old_head) = new_node.next {
            old_head.prev = raw_node;
        } else {
            self.tail = raw_node;
        }

        self.head = Some(new_node);
    }
}
```

**关键点**:

- 使用 Box 管理所有权
- 使用裸指针处理反向链接
- 需要 unsafe 但保证安全不变量

</details>

---

## 5. 思考题与讨论

### 思考题 1: 为什么 Rust 选择仿射类型而非线性类型？

**参考答案要点**:

1. 实用性：允许未使用的变量
2. Drop trait：自动清理资源
3. 更符合直觉：程序员不需要显式处理每个值
4. 可判定性：完整仿射逻辑可判定，线性逻辑不可判定
5. 编译器优化：允许死代码消除

### 思考题 2: NLL 与词法生命周期的本质区别是什么？

**参考答案要点**:

1. 基于使用位置 vs 基于作用域范围
2. 数据流分析 vs 语法分析
3. 接受更多安全程序
4. 基于 CFG 而非 AST
5. 使用活跃性分析确定生命周期终点

### 思考题 3: 分离逻辑的帧规则有什么意义？

**参考答案要点**:

1. 模块化推理：局部验证蕴含全局正确性
2. 简化内存推理：自动处理不相关部分
3. 组合性：可以组合小证明为大证明
4. 是 RustBelt 等验证工具的基础
5. 对应 Rust 的模块化和封装

### 思考题 4: 为什么 Rust 的泛型约束求解是不可判定的？

**参考答案要点**:

1. 类型系统可以编码图灵机
2. 通过递归 trait 约束实现循环
3. 常量求值可能不终止
4. 编译器使用启发式限制递归深度
5. 实践中大多数代码是可判定的

---

## 6. 参考答案

所有练习的答案都在对应的详情标签中。建议先自己尝试，然后再查看答案。

### 学习建议

1. **逐步深入**: 从所有权基础开始，逐步到借用、生命周期、验证
2. **动手实践**: 多写代码，编译错误是最好的老师
3. **理解原理**: 不只是修复错误，要理解背后的类型理论
4. **阅读源码**: 查看标准库的实现，学习最佳实践
5. **使用工具**: 尝试 Creusot、Prusti 等验证工具

### 进一步学习资源

- [The Rust Programming Language](https://doc.rust-lang.org/book/)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
- [RustBelt Paper](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Creusot Tutorial](https://github.com/creusot-rs/creusot)
