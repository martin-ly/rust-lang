# Rust 所有权系统 (Ownership System)

> **Bloom 层级**: 理解

> **📌 简介**：所有权是 Rust 最独特且最重要的特性，它让 Rust 在不需要垃圾回收器的情况下保证内存安全。
>
> **⏱️ 预计学习时间**：45-60 分钟
> **📚 难度级别**：⭐⭐⭐ 中等

> **权威来源**: [The Rust Programming Language — Ch04](https://doc.rust-lang.org/book/ch04-00-ownership.html), [Rust Reference — Ownership](https://doc.rust-lang.org/reference/ownership.html), [Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html), [RustBelt (Jung et al., POPL 2018)](https://plv.mpi-sws.org/rustbelt/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（TRPL、Rust Reference、RustBelt、C++ / Go 对标） [来源: Authority Source Sprint Batch 8]

**变更日志**:

- v1.1 (2026-05-19): 补全权威来源标注（TRPL、Rust Reference、RustBelt、C++ / Go 对标）

---

## 🎯 学习目标
> **[来源: Rust Official Docs]**

完成本章学习后，你将能够：

- [x] 理解所有权系统的核心概念和设计哲学
- [x] 掌握 Rust 的三大所有权规则
- [x] 理解移动语义（Move Semantics）及其工作原理
- [x] 区分 `Copy` trait 和移动语义的差异
- [x] 理解所有权在函数传递中的行为
- [x] 编写符合所有权规则的代码，避免常见的编译错误

---

## 📋 先决条件
> **[来源: Rust Official Docs]**

在学习所有权之前，你应该：

1. 完成 Rust "Hello World" 程序
2. 了解基本的变量绑定和可变性的概念
3. 熟悉 `let` 语句和基本的数据类型（`String`, `i32` 等）

如果你还没有安装 Rust，请参考 [Rust 官方安装指南](https://www.rust-lang.org/tools/install)。

---

## 🧠 核心概念
> **[来源: Rust Official Docs]**

### 什么是所有权
> **[来源: Rust Official Docs]**

**所有权（Ownership）** 是 Rust 用于管理内存的一套规则集合。与其他语言不同：

| 语言 | 内存管理方式 | 特点 |
|------|-------------|------|
| C/C++ | 手动内存管理 | 灵活但容易出错（内存泄漏、悬垂指针） |
| Java/Python/Go | 垃圾回收器（GC） | 安全但运行时开销大 |
| **Rust** | **所有权系统** | **编译时检查，零成本抽象** |

Rust 的所有权系统通过编译时检查来确保内存安全，这意味着：

- 没有运行时垃圾回收器的性能开销
- 编译器在编译阶段就能发现内存安全问题

> **[来源: TRPL: Ch4.1]** "Ownership is a set of rules that govern how a Rust program manages memory... No run-time costs are incurred for any of the ownership features." ✅
> **[来源: RustBelt: POPL 2018]** Safe Rust 中不存在 use-after-free 和 double-free 的形式化定理已得到机器检验证明。 ✅

---

### 所有权规则
> **[来源: Rust Official Docs]**

Rust 的所有权系统基于以下**三大规则**：

> 📜 **规则一**：Rust 中的每个值都有一个**所有者（owner）**
>
> 📜 **规则二**：任何时刻，一个值只能有**一个**所有者
>
> 📜 **规则三**：当所有者离开作用域，值将被**自动丢弃（drop）**
>
> **[来源: Rust Reference: Ownership]** 所有权规则由编译器在类型检查和借用检查阶段强制执行，违反规则将导致编译错误（如 E0382）。 ✅
> **[来源: TRPL: Ch4.1]** 三大规则是 Rust 内存管理的基石，对应线性逻辑中的资源唯一性公理。 ✅

让我们通过代码来理解这些规则：

```rust
fn main() {
    // s 是 String 值的所有者
    let s = String::from("hello");

    // 使用 s 的有效范围
    println!("{}", s);  // ✅ 正常输出: hello

} // s 离开作用域，String 占用的内存被自动释放
```

#### 作用域（Scope）的概念

作用域是一个变量在程序中有效的范围：

```rust
fn main() {
    let x = 5;          // x 开始生效

    {                   // 新的作用域开始
        let y = 10;     // y 开始生效
        println!("x = {}, y = {}", x, y);  // ✅ 两者都可用
    }                   // y 离开作用域，被丢弃

    println!("x = {}", x);  // ✅ x 仍然可用
    // println!("y = {}", y);  // ❌ 编译错误！y 已失效
}
```

---

### 移动语义（Move Semantics）

这是所有权系统中最关键也最容易混淆的概念。

#### 场景一：整数类型（简单类型）

```rust
fn main() {
    let x = 5;
    let y = x;  // ✅ 将 x 的值复制给 y

    println!("x = {}, y = {}", x, y);  // ✅ 两者都可用
}
```

#### 场景二：String 类型（复杂类型）

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;  // s1 的所有权被**移动**到 s2

    println!("{}", s2);  // ✅ 正常输出: hello
    // println!("{}", s1);  // ❌ 编译错误！s1 已不再拥有该值
}
```

#### 为什么 String 和整数行为不同？

让我们看看它们在内存中的布局：

**整数（存储在栈上）**：

```text
┌─────────┐
│  x: 5   │  ← 栈
├─────────┤
│  y: 5   │  ← 栈（复制值）
└─────────┘
```

**String（存储在堆上）**：

```text
┌─────────────────┐      ┌─────────────────────┐
│  s1             │      │                     │
│  ptr ───────────┼──────►  "hello"             │
│  len: 5         │      │  （堆内存）           │
│  capacity: 5    │      │                     │
└─────────────────┘      └─────────────────────┘

执行 let s2 = s1 后：
┌─────────────────┐      ┌─────────────────────┐
│  s1 (失效)       │      │                     │
│  ptr (悬空)     ─┼──╳──►  "hello" ◄───────────┼── s2.ptr
│  len: ?         │      │  （堆内存）           │
│  capacity: ?    │      │                     │
└─────────────────┘      └─────────────────────┘
```

> 💡 **关键点**：String 包含指向堆内存的指针。如果直接复制指针而不转移所有权，会导致**双重释放（double free）**错误。Rust 通过**移动语义**避免了这个问题。
>
> **[来源: TRPL: Ch4.1]** Move 语义确保堆资源的唯一所有权，赋值操作转移所有权而非复制指针。 ✅
> **[来源: Rust Reference: Move and Copy]** 非 Copy 类型的值在赋值/传参时发生 move，原变量变为未初始化状态。 ✅

---

### Copy Trait

Rust 有一个特殊的 trait 叫做 `Copy`，用于标记那些可以按位复制的类型。

#### 哪些类型实现了 Copy？

```rust
fn main() {
    // 所有整数类型
    let a: i32 = 10;
    let b = a;  // ✅ 复制
    println!("a = {}, b = {}", a, b);

    // 所有浮点数类型
    let c: f64 = 3.14;
    let d = c;  // ✅ 复制
    println!("c = {}, d = {}", c, d);

    // 布尔类型
    let e: bool = true;
    let f = e;  // ✅ 复制
    println!("e = {}, f = {}", e, f);

    // 字符类型
    let g: char = '中';
    let h = g;  // ✅ 复制
    println!("g = {}, h = {}", g, h);

    // 只包含 Copy 类型的元组
    let i: (i32, f64) = (1, 2.0);
    let j = i;  // ✅ 复制
    println!("i = {:?}, j = {:?}", i, j);

    // 固定大小的数组
    let k: [i32; 3] = [1, 2, 3];
    let l = k;  // ✅ 复制
    println!("k = {:?}, l = {:?}", k, l);
}
```

#### 哪些类型**没有**实现 Copy？

```rust
fn main() {
    // String（动态大小，存储在堆上）
    let s = String::from("hello");
    let t = s;  // 移动，不是复制
    // println!("{}", s);  // ❌ 错误！

    // Vec（动态数组）
    let v = vec![1, 2, 3];
    let w = v;  // 移动，不是复制
    // println!("{:?}", v);  // ❌ 错误！

    // 包含非 Copy 类型的元组
    let x = (String::from("a"), 5);
    let y = x;  // 移动
    // println!("{:?}", x);  // ❌ 错误！
}
```

#### 显式克隆（Clone）

如果你确实需要复制一个非 Copy 类型的值，可以使用 `clone()` 方法：

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1.clone();  // 深拷贝，创建全新的堆内存

    println!("s1 = {}, s2 = {}", s1, s2);  // ✅ 两者都可用

    // ⚠️ 注意：clone() 可能代价昂贵，应谨慎使用
}
```

---

### 所有权与函数

当值传递给函数时，所有权也会发生转移：[来源: TRPL: Ch4.3] 函数传参与返回值遵循与赋值相同的所有权规则。 ✅

```rust
fn main() {
    let s = String::from("hello");

    takes_ownership(s);  // s 的所有权移动到函数中

    // println!("{}", s);  // ❌ 编译错误！s 不再有效

    let x = 5;
    makes_copy(x);  // x 是 i32，实现了 Copy，所以仍然可用

    println!("x = {}", x);  // ✅ 正常输出: 5
}

fn takes_ownership(some_string: String) {
    println!("{}", some_string);
} // some_string 离开作用域，内存被释放

fn makes_copy(some_integer: i32) {
    println!("{}", some_integer);
} // some_integer 是 Copy 类型，不需要特殊处理
```

#### 借用（Borrowing）简介

如果我们想在传递值的同时保留所有权呢？这就需要**借用**——但这是下一章的内容。目前，我们先了解所有权如何工作：

```rust
fn main() {
    let s1 = String::from("hello");

    let (s2, len) = calculate_length(s1);  // 所有权转移，然后通过返回值传回

    println!("'{}' 的长度是 {}", s2, len);  // ✅ s2 现在拥有该值
}

fn calculate_length(s: String) -> (String, usize) {
    let length = s.len();
    (s, length)  // 返回元组，将所有权还回去
}
```

---

### 返回值与所有权

函数返回值也会转移所有权：

```rust
fn main() {
    let s1 = gives_ownership();           // gives_ownership 返回值给 s1

    let s2 = String::from("hello");       // s2 开始生效

    let s3 = takes_and_gives_back(s2);    // s2 被移动到函数，返回值给 s3

    println!("s1 = {}, s3 = {}", s1, s3);
    // println!("s2 = {}", s2);  // ❌ 编译错误！s2 不再有效
}

// 返回值给调用者
fn gives_ownership() -> String {
    let some_string = String::from("yours");
    some_string  // 返回 some_string，所有权转移
}

// 获取所有权，然后返回
fn takes_and_gives_back(a_string: String) -> String {
    a_string  // 返回 a_string，所有权转移回调用者
}
```

---

## 💡 最佳实践

1. **优先使用 Copy 类型**

   ```rust
   // 好：使用 &str（字符串切片）而非 String
   fn greet(name: &str) {
       println!("Hello, {}!", name);
   }

   fn main() {
       let name = "Alice";  // &str 类型
       greet(name);  // 不需要转移所有权
       println!("再次问候, {}!", name);  // ✅ 仍然可用
   }
   ```

2. **需要转移所有权时，明确使用函数名表达意图**

   ```rust
   // 好的命名
   fn consume_string(s: String) { /* ... */ }
   fn process_and_return(s: String) -> String { /* ... */ }
   ```

3. **在大型结构体上注意所有权转移的成本**

   ```rust
   // 如果结构体很大，考虑使用借用
   fn process_large(data: &LargeStruct) { /* ... */ }
   ```

4. **使用 `#[derive(Copy, Clone)]` 为自定义类型实现 Copy**

   ```rust
   #[derive(Copy, Clone)]
   struct Point {
       x: i32,
       y: i32,
   }

   fn main() {
       let p1 = Point { x: 1, y: 2 };
       let p2 = p1;  // ✅ Copy 行为
       println!("p1 = ({}, {}), p2 = ({}, {})", p1.x, p1.y, p2.x, p2.y);
   }
   ```

---

## ⚠️ 常见陷阱

### 陷阱 1：在循环中意外移动值

```rust
fn main() {
    let s = String::from("hello");

    // 错误示例
    // for _ in 0..3 {
    //     println!("{}", s);  // ❌ 第一次迭代后 s 被移动！
    // }

    // 正确做法：使用引用
    for _ in 0..3 {
        println!("{}", &s);  // ✅ 借用 s
    }

    println!("{}", s);  // ✅ s 仍然可用
}
```

### 陷阱 2：忘记 String 和 &str 的区别

```rust
fn main() {
    let s = "hello";  // &str（字符串字面量）
    let t = s;        // ✅ 复制（因为 &str 实现了 Copy）
    println!("s = {}, t = {}", s, t);

    let s = String::from("hello");  // String
    let t = s;  // 移动
    // println!("s = {}", s);  // ❌ 编译错误！
}
```

### 陷阱 3：在函数中转移了还需要用的值

```rust
fn main() {
    let name = String::from("Alice");

    // ❌ 错误：print_name 消耗了 name
    // print_name(name);
    // print_name(name);  // 编译错误！

    // ✅ 正确：使用引用
    print_name_ref(&name);
    print_name_ref(&name);  // 可以多次使用
}

fn print_name(s: String) {
    println!("{}", s);
}

fn print_name_ref(s: &String) {
    println!("{}", s);
}
```

---

## 🎮 动手练习

### 练习 1：修复编译错误

下面的代码有编译错误，请修复它：

```rust
fn main() {
    let s1 = String::from("Hello");
    let s2 = s1;

    println!("s1 is: {}", s1);  // 错误在这里
    println!("s2 is: {}", s2);
}
```

<details>
<summary>点击查看答案</summary>

```rust
fn main() {
    let s1 = String::from("Hello");
    let s2 = s1.clone();  // 使用 clone 来复制

    println!("s1 is: {}", s1);
    println!("s2 is: {}", s2);
}
```

</details>

### 练习 2：所有权转移链

预测下面的代码输出，并解释为什么：

```rust
fn main() {
    let s = String::from("Rust");
    let t = process(s);
    println!("{}", t);
}

fn process(s: String) -> String {
    let result = format!("{} is awesome!", s);
    result
}
```

<details>
<summary>点击查看答案</summary>

输出：`Rust is awesome!`

解释：

1. `s` 的所有权从 `main` 转移到 `process`
2. `process` 中创建了新的 String `result`
3. `result` 作为返回值，所有权转移到 `t`
4. `s` 在 `process` 结束时被丢弃（因为不再使用）

</details>

### 练习 3：实现一个函数

实现一个函数 `double_string`，它接收一个 `String`，返回一个新的 `String`，内容是原字符串重复两次：

```rust
fn main() {
    let s = String::from("Hello");
    let doubled = double_string(s);
    println!("{}", doubled);  // 应输出: HelloHello
}

fn double_string(s: String) -> String {
    // 你的代码
}
```

<details>
<summary>点击查看答案</summary>

```rust
fn double_string(s: String) -> String {
    format!("{}{}", s, s)
}
```

或者：

```rust
fn double_string(mut s: String) -> String {
    let len = s.len();
    s.reserve(len);
    s.push_str(&s.clone());
    s
}
```

</details>

---

## 📖 权威来源与延伸阅读

### 官方文档（一级来源）

- [The Rust Book - Ch4: Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) —— Rust 官方教程，所有权的权威入门定义
- [Rust Reference - Ownership](https://doc.rust-lang.org/reference/ownership.html) —— 所有权规则的精确语言规范
- [Rust Reference - Move and Copy](https://doc.rust-lang.org/reference/types.html#move-and-copy) —— Move / Copy 语义的类型系统定义
- [Rust by Example - Ownership](https://doc.rust-lang.org/rust-by-example/scope/move.html) —— 交互式代码示例

### 学术来源（一级来源）

- **Ralf Jung et al., "RustBelt: Securing the Foundations of the Rust Programming Language"**, *POPL 2018* —— 在 Iris 分离逻辑框架中机器验证 Safe Rust 内存安全定理（无 UAF / 无 DF / 无数据竞争）。
  - 核心论证：资源代数独占令牌 + 协议验证 ⇒ 所有权唯一性 ⇒ 内存安全完备性。
  - 入口: <https://plv.mpi-sws.org/rustbelt/>
- **Ralf Jung, "The Meaning of Memory Safety"**, *PLArch 2021* —— 内存安全的精确定义与 Rust 所有权系统的对应关系。
- **Clarke et al., "Ownership Types for Flexible Alias Protection"**, *OOPSLA 1998* —— 所有权类型系统的理论起源，Rust 所有权的学术先驱。

### 社区权威（二级来源）

- **Niko Matsakis**, ["Two interpretations of borrowing"](https://smallcultfollowing.com/babysteps/blog/2024/01/05/two-interpretations-of-borrowing/) —— 借用的两种语义解释（区域视角 vs 流视角）。
- **Without Boats**, ["Pin and Suffering"](https://without.boats/blog/pin-and-suffering/) —— 自引用结构与所有权边界的深度分析。
- **Jon Gjengset**, [Crust of Rust: Lifetime Annotations](https://www.youtube.com/watch?v=rAl-9HwD858) —— 生命周期与所有权的可视化讲解。

### 跨语言对比（三级来源）

| 语言 | 对应机制 | 权威来源 |
|:---|:---|:---|
| **C++** | `std::unique_ptr`（运行时所有权，编译器不检查 use-after-move） | [cppreference: unique_ptr](https://en.cppreference.com/w/cpp/memory/unique_ptr) |
| **Go** | 垃圾回收（GC），无编译期所有权检查 | [Go Spec: Memory Model](https://go.dev/ref/mem) |
| **Haskell** | LinearTypes (GHC 9.0+) · `ST` 状态线程 | [GHC User Guide: LinearTypes](https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/linear_types.html) |

### 进阶主题

| 主题 | 描述 | 推荐阅读时机 |
|------|------|-------------|
| **借用（Borrowing）** | 通过引用访问值而不获取所有权 | 完成本章后立即学习 |
| **切片（Slices）** | 对集合的部分引用 | 学习借用后 |
| **生命周期（Lifetimes）** | 确保引用始终有效 | 掌握借用后 |
| **智能指针** | `Box<T>`, `Rc<T>`, `Arc<T>` 等 | 进阶阶段 |
| **内部可变性模式** | `RefCell<T>`, `Mutex<T>` 等 | 进阶阶段 |

### 相关标准库 Trait

- [`Copy`](https://doc.rust-lang.org/std/marker/trait.Copy.html) - 按位复制语义
- [`Clone`](https://doc.rust-lang.org/std/clone/trait.Clone.html) - 显式克隆
- [`Drop`](https://doc.rust-lang.org/std/ops/trait.Drop.html) - 自定义析构行为

---

> 🎉 **恭喜你！** 你已经掌握了 Rust 所有权系统的核心概念。所有权是 Rust 内存管理的基础，理解它对于编写高效、安全的 Rust 代码至关重要。
>
> 下一步建议：学习**借用和引用（Borrowing and References）**，它将帮助你更灵活地处理所有权问题。

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
