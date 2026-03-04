# 借用概念卡片 (Borrowing Concept Card)

> Rust所有权系统的核心机制 - 临时访问而不转移所有权

---

## 目录

- [借用概念卡片 (Borrowing Concept Card)](#借用概念卡片-borrowing-concept-card)
  - [目录](#目录)
  - [1. 概念定义](#1-概念定义)
    - [1.1 什么是借用](#11-什么是借用)
    - [1.2 借用的本质](#12-借用的本质)
    - [1.3 两种借用类型](#13-两种借用类型)
  - [2. 形式化语义](#2-形式化语义)
    - [2.1 借用作为资源](#21-借用作为资源)
    - [2.2 借用规则的形式化](#22-借用规则的形式化)
    - [2.3 借用状态机](#23-借用状态机)
  - [3. 借用规则详解](#3-借用规则详解)
    - [3.1 核心规则](#31-核心规则)
    - [3.2 规则背后的原理](#32-规则背后的原理)
    - [3.3 NLL (Non-Lexical Lifetimes)](#33-nll-non-lexical-lifetimes)
    - [3.4 重新借用 (Reborrowing)](#34-重新借用-reborrowing)
  - [4. 生命周期机制](#4-生命周期机制)
    - [4.1 生命周期与借用](#41-生命周期与借用)
    - [4.2 生命周期省略规则](#42-生命周期省略规则)
    - [4.3 生命周期与借用检查](#43-生命周期与借用检查)
  - [5. 代码示例](#5-代码示例)
    - [5.1 基础借用模式](#51-基础借用模式)
    - [5.2 复杂借用场景](#52-复杂借用场景)
    - [5.3 高级借用模式](#53-高级借用模式)
  - [6. 常见错误与解决](#6-常见错误与解决)
    - [6.1 同时读写错误](#61-同时读写错误)
    - [6.2 生命周期不匹配](#62-生命周期不匹配)
    - [6.3 迭代器失效](#63-迭代器失效)
  - [7. 设计模式](#7-设计模式)
    - [7.1 访问者模式](#71-访问者模式)
    - [7.2 观察者模式](#72-观察者模式)
    - [7.3 RAII与借用结合](#73-raii与借用结合)
  - [8. 性能考虑](#8-性能考虑)
    - [8.1 借用vs克隆](#81-借用vs克隆)
    - [8.2 零成本抽象](#82-零成本抽象)
    - [8.3 缓存友好性](#83-缓存友好性)
  - [9. 与其他语言对比](#9-与其他语言对比)
    - [9.1 C/C++ 指针](#91-cc-指针)
    - [9.2 Java/C# 引用](#92-javac-引用)
    - [9.3 函数式语言](#93-函数式语言)
  - [总结](#总结)

---

## 1. 概念定义

### 1.1 什么是借用

**借用(Borrowing)** 是Rust中临时获取值的引用而不转移所有权的机制。

```rust
let s = String::from("hello");  // s拥有字符串
let r = &s;                      // r借用s（不转移所有权）
println!("{}", r);               // 使用借用
println!("{}", s);               // s仍然有效！
```

### 1.2 借用的本质

从形式化角度看，借用创建了一个**受限的视图**：

```
所有权:  ┌─────────────┐
        │   值 v      │
        │  (类型 T)   │
        └──────┬──────┘
               │ owns
               ▼
            owner
               │
        ┌──────┴──────┐
        │             │
        ▼             ▼
    借用 &T      借用 &mut T
    (只读视图)    (读写视图)
```

### 1.3 两种借用类型

| 类型 | 符号 | 权限 | 数量限制 | 用例 |
|------|------|------|----------|------|
| 共享借用 | `&T` | 只读 | 无限多个 | 并行读取 |
| 可变借用 | `&mut T` | 读写 | 唯一一个 | 独占修改 |

---

## 2. 形式化语义

### 2.1 借用作为资源

在分离逻辑中，借用可以表示为：

```
共享借用:  &x: T  ↦  Shared(x, T)
可变借用:  &mut x: T  ↦  Mutable(x, T)
```

### 2.2 借用规则的形式化

**规则 2.1** (借用创建):

```
own(x, T)    x: T
────────────────────
Shared(x, T)  &x: &T
```

**规则 2.2** (可变借用创建):

```
own(x, T)    x: T    无活跃借用
───────────────────────────────
Mutable(x, T)  &mut x: &mut T
```

**规则 2.3** (借用结束):

```
Shared(x, T)  →  own(x, T)  （当最后一个共享借用结束）
Mutable(x, T) →  own(x, T)  （当可变借用结束）
```

### 2.3 借用状态机

```
         ┌─────────────┐
         │   Owned     │
         │  (独占)     │
         └──────┬──────┘
                │
       ┌────────┴────────┐
       │                 │
       ▼                 ▼
┌─────────────┐   ┌─────────────┐
│   Shared    │   │   Mutable   │
│  (n个读者)  │   │  (1个写者)  │
│   n ≥ 1     │   │             │
└──────┬──────┘   └──────┬──────┘
       │                 │
       └────────┬────────┘
                ▼
         ┌─────────────┐
         │   Owned     │
         │  (归还)     │
         └─────────────┘
```

**状态转换约束**:

- Owned → Shared: 允许
- Owned → Mutable: 允许
- Shared → Owned: 当所有共享借用结束
- Mutable → Owned: 当可变借用结束
- Shared → Mutable: ❌ 禁止
- Mutable → Shared: ❌ 禁止

---

## 3. 借用规则详解

### 3.1 核心规则

**规则 3.1** (借用不变式):
> 在任意给定时刻，对于同一数据，只能满足以下条件之一：
>
> 1. 一个可变引用 `&mut T`
> 2. 任意数量的不可变引用 `&T`

### 3.2 规则背后的原理

**为什么禁止同时读写？**

```rust
// 假设Rust允许这样（实际不行）
let mut data = vec![1, 2, 3];
let r1 = &data[0];      // 读取第一个元素
let r2 = &mut data;      // 获取可变引用
r2.push(4);              // 重新分配内存！
println!("{}", r1);       // 危险！r1可能指向已释放内存
```

**问题**: `push`可能导致`Vec`重新分配内存，使`r1`成为悬空指针。

### 3.3 NLL (Non-Lexical Lifetimes)

Rust 2018+ 引入NLL，借用的生命周期在**最后使用处**结束，而非词法作用域结束。

```rust
let mut s = String::from("hello");

let r1 = &s;           // ──┐
println!("{}", r1);    //    │ r1的生命周期
                       // ───┘ 在这里结束

let r2 = &mut s;       // 现在可以创建可变借用！
r2.push_str(" world");
```

### 3.4 重新借用 (Reborrowing)

```rust
fn process(s: &mut String) {
    // 重新借用s的可变引用
    let r = &mut *s;
    r.push_str("!");
    // r在这里结束，s恢复有效
}

let mut s = String::from("hello");
process(&mut s);
println!("{}", s);  // "hello!"
```

---

## 4. 生命周期机制

### 4.1 生命周期与借用

每个借用都有隐式或显式的生命周期：

```rust
// 显式生命周期
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 隐式生命周期（省略规则）
fn first_word(s: &str) -> &str {  // 等价于 fn first_word<'a>(s: &'a str) -> &'a str
    // ...
}
```

### 4.2 生命周期省略规则

编译器自动推断的三种情况：

1. **每个输入引用参数获得独立生命周期**
2. **如果只有一个输入生命周期，它分配给所有输出**
3. **如果有`&self`或`&mut self`，其生命周期分配给所有输出**

### 4.3 生命周期与借用检查

```rust
fn example() {
    let r;          // r的生命周期: 'outer
    {
        let x = 5;  // x的生命周期: 'inner
        r = &x;     // 错误: 'inner 比 'outer 短
    }               // x在这里被释放
    println!("{}", r);  // r将引用无效内存！
}
```

**编译器错误**:

```
error: `x` does not live long enough
```

---

## 5. 代码示例

### 5.1 基础借用模式

```rust
// 模式1: 只读遍历
fn print_all(items: &[i32]) {
    for item in items {
        println!("{}", item);
    }
}

// 模式2: 可变修改
fn double_all(items: &mut [i32]) {
    for item in items.iter_mut() {
        *item *= 2;
    }
}

// 模式3: 返回借用
fn first(items: &[i32]) -> Option<&i32> {
    items.first()
}
```

### 5.2 复杂借用场景

```rust
// 同时借用结构体的不同字段
struct Point { x: i32, y: i32 }

fn modify_point(p: &mut Point) -> (&mut i32, &mut i32) {
    (&mut p.x, &mut p.y)  // OK: 借用不同字段
}

// 借用嵌套数据
struct Person { name: String, age: u32 }

fn get_name(person: &Person) -> &str {
    &person.name  // 返回内部数据的借用
}
```

### 5.3 高级借用模式

```rust
// 自引用结构（使用Pin）
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    ptr: *const String,
    _pin: PhantomPinned,
}

impl SelfReferential {
    fn new(data: String) -> Pin<Box<Self>> {
        let mut boxed = Box::pin(Self {
            data,
            ptr: std::ptr::null(),
            _pin: PhantomPinned,
        });

        let ptr = &boxed.data as *const String;
        unsafe {
            let mut_ref = Pin::as_mut(&mut boxed);
            Pin::get_unchecked_mut(mut_ref).ptr = ptr;
        }

        boxed
    }
}
```

---

## 6. 常见错误与解决

### 6.1 同时读写错误

```rust
// 错误代码
let mut s = String::from("hello");
let r1 = &s;
let r2 = &mut s;  // 错误！
println!("{}", r1);
```

**解决方案**:

```rust
// 方案1: 分离作用域
let mut s = String::from("hello");
{
    let r1 = &s;
    println!("{}", r1);
}
let r2 = &mut s;  // OK!

// 方案2: NLL（Rust 2018+）
let mut s = String::from("hello");
let r1 = &s;
println!("{}", r1);  // r1最后一次使用
let r2 = &mut s;      // OK!
```

### 6.2 生命周期不匹配

```rust
// 错误代码
fn return_dangling() -> &String {
    let s = String::from("hello");
    &s  // 错误: s将在函数结束时释放
}
```

**解决方案**:

```rust
// 方案1: 返回所有权
fn return_owned() -> String {
    String::from("hello")
}

// 方案2: 返回静态生命周期
fn return_static() -> &'static str {
    "hello"  // 字符串字面量有'static生命周期
}

// 方案3: 使用智能指针
use std::sync::Arc;
fn return_shared() -> Arc<String> {
    Arc::new(String::from("hello"))
}
```

### 6.3 迭代器失效

```rust
// 错误代码
let mut vec = vec![1, 2, 3];
for item in &vec {
    vec.push(item * 2);  // 错误！
}
```

**解决方案**:

```rust
// 方案1: 先收集再处理
let to_add: Vec<_> = vec.iter().map(|x| x * 2).collect();
vec.extend(to_add);

// 方案2: 使用索引
let len = vec.len();
for i in 0..len {
    let val = vec[i];
    vec.push(val * 2);
}
```

---

## 7. 设计模式

### 7.1 访问者模式

```rust
trait Visitor {
    fn visit_node(&mut self, node: &Node);
}

struct Node {
    value: i32,
    children: Vec<Node>,
}

impl Node {
    fn accept(&self, visitor: &mut dyn Visitor) {
        visitor.visit_node(self);
        for child in &self.children {
            child.accept(visitor);
        }
    }
}
```

### 7.2 观察者模式

```rust
trait Observer {
    fn update(&self, event: &Event);
}

struct Subject<'a> {
    observers: Vec<&'a dyn Observer>,
}

impl<'a> Subject<'a> {
    fn register(&mut self, observer: &'a dyn Observer) {
        self.observers.push(observer);
    }

    fn notify(&self, event: &Event) {
        for observer in &self.observers {
            observer.update(event);
        }
    }
}
```

### 7.3 RAII与借用结合

```rust
struct Guard<'a> {
    data: &'a mut Data,
    original: Data,
}

impl<'a> Guard<'a> {
    fn new(data: &'a mut Data) -> Self {
        let original = data.clone();
        Self { data, original }
    }
}

impl<'a> Drop for Guard<'a> {
    fn drop(&mut self) {
        if !self.commit {
            *self.data = self.original.clone();  // 回滚
        }
    }
}
```

---

## 8. 性能考虑

### 8.1 借用vs克隆

```rust
// 借用 - O(1)，无内存分配
fn process_borrow(data: &[u8]) {
    // 只是传递指针
}

// 克隆 - O(n)，可能分配内存
fn process_clone(data: Vec<u8>) {
    // 数据被复制
}
```

### 8.2 零成本抽象

借用编译后就是指针，无运行时开销：

```rust
pub fn get_first(arr: &[i32]) -> Option<&i32> {
    arr.first()
}
// 编译后等价于C的: const int* get_first(const int* arr, size_t len)
```

### 8.3 缓存友好性

借用允许数据就地处理，提高缓存命中率：

```rust
// 好的: 数据局部性好
fn sum(values: &[i32]) -> i32 {
    values.iter().sum()
}

// 差的: 可能需要间接访问
fn sum_iter(values: impl Iterator<Item = i32>) -> i32 {
    values.sum()
}
```

---

## 9. 与其他语言对比

### 9.1 C/C++ 指针

| 特性 | Rust借用 | C/C++指针 |
|------|----------|-----------|
| 空指针 | 编译期检查 | 运行时错误 |
| 悬空指针 | 编译期检查 | 未定义行为 |
| 数据竞争 | 编译期检查 | 运行时错误 |
| 修改权限 | 显式(&mut) | 隐式 |
| 多引用 | 受控 | 无限制 |

### 9.2 Java/C# 引用

| 特性 | Rust借用 | Java/C#引用 |
|------|----------|-------------|
| 垃圾回收 | 编译期确定 | 运行时GC |
| 空值 | Option<T> | null |
| 可变状态 | 显式控制 | 默认可变 |
| 并发安全 | 编译期保证 | 运行时检查 |

### 9.3 函数式语言

| 特性 | Rust借用 | Haskell/OCaml |
|------|----------|---------------|
| 不可变性 | 默认(&T) | 完全不可变 |
| 可变状态 | &mut T | Monad/Ref |
| 性能 | 零成本 | 可能有开销 |
| 学习曲线 | 陡峭 | 中等 |

---

## 总结

借用是Rust所有权系统的核心创新：

1. **安全**: 编译期防止悬空指针和数据竞争
2. **灵活**: 支持只读和读写两种模式
3. **高效**: 零成本抽象，编译为原始指针
4. **表达**: 支持复杂数据结构和安全并发

掌握借用是掌握Rust的关键。
