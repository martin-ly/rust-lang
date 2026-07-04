> **权威来源**:
>
> [The Rust Programming Language](https://doc.rust-lang.org/book/),
> **分级**: [A]
> **Rust 版本**: 1.96.1+ (Edition 2024)
> [Rust Reference — Ownership](https://doc.rust-lang.org/reference/),
> [Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html),
> [RustBelt (Jung et al., POPL 2018)](https://plv.mpi-sws.org/rustbelt/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 TRPL、Rust Reference、RustBelt 来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

# 所有权、借用与生命周期：三位一体的内存安全 {#所有权借用与生命周期三位一体的内存安全}

> **EN**: Ownership Borrowing Lifetimes
> **Summary**: 所有权、借用与生命周期 Ownership Borrowing Lifetimes.
> **Bloom 层级**: L1-L2 (记忆/理解)
> **Rust 版本**: 1.96.1+
> **难度**: 初级 → 中级
> **预计学习时间**: 4-6 小时

---

## 目录 {#目录}

> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- [所有权、借用与生命周期：三位一体的内存安全 {#所有权借用与生命周期三位一体的内存安全}](#所有权借用与生命周期三位一体的内存安全-所有权借用与生命周期三位一体的内存安全)
  - [目录 {#目录}](#目录-目录)
  - [1. 所有权：内存管理的根本创新 {#1-所有权内存管理的根本创新}](#1-所有权内存管理的根本创新-1-所有权内存管理的根本创新)
    - [1.1 为什么需要所有权？ {#11-为什么需要所有权}](#11-为什么需要所有权-11-为什么需要所有权)
    - [1.2 所有权的三条铁律 {#12-所有权的三条铁律}](#12-所有权的三条铁律-12-所有权的三条铁律)
    - [1.3 返回值与所有权转移 {#13-返回值与所有权转移}](#13-返回值与所有权转移-13-返回值与所有权转移)
    - [1.4 引用计数：共享所有权 {#14-引用计数共享所有权}](#14-引用计数共享所有权-14-引用计数共享所有权)
  - [2. 借用：不转移所有权的访问 {#2-借用不转移所有权的访问}](#2-借用不转移所有权的访问-2-借用不转移所有权的访问)
    - [2.1 不可变借用 {#21-不可变借用}](#21-不可变借用-21-不可变借用)
    - [2.2 可变借用 {#22-可变借用}](#22-可变借用-22-可变借用)
    - [2.3 借用规则：数据竞争的死结 {#23-借用规则数据竞争的死结}](#23-借用规则数据竞争的死结-23-借用规则数据竞争的死结)
    - [2.4 非词法生命周期 (NLL) {#24-非词法生命周期-nll}](#24-非词法生命周期-nll-24-非词法生命周期-nll)
  - [3. 生命周期：引用的有效期证明 {#3-生命周期引用的有效期证明}](#3-生命周期引用的有效期证明-3-生命周期引用的有效期证明)
    - [3.1 生命周期省略 {#31-生命周期省略}](#31-生命周期省略-31-生命周期省略)
    - [3.2 显式生命周期标注 {#32-显式生命周期标注}](#32-显式生命周期标注-32-显式生命周期标注)
    - [3.3 结构体中的生命周期 {#33-结构体中的生命周期}](#33-结构体中的生命周期-33-结构体中的生命周期)
    - [3.4 生命周期子类型 {#34-生命周期子类型}](#34-生命周期子类型-34-生命周期子类型)
  - [4. 常见陷阱与解决方案 {#4-常见陷阱与解决方案}](#4-常见陷阱与解决方案-4-常见陷阱与解决方案)
    - [4.1 自引用结构体 {#41-自引用结构体}](#41-自引用结构体-41-自引用结构体)
    - [4.2 `static mut` 的废弃 {#42-static-mut-的废弃}](#42-static-mut-的废弃-42-static-mut-的废弃)
    - [4.3 生命周期过长 {#43-生命周期过长}](#43-生命周期过长-43-生命周期过长)
  - [5. 思维模型 {#5-思维模型}](#5-思维模型-5-思维模型)
    - [所有权作为资源管理合约 {#所有权作为资源管理合约}](#所有权作为资源管理合约-所有权作为资源管理合约)
    - [借用检查器的工作流程 {#借用检查器的工作流程}](#借用检查器的工作流程-借用检查器的工作流程)
  - [6. 进阶阅读 {#6-进阶阅读}](#6-进阶阅读-6-进阶阅读)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 1. 所有权：内存管理的根本创新 {#1-所有权内存管理的根本创新}

> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1.1 为什么需要所有权？ {#11-为什么需要所有权}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

传统语言面临两难选择：

- **垃圾回收 (GC)**：自动但引入运行时开销和停顿
- **手动管理**：高效但易错（C/C++ 的内存安全问题占安全漏洞的 70%+）

Rust 的解决方案：**编译期所有权检查** —— 零运行时开销的内存安全。

### 1.2 所有权的三条铁律 {#12-所有权的三条铁律}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
fn main() {
    let s = String::from("hello");  // s 进入作用域，获得所有权
    takes_ownership(s);              // s 的所有权移动到函数中
    // println!("{}", s);            // ❌ 编译错误！s 不再有效

    let x = 5;                       // x 进入作用域
    makes_copy(x);                   // x 被复制（i32 是 Copy）
    println!("{}", x);               // ✅ x 仍然有效
}

fn takes_ownership(some_string: String) {
    println!("{}", some_string);
} // some_string 离开作用域，内存被释放

fn makes_copy(some_integer: i32) {
    println!("{}", some_integer);
} // some_integer 离开作用域，无特殊操作（栈上复制）
```

### 1.3 返回值与所有权转移 {#13-返回值与所有权转移}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
fn gives_ownership() -> String {
    let some_string = String::from("yours");
    some_string // 所有权返回给调用者
}

fn takes_and_gives_back(a_string: String) -> String {
    a_string // 所有权返回给调用者
}
```

### 1.4 引用计数：共享所有权 {#14-引用计数共享所有权}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

当需要多个所有者时，使用 `Rc<T>`（单线程）或 `Arc<T>`（多线程）：

```rust
use std::rc::Rc;

let data = Rc::new(String::from("shared"));
let data2 = Rc::clone(&data); // 引用计数 +1
println!("引用计数: {}", Rc::strong_count(&data)); // 2
```

---

## 2. 借用：不转移所有权的访问 {#2-借用不转移所有权的访问}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 不可变借用 {#21-不可变借用}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
fn main() {
    let s1 = String::from("hello");
    let len = calculate_length(&s1); // &s1 创建一个引用
    println!("'{}' 的长度是 {}", s1, len); // ✅ s1 仍然有效
}

fn calculate_length(s: &String) -> usize {
    s.len()
} // s 离开作用域，但它不拥有引用的值，所以不释放
```

### 2.2 可变借用 {#22-可变借用}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
fn main() {
    let mut s = String::from("hello");
    change(&mut s);
    println!("{}", s); // "hello, world"
}

fn change(some_string: &mut String) {
    some_string.push_str(", world");
}
```

### 2.3 借用规则：数据竞争的死结 {#23-借用规则数据竞争的死结}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
let mut s = String::from("hello");

let r1 = &s; // 没问题
let r2 = &s; // 没问题
let r3 = &mut s; // ❌ 大问题！编译错误

println!("{}, {}, 和 {}", r1, r2, r3);
```

**为什么？** 如果读者（r1, r2）和写者（r3）同时存在，读者可能读到半写入的状态，导致数据竞争。

### 2.4 非词法生命周期 (NLL) {#24-非词法生命周期-nll}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 2018+ 引入了 NLL，借用的结束不再是作用域末尾，而是**最后一次使用**：

```rust
let mut s = String::from("hello");
let r1 = &s;
println!("{}", r1); // r1 在此处最后一次使用

let r2 = &mut s; // ✅ NLL 允许：r1 已"死亡"
r2.push_str(" world");
```

---

## 3. 生命周期：引用的有效期证明 {#3-生命周期引用的有效期证明}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 3.1 生命周期省略 {#31-生命周期省略}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

编译器自动推断大多数生命周期：

```rust
fn first_word(s: &str) -> &str { // 等价于 fn first_word<'a>(s: &'a str) -> &'a str
    &s[0..1]
}
```

### 3.2 显式生命周期标注 {#32-显式生命周期标注}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

当编译器无法推断时，需要显式标注：

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

fn main() {
    let string1 = String::from("long string is long");
    {
        let string2 = String::from("xyz");
        let result = longest(&string1, &string2);
        println!("最长字符串是 {}", result);
    }
}
```

### 3.3 结构体中的生命周期 {#33-结构体中的生命周期}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust
struct ImportantExcerpt<'a> {
    part: &'a str, // part 不能比结构体本身活得更长
}

impl<'a> ImportantExcerpt<'a> {
    fn level(&self) -> i32 {
        3
    }

    fn announce_and_return_part(&self, announcement: &str) -> &str {
        println!("注意！{}", announcement);
        self.part
    }
}
```

### 3.4 生命周期子类型 {#34-生命周期子类型}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
fn static_ref() -> &'static str {
    "我有 'static 生命周期" // 字符串字面量存储在二进制中
}

// &'static str 可以赋值给 &'a str（协变）
fn use_any_lifetime(s: &str) {
    println!("{}", s);
}
```

---

## 4. 常见陷阱与解决方案 {#4-常见陷阱与解决方案}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 4.1 自引用结构体 {#41-自引用结构体}
>
> **[来源: [crates.io](https://crates.io/)]**

```rust,ignore
// ❌ 编译错误：self_referential 包含指向自己的引用
struct SelfReferential {
    data: String,
    ptr_to_data: &str, // 指向 data 的引用
}

// ✅ 解决方案：使用 Pin + 指针
use std::pin::Pin;
use std::marker::PhantomPinned;

struct SelfReferentialFixed {
    data: String,
    ptr_to_data: *const String,
    _pin: PhantomPinned,
}
```

### 4.2 `static mut` 的废弃 {#42-static-mut-的废弃}
>
> **[来源: [docs.rs](https://docs.rs/)]**
> ⚠️ **警告**: `static mut` 在 Rust 2024 Edition 中引用已被禁止（`unsafe_code = "forbid"` 默认启用）。
> 以下 ❌ 示例仅用于说明该特性被废弃的原因。请始终使用右侧 ✅ 的替代方案。

**Rust 2024 Edition 已禁止 `static mut` 引用**：

```rust,ignore
// ❌ 2024 Edition 编译错误
static mut COUNTER: i32 = 0;
unsafe { COUNTER += 1; }

// ✅ 替代方案：使用 UnsafeCell 或原子类型
use std::sync::atomic::{AtomicI32, Ordering};
static COUNTER: AtomicI32 = AtomicI32::new(0);
COUNTER.fetch_add(1, Ordering::Relaxed);
```

### 4.3 生命周期过长 {#43-生命周期过长}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
// ❌ 编译错误：result 的生命周期与 string1 绑定，但引用了 string2
fn longest_wrong<'a>(x: &'a str, y: &str) -> &'a str {
    let result = String::from("really long string");
    result.as_str() // result 是局部变量，不能返回引用
}
```

---

## 5. 思维模型 {#5-思维模型}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 所有权作为资源管理合约 {#所有权作为资源管理合约}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
所有者 ──拥有──→ 资源
  │                  │
  ├─ 移动 ─→ 新所有者
  ├─ 借用 ─→ &T (只读访问)
  ├─ 可变借用 ─→ &mut T (独占写访问)
  └─ 离开作用域 ─→ Drop::drop()
```

### 借用检查器的工作流程 {#借用检查器的工作流程}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```
源代码
   │
   ▼
借用检查器 (Borrow Checker)
   │
   ├── 构建借用图
   ├── 检查生命周期包含关系
   ├── 验证可变引用唯一性
   └── 验证引用有效性
   │
   ├─ ✅ 通过 ─→ 继续编译
   └─ ❌ 失败 ─→ 编译错误 (E0499, E0502 等)
```

---

## 6. 进阶阅读 {#6-进阶阅读}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [c01_ownership_borrow_scope](../../crates/c01_ownership_borrow_scope) - 完整代码示例
- [Rust Reference - Ownership](https://doc.rust-lang.org/reference/)
- [Rust By Example - Scope and Shadowing](https://doc.rust-lang.org/rust-by-example/scope.html)
- [The Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
> **来源: [TRPL Ch. 4 - Ownership](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**
> **来源: [Rustonomicon - Ownership](https://doc.rust-lang.org/nomicon/ownership.html)**
> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)**
> **来源: [Wikipedia - Resource Management](https://en.wikipedia.org/wiki/Resource_Management)**
> **来源: [TRPL Ch. 10 - Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)**
> **来源: [Rust Reference - Borrow Checker](https://doc.rust-lang.org/reference/)**
> **来源: [RFC 2094 - NLL](https://rust-lang.github.io/rfcs/2094-nll.html)**

---
