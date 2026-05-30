> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/),
> **分级**: [A]
> [Rust Reference](https://doc.rust-lang.org/reference/),
> [Rustonomicon](https://doc.rust-lang.org/nomicon/)
> **层次定位**: L1-L2 基础-进阶 / 核心概念总览
> **前置依赖**: 无（入门入口）
> **后置延伸**: [docs 指南](../03_guides/) · [docs 参考](../02_reference/) · [concept L1-L2](../../concept/)
> **跨层映射**: docs→concept 工程映射 | L1-L2 概念索引
> **定理链编号**: T-001 → T-010 → T-020 → T-030

>
> **权威来源对齐变更日志**: 2026-05-19 新增 TRPL、Rust Reference、Rustonomicon 来源标注 [来源: Authority Source Sprint Batch 8]

# Rust 核心概念 (Core Concepts)

> **Bloom 层级**: L1-L2 (记忆/理解)
> **Rust 版本**: 1.96.0+
> **Edition**: 2024
> **最后更新**: 2026-05-07
> **状态**: 🚧 持续完善中

---

## 目录

> **[来源: Rust Official Docs]**

- [Rust 核心概念 (Core Concepts)](#rust-核心概念-core-concepts)
  - [目录](#目录)
  - [1. 所有权 (Ownership)](#1-所有权-ownership)
    - [概念定义](#概念定义)
    - [所有权规则](#所有权规则)
    - [移动语义 (Move Semantics)](#移动语义-move-semantics)
    - [Copy 类型](#copy-类型)
  - [2. 借用与引用 (Borrowing \& References)](#2-借用与引用-borrowing--references)
    - [概念定义](#概念定义)
    - [借用规则](#借用规则)
    - [悬垂引用防护](#悬垂引用防护)
  - [3. 生命周期 (Lifetimes)](#3-生命周期-lifetimes)
    - [概念定义](#概念定义)
    - [生命周期省略规则 (Elision Rules)](#生命周期省略规则-elision-rules)
    - [`'static` 生命周期](#static-生命周期)
  - [4. 类型系统基础 (Type System Basics)](#4-类型系统基础-type-system-basics)
    - [核心类型分类](#核心类型分类)
    - [泛型与 Trait](#泛型与-trait)
    - [Rust 2024 Edition 类型系统增强](#rust-2024-edition-类型系统增强)
  - [5. 内存安全保证 (Memory Safety Guarantees)](#5-内存安全保证-memory-safety-guarantees)
    - [Rust 消除的内存错误类别](#rust-消除的内存错误类别)
    - [unsafe Rust](#unsafe-rust)
  - [6. 与 Wikipedia 概念对齐](#6-与-wikipedia-概念对齐)
  - [学习路径](#学习路径)
  - [相关链接](#相关链接)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

---

## 1. 所有权 (Ownership)
>
> **[来源: Rust Official Docs]**

### 概念定义

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**
>
> **[来源: Rust Official Docs]**

所有权是 Rust 最核心、最独特的语言特性。每个值在任意时刻有且仅有一个**所有者 (owner)**，当所有者离开作用域时，值被**丢弃 (drop)**。

```rust
{
    let s = String::from("hello"); // s 是 "hello" 的所有者
    // s 在此有效
} // s 离开作用域，"hello" 被释放
```

### 所有权规则
>
> **[来源: Rust Official Docs]**

1. 每个值有一个所有者
2. 同一时间只能有一个所有者
3. 所有者离开作用域，值被丢弃

### 移动语义 (Move Semantics)
>
> **[来源: Rust Official Docs]**

```rust
let s1 = String::from("hello");
let s2 = s1; // s1 的所有权移动到 s2
// println!("{}", s1); // ❌ 编译错误：s1 已失效
```

### Copy 类型
>
> **[来源: Rust Official Docs]**

实现 `Copy` trait 的类型在赋值时**复制**而非**移动**：

```rust
let x = 5;
let y = x; // i32 是 Copy，x 仍然有效
println!("x = {}, y = {}", x, y); // ✅
```

| 类型类别 | 示例 | 语义 |
|---------|------|------|
| Copy 标量 | `i32`, `f64`, `bool`, `char` | 复制 |
| Copy 元组 | `(i32, bool)`（仅含 Copy 元素） | 复制 |
| Copy 引用 | `&T`, `&mut T` | 复制 |
| 非 Copy | `String`, `Vec<T>`, `Box<T>` | 移动 |

---

## 2. 借用与引用 (Borrowing & References)
>
> **[来源: Rust Official Docs]**

### 概念定义
>
> **[来源: Rust Official Docs]**

**借用 (Borrowing)** 允许在不转移所有权的情况下临时访问数据。

```rust
fn calculate_length(s: &String) -> usize {
    s.len()
} // s 在此处归还，不释放内存

let s1 = String::from("hello");
let len = calculate_length(&s1); // 不可变借用
println!("'{}' 的长度是 {}", s1, len); // ✅ s1 仍然有效
```

### 借用规则
>
> **[来源: Rust Official Docs]**

1. **任意数量**的不可变引用 (`&T`)
2. **仅一个**可变引用 (`&mut T`)
3. 两者**不能同时存在**

```rust
let mut s = String::from("hello");

let r1 = &s; // 不可变引用
let r2 = &s; // 另一个不可变引用 ✅
// let r3 = &mut s; // ❌ 编译错误：不能在有不可变引用时创建可变引用

println!("{} and {}", r1, r2); // r1, r2 最后一次使用

let r3 = &mut s; // ✅ r1, r2 不再使用，可变借用合法
r3.push_str(" world");
```

### 悬垂引用防护
>
> **[来源: Rust Official Docs]**

Rust 编译器确保引用永远不会比被引用的数据活得更长：

```rust,ignore
fn dangle() -> &String { // ❌ 编译错误
    let s = String::from("hello");
    &s
} // s 被释放，返回的引用悬垂
```

---

## 3. 生命周期 (Lifetimes)
>
> **[来源: Rust Official Docs]**

### 概念定义

生命周期是 Rust 借用检查器使用的**形式化标注**，描述引用的有效范围。

```rust
// 显式生命周期标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

### 生命周期省略规则 (Elision Rules)

编译器自动推断常见模式：

1. 每个引用参数获得独立生命周期
2. 如果只有一个输入生命周期，它分配给所有输出生命周期
3. 如果有 `&self` 或 `&mut self`，其生命周期分配给所有输出

### `'static` 生命周期

`'static` 表示**整个程序运行期间**有效：

```rust
let s: &'static str = "我是字符串字面量，存储在二进制中";
```

⚠️ **常见误解**：`'static` 不意味着内存泄漏或永不释放，而是指数据在程序结束前一直有效。

---

## 4. 类型系统基础 (Type System Basics)

### 核心类型分类

| 类别 | 类型 | 说明 |
|------|------|------|
| 标量 | `i32`, `u64`, `f32`, `bool`, `char` | 单一值 |
| 复合 | `[T; N]`, `(T, U)`, `struct`, `enum` | 组合多个值 |
| 引用 | `&T`, `&mut T` | 借用 |
| 指针 | `*const T`, `*mut T` | 裸指针（unsafe） |
| 函数 | `fn(T) -> U` | 函数指针 |
| trait 对象 | `dyn Trait` | 动态分发 |

### 泛型与 Trait

```rust
// 泛型函数
fn largest<T: PartialOrd>(list: &[T]) -> &T {
    let mut largest = &list[0];
    for item in list {
        if item > largest { largest = item; }
    }
    largest
}

// Trait 约束
pub trait Summary {
    fn summarize(&self) -> String;
}

fn notify<T: Summary>(item: &T) {
    println!("快讯！{}", item.summarize());
}
```

### Rust 2024 Edition 类型系统增强

- **RPIT lifetime capture rules**: `impl Trait` 的默认生命周期捕获更精确
- **`use<..>` precise capturing**: 显式控制哪些泛型参数被捕获（实验性演进）
- **Never type fallback**: `!` 类型的回退行为调整

---

## 5. 内存安全保证 (Memory Safety Guarantees)

### Rust 消除的内存错误类别

| 错误类型 | C/C++ 状态 | Rust 防护 |
|---------|-----------|----------|
| 使用已释放内存 (UAF) | 常见漏洞 | ✅ 所有权+Drop 防止 |
| 双重释放 | 常见漏洞 | ✅ 所有权唯一性防止 |
| 缓冲区溢出 | 常见漏洞 | ✅ 边界检查+借用检查防止 |
| 数据竞争 | 常见漏洞 | ✅ 借用规则防止 |
| 悬垂指针 | 常见漏洞 | ✅ 生命周期检查防止 |
| 空指针解引用 | 常见漏洞 | ✅ `Option<T>` + 强制处理 |

### unsafe Rust

当需要绕过编译器检查时，使用 `unsafe` 块：

```rust
unsafe {
    // 解引用裸指针
    // 调用 unsafe 函数
    // 访问 union 字段
    // 等等...
}
```

⚠️ **原则**：`unsafe` 块越小越好，且必须有 `// SAFETY:` 注释说明为何安全。

---

## 6. 与 Wikipedia 概念对齐

| Rust 概念 | Wikipedia 对应条目 | 核心属性 | Rust 特定实现 |
|----------|-------------------|---------|-------------|
| Ownership | [Linear type](https://en.wikipedia.org/wiki/Substructural_type_system#Linear_type) | 资源唯一性、移动语义 | `Drop` trait、move |
| Borrowing | [Alias analysis](https://en.wikipedia.org/wiki/Alias_analysis) | 别名控制、读写分离 | `&T` / `&mut T` |
| Lifetime | [Region-based memory management](https://en.wikipedia.org/wiki/Region-based_memory_management) | 作用域绑定、形式化标注 | `'a` 语法 |
| Type Safety | [Type safety](https://en.wikipedia.org/wiki/Type_safety) | 编译期排除未定义行为 | Borrow checker |
| RAII | [Resource acquisition is initialization](https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization) | 构造获取、析构释放 | `Drop` + ownership |
| Pattern Matching | [Pattern matching](https://en.wikipedia.org/wiki/Pattern_matching) | 解构与绑定 | `match`, `if let` |
| Zero-cost Abstraction | [Zero-overhead principle](https://en.wikipedia.org/wiki/Zero-overhead_principle) | 高级特性不引入运行时开销 | 迭代器、泛型 Monomorphization |

---

## 学习路径

```text
初学者
├── 1. 所有权三规则
├── 2. 移动 vs 复制
├── 3. 不可变引用 &T
├── 4. 可变引用 &mut T
├── 5. 借用规则（编译器错误理解）
└── 6. 基础生命周期概念

进阶
├── 7. 生命周期标注语法
├── 8. 生命周期省略规则
├── 9. 结构体中的引用生命周期
├── 10. trait 对象与生命周期
└── 11. 'static 的准确含义

高级
├── 12. 自引用结构体与 Pin
├── 13. 协变/逆变/不变 (Variance)
├── 14. Higher-Ranked Trait Bounds (for<'a>)
└── 15. 形式化语义理解 (Stacked Borrows / Tree Borrows)
```

---

## 相关链接

- [c01_ownership_borrow_scope](../../crates/c01_ownership_borrow_scope/) - 所有权 crate 深度示例
- [c02_type_system](../../crates/c02_type_system/) - 类型系统 crate
- [c03_control_fn](../../crates/c03_control_fn/) - 控制流与函数
- [The Rust Book - Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [The Rustonomicon](https://doc.rust-lang.org/nomicon/)
- [Rust Reference - Lifetimes](https://doc.rust-lang.org/reference/items/generics.html#lifetime-parameters)

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [所有权、借用与生命周期详解](./01_ownership_borrowing_lifetimes.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference - doc.rust-lang.org/reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library - doc.rust-lang.org/std]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**
