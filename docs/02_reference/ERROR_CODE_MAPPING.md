# Rust 编译器错误码映射文档

> **创建日期**: 2026-02-13
> **最后更新**: 2026-03-17
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 常见 Rust 编译器错误码快速定位、理解与修复
> **权威源**: [Compiler Error Index](https://doc.rust-lang.org/error-index.html)

---

## 目录

- [Rust 编译器错误码映射文档](#rust-编译器错误码映射文档)
  - [目录](#目录)
  - [简介](#简介)
    - [使用方式](#使用方式)
  - [错误码快速索引](#错误码快速索引)
  - [借用检查错误 (E01xx-E05xx)](#借用检查错误-e01xx-e05xx)
    - [E0382 - 使用已移动的值](#e0382---使用已移动的值)
    - [E0383 - 部分移动](#e0383---部分移动)
    - [E0499 - 重复可变借用](#e0499---重复可变借用)
    - [E0502 - 可变与不可变借用共存](#e0502---可变与不可变借用共存)
    - [E0503 - 使用已移动的值（在借用后）](#e0503---使用已移动的值在借用后)
    - [E0505 - 在借用时移动](#e0505---在借用时移动)
    - [E0506 - 在借用时赋值](#e0506---在借用时赋值)
    - [E0507 - 从借用内容中移出](#e0507---从借用内容中移出)
    - [E0508 - 从数组/元组中移出](#e0508---从数组元组中移出)
  - [类型系统错误 (E02xx-E03xx)](#类型系统错误-e02xx-e03xx)
    - [E0277 - Trait 约束不满足](#e0277---trait-约束不满足)
    - [E0282 - 需要类型标注](#e0282---需要类型标注)
    - [E0283 - 类型标注不足](#e0283---类型标注不足)
    - [E0308 - 类型不匹配](#e0308---类型不匹配)
    - [E0308 - 返回值类型不匹配](#e0308---返回值类型不匹配)
  - [生命周期错误 (E05xx-E06xx)](#生命周期错误-e05xx-e06xx)
    - [E0106 - 需要生命周期标注](#e0106---需要生命周期标注)
    - [E0107 - 生命周期参数数量不匹配](#e0107---生命周期参数数量不匹配)
    - [E0597 - 生命周期不足](#e0597---生命周期不足)
    - [E0310 - 参数生命周期不足](#e0310---参数生命周期不足)
    - [E0495 - 生命周期不匹配](#e0495---生命周期不匹配)
  - [所有权错误](#所有权错误)
    - [E0381 - 使用未初始化变量](#e0381---使用未初始化变量)
    - [E0384 - 对不可变变量赋值](#e0384---对不可变变量赋值)
  - [模式匹配错误](#模式匹配错误)
    - [E0004 - 非穷尽模式匹配](#e0004---非穷尽模式匹配)
    - [E0005 - 不可反驳模式](#e0005---不可反驳模式)
    - [E0297 - 模式绑定不匹配](#e0297---模式绑定不匹配)
  - [宏系统错误](#宏系统错误)
    - [E0424 - self 使用错误](#e0424---self-使用错误)
    - [E0425 - 未找到函数/变量](#e0425---未找到函数变量)
    - [E0554 - 未知特性](#e0554---未知特性)
  - [模块系统错误](#模块系统错误)
    - [E0432 - 未解析的导入](#e0432---未解析的导入)
    - [E0433 - 未找到 crate](#e0433---未找到-crate)
    - [E0463 - 找不到 crate](#e0463---找不到-crate)
    - [E0603 - 私有模块](#e0603---私有模块)
  - [变量与可变性错误](#变量与可变性错误)
    - [E0596 - 无法借用不可变变量为可变](#e0596---无法借用不可变变量为可变)
    - [E0599 - 未找到方法](#e0599---未找到方法)
    - [E0609 - 未找到字段](#e0609---未找到字段)
    - [E0614 - 类型不能进行此操作](#e0614---类型不能进行此操作)
    - [E0616 - 私有字段](#e0616---私有字段)
  - [Trait 与泛型错误](#trait-与泛型错误)
    - [E0201 - 重复的 Trait 实现](#e0201---重复的-trait-实现)
    - [E0323 - 错误的方法签名](#e0323---错误的方法签名)
    - [E0392 - 参数未使用](#e0392---参数未使用)
    - [E0275 - Trait 解析无限递归](#e0275---trait-解析无限递归)
  - [并发与异步错误](#并发与异步错误)
    - [E0373 - 闭包生命周期问题](#e0373---闭包生命周期问题)
    - [E0378 - Send/Sync 约束不满足](#e0378---sendsync-约束不满足)
    - [E0700 - 异步块中借用](#e0700---异步块中借用)
    - [E0733 - 递归异步函数](#e0733---递归异步函数)
  - [其他常见错误](#其他常见错误)
    - [E0252 - 名称冲突](#e0252---名称冲突)
    - [E0301 - 可变与不可变模式](#e0301---可变与不可变模式)
    - [E0446 - 私有类型在公共接口](#e0446---私有类型在公共接口)
    - [E0515 - 返回局部变量的引用](#e0515---返回局部变量的引用)
    - [E0521 - 借用数据逃逸](#e0521---借用数据逃逸)
    - [E0658 - 不稳定特性](#e0658---不稳定特性)
    - [E0689 - 整数类型后缀](#e0689---整数类型后缀)
  - [警告 (W开头)](#警告-w开头)
    - [W0001 - 未使用的变量](#w0001---未使用的变量)
    - [W0002 - 未使用的导入](#w0002---未使用的导入)
    - [W0003 - 不可达代码](#w0003---不可达代码)
    - [W0004 - 未使用的 mut](#w0004---未使用的-mut)
    - [W0005 - 死代码](#w0005---死代码)
    - [W0006 - 未处理的 Result](#w0006---未处理的-result)
  - [错误码快速修复索引表](#错误码快速修复索引表)
  - [相关资源](#相关资源)
    - [项目内文档](#项目内文档)
    - [速查卡](#速查卡)
    - [官方资源](#官方资源)
    - [形式化理论](#形式化理论)
  - [故障排查建议](#故障排查建议)
  - [🆕 Rust 1.94 更新说明](#-rust-194-更新说明)

---

## 简介

本文档提供 Rust 编译器错误码的详细映射，帮助开发者：

- **快速定位**: 根据错误码找到对应的解释和解决方案
- **理解原理**: 了解错误背后的 Rust 语言规则
- **修复代码**: 提供具体的代码修复示例
- **深入学习**: 链接到相关的概念文档和形式化理论

### 使用方式

1. 在编译错误信息中找到 `error[EXXXX]` 格式的错误码
2. 在本文档中搜索该错误码（如 `E0382`）
3. 查看错误说明、代码示例和修复方案
4. 点击相关概念链接深入学习

---

## 错误码快速索引

| 错误码范围 | 类别 | 常见错误码 |
|:---|:---|:---|
| E01xx | 语法错误 | E0106, E0107 |
| E02xx | 类型系统 | E0201, E0277, E0282, E0283, E0308 |
| E03xx | 所有权与借用 | E0310, E0381, E0382, E0383, E0384 |
| E04xx | 借用检查 | E0499, E0502, E0503, E0505, E0506, E0507 |
| E05xx | 生命周期与类型 | E0596, E0597, E0599, E0609 |
| E06xx | 方法调用与字段 | E0614, E0616 |
| E07xx | 模式与匹配 | E0004, E0005, E0297 |
| E10xx | 模块与路径 | E0432, E0433, E0463 |
| E11xx-E13xx | 宏与属性 | E0424, E0425, E0554 |
| E2xxx+ | 其他高级错误 | E0380, E0700 |

---

## 借用检查错误 (E01xx-E05xx)

### E0382 - 使用已移动的值

**错误信息**: `use of moved value` / `value borrowed here after move`

**触发场景**: 在值被移动后尝试再次使用该值。这是 Rust 所有权系统的核心规则之一。

**错误代码**:

```rust
fn main() {
    let s = String::from("hello");
    let s2 = s;  // s 的所有权转移到 s2
    println!("{}", s);  // Error: E0382 - value borrowed here after move
}
```

**解决方案**:

```rust
// 方案 1: 使用克隆（Clone）
fn main() {
    let s = String::from("hello");
    let s2 = s.clone();  // 深度复制
    println!("{} {}", s, s2);  // ✅ 两者都可用
}

// 方案 2: 使用引用（借用）
fn main() {
    let s = String::from("hello");
    let s2 = &s;  // 借用 s，不转移所有权
    println!("{} {}", s, s2);  // ✅ 两者都可用
}

// 方案 3: 直接使用新变量
fn main() {
    let s = String::from("hello");
    let s2 = s;  // 转移所有权
    println!("{}", s2);  // ✅ 使用 s2，s 不再可用
}

// 方案 4: 在函数中使用引用
fn process(s: &String) -> usize {
    s.len()
}

fn main() {
    let s = String::from("hello");
    let len = process(&s);  // 借用
    println!("{} 的长度是 {}", s, len);  // ✅ s 仍然可用
}
```

**相关概念**:

- [所有权规则](../crates/c01_ownership_borrow_scope/docs/tier_01_foundations/02_主索引导航.md)
- [移动语义](../crates/c01_ownership_borrow_scope/docs/tier_03_references/01_所有权规则参考.md)

**形式化解释**:

- 违反规则: [规则 2 - 移动语义](../research_notes/formal_methods/ownership_model.md)
- 形式化: $\text{move}(x, y) \rightarrow \Omega(x) = \text{Moved} \land \Omega(y) = \text{Owned}$

---

### E0383 - 部分移动

**错误信息**: `partial move` / `borrow of partially moved value`

**触发场景**: 结构体或元组的部分字段被移动后，整体不能再使用，但未移动的字段仍可用。

**错误代码**:

```rust
struct Person {
    name: String,
    age: u32,
}

fn main() {
    let p = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = p.name;  // name 字段被移动
    println!("{:?}", p);  // Error: E0383 - borrow of partially moved value
}
```

**解决方案**:

```rust
// 方案 1: 克隆字段
fn main() {
    let p = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = p.name.clone();  // 克隆而非移动
    println!("{:?}", p);  // ✅ 可以完整使用 p
    println!("{}", name);
}

// 方案 2: 使用引用
fn main() {
    let p = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = &p.name;  // 借用
    println!("{} 年龄 {}", name, p.age);  // ✅ 可以访问其他字段
    println!("{:?}", p.age);  // ✅ 未移动字段可用
}

// 方案 3: 使用未移动的字段
fn main() {
    let p = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = p.name;  // 移动 name
    println!("年龄: {}", p.age);  // ✅ age 字段仍可用
    // println!("{:?}", p);  // ❌ 不能使用整个 p
}
```

**相关概念**:

- [部分移动](../crates/c01_ownership_borrow_scope/docs/tier_03_references/01_所有权规则参考.md)
- [结构体所有权](../crates/c02_type_system/docs/tier_02_guides/02_复合类型指南.md)

---

### E0499 - 重复可变借用

**错误信息**: `cannot borrow as mutable more than once at a time`

**触发场景**: 在同一作用域内对同一数据进行多次可变借用。

**错误代码**:

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;
    let r2 = &mut s;  // Error: E0499

    println!("{} {}", r1, r2);
}
```

**解决方案**:

```rust
// 方案 1: 使用作用域隔离
fn main() {
    let mut s = String::from("hello");

    {
        let r1 = &mut s;
        r1.push_str(" world");
        println!("{}", r1);
    }  // r1 在这里结束

    let r2 = &mut s;  // ✅ 可以新的可变借用
    r2.push_str("!");
    println!("{}", r2);
}

// 方案 2: 按顺序使用（利用 NLL - Non-Lexical Lifetimes）
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;
    r1.push_str(" world");
    // r1 不再使用，隐式结束

    let r2 = &mut s;  // ✅ NLL 允许，因为 r1 不再使用
    println!("{}", r2);
}

// 方案 3: 重构数据结构
use std::mem::take;

fn main() {
    let mut s = String::from("hello");
    let taken = take(&mut s);  // 取出所有权
    s = process(taken);        // 处理后再放回去
    s.push_str(" done");
    println!("{}", s);
}

fn process(s: String) -> String {
    s + " processed"
}
```

**相关概念**:

- [可变借用规则](../crates/c01_ownership_borrow_scope/docs/tier_03_references/02_借用检查器详解.md)
- [NLL](../crates/c01_ownership_borrow_scope/docs/tier_03_references/02_借用检查器详解.md)

**形式化解释**:

- 违反规则: [规则 1 - 可变借用唯一性](../research_notes/formal_methods/borrow_checker_proof.md)
- 形式化: $\forall b_1, b_2: \text{type}(b_1) = \&mut T \land \text{target}(b_1) = \text{target}(b_2) \rightarrow b_1 = b_2$
- 目的: 保证数据竞争自由

---

### E0502 - 可变与不可变借用共存

**错误信息**: `cannot borrow as immutable because it is borrowed as mutable`

**触发场景**: 在可变借用存在时尝试获取不可变借用。

**错误代码**:

```rust
fn main() {
    let mut s = String::from("hello");

    let r1 = &mut s;
    let r2 = &s;  // Error: E0502

    println!("{} {}", r1, r2);
}
```

**解决方案**:

```rust
// 方案 1: 先不可变后可变
fn main() {
    let mut s = String::from("hello");

    let r1 = &s;
    println!("读取: {}", r1);
    // r1 不再使用

    let r2 = &mut s;  // ✅ 现在可以可变借用
    r2.push_str(" world");
    println!("修改后: {}", r2);
}

// 方案 2: 使用作用域隔离
fn main() {
    let mut s = String::from("hello");

    {
        let r1 = &s;
        println!("读取: {}", r1);
    }  // 不可变借用结束

    {
        let r2 = &mut s;
        r2.push_str(" world");
        println!("修改后: {}", r2);
    }  // 可变借用结束
}

// 方案 3: 复制所需数据
fn main() {
    let mut s = String::from("hello");

    let len = s.len();  // 复制长度信息
    let r = &mut s;     // ✅ 可变借用
    r.push_str(" world");
    println!("原长度: {}, 新字符串: {}", len, r);
}
```

**相关概念**:

- [借用规则](../crates/c01_ownership_borrow_scope/docs/tier_03_references/02_借用检查器详解.md)
- [读写锁原理](../crates/c05_threads/docs/tier_02_guides/02_同步原语实践.md)

---

### E0503 - 使用已移动的值（在借用后）

**错误信息**: `cannot use because it was mutably borrowed` / `value used after move`

**触发场景**: 值被移动后仍尝试使用，通常在复杂的控制流中出现。

**错误代码**:

```rust
fn main() {
    let s = String::from("hello");
    let s2 = s;  // s 被移动
    println!("{}", s);  // Error: E0503
}
```

**解决方案**:

```rust
// 方案 1: 克隆
fn main() {
    let s = String::from("hello");
    let s2 = s.clone();
    println!("{} {}", s, s2);  // ✅
}

// 方案 2: 引用
fn main() {
    let s = String::from("hello");
    let s2 = &s;
    println!("{} {}", s, s2);  // ✅
}

// 方案 3: 函数返回值
fn give_ownership() -> String {
    String::from("hello")
}

fn main() {
    let s = give_ownership();
    println!("{}", s);  // ✅
}
```

**相关概念**: [所有权转移](../crates/c01_ownership_borrow_scope/docs/tier_02_guides/01_所有权快速入门.md)

---

### E0505 - 在借用时移动

**错误信息**: `cannot move out of because it is borrowed`

**触发场景**: 尝试移动一个已被借用的值。

**错误代码**:

```rust
fn main() {
    let s = String::from("hello");
    let r = &s;
    let s2 = s;  // Error: E0505 - cannot move out of `s` because it is borrowed
    println!("{}", r);
}
```

**解决方案**:

```rust
// 方案 1: 确保借用结束后再移动
fn main() {
    let s = String::from("hello");
    {
        let r = &s;
        println!("{}", r);
    }  // 借用结束
    let s2 = s;  // ✅ 可以移动
}

// 方案 2: 克隆
fn main() {
    let s = String::from("hello");
    let r = &s;
    println!("{}", r);
    let s2 = s.clone();  // ✅ 克隆而非移动
}
```

---

### E0506 - 在借用时赋值

**错误信息**: `cannot assign to because it is borrowed`

**触发场景**: 尝试给一个已被借用的变量重新赋值。

**错误代码**:

```rust
fn main() {
    let mut s = String::from("hello");
    let r = &s;
    s = String::from("world");  // Error: E0506
    println!("{}", r);
}
```

**解决方案**:

```rust
fn main() {
    let mut s = String::from("hello");
    {
        let r = &s;
        println!("{}", r);
    }  // 借用结束
    s = String::from("world");  // ✅ 可以赋值
    println!("{}", s);
}
```

---

### E0507 - 从借用内容中移出

**错误信息**: `cannot move out of borrowed content`

**触发场景**: 尝试从引用或借用中移出值。

**错误代码**:

```rust
fn main() {
    let s = String::from("hello");
    let r = &s;
    let s2 = *r;  // Error: E0507 - cannot move out of `*r` which is behind a shared reference
}
```

**解决方案**:

```rust
// 方案 1: 克隆
fn main() {
    let s = String::from("hello");
    let r = &s;
    let s2 = r.clone();  // ✅ 克隆
    println!("{} {}", s, s2);
}

// 方案 2: 使用引用
fn main() {
    let s = String::from("hello");
    let r = &s;
    print_string(r);  // ✅ 传递引用
}

fn print_string(s: &String) {
    println!("{}", s);
}

// 方案 3: Copy 类型可以直接解引用
fn main() {
    let x: i32 = 42;
    let r = &x;
    let y = *r;  // ✅ i32 实现了 Copy
    println!("{} {}", x, y);
}
```

---

### E0508 - 从数组/元组中移出

**错误信息**: `cannot move out of type which is behind a shared reference`

**触发场景**: 尝试从数组或切片的借用中移出元素。

**错误代码**:

```rust
fn main() {
    let arr = [String::from("a"), String::from("b")];
    let r = &arr;
    let first = r[0];  // Error: E0508
}
```

**解决方案**:

```rust
// 方案 1: 克隆
fn main() {
    let arr = [String::from("a"), String::from("b")];
    let r = &arr;
    let first = r[0].clone();  // ✅
    println!("{} {:?}", first, arr);
}

// 方案 2: 使用引用
fn main() {
    let arr = [String::from("a"), String::from("b")];
    let r = &arr;
    let first = &r[0];  // ✅ 获取引用
    println!("{} {:?}", first, arr);
}
```

---

## 类型系统错误 (E02xx-E03xx)

### E0277 - Trait 约束不满足

**错误信息**: `trait bound not satisfied` / `doesn't implement trait`

**触发场景**: 使用了一个未实现所需 Trait 的类型。

**错误代码**:

```rust
fn print_it<T>(x: T) {
    println!("{}", x);  // Error: E0277 - T doesn't implement Display
}

fn main() {
    print_it(42);
}
```

**解决方案**:

```rust
use std::fmt::Display;

// 方案 1: 添加 Trait Bound
fn print_it<T: Display>(x: T) {
    println!("{}", x);  // ✅ T 实现了 Display
}

// 方案 2: 使用 where 从句
fn print_it<T>(x: T)
where
    T: Display,
{
    println!("{}", x);
}

// 方案 3: 为自定义类型实现 Trait
struct Point { x: i32, y: i32 }

impl Display for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.x, self.y)
    }
}

fn main() {
    print_it(Point { x: 1, y: 2 });  // ✅
    print_it(42);  // ✅ i32 实现了 Display
    print_it("hello");  // ✅ &str 实现了 Display
}
```

**相关概念**:

- [Trait Bound](../crates/c04_generic/docs/tier_02_guides/02_Trait系统指南.md)
- [标准库 Trait](../crates/c02_type_system/docs/tier_03_references/01_类型系统规范.md)

---

### E0282 - 需要类型标注

**错误信息**: `type annotations needed` / `cannot infer the type`

**触发场景**: 编译器无法推断变量的类型。

**错误代码**:

```rust
fn main() {
    let v = Vec::new();  // Error: E0282 - cannot infer type for type parameter `T`
    v.push(42);
}
```

**解决方案**:

```rust
// 方案 1: 显式类型标注
fn main() {
    let v: Vec<i32> = Vec::new();  // ✅
    v.push(42);
}

// 方案 2: 使用 turbofish 语法
fn main() {
    let v = Vec::<i32>::new();  // ✅
    v.push(42);
}

// 方案 3: 从值推断
fn main() {
    let v = vec![42];  // ✅ 从元素推断为 Vec<i32>
    let mut v = Vec::new();
    v.push(42i32);  // ✅ 从 push 的值推断
}
```

---

### E0283 - 类型标注不足

**错误信息**: `type annotations required` / `cannot resolve`

**触发场景**: 编译器需要更多类型信息来决定调用哪个方法或实现。

**错误代码**:

```rust
fn main() {
    let s = "hello".into();  // Error: E0283 - type annotations needed
}
```

**解决方案**:

```rust
// 方案 1: 显式类型
fn main() {
    let s: String = "hello".into();  // ✅
}

// 方案 2: 指定具体方法
fn main() {
    let s = String::from("hello");  // ✅
}
```

---

### E0308 - 类型不匹配

**错误信息**: `mismatched types` / `expected ... found ...`

**触发场景**: 赋值或传参时类型不匹配。

**错误代码**:

```rust
fn main() {
    let x: i32 = "hello";  // Error: E0308 - expected i32, found &str
}
```

**解决方案**:

```rust
// 方案 1: 修正类型声明
fn main() {
    let x: &str = "hello";  // ✅
}

// 方案 2: 类型转换
fn main() {
    let s = "42";
    let x: i32 = s.parse().unwrap();  // ✅ 显式解析转换
}

// 方案 3: 类型推断
fn main() {
    let x = "hello";  // ✅ 编译器自动推断为 &str
}

// 方案 4: 数值类型转换
fn main() {
    let x: i32 = 42;
    let y: f64 = x as f64;  // ✅ 使用 as 进行数值类型转换
}
```

**相关概念**: [类型转换](../crates/c02_type_system/docs/tier_03_references/01_类型转换参考.md)

---

### E0308 - 返回值类型不匹配

**错误信息**: `mismatched types` (返回类型)

**错误代码**:

```rust
fn add(a: i32, b: i32) -> i32 {
    "not a number"  // Error: E0308
}
```

**解决方案**:

```rust
fn add(a: i32, b: i32) -> i32 {
    a + b  // ✅ 返回 i32
}

// 或者返回 Result
fn add_result(a: i32, b: i32) -> Result<i32, String> {
    Ok(a + b)
}
```

---

## 生命周期错误 (E05xx-E06xx)

### E0106 - 需要生命周期标注

**错误信息**: `missing lifetime specifier`

**触发场景**: 函数返回引用或结构体包含引用时，需要显式生命周期标注。

**错误代码**:

```rust
fn longest(x: &str, y: &str) -> &str {  // Error: E0106
    if x.len() > y.len() { x } else { y }
}
```

**解决方案**:

```rust
// 方案 1: 显式生命周期标注
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 方案 2: 返回独立的生命周期（如果可能）
fn first<'a>(x: &'a str, _y: &str) -> &'a str {
    x
}

// 方案 3: 返回所有权
fn longest_owned(x: &str, y: &str) -> String {
    if x.len() > y.len() { x.to_string() } else { y.to_string() }
}

fn main() {
    let s1 = String::from("hello");
    let s2 = String::from("world!");
    let result = longest(&s1, &s2);
    println!("最长的是 {}", result);
}
```

**相关概念**:

- [生命周期标注](../crates/c01_ownership_borrow_scope/docs/tier_02_guides/03_生命周期实践.md)
- [生命周期省略规则](../crates/c01_ownership_borrow_scope/docs/tier_03_references/03_生命周期参考.md)

---

### E0107 - 生命周期参数数量不匹配

**错误信息**: `wrong number of lifetime parameters`

**触发场景**: 提供的生命周期参数数量与定义不匹配。

**错误代码**:

```rust
struct Wrapper<'a, 'b> {
    x: &'a str,
    y: &'b str,
}

fn main() {
    let w: Wrapper = Wrapper { x: "a", y: "b" };  // Error: E0107
}
```

**解决方案**:

```rust
struct Wrapper<'a, 'b> {
    x: &'a str,
    y: &'b str,
}

fn main() {
    let w: Wrapper<'_, '_> = Wrapper { x: "a", y: "b" };  // ✅
    // 或者让编译器推断
    let w = Wrapper { x: "a", y: "b" };  // ✅
}
```

---

### E0597 - 生命周期不足

**错误信息**: `does not live long enough`

**触发场景**: 引用的生命周期超过了被引用数据的生命周期。

**错误代码**:

```rust
fn main() {
    let r;
    {
        let s = String::from("hello");
        r = &s;  // Error: E0597 - s does not live long enough
    }  // s 在这里被丢弃
    println!("{}", r);  // r 引用已释放的内存
}
```

**解决方案**:

```rust
// 方案 1: 确保引用不超过被引用者的生命周期
fn main() {
    let s = String::from("hello");
    let r = &s;  // ✅ r 的生命周期在 s 之内
    println!("{}", r);
}  // s 和 r 一起结束

// 方案 2: 使用返回值传递所有权
fn get_string() -> String {
    String::from("hello")
}

fn main() {
    let s = get_string();
    println!("{}", s);
}

// 方案 3: 使用 'static 生命周期的字符串
fn main() {
    let r: &'static str = "hello";  // ✅ 字符串字面量生命周期为 'static
    println!("{}", r);
}

// 方案 4: 使用智能指针
use std::rc::Rc;

fn main() {
    let s = Rc::new(String::from("hello"));
    let r = Rc::clone(&s);  // ✅ 引用计数，共享所有权
    println!("{}", r);
}
```

**相关概念**:

- [悬垂引用](../crates/c01_ownership_borrow_scope/docs/tier_02_guides/03_生命周期实践.md)
- [作用域规则](../crates/c01_ownership_borrow_scope/docs/tier_03_references/04_Drop与RAII参考.md)

**形式化解释**:

- 违反规则: [规则 3 - 借用有效性](../research_notes/formal_methods/borrow_checker_proof.md)
- 形式化: $\text{Valid}(b) \leftrightarrow \text{Lifetime}(b) \subseteq \text{Scope}(b)$

---

### E0310 - 参数生命周期不足

**错误信息**: `parameter ... may not live long enough`

**触发场景**: 泛型参数的生命周期可能不满足约束。

**错误代码**:

```rust
struct Container<'a> {
    value: &'a str,
}

fn make_container(s: &str) -> Container {
    Container { value: s }  // Error: E0310
}
```

**解决方案**:

```rust
struct Container<'a> {
    value: &'a str,
}

// 方案 1: 显式生命周期
fn make_container<'a>(s: &'a str) -> Container<'a> {
    Container { value: s }
}

// 方案 2: 使用所有权
struct ContainerOwned {
    value: String,
}

fn make_container_owned(s: &str) -> ContainerOwned {
    ContainerOwned { value: s.to_string() }
}
```

---

### E0495 - 生命周期不匹配

**错误信息**: `cannot infer an appropriate lifetime due to conflicting requirements`

**触发场景**: 多个生命周期约束之间存在冲突。

**错误代码**:

```rust
fn foo<'a, 'b>(x: &'a str, y: &'b str) -> &'a str {
    if x.len() > y.len() { x } else { y }  // Error: E0495
}
```

**解决方案**:

```rust
// 方案 1: 统一生命周期
fn foo<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

// 方案 2: 返回枚举
enum Either<'a, 'b> {
    First(&'a str),
    Second(&'b str),
}

fn foo<'a, 'b>(x: &'a str, y: &'b str) -> Either<'a, 'b> {
    if x.len() > y.len() { Either::First(x) } else { Either::Second(y) }
}
```

---

## 所有权错误

### E0381 - 使用未初始化变量

**错误信息**: `use of possibly-uninitialized variable`

**触发场景**: 使用可能未初始化的变量。

**错误代码**:

```rust
fn main() {
    let x: i32;
    println!("{}", x);  // Error: E0381
}
```

**解决方案**:

```rust
fn main() {
    let x: i32 = 42;  // ✅ 初始化
    println!("{}", x);
}
```

---

### E0384 - 对不可变变量赋值

**错误信息**: `cannot assign twice to immutable variable`

**触发场景**: 尝试给不可变变量重新赋值。

**错误代码**:

```rust
fn main() {
    let x = 5;
    x = 6;  // Error: E0384
}
```

**解决方案**:

```rust
fn main() {
    let mut x = 5;  // ✅ 使用 mut
    x = 6;
    println!("{}", x);
}
```

**相关概念**: [可变性](../crates/c01_ownership_borrow_scope/docs/tier_03_references/01_所有权规则参考.md)

---

## 模式匹配错误

### E0004 - 非穷尽模式匹配

**错误信息**: `non-exhaustive patterns`

**触发场景**: match 表达式没有覆盖所有可能的值。

**错误代码**:

```rust
enum Direction {
    North,
    South,
    East,
    West,
}

fn main() {
    let d = Direction::North;
    match d {
        Direction::North => println!("北"),
        Direction::South => println!("南"),
        // Error: E0004 - non-exhaustive patterns: `East` and `West` not covered
    }
}
```

**解决方案**:

```rust
fn main() {
    let d = Direction::North;
    match d {
        Direction::North => println!("北"),
        Direction::South => println!("南"),
        Direction::East => println!("东"),
        Direction::West => println!("西"),
    }

    // 或者使用通配符
    match d {
        Direction::North => println!("北"),
        Direction::South => println!("南"),
        _ => println!("其他方向"),  // ✅ 通配符覆盖剩余情况
    }
}
```

**相关概念**:

- [模式匹配](../crates/c03_control_fn/docs/tier_02_guides/04_模式匹配指南.md)
- [穷尽性检查](../crates/c03_control_fn/docs/tier_04_advanced/01_高级模式匹配.md)

---

### E0005 - 不可反驳模式

**错误信息**: `refutable pattern in local binding`

**触发场景**: 在 `let` 绑定中使用可能失败的模式。

**错误代码**:

```rust
fn main() {
    let Some(x) = None;  // Error: E0005
}
```

**解决方案**:

```rust
fn main() {
    // 方案 1: 使用 if let
    let opt = Some(42);
    if let Some(x) = opt {
        println!("{}", x);
    }

    // 方案 2: 使用 match
    let opt = Some(42);
    match opt {
        Some(x) => println!("{}", x),
        None => println!("无值"),
    }

    // 方案 3: 使用 unwrap_or
    let opt: Option<i32> = None;
    let x = opt.unwrap_or(0);
    println!("{}", x);
}
```

---

### E0297 - 模式绑定不匹配

**错误信息**: `refutable pattern in function argument`

**触发场景**: 函数参数使用可能失败的模式。

**错误代码**:

```rust
fn foo((x, y): (i32, i32)) {}  // 正常情况

fn bar(Some(x): Option<i32>) {  // Error: E0297
    println!("{}", x);
}
```

**解决方案**:

```rust
fn bar(opt: Option<i32>) {
    if let Some(x) = opt {
        println!("{}", x);
    }
}
```

---

## 宏系统错误

### E0424 - self 使用错误

**错误信息**: `self` is not available in a static method`

**触发场景**: 在静态方法中尝试使用 `self`。

**错误代码**:

```rust
struct Foo;

impl Foo {
    fn static_method() {
        self.do_something();  // Error: E0424
    }

    fn do_something(&self) {}
}
```

**解决方案**:

```rust
struct Foo;

impl Foo {
    fn static_method() {
        // 静态方法没有 self
        println!("静态方法");
    }

    fn instance_method(&self) {
        self.do_something();  // ✅
    }

    fn do_something(&self) {
        println!("实例方法");
    }
}
```

---

### E0425 - 未找到函数/变量

**错误信息**: `cannot find function/variable ... in this scope`

**触发场景**: 使用了未定义的函数或变量。

**错误代码**:

```rust
fn main() {
    println!("{}", unknown_var);  // Error: E0425
}
```

**解决方案**:

```rust
fn main() {
    let unknown_var = 42;  // ✅ 定义变量
    println!("{}", unknown_var);
}
```

---

### E0554 - 未知特性

**错误信息**: `feature may not be used on the ... release channel`

**触发场景**: 在非 Nightly 频道使用不稳定特性。

**错误代码**:

```rust
#![feature(box_syntax)]  // Error: E0554 (在 stable/beta)

fn main() {}
```

**解决方案**:

```rust
// 方案 1: 使用标准语法替代
fn main() {
    let b = Box::new(5);  // ✅ 标准语法
}

// 方案 2: 切换到 nightly (如确实需要)
// rustup default nightly
```

---

## 模块系统错误

### E0432 - 未解析的导入

**错误信息**: `unresolved import`

**触发场景**: 导入的模块或 crate 不存在。

**错误代码**:

```rust
use non_existent::Module;  // Error: E0432

fn main() {}
```

**解决方案**:

```rust
// 方案 1: 检查模块路径
use std::collections::HashMap;  // ✅ 正确路径

// 方案 2: 确保依赖在 Cargo.toml 中
// [dependencies]
// serde = "1.0"

use serde::Serialize;  // ✅ 添加依赖后

fn main() {}
```

---

### E0433 - 未找到 crate

**错误信息**: `failed to resolve: use of undeclared crate or module`

**触发场景**: 使用了未声明的 crate。

**错误代码**:

```rust
use serde::Serialize;  // Error: E0433 - 未在 Cargo.toml 中添加 serde

fn main() {}
```

**解决方案**:

```toml
# Cargo.toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
```

```rust
use serde::Serialize;  // ✅

#[derive(Serialize)]
struct Point { x: i32, y: i32 }

fn main() {}
```

---

### E0463 - 找不到 crate

**错误信息**: `can't find crate for ...`

**触发场景**: 编译时找不到依赖的 crate。

**解决方案**:

```bash
# 方案 1: 重新构建
cargo clean
cargo build

# 方案 2: 更新依赖
cargo update

# 方案 3: 检查 Cargo.toml 中的依赖声明
```

---

### E0603 - 私有模块

**错误信息**: `module is private`

**触发场景**: 尝试访问私有模块。

**错误代码**:

```rust
// 在某个 crate 中
mod internal {
    pub fn secret() {}
}

// 在其他地方
use crate::internal;  // Error: E0603
```

**解决方案**:

```rust
// 方案 1: 将模块声明为 pub
pub mod internal {
    pub fn secret() {}
}

// 方案 2: 只导出需要的项
mod internal {
    pub fn secret() {}
}

pub use internal::secret;  // ✅ 重新导出
```

---

## 变量与可变性错误

### E0596 - 无法借用不可变变量为可变

**错误信息**: `cannot borrow as mutable`

**触发场景**: 尝试将不可变变量借用为可变。

**错误代码**:

```rust
fn main() {
    let s = String::from("hello");
    s.push_str(" world");  // Error: E0596
}
```

**解决方案**:

```rust
fn main() {
    let mut s = String::from("hello");  // ✅ 使用 mut
    s.push_str(" world");
    println!("{}", s);
}
```

---

### E0599 - 未找到方法

**错误信息**: `no method named ... found for type`

**触发场景**: 类型上没有调用的方法。

**错误代码**:

```rust
fn main() {
    let x = 42;
    x.push(5);  // Error: E0599 - i32 没有 push 方法
}
```

**解决方案**:

```rust
fn main() {
    let mut v = vec![42];  // ✅ 使用 Vec
    v.push(5);
    println!("{:?}", v);
}
```

---

### E0609 - 未找到字段

**错误信息**: `no field ... on type`

**触发场景**: 访问结构体不存在的字段。

**错误代码**:

```rust
struct Point { x: i32, y: i32 }

fn main() {
    let p = Point { x: 1, y: 2 };
    println!("{}", p.z);  // Error: E0609
}
```

**解决方案**:

```rust
struct Point { x: i32, y: i32 }

fn main() {
    let p = Point { x: 1, y: 2 };
    println!("{}", p.x);  // ✅ 使用正确字段名
}
```

---

### E0614 - 类型不能进行此操作

**错误信息**: `type ... cannot be ...` / `cannot be dereferenced`

**触发场景**: 对类型进行不支持的操作。

**错误代码**:

```rust
fn main() {
    let x = 42;
    let y = *x;  // Error: E0614 - i32 不能解引用
}
```

**解决方案**:

```rust
fn main() {
    let x = Box::new(42);
    let y = *x;  // ✅ Box 可以解引用
    println!("{}", y);
}
```

---

### E0616 - 私有字段

**错误信息**: `field ... of ... is private`

**触发场景**: 访问结构体的私有字段。

**错误代码**:

```rust
mod inner {
    pub struct Foo {
        secret: i32,
    }
}

fn main() {
    let f = inner::Foo { secret: 42 };  // Error: E0616
}
```

**解决方案**:

```rust
mod inner {
    pub struct Foo {
        secret: i32,
    }

    impl Foo {
        pub fn new(secret: i32) -> Self {
            Self { secret }
        }

        pub fn secret(&self) -> i32 {
            self.secret
        }
    }
}

fn main() {
    let f = inner::Foo::new(42);  // ✅ 使用构造函数
    println!("{}", f.secret());    // ✅ 使用访问器方法
}
```

---

## Trait 与泛型错误

### E0201 - 重复的 Trait 实现

**错误信息**: `duplicate definitions with name ...`

**触发场景**: 为同一类型多次实现同一 Trait。

**错误代码**:

```rust
struct Foo;

trait Bar {
    fn baz(&self);
}

impl Bar for Foo {
    fn baz(&self) {}
}

impl Bar for Foo {  // Error: E0201
    fn baz(&self) {}
}
```

**解决方案**:

```rust
struct Foo;

trait Bar {
    fn baz(&self);
}

impl Bar for Foo {
    fn baz(&self) {
        println!("实现");
    }
}
```

---

### E0323 - 错误的方法签名

**错误信息**: `item ... is an associated method, which doesn't match the trait`

**触发场景**: Trait 实现的方法签名与定义不匹配。

**错误代码**:

```rust
trait Greet {
    fn greet(&self, name: &str);
}

struct Person;

impl Greet for Person {
    fn greet(&self) {  // Error: E0323 - 参数不匹配
        println!("Hello");
    }
}
```

**解决方案**:

```rust
trait Greet {
    fn greet(&self, name: &str);
}

struct Person;

impl Greet for Person {
    fn greet(&self, name: &str) {  // ✅ 匹配签名
        println!("Hello, {}", name);
    }
}
```

---

### E0392 - 参数未使用

**错误信息**: `parameter ... is never used`

**触发场景**: 泛型参数在定义中未使用。

**错误代码**:

```rust
struct Wrapper<T> {  // Error: E0392
    value: i32,
}
```

**解决方案**:

```rust
// 方案 1: 使用泛型参数
struct Wrapper<T> {
    value: T,
}

// 方案 2: 移除未使用的参数
struct Wrapper {
    value: i32,
}

// 方案 3: 使用 PhantomData
use std::marker::PhantomData;

struct Wrapper<T> {
    value: i32,
    _phantom: PhantomData<T>,  // ✅ 标记使用 T
}
```

---

### E0275 - Trait 解析无限递归

**错误信息**: `overflow evaluating the requirement`

**触发场景**: Trait 约束导致无限递归。

**解决方案**:

```rust
// 避免循环约束
// 如果 T: Foo 要求 T: Bar，而 T: Bar 又要求 T: Foo，会导致无限递归

// 正确设计：
trait Foo {}
trait Bar: Foo {}  // ✅ 单向约束
```

---

## 并发与异步错误

### E0373 - 闭包生命周期问题

**错误信息**: `closure may outlive current function`

**触发场景**: 闭包捕获的变量生命周期可能不足。

**错误代码**:

```rust
fn make_closure() -> Box<dyn Fn() -> i32> {
    let x = 42;
    Box::new(|| x)  // Error: E0373
}
```

**解决方案**:

```rust
// 方案 1: 使用 move 关键字
fn make_closure() -> impl FnOnce() -> i32 {
    let x = 42;
    move || x  // ✅ 将 x 的所有权移入闭包
}

// 方案 2: 使用 Arc 共享
use std::sync::Arc;

fn make_closure_shared() -> impl Fn() -> i32 {
    let x = Arc::new(42);
    let x_clone = Arc::clone(&x);
    move || *x_clone  // ✅ Arc 可以安全共享
}

// 方案 3: 使用 'static 数据
fn make_closure_static() -> impl Fn() -> i32 {
    let x: i32 = 42;  // i32 实现 Copy
    move || x  // ✅ 复制而非移动
}
```

**相关概念**:

- [闭包](../crates/c03_control_fn/docs/tier_03_references/04_闭包参考.md)
- [move 闭包](../crates/c05_threads/docs/tier_02_guides/01_线程基础与生命周期.md)

---

### E0378 - Send/Sync 约束不满足

**错误信息**: `trait bound ... is not satisfied` (Send/Sync)

**触发场景**: 类型不满足 Send 或 Sync 约束。

**错误代码**:

```rust
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);
    thread::spawn(move || {
        println!("{}", data);  // Error: E0378 - Rc 不是 Send
    });
}
```

**解决方案**:

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(42);  // ✅ Arc 是 Send + Sync
    thread::spawn(move || {
        println!("{}", data);
    }).join().unwrap();
}
```

**相关概念**:

- [Send/Sync](../crates/c05_threads/docs/tier_01_foundations/03_术语表.md)
- [线程安全](../crates/c05_threads/docs/tier_02_guides/01_线程基础与生命周期.md)

---

### E0700 - 异步块中借用

**错误信息**: `cannot borrow as mutable more than once at a time in async block`

**触发场景**: 异步块中的借用规则更加严格。

**错误代码**:

```rust
async fn bad_async() {
    let mut s = String::from("hello");
    let r1 = &mut s;
    some_async().await;  // 跨越 await 点
    let r2 = &mut s;  // 可能错误：E0700
    println!("{} {}", r1, r2);
}

async fn some_async() {}
```

**解决方案**:

```rust
// 方案 1: 限制借用范围
async fn good_async() {
    let mut s = String::from("hello");
    {
        let r1 = &mut s;
        println!("{}", r1);
    }  // r1 结束
    some_async().await;
    let r2 = &mut s;
    println!("{}", r2);
}

// 方案 2: 使用内部作用域
async fn good_async2() {
    let mut s = String::from("hello");
    some_async().await;
    let r = &mut s;
    println!("{}", r);
}

async fn some_async() {}
```

**相关概念**:

- [异步借用](../crates/c06_async/docs/tier_02_guides/04_异步设计模式实践.md)
- [Pin](../crates/c06_async/docs/tier_03_references/04_Pin与Unsafe参考.md)

---

### E0733 - 递归异步函数

**错误信息**: `recursion in an async fn requires boxing`

**触发场景**: 异步函数递归调用没有使用 Box::pin。

**错误代码**:

```rust
async fn fib(n: u32) -> u32 {  // Error: E0733
    if n <= 1 { n } else { fib(n - 1).await + fib(n - 2).await }
}
```

**解决方案**:

```rust
use std::future::Future;
use std::pin::Pin;

fn fib(n: u32) -> Pin<Box<dyn Future<Output = u32>>> {
    Box::pin(async move {
        if n <= 1 { n } else { fib(n - 1).await + fib(n - 2).await }
    })
}
```

**相关概念**: [递归异步](../crates/c09_design_pattern/docs/ASYNC_RECURSION_ANALYSIS.md)

---

## 其他常见错误

### E0252 - 名称冲突

**错误信息**: `a name ... is defined multiple times`

**触发场景**: 同一作用域内定义了同名项。

**错误代码**:

```rust
use std::io;
use std::fmt::Write as io;  // Error: E0252
```

**解决方案**:

```rust
use std::io;
use std::fmt::Write as FmtWrite;  // ✅ 使用别名

fn main() {
    let mut s = String::new();
    FmtWrite::write_str(&mut s, "hello").unwrap();
    println!("{}", s);
}
```

---

### E0301 - 可变与不可变模式

**错误信息**: `cannot mutably borrow in a pattern guard`

**触发场景**: 在模式守卫中可变借用。

**解决方案**:

```rust
fn main() {
    let mut v = vec![1, 2, 3];

    match v.get(0) {
        Some(x) if *x > 0 => {
            v.push(4);  // ✅ 在 match 后修改
        }
        _ => {}
    }
}
```

---

### E0446 - 私有类型在公共接口

**错误信息**: `private type in public interface`

**触发场景**: 公共 API 使用了私有类型。

**错误代码**:

```rust
mod inner {
    pub struct PublicType;
    struct PrivateType;

    impl PublicType {
        pub fn method(&self) -> PrivateType {  // Error: E0446
            PrivateType
        }
    }
}
```

**解决方案**:

```rust
mod inner {
    pub struct PublicType;
    pub struct PrivateType;  // ✅ 设为 pub

    impl PublicType {
        pub fn method(&self) -> PrivateType {
            PrivateType
        }
    }
}
```

---

### E0515 - 返回局部变量的引用

**错误信息**: `cannot return reference to local variable`

**触发场景**: 函数返回局部变量的引用。

**错误代码**:

```rust
fn bad() -> &str {
    let s = String::from("hello");
    &s  // Error: E0515
}
```

**解决方案**:

```rust
// 方案 1: 返回所有权
fn good() -> String {
    let s = String::from("hello");
    s
}

// 方案 2: 返回 'static 字符串
fn good_static() -> &'static str {
    "hello"
}

// 方案 3: 使用生命周期参数（如果参数是引用）
fn good_lifetime<'a>(input: &'a str) -> &'a str {
    input
}
```

---

### E0521 - 借用数据逃逸

**错误信息**: `borrowed data escapes outside of function`

**触发场景**: 借用的数据逃逸出函数作用域。

**错误代码**:

```rust
fn get_ref() -> &'static str {
    let s = String::from("hello");
    &s  // Error: E0521
}
```

**解决方案**: 同 E0515

---

### E0658 - 不稳定特性

**错误信息**: `feature is unstable`

**触发场景**: 使用了不稳定特性且未启用。

**解决方案**:

```rust
#![feature(async_closure)]  // 需要 nightly

fn main() {
    // 使用不稳定特性
}
```

---

### E0689 - 整数类型后缀

**错误信息**: `can't call method on ambiguous numeric type`

**触发场景**: 数值字面量类型不明确。

**错误代码**:

```rust
fn main() {
    let x = 42.to_string();  // Error: E0689 - 42 是什么类型？
}
```

**解决方案**:

```rust
fn main() {
    let x = 42i32.to_string();  // ✅ 明确类型后缀
    let x = 42_u64.to_string();  // ✅ 明确类型后缀
    let x: i32 = 42;
    let s = x.to_string();  // ✅ 变量有明确类型
}
```

---

## 警告 (W开头)

### W0001 - 未使用的变量

**警告信息**: `unused variable`

**触发场景**: 定义了但未使用的变量。

**代码示例**:

```rust
fn main() {
    let x = 42;  // Warning: unused variable
    println!("Hello");
}
```

**解决方案**:

```rust
fn main() {
    let _x = 42;  // ✅ 以下划线开头表示故意不用

    let x = 42;
    println!("{}", x);  // ✅ 使用变量

    let x = 42;
    #[allow(unused_variables)]
    let _ = x;  // ✅ 或者允许警告
}
```

---

### W0002 - 未使用的导入

**警告信息**: `unused import`

**触发场景**: 导入但未使用的模块或项。

**代码示例**:

```rust
use std::collections::HashMap;  // Warning: unused import

fn main() {
    println!("Hello");
}
```

**解决方案**:

```rust
use std::collections::HashMap;

fn main() {
    let mut map = HashMap::new();  // ✅ 使用导入
    map.insert("key", "value");
}
```

---

### W0003 - 不可达代码

**警告信息**: `unreachable code`

**触发场景**: 永远不会执行的代码。

**代码示例**:

```rust
fn main() {
    return;
    println!("Hello");  // Warning: unreachable statement
}
```

---

### W0004 - 未使用的 mut

**警告信息**: `variable does not need to be mutable`

**触发场景**: 声明为可变但从未修改的变量。

**代码示例**:

```rust
fn main() {
    let mut x = 42;  // Warning: does not need to be mutable
    println!("{}", x);
}
```

**解决方案**:

```rust
fn main() {
    let x = 42;  // ✅ 移除 mut
    println!("{}", x);
}
```

---

### W0005 - 死代码

**警告信息**: `dead_code`

**触发场景**: 私有函数或模块从未使用。

**代码示例**:

```rust
fn unused_function() {  // Warning: dead_code
    println!("Never called");
}

fn main() {}
```

**解决方案**:

```rust
#[allow(dead_code)]
fn unused_function() {  // ✅ 允许死代码（开发中）
    println!("May be used later");
}

pub fn public_function() {  // ✅ 公共函数不会被警告
    println!("Public API");
}

fn main() {}
```

---

### W0006 - 未处理的 Result

**警告信息**: `unused Result that must be used`

**触发场景**: 忽略了可能出错的 Result。

**代码示例**:

```rust
use std::fs::File;

fn main() {
    File::open("file.txt");  // Warning: unused Result
}
```

**解决方案**:

```rust
use std::fs::File;

fn main() {
    // 方案 1: 正确处理
    match File::open("file.txt") {
        Ok(file) => println!("打开成功"),
        Err(e) => println!("错误: {}", e),
    }

    // 方案 2: 使用 ? 运算符（在返回 Result 的函数中）
    // let file = File::open("file.txt")?;

    // 方案 3: 显式忽略（如果确定安全）
    let _ = File::open("file.txt");
}
```

---

## 错误码快速修复索引表

| 错误码 | 常见原因 | 快速修复 | 相关概念 |
|:---|:---|:---|:---|
| **E0106** | 缺少生命周期标注 | 添加 `'a` 生命周期参数 | 生命周期标注 |
| **E0277** | Trait 未实现 | 添加 `impl Trait` 或修改 bound | Trait 系统 |
| **E0282** | 类型无法推断 | 添加类型标注 `let x: T` | 类型推断 |
| **E0308** | 类型不匹配 | 类型转换或修正声明 | 类型系统 |
| **E0381** | 使用未初始化变量 | 初始化变量 `let x = value` | 变量初始化 |
| **E0382** | 使用已移动的值 | 使用引用 `.clone()` 或重构 | 移动语义 |
| **E0383** | 部分移动 | 克隆字段或使用引用 | 部分移动 |
| **E0384** | 修改不可变变量 | 使用 `let mut` | 可变性 |
| **E0432** | 导入未找到 | 检查路径和 Cargo.toml | 模块系统 |
| **E0433** | Crate 未找到 | 添加依赖到 Cargo.toml | 包管理 |
| **E0499** | 重复可变借用 | 使用作用域隔离或 NLL | 借用规则 |
| **E0502** | 可变不可变共存 | 分离借用作用域 | 借用规则 |
| **E0503** | 使用已移动值 | 克隆或引用 | 所有权转移 |
| **E0505** | 在借用时移动 | 等待借用结束 | 借用与移动 |
| **E0506** | 在借用时赋值 | 等待借用结束 | 赋值规则 |
| **E0507** | 从引用中移出 | 使用 `.clone()` | 解引用移动 |
| **E0596** | 不可变借可变 | 使用 `let mut` | 可变性 |
| **E0597** | 生命周期不足 | 确保引用在有效期内 | 生命周期 |
| **E0599** | 方法未找到 | 检查类型或实现 Trait | 方法解析 |
| **E0609** | 字段未找到 | 检查字段名 | 结构体访问 |
| **E0616** | 私有字段 | 使用公共 API 或设为 pub | 可见性 |
| **E0700** | 异步借用问题 | 限制跨 await 的借用 | 异步借用 |

---

## 相关资源

### 项目内文档

| 主题 | 路径 | 描述 |
|:---|:---|:---|
| 所有权与借用 | `crates/c01_ownership_borrow_scope/docs/` | 所有权系统核心概念 |
| 类型系统 | `crates/c02_type_system/docs/` | 类型系统详解 |
| 模式匹配 | `crates/c03_control_fn/docs/tier_02_guides/04_模式匹配指南.md` | 模式匹配完整指南 |
| 生命周期 | `crates/c01_ownership_borrow_scope/docs/tier_02_guides/03_生命周期实践.md` | 生命周期实践 |
| 并发编程 | `crates/c05_threads/docs/` | 线程与并发 |
| 异步编程 | `crates/c06_async/docs/` | async/await |
| 宏系统 | `crates/c11_macro_system/docs/` | 宏编程指南 |

### 速查卡

| 速查卡 | 路径 | 内容 |
|:---|:---|:---|
| 所有权 | `quick_reference/ownership_cheatsheet.md` | 所有权规则速查 |
| 类型系统 | `quick_reference/type_system.md` | 类型相关速查 |
| 错误处理 | `quick_reference/error_handling_cheatsheet.md` | 错误处理模式 |
| 生命周期 | `quick_reference/lifetimes_cheatsheet.md` | 生命周期速查 |

### 官方资源

- [Compiler Error Index](https://doc.rust-lang.org/error-index.html) - 官方错误码索引
- [Rust Reference](https://doc.rust-lang.org/reference/) - 语言参考
- [The Rust Book](https://doc.rust-lang.org/book/) - Rust 官方教程

### 形式化理论

- [所有权模型形式化](../research_notes/formal_methods/ownership_model.md)
- [借用检查器证明](../research_notes/formal_methods/borrow_checker_proof.md)
- [生命周期形式化](../research_notes/formal_methods/lifetime_formalization.md)

---

## 故障排查建议

1. **阅读完整错误信息**: Rust 编译器错误信息通常很详细，包含具体位置和建议
2. **使用 `--explain`**: `rustc --explain EXXXX` 查看官方解释
3. **检查 Cargo.toml**: 确保依赖正确声明
4. **使用 `cargo check`**: 比 `cargo build` 更快，适合快速检查错误
5. **使用 Clippy**: `cargo clippy` 提供更多有用的警告和建议
6. **查阅文档**: 本文档或官方错误索引

---

## 🆕 Rust 1.94 更新说明

> **适用版本**: Rust 1.94.0+

Rust 1.94 对错误诊断进行了多项改进：

- **更清晰的借用错误提示**: 错误信息包含可视化借用图
- **异步错误改进**: 更好的 async/await 错误定位
- **类型推断增强**: 更好的类型推断失败提示

详见 [Rust 1.94 发布说明](./16_rust_1.94_release_notes.md)

---

**最后更新**: 2026-03-17
**状态**: ✅ 深度整合完成
