> **内容分级**: [基础级]

# Implementations（实现块）
>
> **EN**: Implementations
> **Summary**: Implementations: `impl` blocks for defining methods and trait implementations, covering associated functions, `self`, `&self`, `&mut self`, trait impls, and inherent impls.
> **受众**: [初学者]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: F×App — 掌握 `impl` 块将行为绑定到类型的机制
> **定位**: 系统讲解 Rust `impl` 块的两种形式（固有实现、Trait 实现）、方法 receiver、关联函数，以及与结构体/枚举/Trait 的关系。
> **前置概念**: [Structs](14_structs.md) · [Enumerations](15_enumerations.md) · [Traits](../../02_intermediate/00_traits/01_traits.md) · [Functions](12_functions.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Generics](../../02_intermediate/01_generics/02_generics.md) · [Type Conversions](../../02_intermediate/04_types_and_conversions/37_type_conversions.md) · [Advanced Traits](../../02_intermediate/00_traits/19_advanced_traits.md)
>
> **来源**: [The Rust Programming Language — Method Syntax](https://doc.rust-lang.org/book/ch05-03-method-syntax.html) · [Rust Reference — Implementations](https://doc.rust-lang.org/reference/items/implementations.html)

---

> **对应 Crate**: [`c02_type_system`](../../crates/c02_type_system)
> **对应练习**: [`exercises/src/type_system/`](../../exercises/src/type_system)

## 📑 目录

- [Implementations（实现块）](#implementations实现块)
  - [📑 目录](#-目录)
  - [一、核心命题](#一核心命题)
  - [二、固有实现（Inherent Impl）](#二固有实现inherent-impl)
  - [三、方法 Receiver](#三方法-receiver)
  - [四、关联函数](#四关联函数)
  - [五、Trait 实现](#五trait-实现)
  - [六、反例与边界测试](#六反例与边界测试)
    - [6.1 在 `&self` 方法中修改字段](#61-在-self-方法中修改字段)
    - [6.2 调用获取所有权的方法后继续使用](#62-调用获取所有权的方法后继续使用)
    - [6.3 Orphan Rule 违规](#63-orphan-rule-违规)
  - [七、权威来源索引](#七权威来源索引)

---

## 一、核心命题

> **命题 1**: `impl` 块将**函数（方法）**绑定到类型，分为固有实现和 Trait 实现。
>
> **命题 2**: 方法第一个参数为 `self`、`&self` 或 `&mut self`，决定调用时所有权的转移/借用方式。
>
> **命题 3**: 关联函数没有 `self` 参数，通常用作构造函数，通过 `Type::function()` 调用。
>
> **命题 4**: 一个类型可以为多个 Trait 实现，但受 Orphan Rule 与 Coherence 约束。

---

## 二、固有实现（Inherent Impl）

```rust
struct Rectangle {
    width: u32,
    height: u32,
}

impl Rectangle {
    fn area(&self) -> u32 {
        self.width * self.height
    }

    fn can_hold(&self, other: &Rectangle) -> bool {
        self.width > other.width && self.height > other.height
    }
}

fn main() {
    let r = Rectangle { width: 10, height: 5 };
    println!("{}", r.area()); // 50
}
```

> **关键洞察**: 固有实现让类型拥有"面向对象"风格的方法，但不引入继承，所有行为通过组合和 Trait 表达。

---

## 三、方法 Receiver

| Receiver | 调用方式 | 所有权 |
|:---|:---|:---|
| `self` | `obj.method()` | 获取所有权 |
| `&self` | `obj.method()` | 不可变借用 |
| `&mut self` | `obj.method()` | 可变借用 |

```rust
impl String {
    // 不可变借用
    fn len(&self) -> usize { self.as_bytes().len() }

    // 可变借用
    fn push_str(&mut self, s: &str) { /* ... */ }

    // 获取所有权并返回转换后的值
    fn into_bytes(self) -> Vec<u8> { /* ... */ }
}
```

---

## 四、关联函数

```rust
impl Rectangle {
    fn square(size: u32) -> Rectangle {
        Rectangle { width: size, height: size }
    }
}

fn main() {
    let sq = Rectangle::square(5);
}
```

> **注意**: 关联函数没有 `self`，不是方法，但通常作为构造函数或工具函数。

---

## 五、Trait 实现

```rust
trait Drawable {
    fn draw(&self);
}

impl Drawable for Rectangle {
    fn draw(&self) {
        println!("{}x{} rectangle", self.width, self.height);
    }
}

fn main() {
    let r = Rectangle { width: 4, height: 2 };
    r.draw();
}
```

> **规则**:
>
> - `impl Trait for Type { ... }` 实现 Trait。
> - 实现的方法签名必须与 Trait 定义一致。
> - 受 Orphan Rule 约束：Trait 或类型至少有一个由当前 crate 定义。

---

## 六、反例与边界测试

### 6.1 在 `&self` 方法中修改字段

```rust,compile_fail
impl Rectangle {
    fn set_width(&self, w: u32) {
        self.width = w; // ❌ 不可变借用无法修改
    }
}
```

**修正**: 使用 `&mut self`。

### 6.2 调用获取所有权的方法后继续使用

```rust,compile_fail
fn main() {
    let s = String::from("hello");
    s.into_bytes();
    println!("{s}"); // ❌ s 已被移动
}
```

**修正**: 使用 `s.as_bytes()` 或 `s.clone().into_bytes()`。

### 6.3 Orphan Rule 违规

```rust,compile_fail
trait MyTrait {}
impl MyTrait for String {} // ❌ 当前 crate 既未定义 MyTrait 也未定义 String
```

**修正**: 使用 newtype 包装 `struct MyString(String); impl MyTrait for MyString {}`。

---

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Method Syntax](https://doc.rust-lang.org/book/ch05-03-method-syntax.html) | ✅ 一级 | 方法与 impl 入门 |
| [Rust Reference — Implementations](https://doc.rust-lang.org/reference/items/implementations.html) | ✅ 一级 | 完整规范 |
