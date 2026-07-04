> **内容分级**: [基础级]

# Structs（结构体）
>
> **EN**: Structs
> **Summary**: Structs: Rust's custom product type, covering named-field structs, tuple structs, unit-like structs, struct update syntax, methods, and field visibility.
> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 理解 → 应用
> **A/S/P 标记**: **S** — Structure
> **双维定位**: F×Und — 理解结构体作为自定义复合类型的基础构造
> **定位**: 系统讲解 Rust 结构体的三种形式、字段可见性、结构体更新语法与方法基础，为后续 Trait、Enum、泛型奠定类型基础。
> **前置概念**: [Type System](../02_type_system/04_type_system.md) · [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) · [Functions](12_functions.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Enumerations](15_enumerations.md) · [Implementations](16_implementations.md) · [Traits](../../02_intermediate/00_traits/01_traits.md)
>
> **来源**: [The Rust Programming Language — Structs](https://doc.rust-lang.org/book/ch05-00-structs.html) · [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html)

---

> **对应 Crate**: [`c02_type_system`](../../crates/c02_type_system)
> **对应练习**: [`exercises/src/type_system/`](../../exercises/src/type_system)

## 📑 目录

- [Structs（结构体）](#structs结构体)
  - [📑 目录](#-目录)
  - [一、核心命题](#一核心命题)
  - [二、三种结构体](#二三种结构体)
  - [三、结构体更新语法](#三结构体更新语法)
  - [四、字段可见性](#四字段可见性)
  - [五、元组结构体与 newtype 模式](#五元组结构体与-newtype-模式)
  - [六、反例与边界测试](#六反例与边界测试)
    - [6.1 未实现 `Copy` 时的更新语法陷阱](#61-未实现-copy-时的更新语法陷阱)
    - [6.2 字段名与变量名相同](#62-字段名与变量名相同)
    - [6.3 试图给不可变结构体字段赋值](#63-试图给不可变结构体字段赋值)
  - [七、权威来源索引](#七权威来源索引)

---

## 一、核心命题

> **命题 1**: 结构体是 Rust 的**命名乘积类型（Named Product Type）**，将多个相关值组合成一个类型。
>
> **命题 2**: Rust 有三种结构体：**命名字段型**、**元组型**、**单元型**。
>
> **命题 3**: 结构体字段默认私有；通过 `pub` 暴露给模块外部。
>
> **命题 4**: 结构体更新语法 `..old` 使用旧实例的未显式指定字段，但会移动所有权。

---

## 二、三种结构体

```rust
// 1. 命名字段型
struct User {
    username: String,
    email: String,
    active: bool,
}

// 2. 元组型
struct Point(f64, f64);

// 3. 单元型（常用于类型状态机或标记）
struct Electron;
```

**对比**:

| 形式 | 用途 | 访问字段 |
|:---|:---|:---|
| 命名字段 | 语义明确的复合数据 | `user.username` |
| 元组 | 轻量包装，newtype | `p.0` |
| 单元 | 零大小类型，类型标记 | 无字段 |

---

## 三、结构体更新语法

```rust
let u1 = User {
    username: String::from("alice"),
    email: String::from("a@example.com"),
    active: true,
};

let u2 = User {
    email: String::from("b@example.com"),
    ..u1 // 其余字段从 u1 移动
};

// u1.username 已移动，不能再使用
```

> **注意**: `..u1` 会**移动**未显式列出的字段。若字段未实现 `Copy`，原实例将部分失效。

---

## 四、字段可见性

```rust
mod user {
    pub struct User {
        pub username: String, // 外部可见
        email: String,        // 模块外部不可见
    }
}

fn main() {
    let u = user::User {
        username: String::from("tom"),
        email: String::from("tom@example.com"), // ❌ 私有字段
    };
}
```

> **规则**: 结构体本身标记 `pub` 只是让类型名可见；每个字段仍需单独标记 `pub`。

---

## 五、元组结构体与 newtype 模式

```rust
struct Meters(u32);
struct Kilometers(u32);

fn run(m: Meters) {
    println!("{} meters", m.0);
}

fn main() {
    let d = Meters(1000);
    // run(Kilometers(1000)); // ❌ 类型不同
    run(d);
}
```

> **关键洞察**: 元组结构体是零成本抽象，可在编译期区分语义不同的同底层类型。

---

## 六、反例与边界测试

### 6.1 未实现 `Copy` 时的更新语法陷阱

```rust,compile_fail
struct Data {
    s: String,
    n: i32,
}

fn main() {
    let d1 = Data { s: String::from("x"), n: 1 };
    let d2 = Data { n: 2, ..d1 };
    println!("{}", d1.s); // ❌ d1.s 已被移动
}
```

**修正**: 对 `s` 显式 clone：`..d1.clone()`。

### 6.2 字段名与变量名相同

```rust
let username = String::from("bob");
let email = String::from("bob@example.com");

let u = User {
    username, // 字段初始化简写
    email,
    active: true,
};
```

### 6.3 试图给不可变结构体字段赋值

```rust,compile_fail
fn main() {
    let u = User { username: String::from("a"), email: String::from("b"), active: true };
    u.active = false; // ❌ 不能给不可变字段赋值
}
```

**修正**: 使用 `let mut u = ...`。

---

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Structs](https://doc.rust-lang.org/book/ch05-00-structs.html) | ✅ 一级 | 官方教程 |
| [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html) | ✅ 一级 | 语言规范 |
