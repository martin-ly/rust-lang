> **内容分级**: [基础级]

# Enumerations（枚举）
>
> **EN**: Enumerations
> **Summary**: Enumerations: Rust's tagged unions with variants carrying data, covering variant types, `Option<T>`, `Result<T, E>`, pattern matching, and `#[non_exhaustive]`.
> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 理解 → 应用
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: F×App — 掌握枚举作为带标签联合类型的表达力
> **定位**: 系统讲解 Rust 枚举的定义、变体负载、Option/Result 两个核心枚举、模式匹配穷尽性检查，以及与错误处理的关系。
> **前置概念**: [Type System](../02_type_system/04_type_system.md) · [Structs](14_structs.md) · [Pattern Matching](../04_control_flow/40_patterns.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Error Handling Basics](../08_error_handling/32_error_handling_basics.md) · [Result and Option Deep Dive](../../02_intermediate/03_error_handling/04_error_handling.md) · [Algebraic Data Types](../../04_formal/00_type_theory/02_type_theory.md)
>
> **来源**: [The Rust Programming Language — Enums](https://doc.rust-lang.org/book/ch06-00-enums.html) · [Rust Reference — Enumerations](https://doc.rust-lang.org/reference/items/enumerations.html) · [RFC 2008 — non_exhaustive](https://github.com/rust-lang/rfcs/pull/2008)

---

> **对应 Crate**: [`c02_type_system`](../../crates/c02_type_system)
> **对应练习**: [`exercises/src/type_system/`](../../exercises/src/type_system)

## 📑 目录

- [Enumerations（枚举）](#enumerations枚举)
  - [📑 目录](#-目录)
  - [一、核心命题](#一核心命题)
  - [二、枚举变体](#二枚举变体)
  - [三、`Option<T>` 与 `Result<T, E>`](#三optiont-与-resultt-e)
  - [四、模式匹配与穷尽性](#四模式匹配与穷尽性)
  - [五、`#[non_exhaustive]`](#五non_exhaustive)
  - [六、反例与边界测试](#六反例与边界测试)
    - [6.1 未处理 `None`](#61-未处理-none)
    - [6.2 错误使用 `if let` 处理 Result](#62-错误使用-if-let-处理-result)
    - [6.3 枚举变体携带的所有权移动](#63-枚举变体携带的所有权移动)
  - [七、权威来源索引](#七权威来源索引)

---

## 一、核心命题

> **命题 1**: Rust 枚举是**带标签的联合类型（Tagged Union / Sum Type）**，每个变体可以携带不同类型和数量的数据。
>
> **命题 2**: `Option<T>` 显式表达"值可能存在或不存在"，替代空指针。
>
> **命题 3**: `Result<T, E>` 显式表达"操作可能失败"，是 Rust 错误处理的基础。
>
> **命题 4**: 编译器对 `match` 执行**穷尽性检查**，要求覆盖所有变体。

---

## 二、枚举变体

```rust
enum Message {
    Quit,                           // 单元变体
    Move { x: i32, y: i32 },        // 命名字段变体
    Write(String),                  // 单字段元组变体
    ChangeColor(u8, u8, u8),        // 多字段元组变体
}

fn main() {
    let msg = Message::Move { x: 10, y: 20 };
}
```

> **关键洞察**: 一个枚举的不同变体在内存中共享同一个标签位，但负载大小可能不同；Rust 自动计算所需空间。

---

## 三、`Option<T>` 与 `Result<T, E>`

```rust
let maybe: Option<i32> = Some(5);
let none: Option<i32> = None;

let ok: Result<i32, &str> = Ok(42);
let err: Result<i32, &str> = Err("failed");
```

| 类型 | 含义 | 常用场景 |
|:---|:---|:---|
| `Option<T>` | 有值 / 无值 | 查找、可选配置 |
| `Result<T, E>` | 成功 / 失败 | IO、解析、网络请求 |

```rust
fn divide(a: f64, b: f64) -> Result<f64, &'static str> {
    if b == 0.0 {
        Err("division by zero")
    } else {
        Ok(a / b)
    }
}
```

---

## 四、模式匹配与穷尽性

```rust
fn handle(msg: Message) {
    match msg {
        Message::Quit => println!("quit"),
        Message::Move { x, y } => println!("move to ({x}, {y})"),
        Message::Write(text) => println!("{text}"),
        Message::ChangeColor(r, g, b) => println!("RGB({r}, {g}, {b})"),
    }
}
```

> **规则**: `match` 必须覆盖枚举所有变体，否则编译错误。这是 Rust "无遗漏" 安全保证的一部分。

```rust,compile_fail
fn incomplete(msg: Message) {
    match msg {
        Message::Quit => println!("quit"),
        // ❌ 缺少其他变体
    }
}
```

---

## 五、`#[non_exhaustive]`

```rust
#[non_exhaustive]
pub enum ApiError {
    NotFound,
    BadRequest,
}
```

**语义**:

- 对外部 crate 的消费者，`match` 必须包含 `_ =>` 分支。
- 允许库作者在未来版本添加新变体而不破坏下游编译。
- 不影响定义该枚举的 crate 内部穷尽性检查。

---

## 六、反例与边界测试

### 6.1 未处理 `None`

```rust,compile_fail
fn unwrap_unsafe(x: Option<i32>) -> i32 {
    x.unwrap() // 运行时 panic if None
}
```

**修正**: 使用 `match` 或 `if let Some(v) = x`。

### 6.2 错误使用 `if let` 处理 Result

```rust
fn may_fail() -> Result<(), &'static str> { Ok(()) }

fn main() {
    if let Err(e) = may_fail() {
        println!("error: {e}");
    }
    // Ok 分支被忽略，可能不是预期行为
}
```

**建议**: 明确处理 `Ok` 或返回错误给调用者。

### 6.3 枚举变体携带的所有权移动

```rust,compile_fail
enum Packet {
    Data(String),
}

fn main() {
    let p = Packet::Data(String::from("x"));
    match p {
        Packet::Data(s) => println!("{s}"),
    }
    println!("{:?}", p); // ❌ p 已被移动
}
```

**修正**: 对变体使用引用匹配 `Packet::Data(ref s)`，或让 `Packet` 实现 `Clone`。

---

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Enums](https://doc.rust-lang.org/book/ch06-00-enums.html) | ✅ 一级 | 官方教程 |
| [Rust Reference — Enumerations](https://doc.rust-lang.org/reference/items/enumerations.html) | ✅ 一级 | 语言规范 |
| [RFC 2008 — non_exhaustive](https://github.com/rust-lang/rfcs/pull/2008) | ✅ 一级 | 向后兼容枚举扩展 |
