> **内容分级**: [基础级]

# Enumerations（枚举）
>
> **EN**: Enumerations
> **Summary**: Enumerations: Rust's tagged unions with variants carrying data, covering variant types, `Option<T>`, `Result<T, E>`, pattern matching, and `#[non_exhaustive]`.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [初学者]
> **Bloom 层级**: L1-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: F×App — 掌握枚举（Enum）作为带标签联合类型的表达力
> **定位**: 系统讲解 Rust 枚举（Enum）的定义、变体负载、Option/Result 两个核心枚举、模式匹配（Pattern Matching）穷尽性检查，以及与错误处理（Error Handling）的关系。
> **前置概念**: [Type System](../02_type_system/01_type_system.md) · [Structs](04_structs.md) · [Pattern Matching](../04_control_flow/02_patterns.md) · [Terminology Glossary](../../00_meta/01_terminology/01_terminology_glossary.md)
> **后置概念**: [Error Handling Basics](../08_error_handling/01_error_handling_basics.md) · [Result and Option Deep Dive](../../02_intermediate/03_error_handling/01_error_handling.md) · [Algebraic Data Types](../../04_formal/00_type_theory/01_type_theory.md)
>
> **来源**: [The Rust Programming Language — Enums](https://doc.rust-lang.org/book/ch06-00-enums.html) · [Rust Reference — Enumerations](https://doc.rust-lang.org/reference/items/enumerations.html) · [RFC 2008 — non_exhaustive](https://github.com/rust-lang/rfcs/pull/2008)

---

> **对应 Crate**: [`c02_type_system`](../../crates/c02_type_system)
> **对应练习**: [`exercises/src/type_system/`](../../exercises/src/type_system)
> **权威来源**: [Rust Reference — Enumerations](https://doc.rust-lang.org/reference/items/enumerations.html) · [TRPL — Enums](https://doc.rust-lang.org/book/ch06-00-enums.html) · [RFC 2008 — non_exhaustive](https://github.com/rust-lang/rfcs/pull/2008)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（Rust Reference、TRPL、RFC 2008）

## 认知路径

> **认知路径**: 本节从“如何表达一组互斥的状态”出发，依次建立枚举变体、`Option<T>`、`Result<T, E>` 与模式匹配（Pattern Matching）穷尽性的完整图景。

1. **问题识别**: 当变量只能处于若干互斥状态之一时，如何用类型安全地表达？
2. **概念建立**: 掌握枚举定义、变体负载、`Option`、`Result`、穷尽性检查。
3. **机制推理**: 通过 ⟹ 定理链将枚举、模式匹配与错误处理（Error Handling）规则串联起来。
4. **边界辨析**: 借助反命题/反例理解未处理 `None`、`if let` 误用、变体所有权（Ownership）移动等问题。
5. **迁移应用**: 将枚举与错误处理、代数数据类型、形式化语义等后置概念链接。

---

> **过渡**: 从枚举的直观描述转向其形式化定义，需要先把“多选一”的直觉转化为带标签联合类型与变体构造的精确规则。
> **过渡**: 在建立枚举的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。
> **过渡**: 最后，将枚举与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 1]: 枚举是带标签联合类型 ⟹ 其值恰好属于一个变体，编译器可在 `match` 中强制穷尽所有可能。
>
> **定理 2** [Tier 1]: `Option<T>` 显式区分“有值”与“无值” ⟹ 替代空指针，消除解引用（Reference）空指针的运行时（Runtime）错误。
>
> **定理 3** [Tier 1]: `Result<T, E>` 显式区分“成功”与“失败” ⟹ 错误处理成为类型系统（Type System）的一部分，不可静默忽略。

---

> **反向推理 1** [Tier 1]: 若编译器报错 `non-exhaustive patterns` ⟸ 应检查 `match` 是否覆盖了所有枚举变体（包括 `None` / `Err`）。
>
> **反向推理 2** [Tier 1]: 若需要从枚举变体中提取值 ⟸ 优先使用 `match` 或 `if let`，并注意所有权（Ownership）移动。

---

## 📑 目录

- [Enumerations（枚举）](#enumerations枚举)
  - [认知路径](#认知路径)
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
    - [6.4 判定表：枚举建模与匹配处置](#64-判定表枚举建模与匹配处置)
  - [七、权威来源索引](#七权威来源索引)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)

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

> (Source: [Rust Reference — Enumerations](https://doc.rust-lang.org/reference/items/enumerations.html))

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

> (Source: [TRPL — Enums](https://doc.rust-lang.org/book/ch06-00-enums.html))

```rust
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
    ChangeColor(u8, u8, u8),
}

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

「反例与边界测试」涉及未处理 `None`、错误使用 `if let` 处理 Result、枚举变体携带的所有权移动与判定表：枚举建模与匹配处置，本节逐一说明其要点。

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

**修正**: 对变体使用引用（Reference）匹配 `Packet::Data(ref s)`，或让 `Packet` 实现 `Clone`。

---

### 6.4 判定表：枚举建模与匹配处置

| 场景/条件 | 判定结论 | 依据（定理/规则） | 反例或失效条件 |
|:---|:---|:---|:---|
| 一组互斥状态 | 枚举（带标签联合） | 定理 1 | 状态可组合共存 ⟹ 用结构体或位标志 |
| 值可能缺失 | `Option<T>` | 定理 2 | 缺失即错误 ⟹ 用 `Result` |
| 可恢复的失败 | `Result<T, E>` | §三 `Option<T>` 与 `Result<T, E>` | 不可恢复的程序 bug ⟹ panic |
| 多分支处理 | `match`，编译器强制穷尽 | §四 模式匹配与穷尽性 | 遗漏分支 ⟹ 编译错误 |
| 只关心一个分支 | `if let` | §四 | 静默忽略其他分支可能非预期（§6.2） |
| 库枚举未来可能扩展 | `#[non_exhaustive]` | §五 | 外部 `match` 必须加 `_` 通配分支 |
| 匹配后仍需使用原值 | 引用匹配（`ref`/`&`） | §6.3 | 按值匹配 ⟹ 变体数据被 move |

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Enums](https://doc.rust-lang.org/book/ch06-00-enums.html) | ✅ 一级 | 官方教程 |
| [Rust Reference — Enumerations](https://doc.rust-lang.org/reference/items/enumerations.html) | ✅ 一级 | 语言规范 |
| [RFC 2008 — non_exhaustive](https://github.com/rust-lang/rfcs/pull/2008) | ✅ 一级 | 向后兼容枚举扩展 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Cardelli & Wegner: On Understanding Types, Data Abstraction, and Polymorphism (ACM Comput. Surv. 1985)](https://dl.acm.org/doi/10.1145/6041.6042)
- **P2 生态/社区**: [docs.rs/cargo_metadata — 生态权威 API 文档](https://docs.rs/cargo_metadata) · [docs.rs/semver — 生态权威 API 文档](https://docs.rs/semver)
