> **内容分级**: [基础级]

# Structs（结构体）
>
> **EN**: Structs
> **Summary**: Structs: Rust's custom product type, covering named-field structs, tuple structs, unit-like structs, struct update syntax, methods, and field visibility.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [初学者]
> **Bloom 层级**: L1-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: F×Und — 理解结构体（Struct）作为自定义复合类型的基础构造
> **定位**: 系统讲解 Rust 结构体（Struct）的三种形式、字段可见性、结构体更新语法与方法基础，为后续 Trait、Enum、泛型（Generics）奠定类型基础。
> **前置概念**: [Type System](../02_type_system/04_type_system.md) · [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) · [Functions](12_functions.md) · [Terminology Glossary](../../00_meta/01_terminology/terminology_glossary.md)
> **后置概念**: [Enumerations](15_enumerations.md) · [Implementations](16_implementations.md) · [Traits](../../02_intermediate/00_traits/01_traits.md)
>
> **来源**: [The Rust Programming Language — Structs](https://doc.rust-lang.org/book/ch05-00-structs.html) · [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html)

---

> **对应 Crate**: [`c02_type_system`](../../crates/c02_type_system)
> **对应练习**: [`exercises/src/type_system/`](../../exercises/src/type_system)
> **权威来源**: [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html) · [TRPL — Structs](https://doc.rust-lang.org/book/ch05-00-structs.html)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（Rust Reference、TRPL）

## 认知路径

> **认知路径**: 本节从“如何组合多个相关值”出发，依次建立命名字段型、元组型、单元型结构体的完整图景。

1. **问题识别**: 当多个值在逻辑上属于同一实体时，如何用类型表达？
2. **概念建立**: 掌握三种结构体形式、字段可见性、结构体更新语法。
3. **机制推理**: 通过 ⟹ 定理链将结构体定义、字段所有权（Ownership）与借用（Borrowing）规则串联起来。
4. **边界辨析**: 借助反命题/反例理解更新语法的所有权（Ownership）陷阱、字段可变性问题。
5. **迁移应用**: 将结构体与枚举（Enum）、实现块、泛型（Generics）、Trait 等后置概念链接。

---

> **过渡**: 从结构体的直观描述转向其形式化定义，需要先把“组合数据”的直觉转化为乘积类型与字段访问的精确规则。
> **过渡**: 在建立结构体的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。
> **过渡**: 最后，将结构体与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 1]: 结构体是命名乘积类型 ⟹ 其值由所有字段共同决定，字段顺序不影响类型相等性。
>
> **定理 2** [Tier 1]: 结构体字段默认私有 ⟹ 跨模块（Module）访问需显式标注 `pub`，否则编译器拒绝访问。
>
> **定理 3** [Tier 1]: 结构体更新语法 `..old` 会移动未显式指定字段的所有权 ⟹ 若字段未实现 `Copy`，原实例将部分失效。

---

> **反向推理 1** [Tier 1]: 若编译器报错 `field ... is private` ⟸ 应检查字段可见性或添加 `pub`。
>
> **反向推理 2** [Tier 1]: 若使用 `..old` 后出现 `use of partially moved value` ⟸ 应检查被更新字段是否实现了 `Copy`。

---

## 📑 目录

- [Structs（结构体）](#structs结构体)
  - [认知路径](#认知路径)
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
    - [6.4 判定表：结构体形式与更新语法处置](#64-判定表结构体形式与更新语法处置)
  - [七、权威来源索引](#七权威来源索引)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)

---

## 一、核心命题

> **命题 1**: 结构体是 Rust 的**命名乘积类型（Named Product Type）**，将多个相关值组合成一个类型。
>
> **命题 2**: Rust 有三种结构体：**命名字段型**、**元组型**、**单元型**。
>
> **命题 3**: 结构体字段默认私有；通过 `pub` 暴露给模块（Module）外部。
>
> **命题 4**: 结构体更新语法 `..old` 使用旧实例的未显式指定字段，但会移动所有权。

---

## 二、三种结构体

> (Source: [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html))

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

> (Source: [TRPL — Structs](https://doc.rust-lang.org/book/ch05-00-structs.html))

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

> **关键洞察**: 元组结构体是零成本抽象（Zero-Cost Abstraction），可在编译期区分语义不同的同底层类型。

---

## 六、反例与边界测试

本节围绕「反例与边界测试」展开，依次讨论未实现 `Copy` 时的更新语法陷阱、字段名与变量名相同、试图给不可变结构体字段赋值与判定表：结构体形式与更新语法处置。

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

### 6.4 判定表：结构体形式与更新语法处置

| 场景/条件 | 判定结论 | 依据（定理/规则） | 反例或失效条件 |
|:---|:---|:---|:---|
| 语义明确的复合数据 | 命名字段结构体 | §二 三种结构体对比 | 字段过多且可分组 ⟹ 考虑拆分嵌套结构 |
| 轻量包装/newtype | 元组结构体 | §五 元组结构体与 newtype 模式 | 字段需要语义名 ⟹ 改用命名字段形式 |
| 类型标记/类型状态机 | 单元结构体 | §二 三种结构体 | 需要携带数据 ⟹ 不适用 |
| 基于旧实例修改少数字段 | 更新语法 `..old` | §三 结构体更新语法 | 未 `Copy` 字段被 move ⟹ 原实例部分失效（§6.1、定理 3） |
| 跨模块访问字段 | 字段显式标 `pub` | 定理 2 | 默认私有 ⟹ `field is private`（反向推理 1） |
| 修改不可变实例的字段 | 编译拒绝 | §6.3 | 需整体替换，或引入内部可变性 |

## 七、权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [TRPL — Structs](https://doc.rust-lang.org/book/ch05-00-structs.html) | ✅ 一级 | 官方教程 |
| [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html) | ✅ 一级 | 语言规范 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Cardelli & Wegner: On Understanding Types, Data Abstraction, and Polymorphism (ACM Comput. Surv. 1985)](https://dl.acm.org/doi/10.1145/6041.6042)
- **P2 生态/社区**: [docs.rs/semver — 生态权威 API 文档](https://docs.rs/semver) · [docs.rs/toml — 生态权威 API 文档](https://docs.rs/toml)
