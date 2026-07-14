# Default Field Values 预研：结构体字段默认值

> **代码状态**: ✅ 含 nightly 实测示例（`#![feature(default_field_values)]`，rustc 1.99.0-nightly 2026-07-10 通过）
>
> **EN**: Default Field Values Preview
> **Summary**: Preview of struct default field values (RFC 3681) — declaring per-field defaults in struct definitions that apply in functional record update (`..`) syntax, changing struct construction ergonomics and `Default` trait interactions.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **状态**: 🧪 Nightly 实验性（feature gate `default_field_values`）
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.99.0 可用；stable 1.97.0 不可用
> **预计稳定**: 待定（RFC 已接受，实现与边界语义评审中）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S** — Structure
> **双维定位**: C×Ana — 分析字段默认值语义
> **定位**: 跟踪 [RFC 3681](https://rust-lang.github.io/rfcs/3681-default-field-values.html) 引入的结构体字段默认值语法，说明其与函数式记录更新（Functional Record Update, FRU）、`Default` trait 及私有字段的交互。
> **前置概念**: [Structs](../../01_foundation/07_modules_and_items/04_structs.md) · [构造与初始化](../../02_intermediate/00_traits/05_construction_and_initialization.md) · [Derive Traits](../../02_intermediate/00_traits/06_derive_traits.md)
> **后置概念**: [Version Tracking](../00_version_tracking/01_rust_version_tracking.md) · [Type System Basics](../../01_foundation/02_type_system/01_type_system.md)
> **定理链**: N/A — 描述性/跟踪性文档，不涉及形式化定理链
---

> **来源**: [RFC 3681 — Default Field Values](https://rust-lang.github.io/rfcs/3681-default-field-values.html) ·
> [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html) ·
> [Rust Reference — Struct Expressions](https://doc.rust-lang.org/reference/expressions/struct-expr.html)
> **国际权威来源（2026-07-13 补录）**: **P1** [Weiss et al. — Oxide: The Essence of Rust（arXiv:1903.00982）](https://arxiv.org/abs/1903.00982)（结构体构造语义的核心演算参照；curl 200 实测 2026-07-13） · **P2** [smart-default docs](https://docs.rs/smart-default)（生态中字段默认值 derive 的现行方案；curl 200 实测）

## 📑 目录

- [Default Field Values 预研：结构体字段默认值](#default-field-values-预研结构体字段默认值)
  - [📑 目录](#-目录)
  - [一、动机与语法](#一动机与语法)
  - [二、语义规则](#二语义规则)
  - [三、实测示例（nightly 1.99.0）](#三实测示例nightly-1990)
  - [四、与既有机制的交互](#四与既有机制的交互)
  - [五、反命题与边界分析](#五反命题与边界分析)
  - [权威来源索引](#权威来源索引)
  - [⚠️ 反例与陷阱：结构体字段默认值语法（未稳定）](#️-反例与陷阱结构体字段默认值语法未稳定)

## 一、动机与语法

当前 Rust 中"带默认值的构造"只有两条路：实现 `Default` trait（全结构体级默认），或手写 builder。两者都无法表达"**部分字段有默认、其余必填**"这一高频模式（配置结构体尤甚）。

RFC 3681 允许在结构体定义处直接声明字段默认值：

```rust,ignore
#![feature(default_field_values)]
struct Config {
    name: String,          // 必填
    retries: u32 = 3,      // 默认值
    timeout_ms: u64 = 1000,
}
```

带默认值的字段在构造表达式中可经 `..` 函数式记录更新省略：`Config { name: "svc".into(), .. }`。

## 二、语义规则

RFC 3681 的核心规则（§Reference-level explanation）：

1. **默认值表达式位置**：出现在字段类型之后，经 `=` 引入；须为 const 可求值上下文受限的普通表达式（每次构造时求值，非 `const` 单例）。
2. **`..` 基数省略**：`Struct { .. }`（无基数表达式）仅在**所有省略字段都有默认值**时合法；有默认值的字段可被省略，无默认值的字段必须显式给出。
3. **与 `..base` 的交互**：`..base` 形式中，已声明默认值的字段优先取 `base` 的对应字段值（FRU 语义不变）；`..`（无 base）形式则取声明的默认值。
4. **私有性**：默认值声明不改变字段可见性规则；含私有必填字段的结构体仍不能在模块外构造（参见 [Visibility and Privacy](../../03_advanced/06_low_level_patterns/10_visibility_and_privacy.md)）。
5. **`#[derive(Default)]` 演进**：RFC 预留了让 derive 生成的 `Default::default()` 复用字段默认值的路径，减少"默认值写两遍"。

## 三、实测示例（nightly 1.99.0）

以下示例在 `rustc 1.99.0-nightly (375b1431b 2026-07-10) --edition 2024` 实测编译通过：

```rust,ignore
// rust-toolchain: nightly；#![feature(default_field_values)]
#![feature(default_field_values)]

#[derive(Default)]
struct Config {
    name: String,
    retries: u32 = 3,
    timeout_ms: u64 = 1000,
}

fn main() {
    // 仅给出必填字段，其余取声明默认值
    let c = Config { name: "svc".into(), ..Default::default() };
    assert_eq!(c.retries, 3);
    assert_eq!(c.timeout_ms, 1000);
}
```

## 四、与既有机制的交互

| 机制 | 交互 |
|:---|:---|
| `Default` trait | 字段默认值 ≠ `Default::default()`；前者是构造语法糖，后者是 trait 方法。两者共存时以显式构造表达式为准 |
| Builder 模式 | 字段默认值覆盖 builder 的 80% 简单场景；类型状态 builder（Typestate）仍不可替代（编译期必填校验） |
| FRU（`..base`） | 语义不变；`..`（无 base）是新形式，要求省略字段全有默认值 |
| 模式匹配 | 默认值只作用于构造，不影响解构；`let Config { retries, .. } = c;` 照旧 |
| const 上下文 | 带默认值的结构体字面量可用于 `const`，前提是默认值表达式本身 const 兼容 |

## 五、反命题与边界分析

- **反命题 1：「字段默认值让 Default trait 过时」**——错误。`Default` 是**类型级**协议（泛型边界 `T: Default` 可用），字段默认值是**构造点**语法；泛型代码仍依赖 trait。
- **反命题 2：「默认值在编译期求值一次」**——错误。默认值表达式在**每次构造时**求值（否则 `String::new()` 之类将无法共享）。这一点与 Python 的默认参数陷阱形成对比。
- **边界**：默认值声明是 API 契约的一部分——变更默认值是 semver 兼容性行为变更，与变更 `Default` 实现同等敏感（参见 [Cargo Registries 与发布](../../06_ecosystem/01_cargo/08_cargo_registries_and_publishing.md) 的 SemVer 讨论）。

## 权威来源索引

> **权威来源**: [RFC 3681 — Default Field Values](https://rust-lang.github.io/rfcs/3681-default-field-values.html) ·
> [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html) ·
> [Rust Reference — Struct Expressions](https://doc.rust-lang.org/reference/expressions/struct-expr.html) ·
> [TRPL — Using Structs](https://doc.rust-lang.org/book/ch05-01-defining-structs.html)
>
> 以上链接于 2026-07-12 经 curl 实测全部返回 HTTP 200；代码示例经 `rustc 1.99.0-nightly --edition 2024` 实测编译通过。

---

## ⚠️ 反例与陷阱：结构体字段默认值语法（未稳定）

**反例**（rustc 1.97 实测编译失败，无错误码，解析错误））：

```rust,compile_fail
struct Config {
    retries: u32 = 3,
    timeout: u32 = 30,
}
fn main() { let _ = Config { retries: 1, .. }; }
```

字段默认值（default field values）仍是 `default_field_values` 未稳定特性；stable 1.97 上 `字段: 类型 = 值` 直接解析失败，`..` 语法亦不可用。

**修正**：

```rust
#[derive(Default)]
struct Config {
    retries: u32,
    timeout: u32,
}
fn main() { let _ = Config { retries: 1, ..Default::default() }; }
```
