# Inline Const Pattern 预览（Rust 1.98+ Nightly）

> **代码状态**: [已验证（rustc 1.97）] — 代码块经 rustc 1.97.0 `--edition 2024` 单文件编译验证（2026-07-12）
>
> **EN**: Inline Const Pattern Preview
> **Summary**: Preview of inline const patterns (`const { expr }` in match arms), extending stable inline const expressions into pattern matching contexts; nightly experimental.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: 🧪 Nightly 实验性
> **Rust 属性标记**: `#[experimental]` `#[nightly_only]`
> **跟踪版本**: nightly 1.98.0 (2026-05-31)
> **预计稳定**: 待定（需等待 RFC / MCP 完成）
>
> **受众**: [专家]
> **内容分级**: [实验级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: F×App — 应用 const 块于模式匹配（Pattern Matching）
> **前置依赖**: [Const Generics](../../02_intermediate/01_generics/01_generics.md) · [Pattern Matching](../../01_foundation/04_control_flow/01_control_flow.md) · [Patterns](../../01_foundation/04_control_flow/02_patterns.md) · [Const Items and Const Fn](../../01_foundation/07_modules_and_items/09_const_items_and_const_fn.md)
> **后置延伸**: [Const Trait](19_const_trait_preview.md)
> **来源**: [Rust Reference — Patterns](https://doc.rust-lang.org/reference/patterns.html) · [RFC 2920 — Inline Const](https://rust-lang.github.io/rfcs/2920-inline-const.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>

## 一、功能动机：为什么需要 Inline Const Pattern？

稳定 Rust 已经支持 **inline const 表达式**（自 1.79.0 起），允许在需要 const 值的位置直接写 `const { expr }`：

```rust,editable
fn main() {
    let arr: [u8; const { 2 + 2 }] = [0; 4];
    assert_eq!(arr.len(), 4);
}
```

然而，稳定 Rust 目前**不允许**在模式匹配（pattern matching）的 match arm 中直接使用 inline const。例如：

```rust,ignore
match x {
    const { 1 + 1 } => ...,   // 稳定 Rust 不支持
}
```

这导致开发者必须在外部定义一个命名常量，增加了样板代码，也削弱了 `match` 表达局部计算的能力。Inline Const Pattern 的目标就是将 inline const 扩展到 pattern 位置，让常量表达式可以直接参与模式匹配（Pattern Matching）。

---

## 二、语法说明

「语法说明」涉及稳定基础：Inline Const 表达式（Rust 1.79+）、未来语法：Inline Const in Patterns与适用场景，本节逐一说明其要点。

### 2.1 稳定基础：Inline Const 表达式（Rust 1.79+）

```rust,editable
const fn compute_threshold(base: i32) -> i32 {
    base * 2 + 10
}

fn main() {
    let arr: [u8; const { compute_threshold(5) as usize }] = [0; 20];
    assert_eq!(arr.len(), 20);
}
```

### 2.2 未来语法：Inline Const in Patterns

```rust,ignore
#![feature(inline_const_pat)]

fn classify(x: u32) -> &'static str {
    match x {
        const { 1 << 0 } => "bit 0",
        const { 1 << 1 } => "bit 1",
        const { 1 << 2 } => "bit 2",
        const { 1 << 3 } => "bit 3",
        _ => "other",
    }
}
```

### 2.3 适用场景

1. **位掩码匹配**：`const { FLAG_A | FLAG_B }`；
2. **派生常量**：从其他 const 计算得出，无需单独命名；
3. **const generics 与值匹配结合**：将类型级计算结果用于值级模式。

---

## 三、与稳定 Rust 的对比及迁移建议

| 场景 | 稳定 Rust（1.79+） | Nightly + inline const pat |
|:---|:---|:---|
| 数组长度 const 计算 | `let a: [T; const { N }]` | 同上 |
| match arm 中直接使用计算常量 | ❌ 必须定义命名 `const` | ✅ `const { expr }` |
| 复杂位运算匹配 | 代码可读性较低 | 计算逻辑直接内联 |
| 版本门槛 | 稳定可用 | nightly only |

### 3.1 当前替代写法

```rust,editable
const BIT_0: u32 = 1 << 0;
const BIT_1: u32 = 1 << 1;
const BIT_2: u32 = 1 << 2;

fn classify(x: u32) -> &'static str {
    match x {
        BIT_0 => "bit 0",
        BIT_1 => "bit 1",
        BIT_2 => "bit 2",
        _ => "other",
    }
}

fn main() {
    assert_eq!(classify(2), "bit 1");
}
```

### 3.2 迁移建议

1. **稳定生产代码仍使用命名 `const`**：这是当前唯一可靠的方式；
2. **内部工具或 nightly 实验项目可尝试 `inline_const_pat`**：注意 feature gate 可能在稳定前变化；
3. **避免在模式中写复杂逻辑**：即使语法支持，过于复杂的 inline const 也会降低可读性；
4. **关注 `match` 穷尽性检查**：inline const pattern 必须能被编译器正确求值，否则会影响模式覆盖分析。

> **版本说明**：Inline const 表达式自 Rust 1.79.0 起稳定；inline const **in patterns** 目前仍是 nightly 实验特性，没有明确的稳定时间表。

---

## 四、边界测试：`const {}` 块在 pattern 中的使用（编译错误/未来特性）

```rust,ignore
fn main() {
    let x = 42;
    match x {
        // ❌ 编译错误: 当前稳定 Rust 不支持 const 块 in pattern
        // const { 40 + 2 } => println!("forty-two"),
        _ => println!("other"),
    }

    // 正确: 使用字面量或 const item
    const ANSWER: i32 = 42;
    match x {
        ANSWER => println!("forty-two"),
        _ => println!("other"),
    }
}
```

> **修正**: **Inline const patterns**（`const { expr }` in patterns）允许在 match arm 中直接写常量表达式：
>
> 1) `match x { const { 1 + 1 } => ... }` — 编译期计算；
> 2) 避免定义单独的 `const` item；
> 3) 适用于复杂常量（如位运算、数组长度）。
>
> 相关特性：
>
> 1) **Inline const**（稳定于 1.79）：`let x: [u8; const { 1 + 1 }] = [0; 2]`；
> 2) **Const blocks in patterns**（开发中）：将 inline const 扩展到 pattern 位置。
>
> 使用场景：
>
> 1) 复杂的 match 条件；
> 2) 从其他常量派生的常量；
> 3) 类型级计算的结果用于值级匹配。
>
> 这与 C++ 的 `constexpr`（可在编译期计算，但不支持在 switch case 中使用复杂表达式）或 C 的 `case`（仅支持整型常量表达式）不同——Rust 的 `const {}` 更灵活，支持任意编译期可计算的 Rust 代码。
> [来源: [Inline Const RFC](https://rust-lang.github.io/rfcs/2920-inline-const.html)] ·
> [来源: [Const Generics](https://rust-lang.github.io/rfcs/2000-const-generics.html)]
>
> **后置概念**: [Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)
> **前置依赖**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md)
> **前置依赖**: [Toolchain](../../06_ecosystem/00_toolchain/01_toolchain.md)

## ⚠️ 反例与陷阱

**陷阱：在稳定 Rust 的 pattern 位置写内联 const 表达式**。这正是 `inline_const_pat` 要解决的问题——稳定编译器直接拒绝：

```rust,compile_fail
fn classify(n: u8) -> &'static str {
    match n {
        const { 1 + 1 } => "two",
        _ => "other",
    }
}
```

rustc 1.97.0（stable）实测：`error: const blocks cannot be used as patterns`。

**修正（稳定方案）**：提取命名常量，语义完全等价，也是本特性稳定前的推荐迁移写法：

```rust
const TWO: u8 = 1 + 1;
fn classify(n: u8) -> &'static str {
    match n { TWO => "two", _ => "other" }
}
```

## 认知路径

> **认知路径**: 从 Rust 核心语言特性出发，经由 **Inline Const Pattern Preview** 的生态/前沿实践，通向系统化工程能力与未来语言演进方向。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
| :--- | :--- | :--- | :--- |
| Inline Const Pattern Preview 基础原理 ⟹ 正确选型 | 理解核心概念与适用边界 | 能在实际项目中做出合理决策 | 高 |
| Inline Const Pattern Preview 选型实践 ⟹ 常见陷阱 | 忽视版本兼容性与生态成熟度 | 技术债务或迁移成本 | 中 |
| Inline Const Pattern Preview 陷阱规避 ⟹ 深度掌握 | 持续跟踪社区演进与最佳实践 | 能进行架构设计与技术预研 | 高 |

## 嵌入式测验（Embedded Quiz）

本节围绕「嵌入式测验（Embedded Quiz）」展开，依次讨论测验 1：`inline const` 模式是什么？它解决了什么问题？…、测验 2：这个特性对 `match` 的表达能力有什么提升？（理解层）、测验 3：`inline const` 与 `const` 块有什么关…、测验 4：这个特性目前的实现状态如何？（理解层）等5个方面。

### 测验 1：`inline const` 模式是什么？它解决了什么问题？（理解层）

**题目**: `inline const` 模式是什么？它解决了什么问题？

<details>
<summary>✅ 答案与解析</summary>

允许在模式匹配（Pattern Matching）中使用常量表达式，如 `match x { const { 1 + 2 } => ... }`。目前模式中的常量必须是字面量或命名常量。
</details>

> **前置概念**: N/A
---

### 测验 2：这个特性对 `match` 的表达能力有什么提升？（理解层）

**题目**: 这个特性对 `match` 的表达能力有什么提升？

<details>
<summary>✅ 答案与解析</summary>

可以在模式中表达计算得出的常量值，如位掩码检查、数组长度比较等，无需在 match 外预先计算。
</details>

---

### 测验 3：`inline const` 与 `const` 块有什么关系？（理解层）

**题目**: `inline const` 与 `const` 块有什么关系？

<details>
<summary>✅ 答案与解析</summary>

`inline const { expr }` 在模式上下文中创建匿名常量表达式，类似于 `const` 块在表达式上下文中的作用。
</details>

---

### 测验 4：这个特性目前的实现状态如何？（理解层）

**题目**: 这个特性目前的实现状态如何？

<details>
<summary>✅ 答案与解析</summary>

作为 Rust 语言演进的一部分正在讨论中。具体语法和语义仍在 RFC 阶段，预计在未来 1-2 年内稳定化。
</details>

---

### 测验 5：`inline const` 对代码可读性有什么影响？（理解层）

**题目**: `inline const` 对代码可读性有什么影响？

<details>
<summary>✅ 答案与解析</summary>

将常量的计算逻辑直接放在使用位置，减少跳转阅读，但可能使复杂模式更冗长。适合简单计算，复杂逻辑仍应使用命名常量。
</details>

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/hyper — 生态权威 API 文档](https://docs.rs/hyper) · [docs.rs/tokio — 生态权威 API 文档](https://docs.rs/tokio)
