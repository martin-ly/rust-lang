# 类型系统使用指南 {#类型系统使用指南}

> **EN**: Type System Usage Guide
> **Summary**: Learning entry stub for the Rust type system; full explanation lives in the `concept/` authority page.
> **分级**: [A]
> **Bloom 层级**: L3-L4
>
> **受众**: [进阶]
> **内容分级**: [专家级]
> **状态**: ✅ 已按 AGENTS.md §3.4 规范化为重定向 stub
>
> **权威来源**: 本文件为 `docs/` 使用指南入口 stub，通用 Rust 概念解释请见：
> [`concept/01_foundation/02_type_system/01_type_system.md`](../../concept/01_foundation/02_type_system/01_type_system.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> `docs/` 仅保留使用入口、速查与链接，不重复概念推导。

## 速查要点

- Rust 拥有静态、强类型系统，编译期捕获类型错误。
- 基础类型包括标量（整数、浮点、布尔、字符）与复合类型（元组、数组、切片）。
- 自定义类型通过 `struct` 与 `enum` 定义；`Option<T>` 与 `Result<T, E>` 是标准库中的核心枚举。
- 泛型与 trait 实现零成本抽象；`where` 子句用于组织复杂约束。
- 型变（Variance）决定带有生命周期或泛型参数的复合类型之间的子类型关系。
- 相关 crates 示例见 [`crates/c02_type_system`](../../crates/c02_type_system/)。

## 相关权威页

| 主题 | 权威来源 |
| :--- | :--- |
| 类型系统基础 | [`concept/01_foundation/02_type_system/01_type_system.md`](../../concept/01_foundation/02_type_system/01_type_system.md) |
| 数值类型 | [`concept/01_foundation/02_type_system/03_numerics.md`](../../concept/01_foundation/02_type_system/03_numerics.md) |
| 泛型 | [`concept/02_intermediate/01_generics/01_generics.md`](../../concept/02_intermediate/01_generics/01_generics.md) |
| Trait | [`concept/02_intermediate/00_traits/01_traits.md`](../../concept/02_intermediate/00_traits/01_traits.md) |
| 模式匹配 | [`concept/01_foundation/04_control_flow/02_patterns.md`](../../concept/01_foundation/04_control_flow/02_patterns.md) |
| 高级类型 | [`concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md`](../../concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md) |
| 形式化视角 | [`concept/04_formal/00_type_theory/09_type_system_reference.md`](../../concept/04_formal/00_type_theory/09_type_system_reference.md) |

---

## 权威来源（References · 国际权威对齐）

> 仅追加来源链接以闭合权威覆盖，不改本文正文；通用概念请以 `concept/` 权威页为准（AGENTS.md §2）。

- **P0 官方 — TRPL Ch4 Understanding Ownership**: <https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html>
- **P0 官方 — TRPL Ch10 Generic Types, Traits, and Lifetimes**: <https://doc.rust-lang.org/book/ch10-00-generic-types-traits-and-lifetimes.html>
- **P0 Reference — Types**: <https://doc.rust-lang.org/reference/types.html>
- **P0 RFCs**: <https://rust-lang.github.io/rfcs/>
