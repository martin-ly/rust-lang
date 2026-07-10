# 教程：类型系统

**EN**: Tutorial Type System
**Summary**: Learning entry stub for the Rust type system; full explanation lives in the `concept/` authority page.

> **权威来源**: 本文件为学习入口 stub，完整概念解释请见：
> [`concept/01_foundation/02_type_system/04_type_system.md`](../../concept/01_foundation/02_type_system/04_type_system.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> 本文件仅保留摘要、速查与链接。

## 速查要点

- Rust 拥有静态、强类型系统，编译期捕获类型错误。
- 基础类型包括标量（整数、浮点、布尔、字符）与复合类型（元组、数组、切片）。
- 自定义类型通过 `struct` 与 `enum` 定义；`Option<T>` 与 `Result<T, E>` 是标准库中的核心枚举。
- `match`、`if let`、匹配守卫与 `@` 绑定提供灵活的模式匹配。
- 泛型与 trait 实现零成本抽象；`where` 子句用于组织复杂约束。

## 相关权威页

| 主题 | 权威来源 |
| :--- | :--- |
| 类型系统基础 | [`concept/01_foundation/02_type_system/04_type_system.md`](../../concept/01_foundation/02_type_system/04_type_system.md) |
| 数值类型 | [`concept/01_foundation/02_type_system/10_numerics.md`](../../concept/01_foundation/02_type_system/10_numerics.md) |
| 泛型 | [`concept/02_intermediate/01_generics/02_generics.md`](../../concept/02_intermediate/01_generics/02_generics.md) |
| Trait | [`concept/02_intermediate/00_traits/01_traits.md`](../../concept/02_intermediate/00_traits/01_traits.md) |
| 模式匹配 | [`concept/01_foundation/04_control_flow/40_patterns.md`](../../concept/01_foundation/04_control_flow/40_patterns.md) |
| 高级类型 | [`concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md`](../../concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md) |
| 形式化视角 | [`concept/04_formal/00_type_theory/50_type_system_reference.md`](../../concept/04_formal/00_type_theory/50_type_system_reference.md) |
