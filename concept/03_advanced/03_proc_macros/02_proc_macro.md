# 过程宏：编译期代码生成的元编程工具

> **EN**: Procedural Macros
> **Summary**: Redirect stub for procedural macros; full coverage now lives at the canonical L3-L4 page.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件已转为重定向 stub。过程宏的完整概念解释已迁移至 `concept/` 唯一权威页：
> [`concept/02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md`](../../02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md)
>
> 根据 AGENTS.md §2 Canonical 规则，通用 Rust 概念解释统一维护在上述权威页；本页仅保留导航入口。

## ⚠️ 实测反例（按 Canonical 规则指向权威页）

本页为重定向 stub，不重复 canonical 代码。过程宏边界的本机实测反例见权威页：

- [05_procedural_macros.md §10.5 实测反例：proc-macro crate 类型约束与卫生性边界（rustc 1.99.0 实编译）](../../02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md) — 权威页含 2 个 `rust,compile_fail` 围栏：`#[proc_macro]` 出现在非 proc-macro crate、proc-macro crate 导出非宏条目等编译期约束，均经本机 rustc 实编译验证。
