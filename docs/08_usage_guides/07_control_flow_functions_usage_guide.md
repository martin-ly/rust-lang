# 控制流与函数使用指南 {#控制流与函数使用指南}

> **EN**: Control Flow Functions Usage Guide
> **Summary**: Learning entry stub for Rust control flow and functions; full explanation lives in the `concept/` authority page.
> **分级**: [A]
> **Bloom 层级**: L3-L4
>
> **受众**: [进阶]
> **内容分级**: [专家级]
> **状态**: ✅ 已按 AGENTS.md §3.4 规范化为重定向 stub
>
> **权威来源**: 本文件为 `docs/` 使用指南入口 stub，通用 Rust 概念解释请见：
> [`concept/01_foundation/04_control_flow/01_control_flow.md`](../../concept/01_foundation/04_control_flow/01_control_flow.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> `docs/` 仅保留使用入口、速查与链接，不重复概念推导。

## 速查要点

- Rust 控制流包括 `if`/`else`、`match`、循环（`loop`/`while`/`for`）以及 `break`/`continue` 标签。
- 函数支持参数、返回值、泛型与 `where` 约束；返回表达式末尾可省略 `return`。
- 闭包（Closure）使用 `|args| body` 语法，可捕获环境变量并自动推导 trait（`Fn`/`FnMut`/`FnOnce`）。
- 模式匹配覆盖 `match`、`if let`、`while let`、解构与守卫（guard）。
- 相关 crates 示例见 [`crates/c03_control_fn`](../../crates/c03_control_fn/)。

## 相关权威页

| 主题 | 权威来源 |
| :--- | :--- |
| 控制流基础 | [`concept/01_foundation/04_control_flow/01_control_flow.md`](../../concept/01_foundation/04_control_flow/01_control_flow.md) |
| 模式匹配 | [`concept/01_foundation/04_control_flow/02_patterns.md`](../../concept/01_foundation/04_control_flow/02_patterns.md) |
| 函数与闭包 | [`concept/01_foundation/05_functions/01_functions.md`](../../concept/01_foundation/07_modules_and_items/02_functions.md) |
| 错误处理 | [`concept/02_intermediate/03_error_handling/01_error_handling.md`](../../concept/02_intermediate/03_error_handling/01_error_handling.md) |
| 迭代器 | [`concept/02_intermediate/05_iterator/01_iterator.md`](../../concept/02_intermediate/07_iterators_and_closures/01_iterator_patterns.md) |

---

## 权威来源（References · 国际权威对齐）

> 仅追加来源链接以闭合权威覆盖，不改本文正文；通用概念请以 `concept/` 权威页为准（AGENTS.md §2）。

- **P0 官方 — TRPL Ch3 Common Programming Concepts**: <https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html>
- **P0 官方 — TRPL Ch18 Patterns and Matching**: <https://doc.rust-lang.org/book/ch18-00-patterns.html>
- **P0 Reference**: <https://doc.rust-lang.org/reference/>
