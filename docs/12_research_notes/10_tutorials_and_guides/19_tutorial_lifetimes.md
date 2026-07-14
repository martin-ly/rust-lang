# 教程：理解生命周期

**EN**: Tutorial Lifetimes
**Summary**: Learning entry stub for Rust lifetimes; full explanation lives in the `concept/` authority page.

> **权威来源**: 本文件为学习入口 stub，完整概念解释请见：
> [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)
>
> 根据 [AGENTS.md](../../../AGENTS.md) §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> 本文件仅保留摘要、速查与链接。

## 速查要点

- 生命周期是编译期对引用有效范围的标注，核心规则：**引用不能比它指向的数据活得更长**。
- 函数签名中可显式标注生命周期，如 `fn longest<'a>(x: &'a str, y: &'a str) -> &'a str`。
- 生命周期省略规则覆盖大多数常见场景，减少样板代码。
- `'static` 表示整个程序运行期间有效；字符串字面量即具有 `'static` 生命周期。
- 高阶 trait bound（HRTB）如 `for<'a> Fn(&'a str)` 用于处理任意生命周期的回调类型。

## 相关权威页

| 主题 | 权威来源 |
| :--- | :--- |
| 生命周期基础 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| 高级生命周期 | [`concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md`](../../../concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) |
| 借用 | [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| 所有权 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) |
| 形式化视角 | [`concept/04_formal/01_ownership_logic/02_ownership_formal.md`](../../../concept/04_formal/01_ownership_logic/02_ownership_formal.md) |

---

## 权威来源（References · 国际权威对齐）

> 仅追加来源链接以闭合权威覆盖，不改本文正文；通用概念请以 `concept/` 权威页为准（AGENTS.md §2）。

- **P0 官方 — TRPL Ch4 Ownership**: <https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html>
- **P0 官方 — TRPL Ch10 Lifetimes**: <https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html>
- **P0 Reference**: <https://doc.rust-lang.org/reference/>
- **P0 Nomicon**: <https://doc.rust-lang.org/nomicon/>
- **P1 RustBelt / Stacked & Tree Borrows (Jung et al.)**: <https://plv.mpi-sws.org/rustbelt/>
