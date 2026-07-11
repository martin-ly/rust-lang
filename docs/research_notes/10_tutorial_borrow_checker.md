# 教程：理解借用检查器

**EN**: Tutorial Borrow Checker
**Summary**: Learning entry stub for Rust's borrow checker; full explanation lives in the `concept/` authority page.

> **权威来源**: 本文件为学习入口 stub，完整概念解释请见：
> [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> 本文件仅保留摘要、速查与链接。

## 速查要点

- 借用检查器在编译期强制执行 **aliasing XOR mutability**：同一作用域内，要么多个不可变借用 `&T`，要么唯一一个可变借用 `&mut T`。
- 引用必须始终有效，禁止悬垂引用与使用已释放内存。
- 非词法生命周期（NLL）让借用的结束点以最后一次使用为准，而非词法作用域边界。
- 内部可变性（`Cell<T>` / `RefCell<T>` / `Mutex<T>` / `RwLock<T>`）将部分检查推迟到运行时。

## 相关权威页

| 主题 | 权威来源 |
| :--- | :--- |
| 借用与引用 | [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| 所有权 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) |
| 生命周期 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| 内部可变性 | [`concept/02_intermediate/02_memory_management/03_memory_management.md`](../../concept/02_intermediate/02_memory_management/03_memory_management.md) |
| 形式化视角 | [`concept/04_formal/01_ownership_logic/03_ownership_formal.md`](../../concept/04_formal/01_ownership_logic/03_ownership_formal.md) |

---

## 权威来源（References · 国际权威对齐）

> 仅追加来源链接以闭合权威覆盖，不改本文正文；通用概念请以 `concept/` 权威页为准（AGENTS.md §2）。

- **P0 官方 — TRPL Ch4 Ownership**: <https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html>
- **P0 官方 — TRPL Ch10 Lifetimes**: <https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html>
- **P0 Reference**: <https://doc.rust-lang.org/reference/>
- **P0 Nomicon**: <https://doc.rust-lang.org/nomicon/>
- **P1 RustBelt / Stacked & Tree Borrows (Jung et al.)**: <https://plv.mpi-sws.org/rustbelt/>
