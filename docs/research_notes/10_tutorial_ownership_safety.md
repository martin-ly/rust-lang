# 教程：所有权与内存安全

**EN**: Tutorial Ownership Safety
**Summary**: Learning entry stub for Rust ownership and memory safety; full explanation lives in the `concept/` authority page.

> **权威来源**: 本文件为学习入口 stub，完整概念解释请见：
> [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> 本文件仅保留摘要、速查与链接。

## 速查要点

- Rust 通过**所有权**在编译期保证内存安全，无需垃圾回收器。
- 所有权三规则：每个值有唯一所有者；同一时间只能有一个所有者；所有者离开作用域时值被丢弃。
- 赋值与传参默认发生**移动（Move）**，原变量失效，避免双重释放。
- 实现 `Copy` trait 的类型按位复制，移动后仍可继续使用原变量。
- 借用（`&T` / `&mut T`）允许临时访问而不转移所有权。

## 相关权威页

| 主题 | 权威来源 |
| :--- | :--- |
| 所有权基础 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) |
| 移动语义 | [`concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md) |
| 借用 | [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| 生命周期 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| 形式化视角 | [`concept/04_formal/01_ownership_logic/03_ownership_formal.md`](../../concept/04_formal/01_ownership_logic/03_ownership_formal.md) |
