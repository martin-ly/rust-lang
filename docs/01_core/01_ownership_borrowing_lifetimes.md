> **权威来源**:
>
> [The Rust Programming Language](https://doc.rust-lang.org/book/),
> **分级**: [A]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> [Rust Reference — Ownership](https://doc.rust-lang.org/reference/),
> [Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html),
> [RustBelt (Jung et al., POPL 2018)](https://plv.mpi-sws.org/rustbelt/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 TRPL、Rust Reference、RustBelt 来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)
> **权威来源**: [concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md)

# 所有权、借用与生命周期：学习路径与易错点索引 {#所有权借用与生命周期三位一体的内存安全}

> **EN**: Ownership Borrowing Lifetimes Learning Path
> **Summary**: A learning-path index for ownership, borrowing, and lifetimes. Core explanations are maintained in the `concept/` canonical pages; this guide only lists study order, key pitfalls, and quick references.
> **Bloom 层级**: L1-L2
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **难度**: 初级 → 中级
> **预计学习时间**: 4-6 小时

---

> **权威来源**: 本文件为 `docs/` 学习路径入口，完整概念解释请见：
>
> - [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md)
> - [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)
> - [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)
>
> 根据 AGENTS.md §3.4，通用 Rust 概念解释统一维护在 `concept/` 中；`docs/` 仅保留学习路径、决策树、速查与链接。

## 学习路径 {#学习路径}

| 顺序 | 主题 | 权威页 | 重点 |
|:---:|:---|:---|:---|
| 1 | 所有权 | [`01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | 唯一所有者、Move、Copy、Drop |
| 2 | 借用 | [`02_borrowing.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) | &T / &mut T、别名-可变性规则、悬垂引用 |
| 3 | 生命周期 | [`03_lifetimes.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | 生命周期标注、子类型、NLL |
| 4 | 进阶 | [`30_lifetimes_advanced.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md) | Polonius、Elision、自引用结构 |

## 常见易错点 {#常见易错点}

- **自引用结构体**：无法直接在栈上构造持有自身引用的类型，需使用 `Pin` 或间接层。
- **`static mut` 已废弃**：优先使用 `static` + 内部可变性（如 `Mutex`、`Atomic`）。
- **生命周期过长**：返回值生命周期默认取输入参数最小上界，需显式标注跨函数边界的引用。
- **可变与不可变借用互斥**：同一作用域内不能同时存在 `&mut T` 和 `&T`。

## 代码练习 {#代码练习}

参见对应 crate：

- [`crates/c01_ownership_borrow_scope/`](../../crates/c01_ownership_borrow_scope/)
- [`exercises/rustlings_style/`](../../exercises/rustlings_style/)
