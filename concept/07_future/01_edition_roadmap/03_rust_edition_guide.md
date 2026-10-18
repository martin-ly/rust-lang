# Rust Edition 机制与迁移指南

> **Summary**: Redirect stub for Rust Edition mechanism and migration guide; authoritative content is in 44_edition_guide.md.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **EN**: Rust Edition Mechanism and Migration Guide
> **受众**: [研究者]
> **Bloom 层级**: L2-L3
> **内容分级**: [研究者级]
> **权威来源**: 本文件为 `concept/` 权威页。
> **前置概念**: [Rust Edition Guide](02_edition_guide.md)
> **后置概念**: [Rust Edition Guide](02_edition_guide.md)
> **主要来源**: [Rust Edition Guide](02_edition_guide.md) · [TRPL — Appendix E](https://doc.rust-lang.org/book/appendix-05-editions.html) · [RFC 2052 — Epochs](https://rust-lang.github.io/rfcs/2052-epochs.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) · [Rust Blog — Rust 1.82.0](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0.html) · [crates.io — cargo](https://crates.io/crates/cargo)

> **注意**: 本主题内容已整合到 `concept/07_future/44_edition_guide.md`。
> 请以 [concept/07_future/44_edition_guide.md](02_edition_guide.md) 为权威来源。

## ⚠️ 实测反例：本页为索引页，完整实测见 canonical

完整实测反例节见 canonical：[02_edition_guide.md §实测反例（rustc 1.99.1 双 edition 实编译，2026-10-19）](02_edition_guide.md)。

口径摘要（本页保留最小可机检证据）：同一源码 `fn gen() -> i32 { 1 }` 在 rustc 1.99.1 下 `--edition 2021` EXIT=0、`--edition 2024` 硬拒：

```rust,compile_fail
// rustc 1.99.1 --edition 2024（--edition 2021 下同一代码编译通过）
fn gen() -> i32 { 1 }
fn main() { println!("{}", gen()); }
```

```text
error: expected identifier, found reserved keyword `gen`
help: escape `gen` to use it as an identifier: fn r#gen() -> i32 { 1 }
```

---

**历史内容已迁移**：本文件不再维护，请点击上方链接查看最新内容。
