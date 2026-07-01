# Rust 2024 Edition (1.85.0+ stable)

> **内容重叠提示**: 本文与 [`knowledge/06_ecosystem/02_edition_2024.md`](../../knowledge/06_ecosystem/02_edition_2024.md) 内容高度重叠。`knowledge/` 版本提供专项深入；`concept/` 版本为项目权威主轨。
> **EN**: Rust 2024 Edition Preview and Migration Notes
> **Summary**: Rust 2024 Edition, stabilized in Rust 1.85.0, introduces language improvements including the reserved `gen` keyword, async closures, never type fallback, lifetime capture in `impl Trait`, and narrowed `if let` temporary scopes. This concept previews the major changes, explains how the edition mechanism lets crates opt into new syntax without breaking dependencies, and provides migration guidance using `cargo fix --edition` from the 2021 Edition.
>
> **受众**: [进阶]
> **层级**: L3 高级概念
> **A/S/P 标记**: A+S — Application + Structure
> **双维定位**: C×App — 应用 Edition 机制
> **前置概念**: [Rust Version Tracking](05_rust_version_tracking.md) · [Async](../03_advanced/02_async.md) · [Generics](../02_intermediate/02_generics.md)
> **后置概念**: [Edition Guide](22_edition_guide.md) · [Rust Edition Mechanism](23_rust_edition_guide.md) · [Evolution](03_evolution.md)
> **主要来源**: [Rust Edition Guide — 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) · [RFC 3501 — Edition 2024](https://rust-lang.github.io/rfcs/3501-edition-2024.html) · [TRPL — Appendix: Rust Editions](https://doc.rust-lang.org/book/appendix-05-editions.html)

---

## 一、核心命题

> **Rust 2024 Edition 在 1.85.0 中稳定，它在保持与 2015/2018/2021 Edition 互操作的前提下，通过 crate 级别的 `edition = "2024"` 引入了一组精心挑选的语法和语义改进。**

---

## 二、主要特性预览

| 特性 | 说明 | 状态 |
|:---|:---|:---:|
| `gen` 关键字保留 | `gen` 成为保留关键字，为未来的 `gen {}` 块做准备 | stable |
| Async closures | `async |x| { ... }` 闭包语法 | stable |
| Never type fallback | `!` 类型的默认回退调整为 `!` 本身 | stable |
| Lifetime capture in RPIT | `impl Trait` 生命周期捕获规则更精确 | stable |
| `if let` 临时作用域收窄 | 临时值在 `if let` 条件中的生命周期缩短 | stable |

> **注意**: `gen {}` 块和 `gen fn` 目前仍是 nightly-only 特性（`feature(gen_blocks)`），不在 2024 Edition stable 范围内。

---

## 三、迁移策略

从 2021 Edition 迁移到 2024 Edition 的推荐流程：

```bash
# 1. 确保当前代码在最新 stable 上编译通过
rustup update stable

# 2. 使用 cargo fix 自动应用 Edition 迁移
cargo fix --edition

# 3. 手动检查 cargo fix 无法自动处理的变更
# 4. 更新 Cargo.toml 中的 edition 字段
# edition = "2024"
```

---

## 四、权威来源

- [Rust Edition Guide — 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)
- [RFC 3501 — Edition 2024](https://rust-lang.github.io/rfcs/3501-edition-2024.html)
- [TRPL — Appendix: Rust Editions](https://doc.rust-lang.org/book/appendix-05-editions.html)
- [Rust 1.85.0 Release Notes](https://releases.rs/1.85.0)

---

> **Checklist**: 已提供 Rust 2024 Edition 核心特性预览 / 说明 Edition 机制 / 给出迁移命令 / 引用官方 Edition Guide 与 RFC。
