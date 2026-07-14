> **内容分级**: [研究级]
>
# Rust 2024 Edition (1.85.0+ stable)

> **内容重叠提示**: 本文与 [`knowledge/06_ecosystem/02_edition_2024.md`](../../../knowledge/06_ecosystem/02_edition_2024.md) 内容高度重叠。`knowledge/` 版本提供专项深入；`concept/` 版本为项目权威主轨。
> **EN**: Rust 2024 Edition Preview and Migration Notes
> **Summary**: Rust 2024 Edition, stabilized in Rust 1.85.0, introduces language improvements including the reserved `gen` keyword, async closures, never type fallback, lifetime capture in `impl Trait`, and narrowed `if let` temporary scopes. This concept previews the major changes, explains how the edition mechanism lets crates opt into new syntax without breaking dependencies, and provides migration guidance using `cargo fix --edition` from the 2021 Edition.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [进阶]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L3 高级概念
> **A/S/P 标记**: A+S — Application + Structure
> **双维定位**: C×App — 应用 Edition 机制
> **前置概念**: [Rust Version Tracking](../00_version_tracking/01_rust_version_tracking.md) · [Async](../../03_advanced/01_async/01_async.md) · [Generics](../../02_intermediate/01_generics/01_generics.md)
> **后置概念**: [Edition Guide](02_edition_guide.md) · [Rust Edition Mechanism](03_rust_edition_guide.md) · [Evolution](../04_research_and_experimental/03_evolution.md)
> **主要来源**: [Rust Edition Guide — 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) · [RFC 3501 — Edition 2024](https://rust-lang.github.io/rfcs/3501-edition-2024.html) · [TRPL — Appendix: Rust Editions](https://doc.rust-lang.org/book/appendix-05-editions.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

## 一、核心命题

> **Rust 2024 Edition 在 1.85.0 中稳定，它在保持与 2015/2018/2021 Edition 互操作的前提下，通过 crate 级别的 `edition = "2024"` 引入了一组精心挑选的语法和语义改进。**

---

## 二、Edition 机制核心原则

| 原则 | 说明 |
|:---|:---|
| crate 级选择 | `Cargo.toml` 中的 `edition` 字段决定当前 crate 使用的 Edition |
| 依赖隔离 | 依赖的 Edition 与当前 crate 互不影响 |
| 向后兼容 | 旧 Edition 继续被同一编译器支持 |
| 迁移自动化 | `cargo fix --edition` 可自动处理大部分语法变更 |

## 三、主要特性预览

| 特性 | 说明 | 状态 |
|:---|:---|:---:|
| `gen` 关键字保留 | `gen` 成为保留关键字，为未来的 `gen {}` 块做准备 | stable |
| Async closures | `async |x| { ... }` 闭包语法 | stable |
| Never type fallback | `!` 类型的默认回退调整为 `!` 本身 | stable |
| Lifetime capture in RPIT | `impl Trait` 生命周期（Lifetimes）捕获规则更精确 | stable |
| `if let` 临时作用域收窄 | 临时值在 `if let` 条件中的生命周期（Lifetimes）缩短 | stable |
| 尾表达式临时作用域 | 块尾表达式的临时值作用域收窄到语句结束 | stable |
| `Macro` 与 `unsafe` 块优先级 | 宏（Macro）调用不再无条件优先于 `unsafe` 块 | stable |

> **注意**: `gen {}` 块和 `gen fn` 目前仍是 nightly-only 特性（`feature(gen_blocks)`），不在 2024 Edition stable 范围内。

## 四、迁移前后代码对比

本节将「迁移前后代码对比」分解为若干主题： Async closures、`if let` 临时作用域与Never type fallback。

### Async closures

```rust
// 2021 Edition：需要显式 async 块
let f = |x: i32| async move { x + 1 };

// 2024 Edition：async 闭包语法
let f = async |x: i32| x + 1;
```

### `if let` 临时作用域

```rust
// 2021 Edition：临时值生命周期可能延续到 if 块外
if let Some(x) = get_temp().as_ref() { /* ... */ }

// 2024 Edition：临时值在条件求值后立即释放
if let Some(x) = get_temp().as_ref() { /* ... */ }
```

### Never type fallback

```rust
let x = match condition {
    true => return,
    false => 42,
};
// 2024 Edition: x 的类型推断为 i32（更直观）
```

---

## 五、迁移策略

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

## 六、权威来源

- [Rust Edition Guide — 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)
- [RFC 3501 — Edition 2024](https://rust-lang.github.io/rfcs/3501-edition-2024.html)
- [TRPL — Appendix: Rust Editions](https://doc.rust-lang.org/book/appendix-05-editions.html)
- [Rust 1.85.0 Release Notes](https://github.com/rust-lang/rust/releases/tag/1.85.0)

---

> **Checklist**: 已提供 Rust 2024 Edition 核心特性预览 / 说明 Edition 机制 / 给出迁移命令 / 引用（Reference）官方 Edition Guide 与 RFC。

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/hyper — 生态权威 API 文档](https://docs.rs/hyper) · [docs.rs/tokio — 生态权威 API 文档](https://docs.rs/tokio)

---

## ⚠️ 反例与陷阱：Edition 2024 保留字 `gen`

**反例**（rustc 1.97 实测编译失败，无错误码，解析错误））：

```rust,compile_fail
fn main() {
    let gen = 42;
    println!("{gen}");
}
```

Edition 2024 为未来生成器（gen blocks）预留 `gen` 关键字；以 `--edition 2024` 编译时 `let gen` 直接解析失败，升级 edition 前需用 `r#gen` 或改名迁移。

**修正**：

```rust
fn main() {
    let r#gen = 42;
    println!("{}", r#gen);
}
```
