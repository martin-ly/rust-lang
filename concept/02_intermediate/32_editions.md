# Rust Editions（语言版本）

> **EN**: Rust Editions
> **Summary**: Rust Edition 机制：2015、2018、2021、2024 各版本的关键差异、版本选择规则、迁移工具 `cargo fix`，以及 edition 与工具链版本的关系。
>
> **受众**: [进阶]
> **内容分级**: [参考级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Toolchain](../06_ecosystem/01_toolchain.md) · [Cargo Getting Started](../06_ecosystem/80_cargo_getting_started.md) · [Module System](10_module_system.md)
> **后置概念**: [Async Advanced](../03_advanced/25_async_advanced.md) · [Cargo 1.96 Features](../06_ecosystem/76_cargo_196_features.md) · [Rust Release Process](33_rust_release_process.md)
> **定理链**: Compiler Version → Edition → Syntax/Behavior → Migration
>
> **来源**: [The Rust Programming Language — Appendix E: Editions](https://doc.rust-lang.org/book/appendix-05-editions.html) · [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

---

## 一、什么是 Edition

**Edition** 是 Rust 语言在保持向后兼容的前提下引入非兼容性语法/语义变更的机制。每个 crate 可独立选择 edition，同一编译单元内可混用不同 edition 的依赖。

## 二、主要 Edition

| Edition | 年份 | 主要变化 |
|:---|:---:|:---|
| 2015 | 1.0 | 初始版本 |
| 2018 | 1.31 | module system 简化、`async`/await 语法准备、NLL、 dyn Trait 必须显式 |
| 2021 | 1.56 | prelude 新增、`IntoIterator` for arrays、panic 宏一致性、reserving syntax |
| 2024 | 1.85+ | temp scope 收窄、unsafe extern blocks、gen blocks、match ergonomics 改进 |

## 三、选择 Edition

在 `Cargo.toml` 中声明：

```toml
[package]
edition = "2024"
```

- 新推荐使用最新稳定 edition。
- 依赖 crate 的 edition 不影响当前 crate 的编译。

## 四、迁移

```bash
# 自动应用 edition 迁移
cargo fix --edition
```

迁移工具会：

1. 扫描需要调整的代码。
2. 应用机械式重写。
3. 对无法自动处理的部分给出警告。

## 五、与工具链版本的关系

- Edition 不是工具链版本；一个 `rustc` 版本可编译多个 edition。
- 新 edition 随新工具链版本启用。
- `rust-version` 字段声明最低工具链版本，与 edition 是不同维度的约束。

---

> **权威来源**: [TRPL — Appendix E](https://doc.rust-lang.org/book/appendix-05-editions.html) · [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)
> **内容分级**: [参考级]
