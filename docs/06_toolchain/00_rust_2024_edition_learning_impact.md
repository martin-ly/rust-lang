# Rust 2024 Edition 学习影响

> **创建日期**: 2026-02-14
> **Rust 2024 Edition**: 2025-02 随 Rust 1.85.0 稳定发布
> **权威来源**: [Rust Blog - Rust 2024](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/)

---

## 一、Rust 2024 Edition 概览

Rust 2024 Edition 是 Rust 迄今为止**最大的 Edition 更新**，于 2025 年 2 月 20 日随 Rust 1.85.0 稳定发布。本项目已全面采用 `edition = "2024"`（根 Cargo.toml 及 12 个 crate）。

---

## 二、对学习路径的主要影响

### 2.1 所有权与借用（C01）

| 变更 | 影响 | 学习建议 |
|------|------|----------|
| **`unsafe_op_in_unsafe_fn` 默认启用** | 在 `unsafe fn` 内必须显式标记 `unsafe` 块 | 学习 Unsafe Rust 时注意新规则 |
| **禁止 `static mut` 引用** | 旧代码中 `&static mut` 将报错 | 使用 `Sync` 类型或 `UnsafeCell` 替代 |

### 2.2 类型系统（C02）

| 变更 | 影响 | 学习建议 |
|------|------|----------|
| **RPIT 生命周期捕获规则** | 返回的 impl Trait 可能捕获更多生命周期 | 理解 RPIT 与生命周期的交互 |
| **Never 类型 (`!`) fallback 变更** | `!` 在类型推断中的行为更一致 | 关注 `panic!`、`loop` 等表达式的类型 |

### 2.3 控制流（C03）

| 变更 | 影响 | 学习建议 |
|------|------|----------|
| **`if let` 与尾表达式临时作用域** | 临时值在 `if let` 分支中的存活期变更 | 注意 `if let Some(x) = foo().lock()` 等模式 |
| **Match ergonomics 保留** | 部分 match 模式匹配行为调整 | 参考 [Edition Guide](https://doc.rust-lang.org/edition-guide/) |

### 2.4 宏系统（C11）

| 变更 | 影响 | 学习建议 |
|------|------|----------|
| **宏片段说明符更新** | 部分宏模式语法扩展 | 编写声明宏时查阅 2024 变更 |
| **`unsafe` 属性** | `unsafe` 可作为属性使用 | 与 `unsafe fn` 配合理解 |

### 2.5 其他

| 变更 | 影响 |
|------|------|
| **Unsafe `extern` 块** | FFI 中 `extern` 块可标记 `unsafe` |
| **`cfg` 谓词关键词** | 使用关键词作为 `cfg` 谓词将报错 |

---

## 三、学习建议

1. **初学者**：按 C01→C02→C03 顺序学习，2024 变更对基础语法影响较小。
2. **进阶者**：重点理解 RPIT 生命周期、`unsafe_op_in_unsafe_fn`、`if let` 临时作用域。
3. **迁移者**：若从 2021 Edition 迁移，参考 [Edition Guide - Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/)。

---

## 四、相关文档

- [Rust 1.93 vs 1.92 对比](./05_rust_1.93_vs_1.92_comparison.md)
- [Rust 1.93 兼容性深度解析](./09_rust_1.93_compatibility_deep_dive.md)
- [Unsafe Rust 指南](../05_guides/UNSAFE_RUST_GUIDE.md)
- [官方 Edition Guide](https://doc.rust-lang.org/edition-guide/)

---

**最后对照 releases.rs**: 2026-02-14
