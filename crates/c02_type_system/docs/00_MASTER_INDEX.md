# C02 类型系统 - 主索引

> **学习导航**: C02 类型系统模块的完整学习路径和资源导航
> **最后更新**: 2026-02-12
> **适用版本**: Rust 1.93.0+

---

## 📋 目录

- [C02 类型系统 - 主索引](#c02-类型系统---主索引)
  - [📋 目录](#-目录)
  - [📚 官方资源映射](#-官方资源映射)
  - [🎯 快速开始](#-快速开始)
  - [📚 Tier 1-4 分层导航](#-tier-1-4-分层导航)
  - [📦 Cargo 包管理专题](#-cargo-包管理专题)
  - [🆕 Rust 版本特性](#-rust-版本特性)
  - [💻 代码示例](#-代码示例)
  - [🔗 相关文档](#-相关文档)

---

## 📚 官方资源映射

| 官方资源 | 链接 | 与本模块对应 |
|----------|------|--------------|
| **The Rust Book** | [Ch. 10 Generic Types, Traits, and Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html) | 泛型、Trait、生命周期 |
| **Rust By Example** | [Custom Types](https://doc.rust-lang.org/rust-by-example/custom_types.html) | 结构体、枚举 |
| **Rust Reference** | [Type system](https://doc.rust-lang.org/reference/types.html) | 类型系统规范 |
| **Rustonomicon** | [Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html) | 型变、高级类型 |

**Rust 1.93 兼容性**: [兼容性注意事项](../../../docs/06_toolchain/06_rust_1.93_compatibility_notes.md) | [深度解析](../../../docs/06_toolchain/09_rust_1.93_compatibility_deep_dive.md)

---

## 🎯 快速开始

**🌱 初学者**:

- [项目概览](tier_01_foundations/01_项目概览.md)
- [术语表](tier_01_foundations/03_术语表.md)
- [常见问题](tier_01_foundations/04_常见问题.md)

**💻 进阶开发者**:

- [基础类型指南](tier_02_guides/01_基础类型指南.md)
- [泛型编程指南](tier_02_guides/03_泛型编程指南.md)
- [Trait 系统指南](tier_02_guides/04_Trait系统指南.md)

**⚡ 高级开发者**:

- [类型系统规范](tier_03_references/01_类型系统规范.md)
- [类型型变参考](tier_03_references/02_类型型变参考.md)
- [分派机制参考](tier_03_references/03_分派机制参考.md)

---

## 📚 Tier 1-4 分层导航

| Tier | 层级名称 | 文档数 | 适合人群 | 入口 |
|------|-----------|--------|----------|------|
| **Tier 1** | 基础层 | 4 个 | 初学者 | [tier_01_foundations/](tier_01_foundations/README.md) |
| **Tier 2** | 核心指南层 | 多篇 | 进阶学习者 | [tier_02_guides/](tier_02_guides/) |
| **Tier 3** | 参考层 | 多篇 | 高级开发者 | [tier_03_references/](tier_03_references/) |
| **Tier 4** | 高级层 | 5 篇 | 专家/研究者 | [tier_04_advanced/](tier_04_advanced/) |

---

## 📦 Cargo 包管理专题

独立的 Cargo 包管理文档体系，涵盖依赖管理、特性系统、工作空间等：

- [Cargo 包管理索引](cargo_package_management/00_INDEX.md)

---

## 🆕 Rust 版本特性

- [Rust 1.91 类型系统改进](RUST_191_TYPE_SYSTEM_IMPROVEMENTS.md)
- [Rust 1.92 类型系统改进](RUST_192_TYPE_SYSTEM_IMPROVEMENTS.md)
- [Rust 1.92 示例集合](RUST_192_EXAMPLES_COLLECTION.md)

---

## 💻 代码示例

```bash
# 运行示例
cargo run -p c02_type_system --example <example_name>

# 运行所有测试
cargo test -p c02_type_system
```

---

## 🔗 相关文档

- **完整文档指南**: [docs/README.md](README.md) - 包含更多主题分类和导航
- **项目根结构**: [PROJECT_STRUCTURE.md](../../../PROJECT_STRUCTURE.md)

---

**最后更新**: 2026-02-12
