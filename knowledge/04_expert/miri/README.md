# Miri 内存模型

> **EN**: Miri Index
> **Summary**: Miri 内存模型 Miri Index. (stub/archive redirect)
> **Bloom 层级**: 理解
> **Rust 内存安全检查与别名模型**
>
> **受众**: [专家] / [研究者]
> **内容分级**: [研究者级]

## 📚 内容
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [tree_borrows.md](01_tree_borrows.md) | Tree Borrows 别名模型 | ⭐⭐⭐⭐⭐ |

## 🎯 前置要求
>
> **[来源: Rust Official Docs]**

- [03_advanced/unsafe/unsafe_rust.md](../../03_advanced/unsafe/04_unsafe_rust.md) - Unsafe Rust 基础
- [04_expert/unsafe_audit.md](../02_unsafe_audit.md) - Unsafe 代码审计

## 🚀 相关层
>
> **[来源: Rust Official Docs]**

- [04_expert/academic/](../academic) - 形式化验证与学术深度解析

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [Tree Borrows (concept)](../../../concept/01_foundation/03_values_and_references/05_reference_semantics.md) — PLDI 2025 Distinguished Paper 详解
- [形式化验证工具链 (concept)](../../../concept/04_formal/05_verification_toolchain.md) — Miri POPL 2026、KVerus、AutoVerus、Vest 2026 状态矩阵

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Miri](https://github.com/rust-lang/miri) | Miri 解释器仓库 |
| [Rustc Dev Guide — MIRI](https://rustc-dev-guide.rust-lang.org/miri.html) | Miri 在编译器中的位置 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [Stacked Borrows — POPL 2021](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | 旧默认别名模型 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | 新默认别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Miri Book](https://github.com/rust-lang/miri) | Miri 文档 |
| [Rust Internals — Miri](https://internals.rust-lang.org/) | 讨论区 |
