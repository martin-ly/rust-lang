# Miri 内存模型

> **Bloom 层级**: 理解
> **Rust 内存安全检查与别名模型**

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

- [04_expert/academic/](../academic/) - 形式化验证与学术深度解析

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [Tree Borrows (concept)](../../../concept/01_foundation/05_reference_semantics.md) — PLDI 2025 Distinguished Paper 详解
- [形式化验证工具链 (concept)](../../../concept/04_formal/05_verification_toolchain.md) — Miri POPL 2026、KVerus、AutoVerus、Vest 2026 状态矩阵
