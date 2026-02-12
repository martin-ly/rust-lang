# 边界体系统一分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: 100% 完成

---

## 宗旨

本目录提供软件设计理论体系的三维边界分析：

1. **安全 vs 非安全**：模式/模型在 Rust 中的安全子集边界
2. **支持 vs 不支持**：语言/库的原生支持程度
3. **充分表达 vs 非充分表达**：相对 OOP/GoF 的语义等价性

---

## 文档索引

| 文档 | 内容 |
|------|------|
| [safe_unsafe_matrix](safe_unsafe_matrix.md) | 安全 vs 非安全边界矩阵 |
| [supported_unsupported_matrix](supported_unsupported_matrix.md) | 支持 vs 不支持边界矩阵 |
| [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) | 充分表达 vs 非充分表达边界矩阵 |

---

## 三维边界快速参考

| 维度 | 取值 | 含义 |
|------|------|------|
| 安全 | 纯 Safe / 需 unsafe / 无法表达 | 是否依赖 unsafe |
| 支持 | 原生 / 库 / FFI | 语言/标准库 vs 第三方 |
| 表达 | 等价 / 近似 / 不可表达 | 相对 GoF/OOP 语义 |

## 使用流程

1. 查模式：在 [04_boundary_matrix](../01_design_patterns_formal/04_boundary_matrix.md) 或对应模式文档
2. 判安全：用 [safe_unsafe_matrix](safe_unsafe_matrix.md) 决策树
3. 判支持：用 [supported_unsupported_matrix](supported_unsupported_matrix.md) 判定
4. 查表达：用 [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) 了解差异

---

## 快速决策

| 问题 | 查文档 |
|------|--------|
| 某模式是否纯 Safe？ | [safe_unsafe_matrix](safe_unsafe_matrix.md) |
| 需哪个 crate？ | [supported_unsupported_matrix](supported_unsupported_matrix.md) |
| 与 GoF 有无差异？ | [expressive_inexpressive_matrix](expressive_inexpressive_matrix.md) |
| 从 OOP 迁移？ | expressive_inexpressive_matrix § 从 OOP 迁移建议 |

---

## 与顶层衔接

本边界体系与 [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) 衔接，扩展至设计模式与执行模型维度。
