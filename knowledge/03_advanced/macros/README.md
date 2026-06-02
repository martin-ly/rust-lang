# Macros 宏系统

> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[属性与宏](../../../concept/01_foundation/12_attributes_and_macros.md)
>
> **层次定位**: L3 高级概念 / 宏子域索引
> **前置依赖**: [knowledge Trait](../../02_intermediate/06_traits.md) · [knowledge 泛型](../../02_intermediate/03_generics.md)
> **后置延伸**: [knowledge 编译器内部](../../04_expert/01_compiler_internals.md) · [concept L3 宏](../../../concept/03_advanced/04_macros.md)
> **跨层映射**: knowledge→concept 直觉映射 | L3 元编程
> **定理链编号**: T-070 宏卫生性 → T-071 展开正确性

## 📑 目录

- [Macros 宏系统](#macros-宏系统)
  - [📑 目录](#-目录)
  - [📚 内容](#-内容)
  - [🎯 学习路径](#-学习路径)
  - [🚀 相关层](#-相关层)

> **Bloom 层级**: 理解
> **Rust 宏编程：声明式宏与过程宏**

## 📚 内容

> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [declarative.md](01_declarative.md) | 声明式宏 (macro_rules!) | ⭐⭐⭐ |
| [procedural.md](02_procedural.md) | 过程宏 (Derive/Attribute/Function-like) | ⭐⭐⭐⭐ |

## 🎯 学习路径
>
> **[来源: Rust Official Docs]**

1. **声明式宏** → [declarative.md](01_declarative.md)
2. **过程宏** → [procedural.md](02_procedural.md)

## 🚀 相关层
>
> **[来源: Rust Official Docs]**

- [03_advanced/type_driven_correctness.md](../06_type_driven_correctness.md) - 类型驱动设计
- [06_ecosystem/emerging/generic_const_exprs.md](../../06_ecosystem/emerging/02_generic_const_exprs.md) - 类型级编程替代方案

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/),
> [The Rust Programming Language](https://doc.rust-lang.org/book/),
> [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
