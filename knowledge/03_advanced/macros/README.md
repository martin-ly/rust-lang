# Macros 宏系统

> **EN**: Macros Index
> **Summary**: Macros 宏系统 Macros Index.
> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[属性与宏](../../../concept/01_foundation/12_attributes_and_macros.md)
>
> **层次定位**: L3 高级概念 / 宏子域索引
> **前置依赖**: [knowledge Trait](../../02_intermediate/06_traits.md) · [knowledge 泛型](../../02_intermediate/03_generics.md)
> **后置延伸**: [knowledge 编译器内部](../../04_expert/01_compiler_internals.md) · [concept L3 宏](../../../concept/03_advanced/04_macros.md)
> **跨层映射**: knowledge→concept 直觉映射 | L3 元编程
> **定理链编号**: T-070 宏卫生性 → T-071 展开正确性
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

## 📑 目录

- [Macros 宏系统](#macros-宏系统)
  - [📑 目录](#-目录)
  - [📚 内容](#-内容)
  - [🎯 学习路径](#-学习路径)
  - [🚀 相关层](#-相关层)
  - [📚 模块 8: 国际化对齐](#-模块-8-国际化对齐)
    - [8.1 官方来源](#81-官方来源)
    - [8.2 学术/工业来源](#82-学术工业来源)
    - [8.3 社区资源](#83-社区资源)

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
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rust Reference — Macros](https://doc.rust-lang.org/reference/macros.html) | 宏系统规范 |
| [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html) | 过程宏规范 |
| [Rust By Example — Macros](https://doc.rust-lang.org/rust-by-example/macros.html) | 宏示例 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RFC 1584 — Macros Literal Matcher](https://rust-lang.github.io/rfcs/1584-macros.html) | 宏字面量匹配 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) | 宏进阶教程 |
| [Rust Cookbook — Macros](https://rust-lang-nursery.github.io/rust-cookbook/) | 宏模式 |
