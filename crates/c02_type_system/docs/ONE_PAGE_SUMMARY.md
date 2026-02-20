# C02 类型系统 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- || **基础类型** | 标量（整数、浮点、bool、char）、复合（元组、数组） |
| **自定义类型** | `struct`、`enum`；`impl` 块实现方法 |
| **泛型** | 类型参数 `T`；trait bounds 约束 |
| **Trait** | 抽象行为；`impl Trait for Type`；关联类型、GATs |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || 生命周期推断失败 | 显式标注 `'a`；检查引用存活范围 |
| 型变理解困难 | 参考 [variance_theory](../../../docs/research_notes/type_theory/variance_theory.md) |
| Trait 对象 vs 泛型 | 运行时多态用 `dyn Trait`；编译时多态用泛型 |
| 泛型约束过严/过松 | 按需添加 `where` 子句 |

---

## 类型选型速查

| 场景 | 选型 |
| :--- | :--- || 可选值 | `Option<T>` |
| 成功/失败 | `Result<T, E>` |
| 多态（编译时） | 泛型 `fn f<T: Trait>(x: T)` |
| 多态（运行时） | `dyn Trait`、`Box<dyn Trait>` |
| 类型转换 | `From`/`Into`、`TryFrom`/`TryInto` |

---

## 学习路径

1. **入门** (1–2 周): 基础类型 → struct/enum → 泛型基础
2. **进阶** (2–4 周): Trait 系统 → 关联类型 → 型变
3. **高级** (持续): GATs、形式化类型理论

---

## 速查与练习

- **速查卡**: [type_system](../../../docs/02_reference/quick_reference/type_system.md) | [generics_cheatsheet](../../../docs/02_reference/quick_reference/generics_cheatsheet.md)
- **RBE 练习**: [Custom Types](https://doc.rust-lang.org/rust-by-example/custom_types.html) · [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) · [Conversion](https://doc.rust-lang.org/rust-by-example/conversion.html)
- **Rustlings**: [04_primitive_types](https://github.com/rust-lang/rustlings/tree/main/exercises/04_primitive_types) · [07_structs](https://github.com/rust-lang/rustlings/tree/main/exercises/07_structs) · [08_enums](https://github.com/rust-lang/rustlings/tree/main/exercises/08_enums) · [15_traits](https://github.com/rust-lang/rustlings/tree/main/exercises/15_traits)
