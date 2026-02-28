# C04 泛型编程 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- |
| **泛型函数与结构体** | `fn f<T>(x: T)`；`struct S<T>`；类型参数 `T` |
| **Trait 约束** | `T: Display`、`where T: Clone + Send`；trait bounds |
| **关联类型** | `type Item` 在 trait 内；简化泛型签名 |
| **GATs** | 泛型关联类型（Rust 1.65+）；生命周期参数化关联类型 |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- |
| 泛型约束过严 | 按需添加 bounds；避免不必要的 `T: Clone` |
| 关联类型 vs 泛型参数 | 单一定义用关联类型；多实现用泛型参数 |
| 型变理解困难 | 参考 [variance_theory](../../../docs/research_notes/type_theory/variance_theory.md) |
| 编译错误「类型推断失败」 | 显式标注类型或添加 `where` 约束 |

---

## 泛型速选

| 场景 | 选型 |
| :--- | :--- |
| 简单泛型 | `fn f<T>(x: T) where T: Trait` |
| 多 trait 约束 | `T: A + B` 或 `where T: A, T: B` |
| 返回泛型 | `impl Trait` 或 `Box<dyn Trait>` |
| 关联类型 | trait 内 `type Output`；impl 时指定 |

---

## 学习路径

1. **入门** (1–2 周): 泛型函数/结构体 → trait bounds → 关联类型
2. **进阶** (2–3 周): 型变 → 高级 trait → GATs
3. **高级** (持续): 类型级编程、形式化

---

## 速查与练习

- **速查卡**: [generics_cheatsheet](../../../docs/02_reference/quick_reference/generics_cheatsheet.md)
- **RBE 练习**: [Generics](https://doc.rust-lang.org/rust-by-example/generics.html)
- **Rustlings**: [14_generics](https://github.com/rust-lang/rustlings/tree/main/exercises/14_generics)
