# C11 宏系统 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
|------|------|
| **声明宏** | `macro_rules!`；模式匹配；卫生性 |
| **过程宏** | Derive、属性、函数宏；`proc-macro` crate |
| **片段类型** | `expr`、`ident`、`ty`、`path` 等；匹配与展开 |
| **递归宏** | 逐步展开；`$($rest)*` 重复 |

---

## 常见坑与解决

| 坑 | 解决 |
|----|------|
| 宏展开顺序 | 宏在编译时展开；注意作用域 |
| 片段类型不匹配 | 用 `tt` 兜底；或拆成多规则 |
| 过程宏编译慢 | 独立 crate；增量编译 |
| 卫生性意外 | 用 `$crate` 引用；避免标识符冲突 |

---

## 宏速选

| 场景 | 选型 |
|------|------|
| 简单重复代码 | 声明宏 `macro_rules!` |
| 自动实现 trait | `#[derive(Trait)]` 过程宏 |
| 属性注解 | 属性过程宏 `#[attr]` |
| 函数式语法扩展 | 函数过程宏 `macro!()` |
| 复杂 DSL | 过程宏 + 声明宏组合 |

---

## 学习路径

1. **入门** (1–2 周): 声明宏基础 → 片段类型 → 递归宏
2. **进阶** (2–3 周): Derive 宏 → 属性宏 → 函数宏
3. **高级** (持续): 复杂 DSL、与 C09 框架性模式结合

---

## 速查与练习

- **速查卡**: [macros_cheatsheet](../../../docs/02_reference/quick_reference/macros_cheatsheet.md)
- **RBE 练习**: [Macros](https://doc.rust-lang.org/rust-by-example/macros.html)
- **Rustlings**: [21_macros](https://github.com/rust-lang/rustlings/tree/main/exercises/21_macros)
