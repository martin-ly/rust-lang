# Rust 类型系统基础指南 / Rust Type System Foundations Guide

> **EN**: Rust Type System Foundations Guide
> **Summary**: Rust 类型系统基础指南 Rust Type System Foundations Guide. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/04_formal/02_type_theory.md](../../../concept/04_formal/00_type_theory/01_type_theory.md)。
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 代数数据类型：积类型（struct/tuple）与和类型（enum）
2. 泛型对应 System F 直觉，trait 提供受限多态
3. 生命周期是区域变量，约束求解决定引用合法性
4. 进展与保持定理保证类型安全

## 关键区分

| 概念 | 形式对应 | Rust 语法 |
|---|---|---|
| 积类型 | 笛卡尔积 | `struct`, `tuple` |
| 和类型 | 不交并 | `enum` |
| 受限多态 | Bounded Quantification | `trait` + Generic |
| 区域变量 | Region Inference | lifetime `'a` |

## 常见陷阱

- 混淆协变/逆变/不变导致 trait 实现错误
- 将生命周期视为运行时检查
- 在 trait bound 中写出不可满足约束

---

**详细内容已迁移**：请点击上方 [concept/04_formal/02_type_theory.md](../../../concept/04_formal/00_type_theory/01_type_theory.md) 查看最新权威解释。
