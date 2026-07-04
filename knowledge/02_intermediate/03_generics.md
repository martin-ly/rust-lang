# 泛型 (Generics)

> **EN**: Generics
> **Summary**: 泛型 Generics. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/02_intermediate/01_generics/02_generics.md](../../concept/02_intermediate/01_generics/02_generics.md)。
> **历史版本存档**: [archive/knowledge/02_intermediate/03_generics.md](../../archive/knowledge/02_intermediate/03_generics.md)
>
> **定位**: 本文件为精简知识卡片，保留核心概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. **泛型让代码在多种类型上复用**，同时保持编译期类型安全。
2. **单态化（Monomorphization）**：编译器为每个具体类型生成专用代码，实现零成本抽象。
3. **Trait Bound** 限制泛型参数必须实现的能力。
4. **Const Generics** 允许泛型参数为常量值。

## 关键区分

| 泛型参数 | 示例 | 说明 |
|---|---|---|
| 类型参数 | `<T>` | 最常见 |
| 生命周期参数 | `<'a>` | 用于引用 |
| Const 泛型 | `<const N: usize>` | 编译期常量 |

## 常见陷阱

- 泛型函数返回 `T` 时未满足 `Sized` 约束。
- 过度使用泛型导致编译时间显著增加。
- 在 trait bound 中写冗余约束。

---

**详细内容已迁移**：请点击上方 [concept/02_intermediate/01_generics/02_generics.md](../../concept/02_intermediate/01_generics/02_generics.md) 查看最新权威解释。
