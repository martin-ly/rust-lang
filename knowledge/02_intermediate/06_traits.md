# Trait 系统

> **EN**: Traits
> **Summary**: Trait 系统 Traits. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/02_intermediate/01_traits.md](../../concept/02_intermediate/01_traits.md)。
> **历史版本存档**: [archive/knowledge/02_intermediate/06_traits.md](../../archive/knowledge/02_intermediate/06_traits.md)
>
> **定位**: 本文件为精简知识卡片，保留核心概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. **Trait 定义共享行为接口**，类似其他语言中的接口，但支持默认实现。
2. **Impl Trait** 让函数签名更简洁；**dyn Trait** 提供动态分发。
3. **Trait Bound** 用于在泛型上约束类型能力。
4. **关联类型（Associated Types）** 在 trait 内部声明类型别名，提升可读性。

## 关键区分

| 形式 | 编译期分发 | 运行时开销 | 使用场景 |
|---|---|---|---|
| `impl Trait` | ✅ 静态 | 无 | 返回单一未命名类型 |
| `dyn Trait` | ❌ 动态 | vtable | 需要同构集合时 |

## 常见陷阱

- 为外部类型实现外部 trait（孤儿规则）。
- 混淆 `impl Trait` 返回类型与 `dyn Trait`。
- 在 trait 对象中使用泛型方法（对象安全限制）。

---

**详细内容已迁移**：请点击上方 [concept/02_intermediate/01_traits.md](../../concept/02_intermediate/01_traits.md) 查看最新权威解释。
