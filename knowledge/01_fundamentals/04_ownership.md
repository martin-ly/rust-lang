# Rust 所有权系统 (Ownership System)

> **权威来源**: 本主题深度解释见 [concept/01_foundation/01_ownership.md](../../concept/01_foundation/01_ownership.md)。
> **历史版本存档**: [archive/knowledge/01_fundamentals/04_ownership.md](../../archive/knowledge/01_fundamentals/04_ownership.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心规则

1. **每个值有且只有一个所有者**。
2. **所有者离开作用域时，值被丢弃**（Drop）。
3. **同一时间只能有一个可变引用，或多个不可变引用**。
4. **引用必须始终有效**（不能悬空）。

## 关键区分

| 类型 | Move | Copy |
|---|---|---|
| 简单标量（`i32`, `bool`, `char`, `f64`） | ❌ | ✅ |
| 堆分配类型（`String`, `Vec<T>`, `Box<T>`） | ✅ | ❌ |
| 自定义类型 | 默认 Move | 实现 `Copy` trait |

## 常见陷阱

- 赋值给另一个变量后继续使用原变量（Move 后使用）。
- 在持有不可变引用期间尝试获取可变引用。
- 返回局部变量的引用（悬空引用）。

---

**详细内容已迁移**：请点击上方 [concept/01_foundation/01_ownership.md](../../concept/01_foundation/01_ownership.md) 查看最新权威解释。
