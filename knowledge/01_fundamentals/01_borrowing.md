# Rust 借用与引用 (Borrowing and References)

> **EN**: Borrowing and References
> **Summary**: Rust 借用与引用 Borrowing and References. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)。
> **历史版本存档**: [archive/knowledge/01_fundamentals/01_borrowing.md](../../archive/knowledge/01_fundamentals/01_borrowing.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则/概念与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心概念

1. 借用不获取所有权，只获得引用 `&T` 或 `&mut T`
2. 同一作用域内，只能有一个可变引用，或多个不可变引用
3. 引用必须始终有效，禁止悬垂引用
4. 可变引用具有排他性，防止数据竞争

## 关键区分

| 引用类型 | 可变性 | 数量限制 | 使用场景 |
|---|---|---|---|
| `&T` | 不可变 | 多个共存 | 只读访问 |
| `&mut T` | 可变 | 同一作用域唯一 | 修改数据 |

## 常见陷阱

- 同时持有可变和不可变引用
- 返回局部变量的引用造成悬垂
- 混淆 `&` 与 `&mut` 的语义

---

**详细内容已迁移**：请点击上方 [concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md](../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) 查看最新权威解释。
