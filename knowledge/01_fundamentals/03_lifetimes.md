# Rust 生命周期 (Lifetimes)

> **EN**: Lifetimes
> **Summary**: Rust 生命周期 Lifetimes. (stub/archive redirect)
> **权威来源**: 本主题深度解释见 [concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)。
> **历史版本存档**: [archive/knowledge/01_fundamentals/03_lifetimes.md](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)
>
> **定位**: 本文件为精简知识卡片，保留核心规则与常见陷阱。详细解释、形式化语义与代码示例请查看权威来源。

---

## 核心规则

1. **生命周期是编译期对引用有效范围的约束**，不是运行时检查。
2. **引用不能比它指向的数据活得更长**。
3. **函数签名中的生命周期标注描述的是输入与输出引用之间的关系**，而非具体存活时间。

## 生命周期省略规则（Elision）

编译器在以下情况可自动推断生命周期：

1. 每个输入参数各有一个独立生命周期。
2. 若只有一个输入生命周期，输出生命周期与之相同。
3. 若有 `&self` 或 `&mut self`，输出生命周期与 `self` 相同。

## 常见陷阱

- 返回函数局部变量的引用。
- 在结构体中存储引用却未标注生命周期。
- 混淆 "生命周期短" 与 "作用域小"。

---

**详细内容已迁移**：请点击上方 [concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) 查看最新权威解释。
