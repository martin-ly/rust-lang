# C01 所有权系统 (Ownership)

> Rust 最核心的特性 - 内存安全无垃圾回收

---

## 📚 学习资源

### 文档

- [所有权与借用检查器练习](./exercises/01_borrow_checker.md)
- [docs/04_thinking/](../docs/04_thinking/) - 思维导图和决策树

### 相关 Crate

- [c01_ownership_borrow_scope](../c01_ownership_borrow_scope/) - 详细的借用和作用域分析

---

## 🎯 核心概念

1. **所有权规则**
   - 每个值有一个所有者
   - 只有一个所有者
   - 所有者离开作用域，值被释放

2. **借用**
   - 不可变借用: `&T`
   - 可变借用: `&mut T`
   - 借用检查器规则

3. **生命周期**
   - 显式生命周期标注
   - 生命周期省略规则
   - 复杂生命周期场景

---

## 🔗 交叉引用

| 概念 | 相关文档 | 相关 Crate |
|------|----------|------------|
| 借用检查 | [CROSS_MODULE_NAVIGATION.md](../docs/CROSS_MODULE_NAVIGATION.md) | c01_ownership_borrow_scope |
| 智能指针 | [docs/05_guides/BEST_PRACTICES.md](../docs/05_guides/BEST_PRACTICES.md) | c04_generic |
| 生命周期 | [docs/04_thinking/](../docs/04_thinking/) | c02_type_system |

---

**状态**: ✅ 100% 完成
