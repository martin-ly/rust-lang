# C03 控制流 (Control Flow)

> Rust 强大的流程控制能力

---

## 📚 学习资源

### 练习

- [模式匹配练习](exercises/01_pattern_matching.rs)

### 相关文档

- [docs/05_guides/BEST_PRACTICES.md](../docs/05_guides/BEST_PRACTICES.md) - 控制流最佳实践
- [docs/04_thinking/decision_trees/](../docs/04_thinking) - 决策树表示

### 相关 Crate

- [c03_control_fn](../c03_control_fn) - 函数式控制流

---

## 🎯 核心概念

1. **条件表达式**
   - `if` / `else if` / `else`
   - `if let` 简化模式
2. **循环**
   - `loop` - 无限循环
   - `while` - 条件循环
   - `for` - 迭代循环
   - `while let`
3. **模式匹配**
   - `match` 表达式
   - 解构
   - 守卫子句
   - `@` 绑定
4. **流程控制**
   - `break` / `continue`
   - 标签跳出
   - `return`

---

## 🔗 交叉引用

| 概念 | 相关文档 | 相关 Crate |
|------|----------|------------|
| 模式匹配 | [docs/05_guides/BEST_PRACTICES.md](../docs/05_guides/BEST_PRACTICES.md) | c02_type_system |
| 迭代器 | [docs/02_reference/](../docs/02_reference) | c04_generic |
| 函数式风格 | [docs/05_guides/](../docs/05_guides) | c03_control_fn |

---

**状态**: ✅ 100% 完成

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
