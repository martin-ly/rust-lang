# 01 - Rust 基础

> **EN**: Fundamentals Index
> **Summary**: 01 - Rust 基础 Fundamentals Index.
> **Bloom 层级**: L2
> **Rust 语言的核心基础：所有权、借用、生命周期、迭代器**
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

## 🎯 本模块学习目标

> **[Rust Official Docs](https://doc.rust-lang.org/)**

完成本模块后，你将能够：

- [ ] 理解 Rust 所有权系统的三条核心规则
- [ ] 掌握借用引用的可变性与生命周期
- [ ] 使用迭代器进行声明式数据处理
- [ ] 在阅读和理解 Rust 代码时识别生命周期标注

## 📚 内容
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 主题 | 难度 |
|------|------|------|
| [ownership.md](04_ownership.md) | 所有权系统 | ⭐⭐ |
| [borrowing.md](01_borrowing.md) | 借用与引用 | ⭐⭐ |
| [lifetimes.md](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | 生命周期 | ⭐⭐⭐ |
| [iterators.md](02_iterators.md) | 迭代器 | ⭐⭐ |

## ⏱️ 预计时间
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

- 所有权: 2-3 小时
- 借用: 1.5-2 小时
- 生命周期: 2-3 小时
- 迭代器: 1-2 小时
- **总计**: 约 7-10 小时

## 🎓 预备知识
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

- [00_start/](../00_start) 的安装和基础概念
- 基本的编程经验（变量、函数、控制流）

## ✅ 完成检查清单
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

- [ ] 能解释所有权转移 (move) 与复制 (copy) 的区别
- [ ] 能写出合法的可变借用和不可变借用代码
- [ ] 能阅读和标注简单的生命周期
- [ ] 能使用 `map`、`filter`、`collect` 等迭代器适配器

## 🚀 下一步

完成本模块后，进入 [02_intermediate/](../02_intermediate) 学习泛型、Trait、错误处理等中级主题。

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/),
> [The Rust Programming Language](https://doc.rust-lang.org/book/),
> [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [所有权深入](04_ownership.md)

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Programming Language — Ch4](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) | 所有权与借用 |
| [Rust Reference — Types](https://doc.rust-lang.org/reference/types.html) | 类型系统规范 |
| [Rust Standard Library](https://doc.rust-lang.org/std/) | 标准库 API |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | 所有权语义形式化 |
| [Tree Borrows — PLDI 2025](https://perso.crans.org/vanille/treebor/) | 别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) | 可视化所有权教学 |
| [Rustlings](https://github.com/rust-lang/rustlings) | 基础练习 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 示例驱动学习 |
