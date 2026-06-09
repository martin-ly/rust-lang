# 01 - Rust 基础

> **Bloom 层级**: 理解
> **Rust 语言的核心基础：所有权、借用、生命周期、迭代器**
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

## 🎯 本模块学习目标

> **[来源: Rust Official Docs]**

完成本模块后，你将能够：

- [ ] 理解 Rust 所有权系统的三条核心规则
- [ ] 掌握借用引用的可变性与生命周期
- [ ] 使用迭代器进行声明式数据处理
- [ ] 在阅读和理解 Rust 代码时识别生命周期标注

## 📚 内容
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [ownership.md](04_ownership.md) | 所有权系统 | ⭐⭐ |
| [borrowing.md](01_borrowing.md) | 借用与引用 | ⭐⭐ |
| [lifetimes.md](03_lifetimes.md) | 生命周期 | ⭐⭐⭐ |
| [iterators.md](02_iterators.md) | 迭代器 | ⭐⭐ |

## ⏱️ 预计时间
>
> **[来源: Rust Official Docs]**

- 所有权: 2-3 小时
- 借用: 1.5-2 小时
- 生命周期: 2-3 小时
- 迭代器: 1-2 小时
- **总计**: 约 7-10 小时

## 🎓 预备知识
>
> **[来源: Rust Official Docs]**

- [00_start/](../00_start/) 的安装和基础概念
- 基本的编程经验（变量、函数、控制流）

## ✅ 完成检查清单
>
> **[来源: Rust Official Docs]**

- [ ] 能解释所有权转移 (move) 与复制 (copy) 的区别
- [ ] 能写出合法的可变借用和不可变借用代码
- [ ] 能阅读和标注简单的生命周期
- [ ] 能使用 `map`、`filter`、`collect` 等迭代器适配器

## 🚀 下一步

完成本模块后，进入 [02_intermediate/](../02_intermediate/) 学习泛型、Trait、错误处理等中级主题。

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/),
> [The Rust Programming Language](https://doc.rust-lang.org/book/),
> [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [所有权深入](04_ownership.md)
