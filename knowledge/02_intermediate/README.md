# 02 - 进阶 Rust

> **Bloom 层级**: 理解

> **掌握 Rust 的核心抽象能力**

## 🎯 本模块学习目标

完成本模块后，你将能够：

- [ ] 使用泛型编写可复用代码
- [ ] 使用 Trait 定义共享行为
- [ ] 处理错误和可选值
- [ ] 使用智能指针管理内存
- [ ] 高效使用集合和迭代器

## 📚 核心主题

### 类型系统

| 文档 | 主题 | 难度 |
|------|------|------|
| [generics.md](generics.md) | 泛型编程 | ⭐⭐⭐ |
| [traits.md](traits.md) | Trait 系统 | ⭐⭐⭐⭐ |
| [lifetimes.md](../01_fundamentals/lifetimes.md) | 生命周期 | ⭐⭐⭐⭐ |

### 数据处理

| 文档 | 主题 | 难度 |
|------|------|------|
| [collections.md](collections.md) | 集合类型 | ⭐⭐⭐ |
| [strings.md](strings.md) | 字符串处理 | ⭐⭐⭐ |
| [error_handling.md](error_handling.md) | 错误处理 | ⭐⭐⭐⭐ |

### 内存管理

| 文档 | 主题 | 难度 |
|------|------|------|
| [smart_pointers.md](smart_pointers.md) | 智能指针（含 RefCell） | ⭐⭐⭐⭐ |
| [type_conversions.md](type_conversions.md) | 类型转换 | ⭐⭐⭐ |

### 控制流与模式匹配

| 文档 | 主题 | 难度 |
|------|------|------|
| [let_chains.md](control_flow/let_chains.md) | let chains | ⭐⭐⭐ |
| [if_let_guards.md](control_flow/if_let_guards.md) | if let guards | ⭐⭐⭐ |
| [cfg_select.md](macros/cfg_select.md) | cfg_select! 宏 | ⭐⭐⭐ |

### 集合与范围

| 文档 | 主题 | 难度 |
|------|------|------|
| [core_range.md](type_system/core_range.md) | core::range 模块 | ⭐⭐⭐ |

## ⏱️ 预计时间

- 类型系统: 15-20 小时
- 数据处理: 15-20 小时
- 内存管理: 15-20 小时
- 控制流与模式匹配: 5-8 小时
- **总计**: 50-70 小时

## 🎯 完成标准

- [ ] 能设计泛型接口
- [ ] 能实现自定义 Trait
- [ ] 能优雅处理错误
- [ ] 能选择合适的智能指针
- [ ] 能编写 2000 行以内的项目

## 🚀 下一步

完成本模块后，进入 [03_advanced/](../03_advanced/) 学习高级主题。

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
