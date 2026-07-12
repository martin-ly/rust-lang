# 02 - 进阶 Rust

> **EN**: Intermediate Index
> **Summary**: 02 - 进阶 Rust Intermediate Index.
> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[闭包](../../concept/01_foundation/00_start/03_closure_basics.md)
> **Bloom 层级**: L2
> **掌握 Rust 的核心抽象能力**
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

## 🎯 本模块学习目标
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

完成本模块后，你将能够：

- [ ] 使用泛型编写可复用代码
- [ ] 使用 Trait 定义共享行为
- [ ] 处理错误和可选值
- [ ] 使用智能指针管理内存
- [ ] 高效使用集合和迭代器

## 📚 核心主题
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

### 类型系统
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 主题 | 难度 |
|------|------|------|
| [generics.md](03_generics.md) | 泛型编程 | ⭐⭐⭐ |
| [traits.md](06_traits.md) | Trait 系统 | ⭐⭐⭐⭐ |
| [lifetimes.md](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | 生命周期 | ⭐⭐⭐⭐ |

### 数据处理
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 主题 | 难度 |
|------|------|------|
| [collections.md](01_collections.md) | 集合类型 | ⭐⭐⭐ |
| [strings.md](05_strings.md) | 字符串处理 | ⭐⭐⭐ |
| [error_handling.md](02_error_handling.md) | 错误处理 | ⭐⭐⭐⭐ |

### 内存管理
>
> **[Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 主题 | 难度 |
|------|------|------|
| [smart_pointers.md](04_smart_pointers.md) | 智能指针（含 RefCell） | ⭐⭐⭐⭐ |
| [type_conversions.md](07_type_conversions.md) | 类型转换 | ⭐⭐⭐ |

### 控制流与模式匹配

| 文档 | 主题 | 难度 |
|------|------|------|
| [let_chains.md](control_flow/02_let_chains.md) | let chains | ⭐⭐⭐ |
| [if_let_guards.md](control_flow/01_if_let_guards.md) | if let guards | ⭐⭐⭐ |
| [cfg_select.md](macros/01_cfg_select.md) | cfg_select! 宏 | ⭐⭐⭐ |

### 集合与范围

| 文档 | 主题 | 难度 |
|------|------|------|
| [core_range.md](type_system/01_core_range.md) | core::range 模块 | ⭐⭐⭐ |

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

完成本模块后，进入 [03_advanced/](../03_advanced) 学习高级主题。

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/),
> [The Rust Programming Language](https://doc.rust-lang.org/book/),
> [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [The Rust Programming Language — Ch10](https://doc.rust-lang.org/book/ch10-00-generics.html) | 泛型、Trait 与生命周期 |
| [Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html) | Trait 规范 |
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/) | API 设计指南 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Trait 对象与泛型语义 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/) | 常用编程模式 |
| [Rust By Example](https://doc.rust-lang.org/rust-by-example/) | 中级示例 |
| [This Week in Rust](https://this-week-in-rust.org/) | 社区动态 |
