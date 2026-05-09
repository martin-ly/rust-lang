# Rust 知识中心

> > **Rust 版本**: 1.95.0 (Edition 2024)
> **更新策略**: 跟随官方稳定版，每版本更新
> **文档规模**: 73 篇核心文档，33,715 行，36 篇按 10 模块标准重构

## 🎯 快速导航

| 路径 | 内容 | 适合人群 |
|------|------|----------|
| [00_start/](00_start/) | 入门指南、环境搭建、Hello World | 零基础 |
| [01_fundamentals/](01_fundamentals/) | 所有权、借用、生命周期、基础语法 | 初学者 |
| [02_intermediate/](02_intermediate/) | 泛型、trait、错误处理、集合 | 有基础者 |
| [03_advanced/](03_advanced/) | 异步、并发、宏、unsafe | 进阶学习者 |
| [04_expert/](04_expert/) | 设计模式、性能优化、架构 | 高级开发者 |
| [05_reference/](05_reference/) | 速查表、术语、标准库 | 全阶段参考 |
| [06_ecosystem/](06_ecosystem/) | 工具链、生态库、最佳实践 | 工程实践 |

## 📚 学习路径

```text
00_start/ → 01_fundamentals/ → 02_intermediate/ → 03_advanced/ → 04_expert/
     ↑                                                    ↓
     └──────────────── 05_reference/ ←────────────────────┘
```

## 🆕 最新更新 (Rust 1.95.0)

| 特性 | 文档位置 | 状态 |
|------|---------|------|
| `cfg_select!` | [03_advanced/macros/declarative.md](03_advanced/macros/declarative.md) | ✅ 已更新 |
| `if let guards` | [02_intermediate/control_flow/if_let_guards.md](02_intermediate/control_flow/if_let_guards.md) | ✅ 已更新 |
| `Atomic*::update/try_update` | [03_advanced/concurrency/atomics.md](03_advanced/concurrency/atomics.md) | ✅ 已更新 |
| `Vec::push_mut` / `insert_mut` | [02_intermediate/collections.md](02_intermediate/collections.md) | ✅ 已更新 |
| `core::hint::cold_path` | [03_advanced/performance_optimization.md](03_advanced/performance_optimization.md) | ✅ 已更新 |
| `bool::TryFrom<{integer}>` | [02_intermediate/type_conversions.md](02_intermediate/type_conversions.md) | ✅ 已更新 |
| `MaybeUninit` / `Cell` 数组转换 | [03_advanced/unsafe/maybe_uninit.md](03_advanced/unsafe/maybe_uninit.md) | ✅ 已更新 |
| PowerPC/PowerPC64 内联汇编 | [03_advanced/unsafe/inline_asm.md](03_advanced/unsafe/inline_asm.md) | ✅ 已更新 |
| `core::range` | [02_intermediate/collections.md](02_intermediate/collections.md) | ✅ 已更新 |

## 🔮 预览版本跟踪

| 版本 | 预计发布 | 关键特性 | 准备状态 |
|------|---------|---------|----------|
| 1.96.0 | 2026-05-28 | 新 Range 类型, cargo script | 🔄 准备中 |
| 1.97.0 | 2026-07 | TBD | ⏳ 等待 |

## 📖 如何使用

1. **新手**: 从 [00_start/](00_start/) 开始，按顺序学习
2. **有基础**: 查看 [INDEX.md](INDEX.md) 找到感兴趣的主题
3. **查询参考**: 使用 [05_reference/](05_reference/) 速查
4. **跟进更新**: 关注本页面的版本更新记录

## 🤝 贡献

发现内容过时或有错误？请提交 Issue 或 PR。

---

**最后更新**: 2026-05-09
**维护者**: Rust 学习项目团队
**重构状态**: Phase 1 核心层完成（28篇 → 16,000+行）| Phase 2 Ecosystem 层进行中
