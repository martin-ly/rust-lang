# 03 - 高级 Rust

> **Bloom 层级**: 理解

> **掌握系统级编程能力**

## 🎯 本模块学习目标
>
> **[来源: Rust Official Docs]**

完成本模块后，你将能够：

- [ ] 编写异步 Rust 代码
- [ ] 实现并发程序
- [ ] 使用宏元编程
- [ ] 理解 Unsafe Rust 边界

## 📚 核心主题
>
> **[来源: Rust Official Docs]**

### 异步编程
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [async/async_await.md](./async/01_async_await.md) | async/await 基础 | ⭐⭐⭐⭐ |
| [async/async_closure.md](./async/02_async_closure.md) | Async Closures | ⭐⭐⭐⭐ |
| [async/async_closures_2024.md](./async/01_async_closures_2024.md) | Async Closures 2024 | ⭐⭐⭐⭐ |

### 并发编程
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [concurrency/threads.md](./concurrency/03_threads.md) | 线程基础 | ⭐⭐⭐ |
| [concurrency/atomics.md](./concurrency/01_atomics.md) | 原子操作 | ⭐⭐⭐⭐ |
| [concurrency/synchronization.md](./concurrency/02_synchronization.md) | 同步原语 | ⭐⭐⭐⭐ |

### Unsafe 与底层
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [unsafe/unsafe_rust.md](./unsafe/04_unsafe_rust.md) | Unsafe 基础 | ⭐⭐⭐⭐ |
| [unsafe/ffi.md](unsafe/01_ffi.md) | FFI | ⭐⭐⭐⭐ |
| [unsafe/maybe_uninit.md](./unsafe/03_maybe_uninit.md) | MaybeUninit | ⭐⭐⭐⭐ |
| [unsafe/inline_asm.md](unsafe/02_inline_asm.md) | 内联汇编 | ⭐⭐⭐⭐⭐ |

### 类型与元编程

| 文档 | 主题 | 难度 |
|------|------|------|
| [lazy_initialization.md](04_lazy_initialization.md) | 延迟初始化 | ⭐⭐⭐ |
| [type_driven_correctness.md](06_type_driven_correctness.md) | 类型驱动正确性 | ⭐⭐⭐⭐⭐ |
| [macros/declarative.md](./macros/01_declarative.md) | 声明宏 | ⭐⭐⭐⭐ |
| [macros/procedural.md](./macros/02_procedural.md) | 过程宏 | ⭐⭐⭐⭐ |

### 性能

| 文档 | 主题 | 难度 |
|------|------|------|
| [performance_optimization.md](05_performance_optimization.md) | 性能优化 | ⭐⭐⭐⭐ |

## ⏱️ 预计时间

- 异步编程: 25-30 小时
- 并发编程: 20-25 小时
- Unsafe 与底层: 15-25 小时
- 类型与元编程: 15-20 小时
- 性能: 5-8 小时
- **总计**: 80-108 小时

## 🎯 完成标准

- [ ] 能编写异步网络程序
- [ ] 能正确处理并发数据共享
- [ ] 能编写安全的 unsafe 代码
- [ ] 能使用宏减少重复代码
- [ ] 能编写复杂系统程序

## 🚀 下一步

完成本模块后，进入 [04_expert/](../04_expert/) 学习专家级主题。

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 相关概念

- [并发编程](./concurrency/03_threads.md)

---

## 相关概念

- [NLL 与 Polonius (concept)](../../concept/03_advanced/08_nll_and_polonius.md) — 三代借用检查器演进分析
