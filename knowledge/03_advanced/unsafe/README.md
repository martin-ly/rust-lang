# Unsafe Rust

> **EN**: Unsafe Rust
> **Summary**: Unsafe Rust Unsafe Rust.
> **📎 交叉引用**
>
> 本主题在 concept 中有深度的概念分析：[Unsafe Rust](../../../concept/03_advanced/02_unsafe/03_unsafe.md)
> **层次定位**: L3 高级概念 / Unsafe 子域索引
> **前置依赖**: [knowledge 所有权](../../01_fundamentals/04_ownership.md) · [knowledge 借用](../../01_fundamentals/01_borrowing.md)
> **后置延伸**: [knowledge 专家层](../../04_expert) · [concept L3 Unsafe](../../../concept/03_advanced/02_unsafe/03_unsafe.md)
> **跨层映射**: knowledge→concept 直觉映射 | L3 底层控制
> **定理链编号**: T-060 unsafe 块 ↔ safe 抽象层可靠性
>
> **受众**: [进阶] / [专家]
> **内容分级**: [专家级]

## 📑 目录

- [Unsafe Rust](#unsafe-rust)
  - [📑 目录](#-目录)
  - [📚 内容](#-内容)
  - [🎯 学习路径](#-学习路径)
  - [⚠️ 安全提醒](#️-安全提醒)
  - [🚀 相关层](#-相关层)
  - [📚 模块 8: 国际化对齐](#-模块-8-国际化对齐)
    - [8.1 官方来源](#81-官方来源)
    - [8.2 学术/工业来源](#82-学术工业来源)
    - [8.3 社区资源](#83-社区资源)

> **Bloom 层级**: 理解
> **Unsafe Rust：原始指针、FFI、内联汇编、MaybeUninit**

## 📚 内容
>
> **[来源: Rust Official Docs]**

| 文档 | 主题 | 难度 |
|------|------|------|
| [unsafe_rust.md](04_unsafe_rust.md) | Unsafe Rust 基础与安全抽象 | ⭐⭐⭐⭐ |
| [ffi.md](01_ffi.md) | 外部函数接口 (FFI) | ⭐⭐⭐⭐ |
| [maybe_uninit.md](03_maybe_uninit.md) | 未初始化内存管理 | ⭐⭐⭐⭐ |
| [inline_asm.md](02_inline_asm.md) | 内联汇编 | ⭐⭐⭐⭐⭐ |

## 🎯 学习路径
>
> **[来源: Rust Official Docs]**

1. **Unsafe 基础** → [unsafe_rust.md](04_unsafe_rust.md)
2. **C 互操作** → [ffi.md](01_ffi.md)
3. **未初始化内存** → [maybe_uninit.md](03_maybe_uninit.md)
4. **底层优化** → [inline_asm.md](02_inline_asm.md)

## ⚠️ 安全提醒
>
> **[来源: Rust Official Docs]**
> 所有 unsafe 代码必须经过 Miri 验证和人工审计。每段 `unsafe` 块必须附带 `// SAFETY:` 注释。

## 🚀 相关层
>
> **[来源: Rust Official Docs]**

- [04_expert/unsafe_audit.md](../../04_expert/02_unsafe_audit.md) - Unsafe 代码审计方法论
- [04_expert/tree_borrows.md](../../04_expert/miri/01_tree_borrows.md) - 别名模型与内存规则

---

**维护者**: Rust 学习项目
**最后更新**: 2026-05-09

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

## 📚 模块 8: 国际化对齐

> 本模块按项目模板补充国际化权威来源：官方文档、学术论文/工业报告、社区权威资源。

### 8.1 官方来源

| 来源 | 说明 |
|:---|:---|
| [Rustonomicon](https://doc.rust-lang.org/nomicon/) | Unsafe Rust 权威指南 |
| [Rust Reference — Unsafe Blocks](https://doc.rust-lang.org/reference/unsafe-blocks.html) | unsafe 块规范 |
| [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html) | UB 列表 |

### 8.2 学术/工业来源

| 来源 | 说明 |
|:---|:---|
| [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Unsafe 边界语义 |
| [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | 别名模型 |

### 8.3 社区资源

| 来源 | 说明 |
|:---|:---|
| [Rust for Linux](https://rust-for-linux.com/) | 内核 Unsafe 实践 |
| [Miri](https://github.com/rust-lang/miri) | UB 检测工具 |
