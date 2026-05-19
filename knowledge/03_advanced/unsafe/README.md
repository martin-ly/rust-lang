# Unsafe Rust

> **Unsafe Rust：原始指针、FFI、内联汇编、MaybeUninit**

## 📚 内容

| 文档 | 主题 | 难度 |
|------|------|------|
| [unsafe_rust.md](unsafe_rust.md) | Unsafe Rust 基础与安全抽象 | ⭐⭐⭐⭐ |
| [ffi.md](ffi.md) | 外部函数接口 (FFI) | ⭐⭐⭐⭐ |
| [maybe_uninit.md](maybe_uninit.md) | 未初始化内存管理 | ⭐⭐⭐⭐ |
| [inline_asm.md](inline_asm.md) | 内联汇编 | ⭐⭐⭐⭐⭐ |

## 🎯 学习路径

1. **Unsafe 基础** → [unsafe_rust.md](unsafe_rust.md)
2. **C 互操作** → [ffi.md](ffi.md)
3. **未初始化内存** → [maybe_uninit.md](maybe_uninit.md)
4. **底层优化** → [inline_asm.md](inline_asm.md)

## ⚠️ 安全提醒

> 所有 unsafe 代码必须经过 Miri 验证和人工审计。每段 `unsafe` 块必须附带 `// SAFETY:` 注释。

## 🚀 相关层

- [04_expert/unsafe_audit.md](../../04_expert/unsafe_audit.md) - Unsafe 代码审计方法论
- [04_expert/tree_borrows.md](../../04_expert/tree_borrows.md) - 别名模型与内存规则

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
