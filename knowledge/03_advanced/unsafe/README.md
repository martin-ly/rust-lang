# Unsafe Rust

> **EN**: Unsafe Rust
> **Summary**: Unsafe Rust knowledge index: raw pointers, FFI, MaybeUninit, inline assembly, and safety abstraction design.

Unsafe 子域速查入口。

- **核心概念**: `unsafe` 块、原始指针、FFI、MaybeUninit、内联汇编
- **安全实践**: 每段 `unsafe` 块必须附带 `// SAFETY:` 注释，建议用 Miri 验证
- **后续延伸**: Unsafe 代码审计、Tree Borrows / Stacked Borrows 别名模型

> **权威来源**: [Unsafe Rust 安全编程 — concept/03_advanced/02_unsafe/03_unsafe.md](../../../concept/03_advanced/02_unsafe/03_unsafe.md)
> **参考规范**: [Unsafe 参考 — concept/03_advanced/02_unsafe/35_unsafe_reference.md](../../../concept/03_advanced/02_unsafe/35_unsafe_reference.md)
