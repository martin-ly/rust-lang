# Rust 对齐知识综合指南 (Alignment Guide) {#rust-对齐知识综合指南}

> **EN**: Alignment Guide
> **Summary**: Rust 对齐知识综合指南 Alignment Guide.

> **权威来源**: 本文件为 docs/ 参考重定向 stub，完整概念解释请见：
> [`concept/01_foundation/02_type_system/01_type_system.md`](../../concept/01_foundation/02_type_system/01_type_system.md)
>
> 根据 AGENTS.md §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> `docs/` 仅保留应用场景、决策树与链接。

## 对齐选型决策树

```text
需要控制内存布局？
├─ 否 → 使用默认 #[repr(Rust)]
└─ 是
   ├─ 与 C/FFI 交互？ → #[repr(C)]
   ├─ 需要紧凑无填充（如协议解析）？ → #[repr(packed)] 或 #[repr(packed(N))]
   ├─ 需要 newtype 与内层同布局？ → #[repr(transparent)]
   ├─ 多线程共享、避免伪共享？ → #[repr(align(64))] + 填充
   └─ 组合需求？ → #[repr(C, align(N))]
```
