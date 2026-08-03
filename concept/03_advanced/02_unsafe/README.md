# Unsafe Rust 专题

> **EN**: Unsafe Rust Topic Index
> **Bloom 层级**: L3-L4
> **Summary**: Directory index for `concept/03_advanced/02_unsafe/` — unsafe blocks, safety contracts, memory model, sanitizers, std unsafe internals, and in-place / pinned initialization patterns.

> **权威来源**: 本目录为 `concept/03_advanced/02_unsafe/` 专题目录。
> **受众**: [专家]
> **内容分级**: [综述级]

## 文件索引

| 文件 | 概念 | 核心内容 |
|:---|:---|:---|
| [00_before_formal.md](00_before_formal.md) | 形式化前置 | 阅读 L4 形式化前的数学与 Rust 基础 |
| [01_unsafe.md](01_unsafe.md) | Unsafe Rust | `unsafe` 块、五 superpowers、UB 分类、safety contract |
| [02_unsafe_boundary_panorama.md](02_unsafe_boundary_panorama.md) | Unsafe 边界全景 | `unsafe` 边界的系统梳理与审计方法 |
| [03_nll_and_polonius.md](03_nll_and_polonius.md) | NLL / Polonius | 非词法生命周期、数据流分析 |
| [04_unsafe_rust_patterns.md](04_unsafe_rust_patterns.md) | Unsafe 模式 | 安全抽象的核心 unsafe 模式 |
| [05_quiz_unsafe.md](05_quiz_unsafe.md) | 测验 | Unsafe Rust 嵌入式测验 |
| [06_memory_model.md](06_memory_model.md) | 内存模型 | 抽象字节、未初始化内存、Tree Borrows |
| [07_unsafe_reference.md](07_unsafe_reference.md) | Unsafe 参考手册 | 速查与决策参考 |
| [08_async_in_unsafe_contexts.md](08_async_in_unsafe_contexts.md) | Async × Unsafe | 异步上下文中的 unsafe 使用 |
| [09_sanitizers.md](09_sanitizers.md) | 检测工具 | Miri / ASan / MSan / KCSan 使用指南 |
| [10_std_unsafe_internals.md](10_std_unsafe_internals.md) | 标准库 unsafe 内部实现 | Vec / HashMap / UnsafeCell / MaybeUninit |
| [11_in_place_pinned_initialization.md](11_in_place_pinned_initialization.md) | 原地与固定初始化 | `MaybeUninit`、std in-place API、`PhantomPinned`、`pin-init` / `zeroize` |

## 跨层关联

- **前置**: [L1 所有权与借用](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) · [L2 内存管理](../../02_intermediate/02_memory_management/01_memory_management.md) · [L2 Pin 与自引用](../01_async/08_pin_unpin.md)
- **形式化 companion**: [原地初始化的操作语义](../../04_formal/03_operational_semantics/13_in_place_initialization_semantics.md)
- **后置**: [FFI](../04_ffi/01_rust_ffi.md) · [L4 RustBelt](../../04_formal/02_separation_logic/01_rustbelt.md)
