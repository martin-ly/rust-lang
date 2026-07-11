# C07 实践示例集

> **权威来源**: [Processes & IPC](../../../../concept/03_advanced/08_process_ipc)
> **文档类型**: 代码示例 / 实践项目 / 教程（crate-specific）

本文件包含与 `Processes & IPC` 相关的可运行代码示例、练习项目或教程步骤。通用概念解释请查阅上方权威来源；此处仅保留 crate 级别的示例实现与学习活动。

---

> **生态状态提示**：
>
> 本文档提及 `async-std` 与/或 `wasm32-wasi`。请注意：
>
> - `async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。

---

# C07 实践示例集

> **文档定位**: 实践示例导航
> **最后更新**: 2026-02-13
> **说明**: 实践示例已整合至 tier 系列文档

---

## 快速导航

| 文档 | 说明 |
| :--- | :--- |
| [06_代码示例集合](../tier_02_guides/06_code_examples.md) | 代码示例集合（Tier 1-2 基础与实践） |
| [07_实战项目集](../tier_02_guides/07_hands_on_projects.md) | 实战项目集 |
| [01_进程模型参考](../tier_03_references/01_process_models_reference.md) | std::process 深入 |
| [02_IPC机制参考](../tier_03_references/02_ipc_mechanisms_reference.md) | IPC 通信进阶 |
| [05_性能优化参考](../tier_03_references/05_performance_optimization_reference.md) | 性能优化实践 |
| [async_stdio_guide](../async_stdio_guide.md) | 异步标准 IO 指南 |

---

## 运行 bin 示例

```bash
cd crates/c07_process
cargo run --bin process_demo
cargo run --bin ipc_demo
cargo run --bin async_demo
cargo run --bin async_stdio_demo   # 需 --features async（默认已启用）
cargo run --bin sync_demo
cargo run --bin process_pool_demo
```

---

**相关**: [README](../README.md) | [00_MASTER_INDEX](../00_master_index.md)
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
