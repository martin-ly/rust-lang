# C07 实践示例集

> **文档定位**: 实践示例导航
> **最后更新**: 2026-02-13
> **说明**: 实践示例已整合至 tier 系列文档

---

## 快速导航

| 文档 | 说明 |
| :--- | :--- |
| [06_代码示例集合](../tier_02_guides/06_代码示例集合.md) | 代码示例集合（Tier 1-2 基础与实践） |
| [07_实战项目集](../tier_02_guides/07_实战项目集.md) | 实战项目集 |
| [01_进程模型参考](../tier_03_references/01_进程模型参考.md) | std::process 深入 |
| [02_IPC机制参考](../tier_03_references/02_IPC机制参考.md) | IPC 通信进阶 |
| [05_性能优化参考](../tier_03_references/05_性能优化参考.md) | 性能优化实践 |
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

**相关**: [README](../README.md) | [00_MASTER_INDEX](../00_MASTER_INDEX.md)
