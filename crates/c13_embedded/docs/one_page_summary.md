> **EN**: c13 Embedded Systems One-Page Summary (c13_embedded example index)
> **Summary**: Stub one-page summary pointing to the canonical concept authority for Rust embedded systems. Common target triples and learning path migrated to the authority page.

# C13 嵌入式系统 - 一页纸总结

> **权威来源**: `no_std`、裸机编程、内存映射寄存器、硬件抽象层（PAC/HAL/BSP）、实时系统、Embassy 等完整解释见
> [`concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md`](../../../concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md)。

本文件原为 `c13_embedded` crate 的通用嵌入式系统速查。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/06_ecosystem/05_systems_and_embedded/`，此处仅保留索引与
canonical 链接。具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| Rust 嵌入式系统开发 | [`concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md`](../../../concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md) |
| 常见目标三元组与学习路径 | [`concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md#六常见嵌入式目标三元组与学习路径`](../../../concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md) |
| 交叉编译 | [`concept/06_ecosystem/05_systems_and_embedded/17_cross_compilation.md`](../../../concept/06_ecosystem/05_systems_and_embedded/17_cross_compilation.md) |

## 主题列表

- `no_std` 与 `core` / `alloc`
- 内存映射 I/O（MMIO）
- UART 串口通信
- 中断与中断向量表
- 硬件抽象层（HAL）与类型状态模式
- FFI 与 C 互操作
- RTIC 实时中断驱动框架
- Embassy 异步嵌入式框架
- 常见嵌入式目标三元组
- 入门 → 进阶 → 高级学习路径
