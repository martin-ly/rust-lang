> **EN**: c13 Embedded Systems Documentation Guide (c13_embedded example index)
> **Summary**: A stub page pointing to the canonical concept authority for Rust embedded systems. The c13_embedded crate provides no_std, MMIO, UART, interrupt handling, HAL, FFI, RTIC and Embassy examples.

# c13 嵌入式系统 - 文档指南

> **权威来源**: `no_std`、裸机编程、内存映射寄存器、硬件抽象层（PAC/HAL/BSP）、实时系统、Embassy 等完整解释见
> [`concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md`](../../../concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md)。

本文件原为 `c13_embedded` crate 的通用嵌入式系统概念教程。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/06_ecosystem/05_systems_and_embedded/`，此处仅保留索引与
canonical 链接。具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 本 crate 相关文档

- [完整索引](00_master_index.md)
- [一页纸总结](04_one_page_summary.md)
- [裸机基础指南](01_bare_metal_guide.md)
- [build-std 与自定义目标](02_build_std_guide.md)
- [embedded-hal 1.0 迁移指南](03_embedded_hal_1_0_migration.md)

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| Rust 嵌入式系统开发 | [`concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md`](../../../concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md) |
| 交叉编译 | [`concept/06_ecosystem/05_systems_and_embedded/02_cross_compilation.md`](../../../concept/06_ecosystem/05_systems_and_embedded/02_cross_compilation.md) |
| Unsafe Rust | [`concept/03_advanced/02_unsafe/01_unsafe.md`](../../../concept/03_advanced/02_unsafe/01_unsafe.md) |

## 主题列表

- `no_std` 环境、启动流程与链接脚本
- 内存映射 I/O（MMIO）与 UART 驱动
- 中断处理与临界区
- 硬件抽象层（HAL）与类型状态模式
- FFI 与 C 代码 / 链接脚本互操作
- RTIC 实时中断驱动框架
- Embassy 异步嵌入式框架
