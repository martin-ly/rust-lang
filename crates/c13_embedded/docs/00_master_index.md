> **EN**: c13 Embedded Systems Master Index (c13_embedded example index)
> **Summary**: Stub master index pointing to the canonical concept authority for Rust embedded systems. Lists crate docs and source modules.

# c13 嵌入式系统 - 主索引

> **权威来源**: `no_std`、裸机编程、内存映射寄存器、硬件抽象层（PAC/HAL/BSP）、实时系统、Embassy 等完整解释见
> [`concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md`](../../../concept/06_ecosystem/05_systems_and_embedded/22_embedded_systems.md)。

本文件原为 `c13_embedded` crate 的通用嵌入式系统主索引。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/06_ecosystem/05_systems_and_embedded/`，此处仅保留索引与
canonical 链接。具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 文档导航

- [c13 嵌入式系统 - 文档指南](README.md)
- [一页纸总结](one_page_summary.md)
- [裸机基础指南](bare_metal_guide.md)
- [build-std 与自定义目标](build_std_guide.md)
- [embedded-hal 1.0 迁移指南](embedded_hal_1_0_migration.md)

## 主题列表

- `no_std`、启动流程、链接脚本
- 内存映射 I/O（MMIO）与外设寄存器访问
- UART 通用异步收发器
- 中断与中断向量表
- 硬件抽象层（HAL）trait 与迁移实践
- FFI 与 C 代码 / 链接脚本互操作
- RTIC 实时中断驱动框架
- Embassy 异步嵌入式框架
