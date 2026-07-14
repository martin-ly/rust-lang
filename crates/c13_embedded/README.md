> **权威来源**: 本文件为 `crates/c13_embedded/` 的 crate 入口页。
> 通用 Rust 概念解释统一维护在 `concept/` 中；详见 [../../concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md](../../concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md)。
>
> 根据 AGENTS.md §2 Canonical 规则，`crates/` 不重复通用 Rust 概念解释；
> 如需深入学习，请前往 `concept/` 权威页。
>
# C13: Rust 嵌入式系统 (Embedded Systems)

## 概述

本 crate 提供 Rust 裸机嵌入式系统（Bare-metal Embedded）学习模块，涵盖：

- **无标准库编程 (`no_std`)**: 内存约束环境下的 Rust
- **硬件抽象层 (HAL)**: 寄存器映射与外设抽象
- **实时框架 (RTIC)**: 实时中断驱动并发
- **FFI 与 C 互操作**: 与现有嵌入式 C 代码集成
- **构建系统**: `build.rs` 与链接脚本配置

## 目标平台

- **Host**: `x86_64`（模拟/文档构建）
- **目标**: `thumbv7em-none-eabihf`（ARM Cortex-M4/M7）

## 功能特性

| Feature | 说明 |
|:---|:---|
| `embedded` | 启用 ARM 目标硬件相关代码路径 |
| `cxx-interop` | 启用 C++ 互操作支持 |

## 硬件依赖（ARM 目标）

- `cortex-m`: ARM Cortex-M 核心支持
- `cortex-m-rt`: 启动与异常处理
- `panic-halt`:  panic 处理策略
- `volatile-register`: 内存映射寄存器访问

## 文档

- [完整索引](docs/00_meta/00_master_index.md)
- [RTIC 实时框架示例](src/rtic_framework.rs)
- [HAL 设计模式](src/hal_design_patterns.rs)

## [来源: The Embedded Rust Book / Rust Embedded Working Group](https://docs.rust-embedded.org/book/)
