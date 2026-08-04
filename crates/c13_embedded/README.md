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
- **ARM Cortex-M4F**: `thumbv7em-none-eabihf`（如 STM32F4 / Nucleo-F446RE）
- **ARM Cortex-M33**: `thumbv8m.main-none-eabihf`（如 STM32H5 / STM32L5，可选验证目标）
- **RISC-V**: `riscv32imac-unknown-none-elf`（通用 32-bit RISC-V MCU，如 SiFive FE310 / GD32VF103）
- **ESP32-C3 (RISC-V no_std)**: `riscv32imc-unknown-none-elf`（ESP32-C3 等 RISC-V 内核 Espressif 芯片，通过 `esp-hal` 构建）
- **AArch64 裸机**: `aarch64-unknown-none-softfloat`（ARM Cortex-A 裸机，如 QEMU `virt`）
- **WebAssembly 裸机**: `wasm32-unknown-unknown`（无标准库 WebAssembly 目标）
- **ESP32-C3/C6 (ESP-IDF std)**: `riscv32imc-esp-espidf` / `riscv32imac-esp-espidf` — **待验证**（当前 Windows 上 `stable-x86_64-pc-windows-msvc` 工具链没有该 target 的预构建产物，无法通过 `rustup target add` 安装）

## 功能特性

| Feature | 说明 |
|:---|:---|
| `embedded` | 启用 ARM 目标硬件相关代码路径 |
| `cxx-interop` | 启用 C++ 互操作支持 |
| `esp32c3-hal` | 启用 ESP32-C3 `esp-hal` / `esp-println` 示例依赖 |

## 硬件依赖（ARM 目标）

- `cortex-m`: ARM Cortex-M 核心支持
- `cortex-m-rt`: 启动与异常处理
- `panic-halt`:  panic 处理策略
- `volatile-register`: 内存映射寄存器访问

## 硬件依赖（AArch64 目标）

- `aarch64-cpu`: AArch64 核心寄存器与屏障原语访问
- `tock-registers`: 类型安全的内存映射寄存器定义
- `panic-halt`: panic 处理策略

## 硬件依赖（WebAssembly 目标）

- `panic-halt`: panic 处理策略（WebAssembly 裸机目标无 std，需要显式 panic handler）

## 可编译示例

### Host 可编译 / 裸机骨架

- [最小 bare-metal 程序](examples/minimal_bare_metal.rs)
- [QEMU 演示](examples/qemu_demo.rs)
- [自定义 bare-metal async executor](examples/custom_async_executor.rs)
- [自定义 bump allocator](examples/custom_allocator.rs)

### 真实目标可编译

- [ARM Cortex-M 最小 blinky](examples/cortex_m_minimal_blinky.rs) — `thumbv7em-none-eabihf`
- [ARM Cortex-M33 最小入口](examples/thumbv8m_minimal_main.rs) — `thumbv8m.main-none-eabihf`
- [RISC-V 最小 blinky](examples/riscv_minimal_blinky.rs) — `riscv32imac-unknown-none-elf`
- [AArch64 裸机最小入口](examples/aarch64_minimal_main.rs) — `aarch64-unknown-none-softfloat`
- [WebAssembly 裸机最小入口](examples/wasm_minimal_main.rs) — `wasm32-unknown-unknown`
- [no_std QEMU blinky](examples/no_std_qemu_blinky.rs) — `thumbv7m-none-eabi`（可在 QEMU 运行）
- [no_std defmt + RTT 日志骨架](examples/no_std_defmt_rtt.rs) — `thumbv7em-none-eabihf`（需取消注释目标依赖）

编译命令：

```bash
# ARM Cortex-M4F
cargo build -p c13_embedded --target thumbv7em-none-eabihf --example cortex_m_minimal_blinky

# ARM Cortex-M33
cargo build -p c13_embedded --target thumbv8m.main-none-eabihf --example thumbv8m_minimal_main

# ARM Cortex-M3 (QEMU 兼容)
cargo build -p c13_embedded --target thumbv7m-none-eabi --example no_std_qemu_blinky

# RISC-V
cargo build -p c13_embedded --target riscv32imac-unknown-none-elf --example riscv_minimal_blinky

# AArch64 裸机
cargo build -p c13_embedded --target aarch64-unknown-none-softfloat --example aarch64_minimal_main

# WebAssembly 裸机
cargo build -p c13_embedded --target wasm32-unknown-unknown --example wasm_minimal_main
```

## ESP32-IDF 支持状态（待验证）

计划在 `crates/c13_embedded` 中增加 ESP-IDF（`std`）目标支持，预期使用：

- `riscv32imc-esp-espidf`（ESP32-C3）
- `riscv32imac-esp-espidf`（ESP32-C6 / 更高性能 RISC-V 内核，若工具链提供）

当前状态：**工具链不可用**。在 Windows 上执行 `rustup target add riscv32imc-esp-espidf` 与 `rustup target add riscv32imac-esp-espidf` 均返回：

```text
error: toolchain 'stable-x86_64-pc-windows-msvc' has no prebuilt artifacts available for target '...-esp-espidf'
```

因此尚未添加 `esp-idf-svc` / `esp-idf-hal` / `esp-idf-sys` 依赖、`.cargo/config.toml` runner 配置及示例。待后续在支持该 target 的环境（如 Linux + `espup` 或 Espressif 自定义 Rust 工具链）中验证后再补齐：

- `Cargo.toml` 中按 `target_os = "espidf"` 添加条件依赖
- `.cargo/config.toml` 中追加 ESP-IDF target 的 runner / link 参数
- `examples/esp32_minimal_main.rs` 最小 ESP-IDF 入口示例
- 在对应目标上执行 `cargo build --target riscv32imc-esp-espidf -p c13_embedded`

本状态记录不影响现有 host / ARM / RISC-V 裸机构建。

## no_std 硬件实测工作台

- [no_std 硬件实测工作台指南](docs/05_no_std_hardware_workbench.md) — probe-rs / QEMU / RTT / defmt 完整流程

## 文档

- [完整索引](docs/00_meta/00_master_index.md)
- [RTIC 实时框架示例](src/rtic_framework.rs)
- [HAL 设计模式](src/hal_design_patterns.rs)

## [来源: The Embedded Rust Book / Rust Embedded Working Group](https://docs.rust-embedded.org/book/)
