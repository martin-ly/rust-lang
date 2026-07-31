# Bare-metal Minimal — 多目标真实硬件最小示例

本目录包含一个**不依赖任何异步框架或 RTOS** 的最小 `no_std` / `no_main` 程序，可在真实 ARM Cortex-M 与 RISC-V 嵌入式目标上交叉编译。

> **设计目标**：验证 Rust 工具链、链接脚本与运行时（`cortex-m-rt` / `riscv-rt`）在真实目标上的最小可用性，作为更复杂示例（RTIC、Embassy）之前的基线。

---

## 支持的编译目标

| 目标三元组 | 架构 | 典型芯片/板卡 |
|---|---|---|
| `thumbv6m-none-eabi` | ARM Cortex-M0/M0+ | Raspberry Pi Pico (RP2040) |
| `thumbv7em-none-eabihf` | ARM Cortex-M4F | STM32F4 Discovery / Nucleo-F446 |
| `riscv32imac-unknown-none-elf` | RISC-V 32-bit IMAC | GD32VF103 / ESP32-C3 |

---

## 前置要求

```bash
rustup target add thumbv6m-none-eabi thumbv7em-none-eabihf riscv32imac-unknown-none-elf
```

---

## 编译

```bash
cd crates/c13_embedded/real-hardware-demos/bare-metal-minimal

# ARM Cortex-M0+
cargo build --release --target thumbv6m-none-eabi

# ARM Cortex-M4F
cargo build --release --target thumbv7em-none-eabihf

# RISC-V 32 IMAC
cargo build --release --target riscv32imac-unknown-none-elf
```

---

## 目录结构

```text
bare-metal-minimal/
├── .cargo/config.toml   # 各目标的链接脚本与 rustflags
├── Cargo.toml           # 目标条件依赖
├── memory.x             # RISC-V 链接脚本内存布局
└── src/main.rs          # 条件编译的 ARM / RISC-V 入口
```

---

## 注意事项

- 本示例**不包含真实硬件外设初始化**（时钟、GPIO、UART 等），仅保证可链接为有效 ELF。
- ARMv6-M 目标中 `AtomicU32::fetch_add` 不可用，示例使用 `load`/`store` 实现计数；如需原子递增请在临界区内执行。
- RISC-V 的 `memory.x` 使用通用地址与大小，烧录到具体芯片前请按数据手册修改。

---

> **权威来源**: [The Embedded Rust Book](https://docs.rust-embedded.org/book/), [cortex-m-rt](https://docs.rs/cortex-m-rt/), [riscv-rt](https://docs.rs/riscv-rt/)

**文档版本**: 1.0
**对应 Rust 版本**: 1.97.0+ (Edition 2021)
**最后更新**: 2026-08-01
