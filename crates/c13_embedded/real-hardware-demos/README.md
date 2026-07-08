# C13 Embedded — 真实硬件演示

本目录包含可在真实嵌入式硬件上编译运行的 Embassy 和 RTIC 示例。

> ⚠️ **重要**: 这些示例需要 ARM Cortex-M 交叉编译工具链，**不在**主 workspace 中注册，避免影响 host 环境 (`cargo check --workspace`)。

---

## 目录结构

```text
real-hardware-demos/
├── README.md                 # 本文件
├── embassy-demo/             # Embassy 异步框架示例 (RP2040)
│   ├── Cargo.toml
│   ├── .cargo/config.toml
│   └── src/main.rs
└── rtic-demo/                # RTIC 实时中断框架示例 (STM32F4)
│   ├── Cargo.toml
│   ├── .cargo/config.toml
│   └── src/main.rs
```

---

## 前置要求

### 1. 安装 Rust 交叉编译目标

```bash
# Embassy (RP2040 - ARM Cortex-M0+)
rustup target add thumbv6m-none-eabi

# RTIC (STM32F4 - ARM Cortex-M4F)
rustup target add thumbv7em-none-eabihf
```

### 2. 安装依赖工具

```bash
# 调试工具
cargo install probe-rs-tools --locked

# ELF 分析
cargo install cargo-binutils
rustup component add llvm-tools-preview
```

### 3. 硬件准备

| 示例 | 开发板 | 连接方式 |
|------|--------|---------|
| `embassy-demo` | Raspberry Pi Pico / Pico W | USB + SWD (debug probe) |
| `rtic-demo` | STM32F407 Discovery / Nucleo-F446 | USB + ST-Link |

---

## Embassy 示例 (`embassy-demo/`)

基于 [Embassy](https://embassy.dev/) 异步框架的 RP2040 LED 闪烁示例。

### 编译

```bash
cd embassy-demo
cargo build --release
```

### 烧录

```bash
# 使用 probe-rs (推荐)
cargo run --release

# 或使用 elf2uf2-rs (Pico 专用)
cargo install elf2uf2-rs --locked
cargo objcopy --release -- -O binary firmware.bin
# 按住 BOOTSEL 连接 USB，复制 firmware.bin 到 RPI-RP2 磁盘
```

### 功能

- 异步 LED 闪烁（300ms 间隔）
- 使用 `embassy-executor` 单线程调度器
- 零开销 async/await 抽象

---

## RTIC 示例 (`rtic-demo/`)

基于 [RTIC](https://rtic.rs/) 框架的 STM32F4 LED 闪烁示例。

### 编译

```bash
cd rtic-demo
cargo build --release
```

### 烧录

```bash
# 使用 probe-rs
cargo run --release

# 或使用 OpenOCD + GDB
openocd -f interface/stlink.cfg -f target/stm32f4x.cfg
arm-none-eabi-gdb target/thumbv7em-none-eabihf/release/rtic-demo
```

### 功能

- 硬件定时器中断驱动的 LED 闪烁
- 利用 NVIC 优先级实现零成本调度
- 编译期资源互斥保证

---

## 与概念代码的关系

`crates/c13_embedded/src/` 中的 `embassy_framework.rs` 和 `rtic_framework.rs` 保留为**理论学习**材料（host 可编译、可阅读）。

`real-hardware-demos/` 中的代码是**动手实践**材料（需要真实硬件或 QEMU 模拟器）。

---

## 常见问题

### Q: 这些示例能在 host (x86_64) 上编译吗？

**不能**。 Embassy 和 RTIC 依赖 ARM Cortex-M 专用的 PAC (Peripheral Access Crate) 和 HAL。在 host 上编译会报错：

```
error: could not compile `cortex-m-rt` (lib) due to 2 previous errors
```

这是预期行为。如需在 host 上验证语法，可使用 `cargo check --target thumbv6m-none-eabi` 等交叉编译目标。

### Q: 我没有硬件，能测试吗？

可以安装 QEMU 进行模拟：

```bash
# ARM Cortex-M 模拟
cargo install cargo-embed
# 或使用 QEMU
cargo run --release --features qemu
```

（具体 QEMU 配置请参考各框架官方文档。）

---

## 参考

- [Embassy Book](https://embassy.dev/book/)
- [RTIC Book](https://rtic.rs/2/book/en/)
- [The Embedded Rust Book](https://docs.rust-embedded.org/book/)
- [probe.rs 文档](https://probe.rs/docs/)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
