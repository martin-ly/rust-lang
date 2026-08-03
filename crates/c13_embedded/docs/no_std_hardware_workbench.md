> **EN**: no_std Hardware Workbench (probe-rs / QEMU / RTT)
> **Summary**: A crate-local guide to building, flashing, and debugging no_std Rust on ARM Cortex-M using probe-rs, cargo-embed, QEMU, and defmt/RTT logging.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4

# no_std 硬件实测工作台（probe-rs / QEMU / RTT）

> **权威来源**: 通用 Rust 概念解释统一维护在
> [`concept/06_ecosystem/05_systems_and_embedded/23_no_std_and_bare_metal_idioms.md`](../../../concept/06_ecosystem/05_systems_and_embedded/23_no_std_and_bare_metal_idioms.md)。
> 本文件为 `crates/c13_embedded/` 的本地操作指南。

---

## 目录

- [前置准备](#前置准备)
- [相关文件](#相关文件)
- [Host 编译检查](#host-编译检查)
- [QEMU 仿真运行](#qemu-仿真运行)
- [真实硬件：probe-rs 烧录与 RTT 日志](#真实硬件probe-rs-烧录与-rtt-日志)
- [defmt 零开销日志](#defmt-零开销日志)
- [cargo-embed 一体化工作流](#cargo-embed-一体化工作流)
- [常见问题](#常见问题)

---

## 前置准备

安装以下工具（以 Ubuntu/WSL/macOS 为例，Windows 可用 `winget` 或 `cargo install`）：

```bash
# Rust 目标（ARM Cortex-M3/M4/M7 无浮点/硬浮点）
rustup target add thumbv7m-none-eabi thumbv7em-none-eabihf

# probe-rs 工具链：烧录、调试、RTT 日志
cargo install probe-rs-tools --locked
# 或仅安装库/CLI（旧版）：cargo install probe-rs --locked

# cargo-embed：基于 Embed.toml 的一体化工作流
cargo install cargo-embed --locked

# QEMU（host 包管理器）
# Ubuntu/Debian
sudo apt-get install qemu-system-arm
# macOS
brew install qemu
# Windows
winget install QEMU.QEMU
```

连接真实开发板（例如 STM32F4DISCOVERY / Nucleo-F446RE）并通过 USB 暴露调试器
（CMSIS-DAP、ST-Link 或 J-Link）。

---

## 相关文件

| 文件 | 作用 |
|:---|:---|
| [`../examples/no_std_qemu_blinky.rs`](../examples/no_std_qemu_blinky.rs) | 最小 ARM Cortex-M blinky，可在 QEMU 运行 |
| [`../examples/no_std_defmt_rtt.rs`](../examples/no_std_defmt_rtt.rs) | `defmt` + RTT 日志骨架（需取消注释目标依赖） |
| [`../build.rs`](../build.rs) | 为 ARM/RISC-V 目标自动生成 `memory.x` |
| [`../Cargo.toml`](../Cargo.toml) | 目标依赖表；`defmt` 相关依赖默认注释 |

---

## Host 编译检查

在 x86_64 Windows/Linux 主机上，先确认 workspace 级检查通过：

```bash
cargo check --workspace
```

预期输出（片段）：

```text
    Checking c13_embedded v3.1.0 (E:/_src/rust-lang/crates/c13_embedded)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in ...
```

`no_std_qemu_blinky.rs` 与 `no_std_defmt_rtt.rs` 在 host 目标下使用占位 `main`，
不会拉取 ARM 专用依赖，因此 host 检查不会失败。

---

## QEMU 仿真运行

### 1. 交叉编译

```bash
cargo build -p c13_embedded --target thumbv7m-none-eabi --example no_std_qemu_blinky
```

预期输出（片段）：

```text
   Compiling c13_embedded v3.1.0 (E:/_src/rust-lang/crates/c13_embedded)
    Finished `dev` profile [unoptimized + debuginfo] target(s) in ...
```

> **链接脚本说明**：本 crate 的 `build.rs` 检测到 `target_arch = "arm"` 时，会在
> `OUT_DIR` 自动生成 `memory.x` 并加入链接器搜索路径，因此无需手动放置链接脚本。
> 在自己的项目中，需要将 `memory.x` 放在 crate 根目录，或在 `build.rs` 中调用
> `println!("cargo:rustc-link-search={}", out_dir)`。

### 2. QEMU 启动

```bash
qemu-system-arm -cpu cortex-m3 -machine stm32-f103c8 -nographic \
  -kernel target/thumbv7m-none-eabi/debug/examples/no_std_qemu_blinky
```

预期现象：

- 若镜像链接成功，QEMU 不会打印任何错误即进入无限循环。
- 在真实 STM32F103 上，PA5 LED 会以软件延时闪烁。
- 按 `Ctrl-A` 然后 `X` 退出 QEMU。

> **调试模式**：加上 `-S -s` 让 QEMU 启动时暂停并开启 GDB server（端口 1234）：
> ```bash
> qemu-system-arm -cpu cortex-m3 -machine stm32-f103c8 -nographic -S -s \
>   -kernel target/thumbv7m-none-eabi/debug/examples/no_std_qemu_blinky
> ```
> 随后可用 `arm-none-eabi-gdb` 或 `gdb-multiarch` 连接单步调试。

---

## 真实硬件：probe-rs 烧录与 RTT 日志

### 1. 列出已连接调试器与芯片

```bash
probe-rs list
probe-rs chip list | grep -i stm32f407
```

### 2. 烧录并运行

```bash
probe-rs run --chip STM32F407VG \
  target/thumbv7m-none-eabi/debug/examples/no_std_qemu_blinky
```

预期输出（片段，无 RTT 时）：

```text
     Erasing sectors ✔ [00:00:00] [##########] 16.00 KiB/16.00 KiB @ 45.00 KiB/s (eta 0s )
 Programming pages   ✔ [00:00:00] [##########] 16.00 KiB/16.00 KiB @ 30.00 KiB/s (eta 0s )
    Finished in 0.5s
```

若固件中包含 RTT 输出（见下一节 `defmt`），`probe-rs run` 会自动附加 RTT 并打印日志。

---

## defmt 零开销日志

[`defmt`](https://defmt.ferrous-systems.com/) 通过“延迟格式化”把日志体积降到最小：
目标端只传输原始数据，格式字符串与解析留在 host 端完成。

### 启用步骤

1. 在 `crates/c13_embedded/Cargo.toml` 的 ARM 目标依赖段取消注释：

   ```toml
   [target.'cfg(target_arch = "arm")'.dependencies]
   defmt = "0.3"
   defmt-rtt = "0.4"
   panic-probe = { version = "0.3", features = ["print-defmt"] }
   ```

2. 在 crate 根启用默认 feature：

   ```toml
   [features]
   default = ["defmt-default"]
   ```

3. 确保链接脚本包含 `defmt.x`。本 crate 的 `build.rs` 生成的 `memory.x` 可与
   `cortex-m-rt` 的 `link.x` 一起工作；使用 `defmt` 时还需追加：

   ```rust,ignore
   // build.rs
   fn main() {
       // ... 现有 memory.x 生成逻辑 ...
       println!("cargo:rustc-link-arg=-Tdefmt.x");
   }
   ```

4. 代码示例见 [`../examples/no_std_defmt_rtt.rs`](../examples/no_std_defmt_rtt.rs)。

### 编译与运行

```bash
cargo build -p c13_embedded --target thumbv7em-none-eabihf --example no_std_defmt_rtt
probe-rs run --chip STM32F407VG \
  target/thumbv7em-none-eabihf/debug/examples/no_std_defmt_rtt
```

预期 RTT 输出：

```text
INFO  booting, version=1
DEBUG sensor reading: 42
```

---

## cargo-embed 一体化工作流

`cargo-embed` 读取项目根目录的 `Embed.toml`，把烧录、RTT、GDB 集成到一条命令：

```toml
# Embed.toml
[default.probe]
protocol = "Swd"

[default.flashing]
enabled = true

[default.rtt]
enabled = true

[default.gdb]
enabled = false
```

运行：

```bash
cd crates/c13_embedded
cargo embed --release --example no_std_defmt_rtt --target thumbv7em-none-eabihf
```

预期输出：自动完成擦除、编程并持续打印 RTT/defmt 日志。

---

## 常见问题

| 现象 | 根因 | 修复 |
|:---|:---|:---|
| `error: linker `rust-lld` not found` | 未安装 `rust-lld`（通常随 stable 提供） | `rustup component add rust-src` 并启用 `build-std` |
| `undefined reference to `__CxxFrameHandler3'` / `rust_eh_personality` | panic 策略为 `unwind` | 在 `.cargo/config.toml` 或 `Cargo.toml` 中设置 `panic = "abort"` |
| `memory.x: No such file or directory` | `cortex-m-rt` 找不到链接脚本 | 放置 `memory.x` 到 crate 根，或让 `build.rs` 写入 `OUT_DIR` 并 `rustc-link-search` |
| `probe-rs` 找不到芯片 | 芯片名称拼写错误或调试器未连接 | 使用 `probe-rs chip list` 确认；检查 USB 驱动 |
| RTT 没有输出 | 固件未初始化 `defmt-rtt` 或 `Embed.toml` 未启用 RTT | 确认 `use defmt_rtt as _;` 且 `[default.rtt] enabled = true` |

---

## 国际权威来源

- [The Embedded Rust Book](https://docs.rust-embedded.org/book/) — Rust Embedded Working Group 官方指南
- [probe.rs 文档](https://probe.rs/docs/) — 调试与烧录工具链
- [defmt Book](https://defmt.ferrous-systems.com/) — 零开销日志框架
- [QEMU ARM 文档](https://www.qemu.org/docs/master/system/target-arm.html)
