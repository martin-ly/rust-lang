# Bare-Metal 嵌入式 Rust 学习指南

> 本指南为 rust-lang 学习项目的 C13 Embedded 模块配套文档，
> 覆盖 no_std 开发、内存映射寄存器、驱动设计、中断处理、HAL 模式和 C 互操作。

---

## 目录

- [Bare-Metal 嵌入式 Rust 学习指南](#bare-metal-嵌入式-rust-学习指南)
  - [目录](#目录)
  - [学习路径](#学习路径)
    - [阶段 1：no\_std 基础（1-2 天）](#阶段-1no_std-基础1-2-天)
    - [阶段 2：内存与外设（2-3 天）](#阶段-2内存与外设2-3-天)
    - [阶段 3：中断与并发（2-3 天）](#阶段-3中断与并发2-3-天)
    - [阶段 4：HAL 设计（3-5 天）](#阶段-4hal-设计3-5-天)
    - [阶段 5：系统集成（3-5 天）](#阶段-5系统集成3-5-天)
  - [工具链安装](#工具链安装)
    - [1. Rust 工具链](#1-rust-工具链)
    - [2. QEMU（用于仿真）](#2-qemu用于仿真)
    - [3. 调试工具](#3-调试工具)
    - [4. 验证安装](#4-验证安装)
  - [核心概念速查](#核心概念速查)
  - [QEMU 仿真步骤](#qemu-仿真步骤)
    - [编译](#编译)
    - [运行](#运行)
    - [调试](#调试)
  - [模块对照索引](#模块对照索引)
  - [权威资源对照](#权威资源对照)
    - [Google Comprehensive Rust - Bare-metal 对照](#google-comprehensive-rust---bare-metal-对照)
    - [The Embedded Rust Book 对照](#the-embedded-rust-book-对照)
    - [Rust Foundation 战略相关](#rust-foundation-战略相关)
    - [Tock OS (Stanford CS340R) 相关](#tock-os-stanford-cs340r-相关)
  - [推荐阅读清单](#推荐阅读清单)
    - [必读](#必读)
    - [选读](#选读)
    - [参考手册](#参考手册)
  - [常见问题 (FAQ)](#常见问题-faq)
    - [Q: 为什么 host 上也能编译 bare-metal 代码？](#q-为什么-host-上也能编译-bare-metal-代码)
    - [Q: 如何在 Windows 上测试 ARM 代码？](#q-如何在-windows-上测试-arm-代码)
    - [Q: `unsafe` 在嵌入式中是不可避免的吗？](#q-unsafe-在嵌入式中是不可避免的吗)
    - [Q: 固定容量的 `FixedRingBuffer` 和 `heapless::Vec` 有什么区别？](#q-固定容量的-fixedringbuffer-和-heaplessvec-有什么区别)

---

## 学习路径

### 阶段 1：no_std 基础（1-2 天）

目标：理解 `no_std` 环境与普通 Rust 的区别。

- [ ] 阅读 `bare_metal_basics.rs`：理解 `#![no_std]`、`#![no_main]`、panic handler
- [ ] 阅读 `no_std_practices.rs`：掌握 `core` 替代 `std`、`alloc` 条件使用
- [ ] 练习：编写一个最小可编译的 `no_std` bin 程序
- [ ] 关键知识点：
  - `core` 包含哪些功能（与 `std` 的交集）
  - 为什么 `format!` 在 `no_std` 中不可用
  - 全局分配器的作用与限制

### 阶段 2：内存与外设（2-3 天）

目标：掌握内存映射寄存器（MMIO）和 volatile 访问。

- [ ] 阅读 `memory_mapped_registers.rs`：寄存器结构体、位操作、volatile 读写
- [ ] 阅读 `uart_driver.rs`：轮询 vs 中断驱动、发送/接收函数
- [ ] 练习：为一个虚拟外设设计寄存器结构体和 safe wrapper
- [ ] 关键知识点：
  - `#[repr(C)]` 的作用
  - `read_volatile` / `write_volatile` 的必要性
  - 位域操作技巧（置位、清零、翻转）

### 阶段 3：中断与并发（2-3 天）

目标：理解嵌入式中断模型和临界区保护。

- [ ] 阅读 `interrupt_handling.rs`：NVIC、ISR 设计、临界区
- [ ] 研究 `cortex_m::interrupt::free` 的实现原理
- [ ] 练习：设计一个中断安全的环形缓冲区
- [ ] 关键知识点：
  - 抢占优先级 vs 子优先级
  - ISR 设计四原则（快速、清标志、不阻塞、静态变量）
  - 临界区应尽量短的原因

### 阶段 4：HAL 设计（3-5 天）

目标：利用 Rust 类型系统构建零成本抽象的硬件抽象层。

- [ ] 阅读 `hal_design_patterns.rs`：类型状态、所有权转移配置、零成本抽象
- [ ] 分析现有 HAL crate（如 `stm32f1xx-hal`）的设计模式
- [ ] 练习：为一个 SPI 外设实现类型状态 API
- [ ] 关键知识点：
  - `PhantomData` 在类型状态中的作用
  - 为什么 "配置步骤只执行一次" 能防止 bug
  - `#[inline(always)]` 与零成本抽象

### 阶段 5：系统集成（3-5 天）

目标：整合所学知识，实现完整应用，并掌握 C 互操作。

- [ ] 阅读 `ffi_c_interop.rs`：`extern "C"`、`#[repr(C)]`、`bindgen`
- [ ] 尝试集成一个 C 驱动库到 Rust 项目
- [ ] 在 QEMU 中运行完整示例
- [ ] 关键知识点：
  - C 调用约定与 Rust 的映射
  - `unsafe` 边界的划分原则
  - `build.rs` 与 `bindgen` 的工作流程

---

## 工具链安装

### 1. Rust 工具链

```bash
# 安装 ARM Cortex-M 目标（根据芯片选择）
rustup target add thumbv6m-none-eabi    # Cortex-M0/M0+
rustup target add thumbv7m-none-eabi    # Cortex-M3
rustup target add thumbv7em-none-eabi   # Cortex-M4/M7 (无 FPU)
rustup target add thumbv7em-none-eabihf # Cortex-M4/M7 (硬浮点)

# 安装常用工具
cargo install cargo-binutils
cargo install cargo-embed
cargo install cargo-flash
rustup component add llvm-tools-preview
```

### 2. QEMU（用于仿真）

```bash
# Ubuntu/Debian
sudo apt update
sudo apt install qemu-system-arm

# macOS
brew install qemu

# Windows
# 从 https://www.qemu.org/download/#windows 下载安装包
```

### 3. 调试工具

```bash
# GDB 多架构支持
sudo apt install gdb-multiarch

# OpenOCD（用于真实硬件调试）
sudo apt install openocd
```

### 4. 验证安装

```bash
# 检查目标平台是否已安装
rustup target list --installed | grep thumb

# 检查 QEMU 版本
qemu-system-arm --version
```

---

## 核心概念速查

| 概念 | 说明 | 对应模块 |
|------|------|----------|
| `#![no_std]` | 禁用标准库，仅使用 core | `bare_metal_basics` |
| `#![no_main]` | 禁用标准 main 入口 | `bare_metal_basics` |
| `#[panic_handler]` | 自定义 panic 处理 | `bare_metal_basics` |
| `volatile` 读写 | 防止编译器优化外设访问 | `memory_mapped_registers` |
| MMIO | 内存映射 I/O | `memory_mapped_registers` |
| NVIC | 嵌套向量中断控制器 | `interrupt_handling` |
| 临界区 | 关闭中断保护共享资源 | `interrupt_handling` |
| 类型状态 | 用类型编码外设状态 | `hal_design_patterns` |
| 零成本抽象 | 编译期消除运行时开销 | `hal_design_patterns` |
| FFI | 与 C 代码互操作 | `ffi_c_interop` |
| `bindgen` | 自动生成 C 头文件绑定 | `ffi_c_interop` |

---

## QEMU 仿真步骤

### 编译

```bash
# 进入项目目录
cd e:\_src\rust-lang

# 编译 c13_embedded 示例（ARM 目标）
cargo build -p c13_embedded --example qemu_demo \
    --target thumbv7m-none-eabi \
    --features c13_embedded/embedded
```

### 运行

```bash
# 使用 QEMU 的 STM32F103 机器模型
qemu-system-arm \
    -cpu cortex-m3 \
    -machine stm32-f103c8 \
    -nographic \
    -kernel target/thumbv7m-none-eabi/debug/examples/qemu_demo
```

### 调试

```bash
# 启动 QEMU 并等待 GDB 连接
qemu-system-arm \
    -cpu cortex-m3 \
    -machine stm32-f103c8 \
    -nographic \
    -s -S \
    -kernel target/thumbv7m-none-eabi/debug/examples/qemu_demo

# 另一个终端启动 GDB
arm-none-eabi-gdb \
    target/thumbv7m-none-eabi/debug/examples/qemu_demo \
    -ex "target remote :1234"
```

---

## 模块对照索引

| 文件 | 主题 | 核心 API |
|------|------|----------|
| `bare_metal_basics.rs` | no_std 环境、panic handler、启动代码 | `PanicHandlerConcept`, `StartupCode` |
| `no_std_practices.rs` | core 替代 std、固定集合、自旋锁 | `CoreUsageDemo`, `FixedRingBuffer` |
| `memory_mapped_registers.rs` | MMIO、volatile、位操作 | `GpioPort`, `BitOps` |
| `uart_driver.rs` | UART 驱动、轮询/中断 | `UartDriver`, `InterruptDrivenUart` |
| `interrupt_handling.rs` | NVIC、ISR、临界区 | `NvicConcept`, `CriticalSectionConcept` |
| `hal_design_patterns.rs` | 类型状态、构建器、零成本抽象 | `Spi`, `UartBuilder` |
| `ffi_c_interop.rs` | C 互操作、bindgen | `SensorData`, `CBindingsConcept` |

---

## 权威资源对照

### Google Comprehensive Rust - Bare-metal 对照

| Google 课程主题 | 本项目对应模块 |
|-----------------|---------------|
| no_std 开发 | `bare_metal_basics.rs`, `no_std_practices.rs` |
| 微控制器编程 | `memory_mapped_registers.rs`, `uart_driver.rs` |
| 应用处理器 | `ffi_c_interop.rs`（含 build-std 概念） |
| UART 驱动编写 | `uart_driver.rs` |
| 内存映射寄存器 | `memory_mapped_registers.rs` |

### The Embedded Rust Book 对照

| Book 章节 | 本项目对应模块 |
|-----------|---------------|
| 介绍与工具链 | `docs/BARE_METAL_GUIDE.md` |
| QEMU 与硬件 | `examples/qemu_demo.rs` |
| 内存映射寄存器 | `memory_mapped_registers.rs` |
| Semihosting | `bare_metal_basics.rs`（注释提及） |
| Panic 与异常 | `bare_metal_basics.rs` |
| 中断处理 | `interrupt_handling.rs` |
| 外设与借用检查器 | `hal_design_patterns.rs` |
| 静态保证与类型状态 | `hal_design_patterns.rs` |
| HAL 设计指南 | `hal_design_patterns.rs` |
| C 互操作 | `ffi_c_interop.rs` |

### Rust Foundation 战略相关

| 战略方向 | 说明 |
|----------|------|
| build-std 稳定化 | 允许为自定义目标构建标准库子集 |
| Rust for Linux | 将 Rust 引入 Linux 内核开发 |
| Ferrocene | Rust 的安全关键认证 |

### Tock OS (Stanford CS340R) 相关

| 概念 | 说明 |
|------|------|
| 用户态驱动 | Tock 将驱动运行在用户态，内核仅提供系统调用 |
| 资源配额 | 防止恶意/错误驱动耗尽系统资源 |
|  capsules | Tock 的内核组件模型 |

---

## 推荐阅读清单

### 必读

1. [The Rust Programming Language - Chapter 19.1: Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html)
2. [The Embedded Rust Book](https://docs.rust-embedded.org/book/)
3. [The Rustonomicon](https://doc.rust-lang.org/nomicon/)（深入理解 unsafe）

### 选读

1. [Google Comprehensive Rust - Bare-metal](https://google.github.io/comprehensive-rust/bare-metal.html)
2. [Cortex-M 设备通用用户指南 (ARM DDI 0439)](https://developer.arm.com/documentation/ddi0439/latest/)
3. [RTFM / RTIC 框架文档](https://rtic.rs/)（实时中断驱动并发）
4. [Tock OS 文档](https://book.tockos.org/)
5. [Ferrous Systems 嵌入式培训材料](https://github.com/ferrous-systems/embedded-trainings)

### 参考手册

1. [Rust Embedded 生态系统概览](https://github.com/rust-embedded/awesome-embedded-rust)
2. [cortex-m-rt 文档](https://docs.rs/cortex-m-rt/latest/cortex_m_rt/)
3. [bindgen 用户指南](https://rust-lang.github.io/rust-bindgen/)

---

## 常见问题 (FAQ)

### Q: 为什么 host 上也能编译 bare-metal 代码？

A: 本项目使用 `#[cfg(target_arch = "arm")]` 条件编译区分目标平台：

- **Host (x86_64)**：使用模拟/桩代码，演示概念，确保 `cargo check` 通过
- **ARM 目标**：使用真实硬件抽象层和 `cortex-m` 等 crate

### Q: 如何在 Windows 上测试 ARM 代码？

A: 三种方式：

1. **QEMU 仿真**（推荐）：无需硬件，完整模拟 Cortex-M
2. **WSL2 + QEMU**：在 Linux 子环境中运行
3. **真实硬件**：使用 ST-Link/J-Link 连接开发板

### Q: `unsafe` 在嵌入式中是不可避免的吗？

A: 是的。与外设寄存器的交互本质上是通过原始指针访问固定内存地址，
这在 Rust 中必须标记为 `unsafe`。但 HAL 的设计目标是将 `unsafe` 封装在底层，
为用户提供类型安全的 API。

### Q: 固定容量的 `FixedRingBuffer` 和 `heapless::Vec` 有什么区别？

A: `FixedRingBuffer` 是本模块的教育实现，展示纯 core 实现技巧。
生产环境推荐使用 [`heapless`](https://docs.rs/heapless) crate，
它提供了更完整的 `Vec`、`Queue`、`IndexMap` 等集合。

---

*本文档最后更新：2026-04-24*
