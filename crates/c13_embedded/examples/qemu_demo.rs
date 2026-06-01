//! QEMU 仿真演示
//! QEMU demonstration
//! QEMU 仿真Demonstration of
//! 本示例展示如何在 QEMU 中运行 bare-metal Rust 程序。
//! this example in QEMU in Run bare-metal Rust program 。
//! ## 环境准备
//! ## environment
//! # 安装 QEMU（ARM 版本）
//! # QEMU（ARM this ）
//! # 安装 QEMU（ARM 版this）
//! # Windows: 从 QEMU 官网下载安装包
//! # Windows: from QEMU under
//! # 安装目标平台
//! # goal platform
//! # 安装goalplatform
//!
//! ## 编译和运行
//! ## and Run
//! # 编译示例（以 STM32F103 为例）
//! # example （ STM32F103 as ）
//! # 编译Example of（以 STM32F103 as例）
//! # 使用 QEMU 运行
//! # QEMU Run
//! ```

#![cfg_attr(target_arch = "arm", no_std)]
#![cfg_attr(target_arch = "arm", no_main)]

#[cfg(target_arch = "arm")]
use panic_halt as _;

#[cfg(target_arch = "arm")]
use cortex_m_rt::entry;

#[cfg(not(target_arch = "arm"))]
fn main() {
    println!("=== QEMU 演示 ===");
    println!("本示例需要在 ARM 嵌入式目标上运行。");
    println!();
    println!("编译命令:");
    println!(
        "  cargo build --example qemu_demo --target thumbv7m-none-eabi --features \
         c13_embedded/embedded"
    );
    println!();
    println!("QEMU 运行命令:");
    println!(
        "  qemu-system-arm -cpu cortex-m3 -machine stm32-f103c8 -nographic -kernel \
         target/thumbv7m-none-eabi/debug/examples/qemu_demo"
    );
    println!();
    println!("注意: 实际运行需要正确的链接脚本和启动代码 (cortex-m-rt 自动处理)。");
}

/// ARM goalunder QEMU 入口
#[cfg(target_arch = "arm")]
#[entry]
fn main() -> ! {
    const USART1_BASE: usize = 0x4001_3800;
    const USART1_DR: *mut u32 = (USART1_BASE + 0x04) as *mut u32;
    const USART1_SR: *mut u32 = (USART1_BASE + 0x00) as *mut u32;

    let message = b"Hello from QEMU bare-metal Rust!\r\n";

    for &byte in message {
        while unsafe { core::ptr::read_volatile(USART1_SR) & (1 << 7) } == 0 {}
        unsafe { core::ptr::write_volatile(USART1_DR, byte as u32) }
    }

    loop {
        cortex_m::asm::wfi();
    }
}
