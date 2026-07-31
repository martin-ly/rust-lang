//! QEMU 仿真演示
//!
//! 本示例展示如何在 QEMU 中运行 bare-metal Rust 程序。
//! 默认演示使用 ARM Cortex-M 目标；RISC-V 目标提供占位入口保证 `--examples` 编译通过。

#![cfg_attr(
    any(
        all(target_arch = "arm", target_os = "none"),
        all(target_arch = "riscv32", target_os = "none")
    ),
    no_std
)]
#![cfg_attr(
    any(
        all(target_arch = "arm", target_os = "none"),
        all(target_arch = "riscv32", target_os = "none")
    ),
    no_main
)]

#[cfg(not(any(
    all(target_arch = "arm", target_os = "none"),
    all(target_arch = "riscv32", target_os = "none")
)))]
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
        "  qemu-system-arm -cpu cortex-m3 -machine stm32-f103c8 -nographic -kernel \\\n         target/thumbv7m-none-eabi/debug/examples/qemu_demo"
    );
    println!();
    println!("注意: 实际运行需要正确的链接脚本和启动代码 (cortex-m-rt 自动处理)。");
}

#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    #[cortex_m_rt::entry]
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
}

#[cfg(all(target_arch = "riscv32", target_os = "none"))]
mod target_impl {
    #[riscv_rt::entry]
    fn main() -> ! {
        loop {
            riscv::asm::wfi();
        }
    }
}
