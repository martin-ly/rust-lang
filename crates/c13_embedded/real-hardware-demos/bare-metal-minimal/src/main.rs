#![no_std]
#![no_main]

//! 最小 bare-metal 程序
//! 演示一个可在真实 ARM Cortex-M 与 RISC-V 嵌入式目标上编译运行的最小 `no_std` 程序。
//!
//! # 支持的编译目标
//!
//! - `thumbv6m-none-eabi`    (ARM Cortex-M0/M0+, e.g., RP2040 core 0)
//! - `thumbv7em-none-eabihf` (ARM Cortex-M4F, e.g., STM32F4)
//! - `riscv32imac-unknown-none-elf` (RISC-V 32-bit IMAC, e.g., ESP32-C3 / GD32VF103)
//!
//! # 编译
//!
//! ```bash
//! rustup target add thumbv6m-none-eabi thumbv7em-none-eabihf riscv32imac-unknown-none-elf
//!
//! cd crates/c13_embedded/real-hardware-demos/bare-metal-minimal
//! cargo build --release --target thumbv6m-none-eabi
//! cargo build --release --target thumbv7em-none-eabihf
//! cargo build --release --target riscv32imac-unknown-none-elf
//! ```

use panic_halt as _;

#[cfg(target_arch = "arm")]
mod arm_impl {
    use core::sync::atomic::{AtomicU32, Ordering};

    #[cortex_m_rt::entry]
    fn main() -> ! {
        static COUNTER: AtomicU32 = AtomicU32::new(0);

        loop {
            // ARMv6-M (Cortex-M0) 不支持 AtomicU32::fetch_add，使用 load/store 实现计数。
            // 在单核 bare-metal 环境中，这等价于一次非原子递增；如需原子性可临界区包裹。
            let val = COUNTER.load(Ordering::Relaxed);
            COUNTER.store(val.wrapping_add(1), Ordering::Relaxed);

            for _ in 0..10_000 {
                cortex_m::asm::nop();
            }
        }
    }
}

#[cfg(target_arch = "riscv32")]
mod riscv_impl {
    #[riscv_rt::entry]
    fn main() -> ! {
        loop {
            riscv::asm::wfi();
        }
    }
}
