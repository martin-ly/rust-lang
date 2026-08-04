//! ARM Cortex-M 最小 bare-metal blinky 骨架
//!
//! 目标板示例：STM32F4 / Nucleo-F446RE / Discovery-F407。
//! 使用 `cortex-m-rt` 入口与内存映射 GPIOA_ODR 模拟 LED 翻转。
//!
//! 编译：
//! ```bash
//! cargo build -p c13_embedded --target thumbv7em-none-eabihf --example cortex_m_minimal_blinky
//! ```
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/13_bare_metal_boot_linker_script.md`
//! `concept/06_ecosystem/05_systems_and_embedded/23_no_std_and_bare_metal_idioms.md`

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

// ---------------------------------------------------------------------------
// Host 模拟入口
// ---------------------------------------------------------------------------
#[cfg(not(any(
    all(target_arch = "arm", target_os = "none"),
    all(target_arch = "riscv32", target_os = "none")
)))]
fn main() {
    println!("cortex_m_minimal_blinky: host 模拟模式");
    println!("真实目标编译命令:");
    println!(
        "  cargo build -p c13_embedded --target thumbv7em-none-eabihf \\\n    --example \
         cortex_m_minimal_blinky"
    );
}

// ---------------------------------------------------------------------------
// ARM Cortex-M 真实目标入口
// ---------------------------------------------------------------------------
#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    // 由 panic-halt crate 提供 #[panic_handler]
    use panic_halt as _;

    use core::sync::atomic::{AtomicU32, Ordering};

    // STM32F4 GPIOA ODR 地址（仅作示例）
    const GPIOA_ODR: *mut u32 = 0x4002_0014 as *mut u32;

    #[cortex_m_rt::entry]
    fn main() -> ! {
        static COUNTER: AtomicU32 = AtomicU32::new(0);

        loop {
            // 翻转 PA5（板载 LED 常见接法）
            unsafe {
                let val = core::ptr::read_volatile(GPIOA_ODR);
                core::ptr::write_volatile(GPIOA_ODR, val ^ (1 << 5));
            }

            COUNTER.fetch_add(1, Ordering::Relaxed);

            // 简单延时
            for _ in 0..100_000 {
                cortex_m::asm::nop();
            }
        }
    }

    #[allow(dead_code)]
    fn _unused() {}
}

// ---------------------------------------------------------------------------
// RISC-V 占位入口（当本文件被误用 riscv32 目标编译时，保证链接通过）
// ---------------------------------------------------------------------------
#[cfg(all(target_arch = "riscv32", target_os = "none"))]
mod target_impl {
    #[riscv_rt::entry]
    fn main() -> ! {
        loop {
            riscv::asm::wfi();
        }
    }
}
