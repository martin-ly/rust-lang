//! 嵌入式硬件测试矩阵：最小可编译目标示例
//!
//! 目标平台：`thumbv7em-none-eabihf`（Cortex-M4F，如 STM32F4 / Nucleo-F446RE）。
//! 本示例演示一个可在真实 ARM 裸机目标上编译、烧录并通过 probe-rs 运行的最小固件骨架。
//!
//! Host 平台（x86_64）上运行时，示例进入模拟模式，仅打印编译命令；不会访问硬件地址。
//!
//! 真实目标编译命令：
//! ```bash
//! cargo build -p c13_embedded --target thumbv7em-none-eabihf --example hardware_test_matrix_blinky
//! ```
//!
//! probe-rs 烧录与运行（需连接 CMSIS-DAP / ST-Link 并替换为实际芯片）：
//! ```bash
//! probe-rs run --chip STM32F446RETx target/thumbv7em-none-eabihf/debug/examples/hardware_test_matrix_blinky
//! ```
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/50_embedded_hardware_test_matrix.md`

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
// Host 模拟入口：保证在非 ARM 目标上 `cargo check --workspace` 直接通过
// ---------------------------------------------------------------------------
#[cfg(not(any(
    all(target_arch = "arm", target_os = "none"),
    all(target_arch = "riscv32", target_os = "none")
)))]
fn main() {
    println!("hardware_test_matrix_blinky: host 模拟模式");
    println!("真实目标编译命令:");
    println!(
        "  cargo build -p c13_embedded --target thumbv7em-none-eabihf \\\n    --example hardware_test_matrix_blinky"
    );
}

// ---------------------------------------------------------------------------
// ARM Cortex-M 真实目标入口：基于 cortex-m-rt + panic-halt
// ---------------------------------------------------------------------------
#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    // panic handler 由 panic-halt crate 提供
    use panic_halt as _;

    use core::sync::atomic::{AtomicU32, Ordering};

    // STM32F4 GPIOA_ODR 地址；实际项目应通过 PAC/HAL 访问，而非硬编码
    const GPIOA_ODR: *mut u32 = 0x4002_0014 as *mut u32;

    #[cortex_m_rt::entry]
    fn main() -> ! {
        static COUNTER: AtomicU32 = AtomicU32::new(0);

        loop {
            // 翻转 PA5（Nucleo-F446RE 板载 LED 常见接法）
            unsafe {
                let val = core::ptr::read_volatile(GPIOA_ODR);
                core::ptr::write_volatile(GPIOA_ODR, val ^ (1 << 5));
            }

            COUNTER.fetch_add(1, Ordering::Relaxed);

            // 简单延时；真实项目应使用定时器
            for _ in 0..100_000 {
                cortex_m::asm::nop();
            }
        }
    }
}

// ---------------------------------------------------------------------------
// RISC-V 占位入口：防止误用 riscv32 目标编译时链接失败
// ---------------------------------------------------------------------------
#[cfg(all(target_arch = "riscv32", target_os = "none"))]
mod target_impl {
    use panic_halt as _;

    #[riscv_rt::entry]
    fn main() -> ! {
        loop {
            riscv::asm::wfi();
        }
    }
}
