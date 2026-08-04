//! probe-rs 嵌入式调试实战：最小可编译目标示例
//!
//! 目标平台：`thumbv7em-none-eabihf`（Cortex-M4F）。
//! 本示例演示如何在一个真实 ARM 裸机目标上集成 DWT 周期计数与 probe-rs 调试链路：
//!   - 使能 DWT CYCCNT 作为低侵入时间戳
//!   - 通过 `cortex_m::asm::bkpt` 触发硬件断点（probe-rs attach 时可捕获）
//!   - 在 Host 模拟模式下打印等价的 probe-rs 命令
//!
//! 真实目标编译命令：
//! ```bash
//! cargo build -p c13_embedded --target thumbv7em-none-eabihf --example probe_rs_debug_blinky
//! ```
//!
//! probe-rs 运行与 RTT 日志捕获（若已集成 defmt，则配合 `--probe` 与 `Embed.toml`）：
//! ```bash
//! probe-rs run --chip STM32F446RETx target/thumbv7em-none-eabihf/debug/examples/probe_rs_debug_blinky
//! ```
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/51_probe_rs_and_embedded_debugging.md`

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
    println!("probe_rs_debug_blinky: host 模拟模式");
    println!("真实目标编译命令:");
    println!(
        "  cargo build -p c13_embedded --target thumbv7em-none-eabihf \\\n    --example probe_rs_debug_blinky"
    );
    println!("probe-rs 运行命令:");
    println!(
        "  probe-rs run --chip STM32F446RETx \\\n    target/thumbv7em-none-eabihf/debug/examples/probe_rs_debug_blinky"
    );
}

// ---------------------------------------------------------------------------
// ARM Cortex-M 真实目标入口
// ---------------------------------------------------------------------------
#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    use panic_halt as _;

    // DWT 调试组件寄存器地址（Cortex-M3/M4/M7）
    const DEMCR: *mut u32 = 0xE000_EDFC as *mut u32;
    const DWT_CTRL: *mut u32 = 0xE000_1000 as *mut u32;
    const DWT_CYCCNT: *mut u32 = 0xE000_1004 as *mut u32;

    // STM32F4 GPIOA_ODR 地址
    const GPIOA_ODR: *mut u32 = 0x4002_0014 as *mut u32;

    #[cortex_m_rt::entry]
    fn main() -> ! {
        unsafe {
            // 使能 DWT 跟踪与 CYCCNT
            core::ptr::write_volatile(DEMCR, core::ptr::read_volatile(DEMCR) | (1 << 24));
            core::ptr::write_volatile(DWT_CYCCNT, 0);
            core::ptr::write_volatile(DWT_CTRL, core::ptr::read_volatile(DWT_CTRL) | (1 << 0));
        }

        loop {
            let start = unsafe { core::ptr::read_volatile(DWT_CYCCNT) };

            // 翻转 LED
            unsafe {
                let val = core::ptr::read_volatile(GPIOA_ODR);
                core::ptr::write_volatile(GPIOA_ODR, val ^ (1 << 5));
            }

            // 简单延时，期间可被 probe-rs 中断/单步
            for _ in 0..100_000 {
                cortex_m::asm::nop();
            }

            let end = unsafe { core::ptr::read_volatile(DWT_CYCCNT) };
            let _elapsed = end.wrapping_sub(start);

            // 触发硬件断点；probe-rs attach 时可在 bkpt 处暂停
            cortex_m::asm::bkpt();
        }
    }
}

// ---------------------------------------------------------------------------
// RISC-V 占位入口
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
