//! RISC-V 最小 bare-metal blinky 骨架
//!
//! 目标示例：SiFive FE310 / GD32VF103 / QEMU virt（RAM 启动）。
//! 使用 `riscv-rt` 入口与一个通用 GPIO 端口地址模拟 LED 翻转。
//!
//! 编译：
//! ```bash
//! cargo build -p c13_embedded --target riscv32imac-unknown-none-elf --example riscv_minimal_blinky
//! ```
//!
//! 对应 concept 页：
//! `concept/06_ecosystem/05_systems_and_embedded/21_riscv_avr_embedded.md`
//! `concept/06_ecosystem/05_systems_and_embedded/13_bare_metal_boot_linker_script.md`

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
    println!("riscv_minimal_blinky: host 模拟模式");
    println!("真实目标编译命令:");
    println!(
        "  cargo build -p c13_embedded --target riscv32imac-unknown-none-elf \\\n    --example \
         riscv_minimal_blinky"
    );
}

// ---------------------------------------------------------------------------
// RISC-V 真实目标入口
// ---------------------------------------------------------------------------
#[cfg(all(target_arch = "riscv32", target_os = "none"))]
mod target_impl {
    use core::sync::atomic::{AtomicU32, Ordering};

    // 通用 GPIO 输出寄存器占位地址（真实项目替换为具体芯片地址）
    const GPIO_OUT: *mut u32 = 0x1001_2000 as *mut u32;

    #[riscv_rt::entry]
    fn main() -> ! {
        static COUNTER: AtomicU32 = AtomicU32::new(0);

        loop {
            // 翻转位 0 模拟 LED
            unsafe {
                let val = core::ptr::read_volatile(GPIO_OUT);
                core::ptr::write_volatile(GPIO_OUT, val ^ 0x1);
            }

            COUNTER.fetch_add(1, Ordering::Relaxed);

            // 简单延时
            for _ in 0..100_000 {
                riscv::asm::nop();
            }
        }
    }
}

// ---------------------------------------------------------------------------
// ARM 占位入口（当本文件被误用 ARM 目标编译时，保证链接通过）
// ---------------------------------------------------------------------------
#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    #[cortex_m_rt::entry]
    fn main() -> ! {
        loop {
            cortex_m::asm::wfi();
        }
    }
}
