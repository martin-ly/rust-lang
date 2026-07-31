//! 最小 bare-metal 程序
//! 演示一个可在真实嵌入式目标上编译的最小 no_std 程序结构。
//! 在 host 目标上，使用模拟代码确保 cargo check 通过。

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
    println!("最小 bare-metal 程序 - Host 模拟模式");

    let mut counter: u32 = 0;
    counter += 1;
    println!("计数器: {}", counter);

    let mut gpio_state: u32 = 0;
    gpio_state |= 1 << 5;
    println!("GPIO 状态: 0b{:032b}", gpio_state);
}

#[cfg(all(target_arch = "arm", target_os = "none"))]
mod target_impl {
    use core::sync::atomic::{AtomicU32, Ordering};

    #[cortex_m_rt::entry]
    fn main() -> ! {
        static COUNTER: AtomicU32 = AtomicU32::new(0);

        loop {
            COUNTER.fetch_add(1, Ordering::Relaxed);

            for _ in 0..10_000 {
                cortex_m::asm::nop();
            }
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
