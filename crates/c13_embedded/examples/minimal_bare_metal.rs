//! 最小 bare-metal 程序
//! 演示一个可在真实嵌入式目标上编译的最小 no_std 程序结构。
//! demonstration in real goal on minimum no_std program structure 。
//! 在 host 目标上，使用模拟代码确保 cargo check 通过。
//! in host goal on ， cargo check 。
//! in host goalon，Use模拟代码Ensure cargo check Via。

#![cfg_attr(target_arch = "arm", no_std)]
#![cfg_attr(target_arch = "arm", no_main)]

#[cfg(target_arch = "arm")]
use panic_halt as _;

#[cfg(target_arch = "arm")]
use cortex_m_rt::entry;

#[cfg(not(target_arch = "arm"))]
fn main() {
    println!("最小 bare-metal 程序 - Host 模拟模式");

    let mut counter: u32 = 0;
    counter += 1;
    println!("计数器: {}", counter);

    let mut gpio_state: u32 = 0;
    gpio_state |= 1 << 5;
    println!("GPIO 状态: 0b{:032b}", gpio_state);
}

/// ARM 目标下的真实入口
/// ARM goal under real
#[cfg(target_arch = "arm")]
#[entry]
fn main() -> ! {
    use core::sync::atomic::{AtomicU32, Ordering};
    static COUNTER: AtomicU32 = AtomicU32::new(0);

    loop {
        COUNTER.fetch_add(1, Ordering::Relaxed);

        for _ in 0..10_000 {
            cortex_m::asm::nop();
        }
    }
}
