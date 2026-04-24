//! 最小 bare-metal 程序
//!
//! 演示一个可在真实嵌入式目标上编译的最小 no_std 程序结构。
//! 在 host 目标上，使用模拟代码确保 cargo check 通过。

#![cfg_attr(target_arch = "arm", no_std)]
#![cfg_attr(target_arch = "arm", no_main)]

#[cfg(target_arch = "arm")]
use panic_halt as _;

#[cfg(target_arch = "arm")]
use cortex_m_rt::entry;

/// Host 目标下的测试入口
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
#[cfg(target_arch = "arm")]
#[entry]
fn main() -> ! {
    static mut COUNTER: u32 = 0;

    unsafe {
        COUNTER = 0;
    }

    loop {
        unsafe {
            COUNTER = COUNTER.wrapping_add(1);
        }

        for _ in 0..10_000 {
            cortex_m::asm::nop();
        }
    }
}
