//! Embedded Demo - 嵌入式演示程序
//!
//! 在 host 目标上运行模拟演示，在 ARM 目标上展示 bare-metal 入口。

#![cfg_attr(target_arch = "arm", no_std)]
#![cfg_attr(target_arch = "arm", no_main)]

#[cfg(target_arch = "arm")]
use panic_halt as _;

#[cfg(target_arch = "arm")]
use cortex_m_rt::entry;

use c13_embedded::get_library_info;

#[cfg(not(target_arch = "arm"))]
fn main() {
    println!("=== C13 Embedded - Host 模拟演示 ===");
    println!("{:#?}", get_library_info());

    println!("\n本演示在 host 目标上展示 c13_embedded 的核心概念。");
    println!("在 ARM 嵌入式目标上，本程序将作为 bare-metal 应用运行。");
    println!("\n=== 演示完成 ===");
}

#[cfg(target_arch = "arm")]
#[entry]
fn main() -> ! {
    loop {
        cortex_m::asm::nop();
    }
}
