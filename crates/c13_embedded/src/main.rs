//! Embedded Demo - 嵌入式演示程序
//! 在 host 目标上运行模拟演示，在 ARM / RISC-V 裸机目标上展示最小入口。

#![cfg_attr(any(target_arch = "arm", target_arch = "riscv32"), no_std)]
#![cfg_attr(any(target_arch = "arm", target_arch = "riscv32"), no_main)]

#[cfg(any(target_arch = "arm", target_arch = "riscv32"))]
use panic_halt as _;

#[cfg(target_arch = "arm")]
use cortex_m_rt::entry;

#[cfg(target_arch = "riscv32")]
use riscv_rt::entry;

#[cfg(not(any(target_arch = "arm", target_arch = "riscv32")))]
use c13_embedded::get_library_info;

#[cfg(not(any(target_arch = "arm", target_arch = "riscv32")))]
fn main() {
    println!("=== C13 Embedded - Host 模拟演示 ===");
    println!("{:#?}", get_library_info());

    println!("\n本演示在 host 目标上展示 c13_embedded 的核心概念。");
    println!("在 ARM / RISC-V 嵌入式目标上，本程序将作为 bare-metal 应用运行。");
    println!("\n=== 演示完成 ===");
}

#[cfg(target_arch = "arm")]
#[entry]
fn main() -> ! {
    loop {
        cortex_m::asm::wfi();
    }
}

#[cfg(target_arch = "riscv32")]
#[entry]
fn main() -> ! {
    loop {
        riscv::asm::wfi();
    }
}
