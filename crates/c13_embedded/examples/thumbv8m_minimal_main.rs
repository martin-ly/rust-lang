//! 最小 ARM Cortex-M33 裸机示例（thumbv8m.main-none-eabihf）
//!
//! 仅演示 `no_std` + `no_main` 入口与 panic handler 的最小链接集合。
//!
//! 编译：
//! ```bash
//! cargo build -p c13_embedded --target thumbv8m.main-none-eabihf --example thumbv8m_minimal_main
//! ```

#![cfg_attr(all(bare_metal, target_arch = "arm"), no_std)]
#![cfg_attr(all(bare_metal, target_arch = "arm"), no_main)]

// Host 模拟入口
#[cfg(not(all(bare_metal, target_arch = "arm")))]
fn main() {
    println!("thumbv8m_minimal_main: host 模拟模式");
    println!(
        "真实目标编译命令:\n  cargo build -p c13_embedded --target thumbv8m.main-none-eabihf \
         --example thumbv8m_minimal_main"
    );
}

// ARM Cortex-M 裸机入口（同样适用于 thumbv8m.main-none-eabihf）
#[cfg(all(bare_metal, target_arch = "arm"))]
mod target_impl {
    // 提供 #[panic_handler]
    use panic_halt as _;

    #[cortex_m_rt::entry]
    fn main() -> ! {
        loop {
            cortex_m::asm::wfi();
        }
    }
}
