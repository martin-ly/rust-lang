//! 最小 AArch64 裸机示例（aarch64-unknown-none-softfloat）
//!
//! 仅演示 `no_std` + `no_main` 入口与 panic handler 的最小链接集合。
//!
//! 编译：
//! ```bash
//! cargo build -p c13_embedded --target aarch64-unknown-none-softfloat --example aarch64_minimal_main
//! ```

#![cfg_attr(all(bare_metal, target_arch = "aarch64"), no_std)]
#![cfg_attr(all(bare_metal, target_arch = "aarch64"), no_main)]

// Host 模拟入口
#[cfg(not(all(bare_metal, target_arch = "aarch64")))]
fn main() {
    println!("aarch64_minimal_main: host 模拟模式");
    println!(
        "真实目标编译命令:\n  cargo build -p c13_embedded --target aarch64-unknown-none-softfloat \
         --example aarch64_minimal_main"
    );
}

// AArch64 裸机入口
#[cfg(all(bare_metal, target_arch = "aarch64"))]
mod target_impl {
    // 提供 #[panic_handler]
    use panic_halt as _;

    #[unsafe(no_mangle)]
    pub extern "C" fn _start() -> ! {
        loop {
            aarch64_cpu::asm::wfi();
        }
    }
}
