//! 最小 RISC-V 裸机示例（riscv32imac-unknown-none-elf）
//!
//! 仅演示 `no_std` + `no_main` 入口与 panic handler 的最小链接集合。
//!
//! 编译：
//! ```bash
//! cargo build -p c13_embedded --target riscv32imac-unknown-none-elf --example riscv_minimal_main
//! ```

#![cfg_attr(all(target_arch = "riscv32", target_os = "none"), no_std)]
#![cfg_attr(all(target_arch = "riscv32", target_os = "none"), no_main)]

// Host 模拟入口
#[cfg(not(all(target_arch = "riscv32", target_os = "none")))]
fn main() {
    println!("riscv_minimal_main: host 模拟模式");
    println!(
        "真实目标编译命令:\n  cargo build -p c13_embedded --target riscv32imac-unknown-none-elf \
         --example riscv_minimal_main"
    );
}

// RISC-V 裸机入口
#[cfg(all(target_arch = "riscv32", target_os = "none"))]
mod target_impl {
    // 提供 #[panic_handler]
    use panic_halt as _;

    #[riscv_rt::entry]
    fn main() -> ! {
        loop {
            riscv::asm::nop();
        }
    }
}
