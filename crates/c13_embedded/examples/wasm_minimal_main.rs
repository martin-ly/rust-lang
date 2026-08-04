//! 最小 WebAssembly 裸机示例（wasm32-unknown-unknown）
//!
//! 仅演示 `no_std` + `no_main` 入口与 panic handler 的最小链接集合。
//!
//! 编译：
//! ```bash
//! cargo build -p c13_embedded --target wasm32-unknown-unknown --example wasm_minimal_main
//! ```

#![cfg_attr(all(bare_metal, target_arch = "wasm32"), no_std)]
#![cfg_attr(all(bare_metal, target_arch = "wasm32"), no_main)]

// Host 模拟入口
#[cfg(not(all(bare_metal, target_arch = "wasm32")))]
fn main() {
    println!("wasm_minimal_main: host 模拟模式");
    println!(
        "真实目标编译命令:\n  cargo build -p c13_embedded --target wasm32-unknown-unknown \
         --example wasm_minimal_main"
    );
}

// WebAssembly 裸机入口
#[cfg(all(bare_metal, target_arch = "wasm32"))]
mod target_impl {
    // 提供 #[panic_handler]
    use panic_halt as _;

    #[unsafe(no_mangle)]
    pub extern "C" fn _start() -> ! {
        loop {}
    }
}
