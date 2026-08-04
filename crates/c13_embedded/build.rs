//! 构建脚本：
//! 1. 检测 nightly 并启用 `cfg(nightly)`。
//! 2. 为 ARM / RISC-V 裸机目标在 OUT_DIR 生成 `memory.x`，并加入链接器搜索路径。
//!    这样 `cortex-m-rt` / `riscv-rt` 能在没有设备 PAC 的情况下完成链接。

use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;

fn main() {
    if is_nightly() {
        println!("cargo:rustc-cfg=nightly");
    }

    // 工具链切换时重新执行 build.rs
    println!("cargo:rerun-if-env-changed=RUSTUP_TOOLCHAIN");
    println!("cargo:rerun-if-env-changed=RUSTC_BOOTSTRAP");

    // 为裸机目标生成 memory.x；host 目标跳过。
    // 当启用 `esp32c3-hal` feature 时，esp-hal 1.x 会自行提供 ESP32-C3 专用的
    // memory.x / linkall.x，本 build.rs 不再生成通用 memory.x，避免链接器冲突。
    if env::var_os("CARGO_FEATURE_ESP32C3_HAL").is_some() {
        return;
    }

    if let Ok(arch) = env::var("CARGO_CFG_TARGET_ARCH") {
        match arch.as_str() {
            "arm" => generate_memory_x_arm(),
            "riscv32" | "riscv64" => generate_memory_x_riscv(),
            _ => {}
        }
    }
}

fn generate_memory_x_arm() {
    let out_dir = env::var("OUT_DIR").expect("OUT_DIR not set");
    let dest = Path::new(&out_dir).join("memory.x");

    // STM32F4 风格布局：1 MiB Flash @ 0x0800_0000，128 KiB RAM @ 0x2000_0000。
    // 仅用于验证链接/编译，真实项目应替换为具体芯片的参考手册数值。
    fs::write(
        &dest,
        r#"/* 由 build.rs 自动生成 — ARM Cortex-M 示例内存布局 */
MEMORY
{
  FLASH (rx) : ORIGIN = 0x08000000, LENGTH = 1024K
  RAM   (rwx): ORIGIN = 0x20000000, LENGTH = 128K
}

_stack_top = ORIGIN(RAM) + LENGTH(RAM);
"#,
    )
    .expect("failed to write memory.x");

    println!("cargo:rustc-link-search={}", out_dir);
}

fn generate_memory_x_riscv() {
    let out_dir = env::var("OUT_DIR").expect("OUT_DIR not set");
    let dest = Path::new(&out_dir).join("memory.x");

    // RAM-only 布局（适合 QEMU virt 或从 RAM 启动的 RISC-V 核）。
    // 仅用于验证链接/编译，真实项目应替换为具体芯片的参考手册数值。
    fs::write(
        &dest,
        r#"/* 由 build.rs 自动生成 — RISC-V 示例内存布局 */
MEMORY
{
  RAM (rwxa) : ORIGIN = 0x80000000, LENGTH = 128K
}

REGION_ALIAS("REGION_TEXT", RAM);
REGION_ALIAS("REGION_RODATA", RAM);
REGION_ALIAS("REGION_DATA", RAM);
REGION_ALIAS("REGION_BSS", RAM);
REGION_ALIAS("REGION_HEAP", RAM);
REGION_ALIAS("REGION_STACK", RAM);
"#,
    )
    .expect("failed to write memory.x");

    println!("cargo:rustc-link-search={}", out_dir);
}

fn is_nightly() -> bool {
    let rustc = env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let Ok(output) = Command::new(&rustc).arg("--version").output() else {
        return false;
    };
    let version = String::from_utf8_lossy(&output.stdout);
    version.contains("nightly")
}
