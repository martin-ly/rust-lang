//! 自动检测当前工具链是否为 nightly，并在编译本 crate 时启用 `cfg(nightly)`。
//!
//! 这样本地默认 nightly 构建会自动包含 nightly-only 预览模块，而 stable
//! 构建（未显式传入 `--cfg nightly`）不会尝试编译不稳定特性。

use std::process::Command;

fn main() {
    if is_nightly() {
        println!("cargo:rustc-cfg=nightly");
    }

    // 工具链切换时重新执行 build.rs
    println!("cargo:rerun-if-env-changed=RUSTUP_TOOLCHAIN");
    println!("cargo:rerun-if-env-changed=RUSTC_BOOTSTRAP");
}

fn is_nightly() -> bool {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let Ok(output) = Command::new(&rustc).arg("--version").output() else {
        return false;
    };
    let version = String::from_utf8_lossy(&output.stdout);
    version.contains("nightly")
}
