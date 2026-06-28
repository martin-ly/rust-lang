//! # c13_embedded - Bare-metal 嵌入式 Rust 学习模块
//!
//! 本 crate 提供 Rust 裸机嵌入式系统学习资源，涵盖 `no_std` 编程、内存映射寄存器、
//! UART 驱动、中断处理、HAL 设计模式、FFI 与 C 互操作，以及 Embassy / RTIC 异步框架。
//!
//! ## 编译说明
//!
//! - **Host 目标** (`x86_64-pc-windows-msvc`): 使用模拟代码演示概念，`cargo check` 可正常通过
//! - **嵌入式目标** (`thumbv7m-none-eabi` 等): 启用 `embedded` feature，使用真实硬件抽象层
//!
//! ## 快速开始
//!
//! ```text
//! # Host 上检查编译
//! cargo check -p c13_embedded
//!
//! # 运行演示程序
//! cargo run -p c13_embedded --bin embedded_demo
//! ```

// [来源: The Embedded Rust Book / Rust Reference]
#![cfg_attr(target_arch = "arm", no_std)]
#![cfg_attr(nightly, feature(core_intrinsics, fn_align))]
#![cfg_attr(nightly, allow(internal_features))]
#![allow(clippy::module_name_repetitions)]

// 核心模块
pub mod bare_metal_basics;
pub mod cxx_interop;
pub mod embassy_framework; // Embassy 异步嵌入式框架
pub mod ffi_c_interop;
pub mod hal_design_patterns;
pub mod interrupt_handling;
pub mod memory_mapped_registers;
pub mod no_std_practices;
pub mod raw_pointers_advanced;
pub mod rtic_framework;
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_192_features;
pub mod rust_193_features;
pub mod rust_195_features; // Rust 1.95 特性 (裸指针 unchecked, PowerPC asm, cfg_select 嵌入式)
pub mod rust_196_features; // Rust 1.96.0+ 特性 (assert_matches!, core::range, From<T> for LazyCell/LazyLock, ManuallyDrop 模式)
pub mod rust_197_features;
#[cfg(nightly)]
pub mod rust_198_features;

pub mod uart_driver; // RTIC 实时中断驱动并发

// 库版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 返回当前库的名称、版本与编译目标。
pub fn get_library_info() -> LibraryInfo {
    LibraryInfo {
        name: "c13_embedded",
        version: VERSION,
        target: if cfg!(target_arch = "arm") {
            "embedded (ARM)"
        } else {
            "host (simulation)"
        },
    }
}

/// 库元信息结构体。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LibraryInfo {
    /// 库名称
    pub name: &'static str,
    /// 版本号
    pub version: &'static str,
    /// 当前编译目标（host 模拟或嵌入式 ARM）
    pub target: &'static str,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_library_info() {
        let info = get_library_info();
        assert_eq!(info.name, "c13_embedded");
        assert!(!info.version.is_empty());
    }
}
