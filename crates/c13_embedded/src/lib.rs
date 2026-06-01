//! Lib

// [来源: The Embedded Rust Book / Rust Reference]
//! Embedded Rust: no_std, bare-metal, RTOS, and hardware abstraction.
#![cfg_attr(target_arch = "arm", no_std)]
#![feature(core_intrinsics, fn_align)]
#![allow(internal_features)]
#![allow(clippy::module_name_repetitions)]

//! # C13 Embedded - Bare-metal 嵌入式 Rust 学习模块
//! # C13 Embedded - Bare-metal 嵌入式 Rust learnmodule
//! This crate providescomplete bare-metal 嵌入式 Rust 编程Example of，包括：
//! - `no_std` 环境编程
//! - `no_std` environment
//! - 内存映射寄存器 (MMIO) 操作
//! - memory mapping (MMIO) operation
//! - memory mapping (MMIO)
//! - UART 驱动设计
//! - UART driver design
//! - 中断处理
//! - in
//! - in断Handle
//! - HAL 设计模式（类型状态）
//! - HAL design （type state ）
//! - C 语言互操作 (FFI)
//! - C operation (FFI)
//! - C (FFI)
//! ## 编译说明
//! ## explain
//! ## 编译explain
//! - **Host 目标** (`x86_64-pc-windows-msvc`): 使用模拟代码演示概念，`cargo check` 可正常通过
//! - **Host goal ** (`x86_64-pc-windows-msvc`): demonstration concept ，`cargo check`
//! - **Host goal** (`x86_64-pc-windows-msvc`): Use模拟代码Demonstration ofconcept，`cargo check` 可正常Via
//! - **嵌入式目标** (`thumbv7m-none-eabi` 等): 启用 `embedded` feature，使用真实硬件抽象层
//! - **goal ** (`thumbv7m-none-eabi` etc. ): `embedded` feature，real hardware
//! ## 快速开始
//! ## fast
//! # Host 上检查编译
//! # Host on
//! # 运行演示程序
//! # Run demonstration program
//! ```

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
pub mod rust_190_features;
pub mod rust_191_features;
pub mod rust_192_features;
pub mod rust_193_features;
pub mod rust_195_features; // Rust 1.95 特性 (裸指针 unchecked, PowerPC asm, cfg_select 嵌入式)
pub mod rust_196_features; // Rust 1.96.0+ 特性 (assert_matches!, core::range, From<T> for LazyCell/LazyLock, ManuallyDrop 模式)
pub mod rust_197_features;
pub mod rust_198_features;

pub mod uart_driver; // RTIC 实时中断驱动并发

// 库版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 获取库信息
/// library
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

/// 库信息结构体
/// library struct
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LibraryInfo {
    /// 库名称
    /// library
    pub name: &'static str,
    /// 版本号
    /// this
    pub version: &'static str,
    /// 当前编译目标
    /// when before goal
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
