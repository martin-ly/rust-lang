#![cfg_attr(target_arch = "arm", no_std)]
#![allow(clippy::empty_line_after_doc_comments)]
#![allow(clippy::duplicated_attributes)]
#![allow(clippy::module_name_repetitions)]

//! # C13 Embedded - Bare-metal 嵌入式 Rust 学习模块
//!
//! 本 crate 提供完整的 bare-metal 嵌入式 Rust 编程示例，包括：
//! - `no_std` 环境编程
//! - 内存映射寄存器 (MMIO) 操作
//! - UART 驱动设计
//! - 中断处理
//! - HAL 设计模式（类型状态）
//! - C 语言互操作 (FFI)
//!
//! ## 编译说明
//!
//! - **Host 目标** (`x86_64-pc-windows-msvc`): 使用模拟代码演示概念，`cargo check` 可正常通过
//! - **嵌入式目标** (`thumbv7m-none-eabi` 等): 启用 `embedded` feature，使用真实硬件抽象层
//!
//! ## 快速开始
//!
//! ```bash
//! # Host 上检查编译
//! cargo check -p c13_embedded
//!
//! # 运行演示程序
//! cargo run -p c13_embedded --bin embedded_demo
//! ```

// 核心模块
pub mod bare_metal_basics;
pub mod ffi_c_interop;
pub mod hal_design_patterns;
pub mod interrupt_handling;
pub mod memory_mapped_registers;
pub mod no_std_practices;
pub mod uart_driver;

// 库版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 获取库信息
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LibraryInfo {
    /// 库名称
    pub name: &'static str,
    /// 版本号
    pub version: &'static str,
    /// 当前编译目标
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
