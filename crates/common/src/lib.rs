//! Common - 共享公共库
//! 
//! 为 Rust 学习项目提供共享的 trait、错误类型、工具函数和基础类型。
//! 
//! # 特性标志
//! 
//! - `std` - 标准库支持（默认启用）
//! - `alloc` - 分配器支持
//! - `serde` - 序列化支持
//! - `error-trait` - 错误处理 trait
//! - `async` - 异步支持
//! - `tracing` - 日志追踪支持
//! - `full` - 启用所有特性
//! 
//! # 使用示例
//! 
//! ```rust
//! use common::{CommonError, Result, Validatable};
//! 
//! fn example() -> Result<()> {
//!     // 使用共享错误类型
//!     Err(CommonError::NotFound("item".into()))
//! }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "alloc")]
extern crate alloc;

// 错误类型模块
#[cfg(feature = "error-trait")]
pub mod error;

// Trait 定义模块
pub mod traits;

// 基础类型模块
pub mod types;

// 工具函数模块
pub mod utils;

// 重新导出常用项
#[cfg(feature = "error-trait")]
pub use error::{CommonError, Result};

pub use traits::*;
pub use types::*;

/// 库版本
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 获取库版本
pub fn version() -> &'static str {
    VERSION
}

/// 检查特性是否启用
pub mod features {
    /// 检查 serde 特性是否启用
    pub const fn serde_enabled() -> bool {
        cfg!(feature = "serde")
    }
    
    /// 检查 async 特性是否启用
    pub const fn async_enabled() -> bool {
        cfg!(feature = "async")
    }
    
    /// 检查 tracing 特性是否启用
    pub const fn tracing_enabled() -> bool {
        cfg!(feature = "tracing")
    }
}

/// 初始化 common 库
/// 
/// # Panics
/// 
/// 如果初始化失败会 panic
#[cfg(feature = "tracing")]
pub fn init() {
    use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};
    
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();
}

#[cfg(not(feature = "tracing"))]
pub fn init() {
    // 无 tracing 时的空初始化
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_version() {
        assert!(!version().is_empty());
    }
    
    #[test]
    fn test_features() {
        // 这些测试根据启用的特性而变化
        println!("serde enabled: {}", features::serde_enabled());
        println!("async enabled: {}", features::async_enabled());
        println!("tracing enabled: {}", features::tracing_enabled());
    }
}
