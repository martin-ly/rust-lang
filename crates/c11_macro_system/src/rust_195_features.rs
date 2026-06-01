//! Rust 195 Features

#![allow(unexpected_cfgs)]

//! Rust 1.95.0 宏系统新特性实现模块
//! Rust 1.95.0 system feature module
//! - `cfg_select!` 宏 ⭐
//! # 版本信息
//! # this
//! - 稳定日期: 2026-04-16
//! - date : 2026-04-16
//! - 稳定date: 2026-04-16
//! - date: 2026-04-16
//! # 参考
//! # reference
//! - [core::macros 文档](https://doc.rust-lang.org/core/macro.cfg_select.html)

// ============================================================================
// 1. cfg_select! 宏深度解析
// ============================================================================

/// # `cfg_select!` 宏
/// ## 概念定义
/// ## concept definition
/// 选择**第一个满足条件的表达式**。它是嵌套 `cfg!` 或 `#[cfg]` 属性的
/// **first condition express **。 `cfg!` or `#[cfg]` attribute
/// 简洁替代方案。
/// 。
/// ## 语法形式
/// ## syntax
/// ##
///     cfg1 => expr1,
///     cfg2 => expr2,
///     _ => fallback_expr, // 可选默认分支
///     _ => fallback_expr, //
///
/// ## Wikipedia 概念对齐
/// - **Conditional Compilation**: 根据目标平台/特性选择不同代码路径
/// - **Conditional Compilation**: according to goal platform /feature
/// ## 对比：传统方式 vs cfg_select!
/// ## to ：way vs cfg_select!
/// ## to比：传统way vs cfg_select!
/// | 维度 | `#[cfg]` 属性 | `cfg!` 宏 | `cfg_select!` (1.95+) |
/// | dimension | `#[cfg]` attribute | `cfg!` 宏 | `cfg_select!` (1.95+) |
/// | 适用位置 | 项级别 (item) | 表达式级别 | 表达式级别 |
/// | position | level (item) | express level | express level |
/// | 语法冗长度 | 高（需重复定义） | 中（嵌套 if） | 低（类 match） |
/// | syntax | high （definition ） | in （ if） | low （ match） |
/// | | （definition ） | in （ if） | （ match） |
/// | 默认分支 | 不支持 | 需显式 else | `_ =>` 清晰表达 |
/// | | | else | `_ =>` clear express |
/// | 默认分支 | 不Supports | 需显式 else | `_ =>` clearexpress |
/// | 组合条件 | 复杂 | 复杂 | 自然扁平 |
/// | combination condition | complex | complex | |
/// | combinationcondition | complex | complex | 自然扁平 |
/// | 返回值统一性 | N/A | 需确保类型一致 | 编译器强制类型一致 |
/// | return value | N/A | type | type |
/// ## 决策树：何时使用什么？
/// ## tree ：？
/// 需要根据 cfg 条件选择代码？
/// according to cfg condition ？
/// ├── 选择整个函数/结构体/模块？ → #[cfg]
/// ├── function /struct /module ？ → #[cfg]
/// ├── 选择整个function/struct/module？ → #[cfg]
/// ├── 选择语句块内的不同实现？
/// ├── inside ？
/// │   ├── 条件简单（1-2个）→ cfg! + if/else
/// │ ├── condition simple （1-2）→ cfg! + if/else
/// │ ├── conditionsimple（1-2个）→ cfg! + if/else
/// │   └── 条件复杂或多分支？ → cfg_select!
/// │ └── condition complex or ？ → cfg_select!
/// └── 需要表达式值？ → cfg_select!
/// └── express ？ → cfg_select!
/// ## 反例 / 限制
/// ## anti-pattern /
/// ## /
/// - 不Supports `cfg_attr` attribute 注入scenario
pub struct CfgSelectExamples;

impl CfgSelectExamples {
    /// 基础示例：选择平台特定的最大路径长度
    /// foundation example ：platform maximum
    /// 传统 `cfg!` 方式需要嵌套 if-else，而 `cfg_select!` 扁平化表达。
    /// `cfg!` way if-else，while `cfg_select!` express 。
    pub fn max_path_length_cfg_bang() -> usize {
        // 传统方式：嵌套 if-else
        if cfg!(target_os = "windows") {
            260
        } else if cfg!(target_os = "linux") {
            4096
        } else if cfg!(target_os = "macos") {
            1024
        } else {
            4096 // fallback
        }
    }

    /// 现代方式获取最大路径长度
    /// way maximum
    /// 使用 `cfg_select!` 扁平化条件选择。
    /// `cfg_select!` condition 。
    pub fn max_path_length_modern() -> usize {
        // 现代方式：cfg_select! 扁平化
        cfg_select! {
            target_os = "windows" => 260,
            target_os = "linux" => 4096,
            target_os = "macos" => 1024,
            _ => 4096, // 默认分支
        }
    }

    /// 特性标志选择：选择哈希算法实现
    /// feature mark ：algorithm
    /// 根据编译时启用的特性选择不同的哈希函数。
    /// according to compile-time feature function 。
    pub fn select_hasher() -> &'static str {
        cfg_select! {
            feature = "blake3" => "blake3",
            feature = "sha256" => "sha256",
            feature = "md5" => "md5",
            _ => "default-fnv",
        }
    }

    /// 架构特定优化：选择 SIMD 宽度
    /// architecture optimization ： SIMD
    pub fn simd_lane_count() -> usize {
        cfg_select! {
            target_feature = "avx512f" => 16,
            target_feature = "avx2" => 8,
            target_feature = "sse2" => 4,
            target_feature = "neon" => 4,
            _ => 1, // 标量回退
        }
    }

    /// 组合条件：目标架构 + 指针宽度
    /// combination condition ：goal architecture + pointer
    /// 展示了复杂条件的选择逻辑。
    /// complex condition 。
    pub fn pointer_optimized_size() -> usize {
        cfg_select! {
            all(target_arch = "x86_64", target_pointer_width = "64") => 64,
            all(target_arch = "aarch64", target_pointer_width = "64") => 64,
            target_pointer_width = "32" => 32,
            _ => 32,
        }
    }

    /// 与常量定义结合
    /// and constant definition
    pub const COMPILE_TIME_PAGE_SIZE: usize = cfg_select! {
        target_os = "windows" => 4096,
        target_os = "linux" => 4096,
        target_os = "macos" => 16384,
        _ => 4096,
    };

    /// 与函数指针结合：选择平台特定的系统调用包装
    /// and function pointer ：platform system
    /// 所有分支必须返回相同类型（函数指针类型）。
    /// all must type （function pointer type ）。
    pub fn select_syscall_wrapper() -> fn(i32) -> i32 {
        cfg_select! {
            target_os = "linux" => linux_wrapper,
            target_os = "macos" => macos_wrapper,
            target_os = "windows" => windows_wrapper,
            _ => generic_wrapper,
        }
    }

    /// 错误码映射：平台特定的错误码转换
    /// error code ：platform error code conversion
    pub fn platform_error_name(code: i32) -> &'static str {
        cfg_select! {
            target_family = "unix" => unix_error_name(code),
            target_family = "windows" => windows_error_name(code),
            _ => unknown_error_name(code),
        }
    }
}

#[allow(dead_code)]
fn linux_wrapper(fd: i32) -> i32 {
    fd + 1
}
#[allow(dead_code)]
fn macos_wrapper(fd: i32) -> i32 {
    fd + 2
}
#[allow(dead_code)]
fn windows_wrapper(fd: i32) -> i32 {
    fd + 3
}
#[allow(dead_code)]
fn generic_wrapper(fd: i32) -> i32 {
    fd
}

#[allow(dead_code)]
fn unix_error_name(code: i32) -> &'static str {
    match code {
        2 => "ENOENT",
        13 => "EACCES",
        _ => "UNKNOWN_UNIX",
    }
}

#[allow(dead_code)]
fn windows_error_name(code: i32) -> &'static str {
    match code {
        2 => "ERROR_FILE_NOT_FOUND",
        5 => "ERROR_ACCESS_DENIED",
        _ => "UNKNOWN_WIN32",
    }
}

#[allow(dead_code)]
fn unknown_error_name(_code: i32) -> &'static str {
    "UNKNOWN"
}

// ============================================================================
// 2. 与 build.rs / 编译脚本结合的高级用法
// ============================================================================

/// 构建清晰的跨平台代码结构。
/// clear platform structure 。
pub struct CrossPlatformPatterns;

impl CrossPlatformPatterns {
    /// 选择平台特定的路径分隔符
    /// platform
    pub const PATH_SEPARATOR: char = cfg_select! {
        target_os = "windows" => '\\',
        _ => '/',
    };

    /// 选择行尾序列
    /// sequence
    pub const LINE_ENDING: &'static str = cfg_select! {
        target_os = "windows" => "\r\n",
        _ => "\n",
    };

    /// 最大文件描述符数量提示
    /// maximum file descriptor quantity hint
    pub const FD_LIMIT_HINT: usize = cfg_select! {
        target_os = "linux" => 1024,
        target_os = "macos" => 256,
        target_os = "windows" => 512,
        _ => 256,
    };

    /// 线程栈大小默认值（平台特定）
    /// thread stack （platform ）
    pub const DEFAULT_STACK_SIZE: usize = cfg_select! {
        target_os = "linux" => 2 * 1024 * 1024,    // 2MB
        target_os = "macos" => 2 * 1024 * 1024,    // 2MB
        target_os = "windows" => 1024 * 1024,  // 1MB
        _ => 2 * 1024 * 1024,
    };
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cfg_select_max_path() {
        // 在测试目标上，通常不是 windows/linux/macos 之一，所以回退到默认
        let len = CfgSelectExamples::max_path_length_modern();
        assert!(len == 260 || len == 4096 || len == 1024);
    }

    #[test]
    fn test_cfg_select_page_size() {
        const { assert!(CfgSelectExamples::COMPILE_TIME_PAGE_SIZE > 0) };
    }

    #[test]
    fn test_cfg_select_syscall_wrapper() {
        let wrapper = CfgSelectExamples::select_syscall_wrapper();
        // 简化：只要调用不 panic 即可，具体值取决于平台
        let _ = wrapper(10);
        let _ = wrapper(42);
    }

    #[test]
    fn test_cfg_select_error_name() {
        let name = CfgSelectExamples::platform_error_name(999);
        assert!(
            name == "UNKNOWN_UNIX" || name == "UNKNOWN_WIN32" || name == "UNKNOWN",
            "unexpected error name: {}",
            name
        );
    }

    #[test]
    fn test_cross_platform_patterns() {
        assert!(
            CrossPlatformPatterns::PATH_SEPARATOR == '\\'
                || CrossPlatformPatterns::PATH_SEPARATOR == '/'
        );
        assert!(
            CrossPlatformPatterns::LINE_ENDING == "\r\n"
                || CrossPlatformPatterns::LINE_ENDING == "\n"
        );
        const { assert!(CrossPlatformPatterns::FD_LIMIT_HINT > 0) };
        const { assert!(CrossPlatformPatterns::DEFAULT_STACK_SIZE >= 1024 * 1024) };
    }

    #[test]
    fn test_cfg_select_simd() {
        let lanes = CfgSelectExamples::simd_lane_count();
        assert!(lanes == 1 || lanes == 4 || lanes == 8 || lanes == 16);
    }
}

// ============================================================================
// 3. RealRust195Features — unsafe_op_in_unsafe_fn, const blocks, if let guards
// ============================================================================

/// # 真实 Rust 1.95 特性演示
/// # real Rust 1.95 feature demonstration
/// 展示 Rust 2024 中 `unsafe fn` 需要显式 `unsafe {}` 块，
pub struct RealRust195Features;

impl RealRust195Features {
    /// Rust 2024 风格 `unsafe fn`
    /// 在 `unsafe fn` 内部，不安全操作仍需显式包裹在 `unsafe {}` 中。
    /// in `unsafe fn` inside ，operation in `unsafe {}` in 。
    /// in `unsafe fn` inside ，in `unsafe {}` in 。
    ///
    /// `ptr` 必须是有效的、正确对齐的指向已初始化 `u32` 的指针。
    /// `ptr` must effective 、to `u32` pointer 。
    pub unsafe fn macro_generated_unsafe_fn(ptr: *const u32) -> u32 {
        // Rust 2024: 必须显式使用 unsafe 块
        unsafe { *ptr }
    }

    pub fn const_block_macro_output() -> [u8; 8] {
        [0u8; const { 4 + 4 }]
    }

    /// 使用 `if let` guard 分类宏标记
    /// `if let` guard classification mark
    pub fn classify_macro_token(token: Option<&str>) -> Result<&'static str, &'static str> {
        match token {
            Some(t)
                if let Ok(n) = t.parse::<i32>()
                    && n > 0 =>
            {
                Ok("positive integer")
            }
            Some("") => Ok("empty token"),
            Some(_) => Ok("other token"),
            None => Err("missing token"),
        }
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_macro_generated_unsafe_fn() {
        let value = 0xDEADBEEF_u32;
        let result = unsafe { RealRust195Features::macro_generated_unsafe_fn(&value) };
        assert_eq!(result, 0xDEADBEEF);
    }

    #[test]
    fn test_const_block_macro_output() {
        let arr = RealRust195Features::const_block_macro_output();
        assert_eq!(arr.len(), 8);
    }

    #[test]
    fn test_classify_macro_token() {
        assert_eq!(
            RealRust195Features::classify_macro_token(Some("42")),
            Ok("positive integer")
        );
        assert_eq!(
            RealRust195Features::classify_macro_token(Some("")),
            Ok("empty token")
        );
        assert_eq!(
            RealRust195Features::classify_macro_token(Some("hello")),
            Ok("other token")
        );
        assert_eq!(
            RealRust195Features::classify_macro_token(None),
            Err("missing token")
        );
    }
}
