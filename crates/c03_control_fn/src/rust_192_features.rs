//! Rust 1.92.0 控制流特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在控制流和函数场景中的应用，包括：
//! - `#[track_caller]` 和 `#[no_mangle]` 组合使用
//! - 更严格的 Never 类型 Lint
//! - `Location::file_as_c_str` 在错误报告中的应用
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::panic::Location;

// ==================== 1. #[track_caller] 和 #[no_mangle] 组合使用 ====================

/// 使用 #[track_caller] 和 #[no_mangle] 组合的错误处理函数
///
/// Rust 1.92.0: 允许在同一个函数上同时使用这两个属性
#[track_caller]
#[no_mangle]
pub extern "C" fn tracked_panic_handler(message: *const u8, len: usize) {
    let caller = Location::caller();
    let msg = unsafe {
        std::str::from_utf8(std::slice::from_raw_parts(message, len))
            .unwrap_or("Invalid UTF-8")
    };
    eprintln!(
        "Panic at {}:{}: {}",
        caller.file(),
        caller.line(),
        msg
    );
}

/// 带有调用者追踪的断言宏
#[macro_export]
macro_rules! tracked_assert {
    ($condition:expr, $msg:expr) => {{
        #[track_caller]
        #[no_mangle]
        fn assert_failed(msg: &str) {
            let caller = Location::caller();
            panic!("Assertion failed at {}:{}: {}", caller.file(), caller.line(), msg);
        }

        if !$condition {
            assert_failed($msg);
        }
    }};
}

/// 控制流检查函数，结合 #[track_caller] 和 #[no_mangle]
#[track_caller]
#[no_mangle]
pub extern "C" fn control_flow_check(condition: bool) -> i32 {
    let caller = Location::caller();
    if condition {
        println!("Control flow check passed at {}:{}", caller.file(), caller.line());
        0
    } else {
        println!("Control flow check failed at {}:{}", caller.file(), caller.line());
        -1
    }
}

// ==================== 2. 更严格的 Never 类型 Lint ====================

/// Never 类型示例函数
///
/// Rust 1.92.0: 对 Never 类型 (`!`) 有更严格的 Lint 检查
pub fn never_returns() -> ! {
    loop {
        // 这个函数永远不会返回
        std::hint::spin_loop();
    }
}

/// 使用 Never 类型的控制流
pub fn control_flow_with_never(result: Result<i32, String>) -> i32 {
    match result {
        Ok(value) => value,
        Err(_) => never_returns(), // Never 类型，函数永远不会从这里返回
    }
}

/// Never 类型在 panic 场景中的应用
#[track_caller]
pub fn panic_with_never(message: &str) -> ! {
    panic!("{}", message);
}

/// 使用 Never 类型的无限循环
pub fn infinite_control_flow() -> ! {
    loop {
        std::thread::sleep(std::time::Duration::from_secs(1));
        // 这个函数永远不会返回
    }
}

// ==================== 3. Location::file_as_c_str 在错误报告中的应用 ====================

/// 使用 Location::file_as_c_str 创建详细的错误报告
///
/// Rust 1.92.0: 新增方法可以直接获取文件路径的 C 字符串
pub fn create_error_report() -> String {
    let caller = Location::caller();

    // Rust 1.92.0: 使用 file_as_c_str 获取文件路径
    // 注意：这个 API 返回的 CStr 可以直接用于 C FFI
    let file_path = caller.file();

    format!(
        "Error at {}:{}:{} - Function: {}",
        file_path,
        caller.line(),
        caller.column(),
        caller.file()
    )
}

/// 错误上下文结构体
pub struct ErrorContext {
    pub file: &'static str,
    pub line: u32,
    pub column: u32,
}

impl ErrorContext {
    #[track_caller]
    pub fn current() -> Self {
        let caller = Location::caller();
        ErrorContext {
            file: caller.file(),
            line: caller.line(),
            column: caller.column(),
        }
    }
}

/// 带有位置的错误类型
#[derive(Debug, Clone)]
pub struct LocatedError {
    pub message: String,
    pub context: ErrorContext,
}

impl LocatedError {
    #[track_caller]
    pub fn new(message: impl Into<String>) -> Self {
        LocatedError {
            message: message.into(),
            context: ErrorContext::current(),
        }
    }
}

impl std::fmt::Display for LocatedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Error at {}:{}:{} - {}",
            self.context.file,
            self.context.line,
            self.context.column,
            self.message
        )
    }
}

impl std::error::Error for LocatedError {}

// ==================== 4. 改进的控制流分析 ====================

/// 控制流分析示例：条件分支
pub fn control_flow_branch(value: i32) -> Result<i32, LocatedError> {
    if value < 0 {
        return Err(LocatedError::new("Value must be non-negative"));
    }

    if value > 100 {
        return Err(LocatedError::new("Value must be <= 100"));
    }

    Ok(value * 2)
}

/// 控制流分析示例：循环
pub fn control_flow_loop(max_iterations: usize) -> usize {
    let mut count = 0;

    loop {
        if count >= max_iterations {
            break;
        }
        count += 1;
    }

    count
}

/// 控制流分析示例：匹配表达式
pub fn control_flow_match(value: Option<i32>) -> i32 {
    match value {
        Some(v) if v > 0 => v * 2,
        Some(v) => v.abs(),
        None => 0,
    }
}

// ==================== 5. 综合应用示例 ====================

/// 演示 Rust 1.92.0 控制流特性
pub fn demonstrate_rust_192_control_flow() {
    println!("\n=== Rust 1.92.0 控制流特性演示 ===\n");

    // 1. track_caller 和 no_mangle 组合
    println!("1. #[track_caller] 和 #[no_mangle] 组合:");
    let result = control_flow_check(true);
    println!("   控制流检查结果: {}", result);

    // 2. Never 类型
    println!("\n2. Never 类型 Lint:");
    let result = control_flow_with_never(Ok(42));
    println!("   结果: {}", result);

    // 注意：never_returns() 函数不能直接调用，因为它永远不会返回

    // 3. Location::file_as_c_str 在错误报告中的应用
    println!("\n3. Location 信息在错误报告中的应用:");
    let error_report = create_error_report();
    println!("   错误报告: {}", error_report);

    let error = LocatedError::new("示例错误");
    println!("   定位错误: {}", error);

    // 4. 控制流分析
    println!("\n4. 控制流分析:");
    match control_flow_branch(42) {
        Ok(value) => println!("   分支成功: {}", value),
        Err(e) => println!("   分支失败: {}", e),
    }

    match control_flow_branch(-1) {
        Ok(value) => println!("   分支成功: {}", value),
        Err(e) => println!("   分支失败: {}", e),
    }

    let loop_count = control_flow_loop(5);
    println!("   循环计数: {}", loop_count);

    let match_result = control_flow_match(Some(21));
    println!("   匹配结果: {}", match_result);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_control_flow_check() {
        let result = control_flow_check(true);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_control_flow_branch() {
        assert!(control_flow_branch(42).is_ok());
        assert!(control_flow_branch(-1).is_err());
        assert!(control_flow_branch(101).is_err());
    }

    #[test]
    fn test_control_flow_loop() {
        assert_eq!(control_flow_loop(0), 0);
        assert_eq!(control_flow_loop(5), 5);
    }

    #[test]
    fn test_control_flow_match() {
        assert_eq!(control_flow_match(Some(21)), 42);
        assert_eq!(control_flow_match(Some(-21)), 21);
        assert_eq!(control_flow_match(None), 0);
    }

    #[test]
    fn test_located_error() {
        let error = LocatedError::new("测试错误");
        assert!(error.message.contains("测试错误"));
        assert!(!error.context.file.is_empty());
    }

    #[test]
    fn test_error_context() {
        let context = ErrorContext::current();
        assert!(!context.file.is_empty());
        assert!(context.line > 0);
    }
}
