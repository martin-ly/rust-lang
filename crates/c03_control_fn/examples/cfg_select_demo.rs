//! Rust 1.95.0 `cfg_select!` 宏专题示例
//! Rust 1.95.0 `cfg_select!` 宏专题Example of
//! 权威来源: https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/
//! 权威source: https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/
//! 运行方式:
//! Run way :
//! cargo run --example cfg_select_demo -p c03_control_fn
//! ```

use std::env;

// ==================== 示例 1: 跨平台函数定义 ====================

// 获取操作系统名称
//
// `cfg_select!` 在编译期根据目标平台选择正确的实现。
cfg_select! {
    target_os = "windows" => {
        fn get_os_name() -> &'static str {
            "Windows"
        }
    }
    target_os = "macos" => {
        fn get_os_name() -> &'static str {
            "macOS"
        }
    }
    target_os = "linux" => {
        fn get_os_name() -> &'static str {
            "Linux"
        }
    }
    _ => {
        fn get_os_name() -> &'static str {
            "Unknown OS"
        }
    }
}

// 获取平台架构名称
cfg_select! {
    target_arch = "x86_64" => {
        fn get_arch_name() -> &'static str {
            "x86_64"
        }
    }
    target_arch = "aarch64" => {
        fn get_arch_name() -> &'static str {
            "ARM64 (AArch64)"
        }
    }
    target_arch = "riscv64" => {
        fn get_arch_name() -> &'static str {
            "RISC-V 64"
        }
    }
    _ => {
        fn get_arch_name() -> &'static str {
            "Unknown Architecture"
        }
    }
}

// ==================== 示例 2: 表达式级条件编译 ====================

/// 获取当前平台的最大文件描述符数量（示意值）
/// when before platform maximum file descriptor quantity （indicate ）
fn get_max_fds() -> u32 {
    cfg_select! {
        target_os = "windows" => 8192,
        target_os = "linux" => 1048576,
        target_os = "macos" => 10240,
        _ => 4096,
    }
}

/// 获取路径分隔符
fn get_path_separator() -> char {
    cfg_select! {
        target_os = "windows" => '\\',
        _ => '/',
    }
}

/// 获取行尾序列
/// sequence
/// Get行尾sequence
fn get_line_ending() -> &'static str {
    cfg_select! {
        target_os = "windows" => "\r\n",
        _ => "\n",
    }
}

// ==================== 示例 3: 特性标志条件编译 ====================

// 根据是否启用 `simd` 特性选择实现
cfg_select! {
    feature = "simd" => {
        fn process_data(data: &[i32]) -> i32 {
            println!("[SIMD enabled] Processing with vectorized instructions");
            data.iter().sum()
        }
    }
    _ => {
        fn process_data(data: &[i32]) -> i32 {
            println!("[SIMD disabled] Processing with scalar fallback");
            data.iter().sum()
        }
    }
}

// ==================== 示例 4: 调试/发布模式差异 ====================

/// 获取日志级别
/// level
/// Get日志level
fn get_log_level() -> &'static str {
    cfg_select! {
        debug_assertions => "DEBUG",
        _ => "INFO",
    }
}

/// 获取超时配置（毫秒）
/// timeout configuration （）
/// （）
/// Get超时Configure（毫秒）
fn get_timeout_ms() -> u64 {
    cfg_select! {
        debug_assertions => 300_000, // 调试模式: 5 分钟
        _ => 30_000,                // 发布模式: 30 秒
    }
}

// ==================== 示例 5: 与 cfg! 宏的对比 ====================

/// 使用 `cfg!` 的运行时检查（编译期求值但生成所有分支代码）
/// `cfg!` runtime （but all ）
fn check_platform_with_cfg_macro() -> &'static str {
    if cfg!(target_os = "windows") {
        "Running on Windows (checked at compile-time, all branches exist in IR)"
    } else if cfg!(target_os = "linux") {
        "Running on Linux (checked at compile-time, all branches exist in IR)"
    } else {
        "Running on something else (checked at compile-time, all branches exist in IR)"
    }
}

fn check_platform_with_cfg_select() -> &'static str {
    cfg_select! {
        target_os = "windows" => "Windows-only code compiled",
        target_os = "linux" => "Linux-only code compiled",
        _ => "Fallback code compiled",
    }
}

// ==================== 示例 6: 复杂条件组合 ====================

/// 获取内存页大小（示意值）
/// memory （indicate ）
fn get_page_size() -> usize {
    cfg_select! {
        all(target_os = "windows", target_arch = "x86_64") => 4096,
        all(target_os = "linux", target_arch = "x86_64") => 4096,
        all(target_os = "linux", target_arch = "aarch64") => 4096,
        all(target_os = "macos", target_arch = "aarch64") => 16384,
        _ => 4096,
    }
}

/// 获取指针宽度描述
/// pointer describe
fn get_pointer_width_desc() -> &'static str {
    cfg_select! {
        target_pointer_width = "64" => "64-bit platform",
        target_pointer_width = "32" => "32-bit platform",
        target_pointer_width = "16" => "16-bit platform",
        _ => "unknown pointer width",
    }
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `cfg_select!` 宏专题演示\n");

    println!("--- 示例 1: 跨平台函数定义 ---");
    println!("  操作系统: {}", get_os_name());
    println!("  架构:    {}", get_arch_name());

    println!("\n--- 示例 2: 表达式级条件编译 ---");
    println!("  最大 FD 数: {}", get_max_fds());
    println!("  路径分隔符: {}", get_path_separator());
    println!("  行尾序列: {:?}", get_line_ending());

    println!("\n--- 示例 3: 特性标志条件编译 ---");
    let data = vec![1, 2, 3, 4, 5];
    let sum = process_data(&data);
    println!("  结果: {}", sum);

    println!("\n--- 示例 4: 调试/发布模式差异 ---");
    println!("  日志级别: {}", get_log_level());
    println!("  超时(ms): {}", get_timeout_ms());

    println!("\n--- 示例 5: cfg! vs cfg_select! ---");
    println!("  [cfg! macro]   {}", check_platform_with_cfg_macro());
    println!("  [cfg_select!]  {}", check_platform_with_cfg_select());

    println!("\n--- 示例 6: 复杂条件组合 ---");
    println!("  内存页大小: {} bytes", get_page_size());
    println!("  指针宽度:   {}", get_pointer_width_desc());

    println!("\n--- 环境变量验证 ---");
    println!(
        "  TARGET: {}",
        env::var("TARGET").unwrap_or_else(|_| "unknown".to_string())
    );

    println!("\n✅ `cfg_select!` 演示完成！");
    println!("   提示: 使用 `cargo expand` 查看宏展开结果，确认仅匹配分支被编译。");
}
