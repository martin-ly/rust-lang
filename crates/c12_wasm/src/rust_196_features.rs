//! # Rust 1.96.0 WASM 新特性实现模块

use std::ops::RangeInclusive;

/// Rust 1.96 `if let` guards 在 WASM 中的应用
///
/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// 减少嵌套层级，使代码更扁平、更易读。
pub struct WasmIfLetGuardExamples;

impl WasmIfLetGuardExamples {
    /// 解析 WASM 内存页数
    pub fn parse_memory_pages(input: Option<&str>) -> Result<usize, &'static str> {
        match input {
            Some(s) if let Ok(pages) = s.parse::<usize>() => Ok(pages),
            Some(_) => Err("无效的内存页数"),
            None => Ok(1), // 默认 1 页 (64KB)
        }
    }

    /// 解析 WASM 表大小限制
    pub fn parse_table_limit(input: Option<&str>) -> Result<u32, &'static str> {
        match input {
            Some(s) if let Ok(limit) = s.parse::<u32>() => Ok(limit),
            Some(_) => Err("无效的表大小限制"),
            None => Ok(1000),
        }
    }
}

/// RangeInclusive 在 WASM 中的应用
pub struct WasmRangeExamples;

impl WasmRangeExamples {
    /// 内存页大小检查
    pub fn memory_pages_category(pages: usize) -> &'static str {
        match pages {
            0..=16 => "small",
            17..=64 => "medium",
            65..=256 => "large",
            _ => "huge",
        }
    }

    /// 表大小限制
    pub fn table_size_check(size: usize) -> &'static str {
        match size {
            0..=1000 => "small",
            1001..=10000 => "medium",
            10001..=100000 => "large",
            _ => "excessive",
        }
    }

    /// 数据段大小分级
    pub fn data_segment_tier(size_bytes: usize) -> &'static str {
        match size_bytes {
            0..=1024 => "tiny",
            1025..=65536 => "small",
            65537..=1048576 => "medium",
            1048577..=16777216 => "large",
            _ => "huge",
        }
    }

    /// 调用栈深度检查
    pub fn call_stack_depth_status(depth: usize) -> &'static str {
        match depth {
            0..=100 => "normal",
            101..=500 => "deep",
            501..=1000 => "very_deep",
            _ => "excessive",
        }
    }

    /// 模块批处理
    pub fn batch_wasm_modules(
        total_modules: usize,
        batch_size: usize,
    ) -> Vec<RangeInclusive<usize>> {
        if batch_size == 0 || total_modules == 0 {
            return vec![];
        }

        let mut ranges = Vec::new();
        let mut start = 0;

        while start < total_modules {
            let end = (start + batch_size - 1).min(total_modules - 1);
            ranges.push(start..=end);
            start = end + 1;
        }

        ranges
    }

    /// 性能指标分级
    pub fn performance_tier(instructions: u64) -> &'static str {
        match instructions {
            0..=1000 => "instant",
            1001..=10000 => "fast",
            10001..=100000 => "moderate",
            100001..=1000000 => "slow",
            _ => "very_slow",
        }
    }
}

/// 元组 coercion 示例
pub struct WasmTupleExamples;

impl WasmTupleExamples {
    /// WASM 调用结果
    pub fn wasm_call_result<T>(
        result: Result<T, String>,
        function: &str,
    ) -> (Result<T, String>, String, u64, &'static str)
    where
        T: Clone,
    {
        let gas_used = 1000;
        let status = if result.is_ok() { "success" } else { "failed" };
        (result, function.to_string(), gas_used, status)
    }

    /// 内存统计
    pub fn memory_stats(
        allocated: usize,
        used: usize,
    ) -> (usize, usize, f64, &'static str) {
        let utilization = if allocated > 0 {
            (used as f64 / allocated as f64) * 100.0
        } else {
            0.0
        };

        let efficiency = if utilization > 90.0 {
            "high"
        } else if utilization > 50.0 {
            "medium"
        } else {
            "low"
        };

        (allocated, used, utilization, efficiency)
    }

    /// 模块信息
    pub fn module_info(
        name: &str,
        version: (u8, u8, u8),
    ) -> (String, u8, u8, u8, &'static str) {
        let (major, minor, patch) = version;
        (name.to_string(), major, minor, patch, "loaded")
    }

    /// 导出函数信息
    pub fn export_function_info(
        name: &str,
        params: usize,
        returns: usize,
    ) -> (String, usize, usize, &'static str, bool) {
        let valid = params <= 10 && returns <= 1;
        let kind = if returns == 0 { "procedure" } else { "function" };
        (name.to_string(), params, returns, kind, valid)
    }
}

/// 实际应用
pub struct PracticalWasmExamples;

impl PracticalWasmExamples {
    /// 内存预算检查
    pub fn memory_budget_check(
        current: usize,
        requested: usize,
        budget: RangeInclusive<usize>,
    ) -> (bool, &'static str) {
        let new_total = current + requested;
        let allowed = budget.contains(&new_total);
        let status = if allowed { "approved" } else { "denied" };
        (allowed, status)
    }

    /// 实例化性能分级
    pub fn instantiation_tier(time_ms: u64) -> &'static str {
        match time_ms {
            0..=10 => "instant",
            11..=100 => "fast",
            101..=1000 => "moderate",
            1001..=5000 => "slow",
            _ => "very_slow",
        }
    }

    /// WASM 执行摘要
    pub fn wasm_execution_summary(
        calls: &[Result<(), String>],
        total_gas: u64,
    ) -> (usize, usize, u64, f64, &'static str) {
        let success = calls.iter().filter(|r| r.is_ok()).count();
        let failure = calls.len() - success;
        let avg_gas = if !calls.is_empty() {
            total_gas as f64 / calls.len() as f64
        } else {
            0.0
        };

        let status = if failure == 0 {
            "perfect"
        } else if failure <= calls.len() / 10 {
            "good"
        } else if failure <= calls.len() / 4 {
            "degraded"
        } else {
            "failed"
        };

        (success, failure, total_gas, avg_gas, status)
    }
}

/// WASM 模块管理器
pub struct WasmModuleManager {
    module_ranges: Vec<RangeInclusive<usize>>,
    active_range: RangeInclusive<usize>,
}

impl WasmModuleManager {
    /// 创建新管理器
    pub fn new(module_count: usize, batch_size: usize) -> Self {
        let ranges = WasmRangeExamples::batch_wasm_modules(module_count, batch_size);
        Self {
            module_ranges: ranges.clone(),
            active_range: 0..=ranges.len().saturating_sub(1),
        }
    }

    /// 获取模块范围
    pub fn get_module_range(&self, batch_id: usize) -> Option<&RangeInclusive<usize>> {
        self.module_ranges.get(batch_id)
    }

    /// 检查批次是否活跃
    pub fn is_batch_active(&self, batch_id: usize) -> bool {
        self.active_range.contains(&batch_id)
    }

    /// 获取所有范围
    pub fn get_all_ranges(&self) -> &[RangeInclusive<usize>] {
        &self.module_ranges
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 WASM 新特性演示");
    println!("========================================\n");

    let pages_cat = WasmRangeExamples::memory_pages_category(32);
    println!("内存页数32类别: {}", pages_cat);

    let table_cat = WasmRangeExamples::table_size_check(5000);
    println!("表大小5000类别: {}", table_cat);

    let data_tier = WasmRangeExamples::data_segment_tier(100000);
    println!("数据段100KB等级: {}", data_tier);

    let stack_status = WasmRangeExamples::call_stack_depth_status(200);
    println!("调用栈深度200状态: {}", stack_status);

    let perf_tier = WasmRangeExamples::performance_tier(50000);
    println!("50000指令性能等级: {}", perf_tier);

    let (alloc, used, util, eff) = WasmTupleExamples::memory_stats(1024, 768);
    println!("内存统计: 分配={}, 使用={}, 利用率={:.1}%, 效率={}",
             alloc, used, util, eff);

    let manager = WasmModuleManager::new(20, 5);
    println!("模块范围: {:?}", manager.get_all_ranges());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_wasm_info() -> String {
    "Rust 1.96.0 WASM 新特性:\n\
        - RangeInclusive for memory and stack management\n\
        - Tuple coercion for WASM call results\n\
        - Better performance tier classification\n\
        - Improved module batch loading"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_pages_category() {
        assert_eq!(WasmRangeExamples::memory_pages_category(8), "small");
        assert_eq!(WasmRangeExamples::memory_pages_category(32), "medium");
        assert_eq!(WasmRangeExamples::memory_pages_category(128), "large");
    }

    #[test]
    fn test_data_segment_tier() {
        assert_eq!(WasmRangeExamples::data_segment_tier(512), "tiny");
        assert_eq!(WasmRangeExamples::data_segment_tier(32768), "small");
        assert_eq!(WasmRangeExamples::data_segment_tier(524288), "medium");
    }

    #[test]
    fn test_performance_tier() {
        assert_eq!(WasmRangeExamples::performance_tier(500), "instant");
        assert_eq!(WasmRangeExamples::performance_tier(5000), "fast");
        assert_eq!(WasmRangeExamples::performance_tier(50000), "moderate");
    }

    #[test]
    fn test_memory_stats() {
        let (alloc, used, util, _eff) = WasmTupleExamples::memory_stats(1024, 768);
        assert_eq!(alloc, 1024);
        assert_eq!(used, 768);
        assert!((util - 75.0).abs() < 0.1);
    }

    #[test]
    fn test_export_function_info() {
        let (name, params, returns, kind, valid) =
            WasmTupleExamples::export_function_info("add", 2, 1);
        assert_eq!(name, "add");
        assert_eq!(params, 2);
        assert_eq!(returns, 1);
        assert_eq!(kind, "function");
        assert!(valid);
    }

    #[test]
    fn test_memory_budget_check() {
        let (allowed, status) =
            PracticalWasmExamples::memory_budget_check(512, 256, 0..=1024);
        assert!(allowed);
        assert_eq!(status, "approved");
    }

    #[test]
    fn test_instantiation_tier() {
        assert_eq!(PracticalWasmExamples::instantiation_tier(5), "instant");
        assert_eq!(PracticalWasmExamples::instantiation_tier(50), "fast");
    }

    #[test]
    fn test_wasm_module_manager() {
        let manager = WasmModuleManager::new(20, 5);
        assert_eq!(manager.get_all_ranges().len(), 4);
        assert!(manager.is_batch_active(0));
    }

    #[test]
    fn test_parse_memory_pages() {
        assert_eq!(WasmIfLetGuardExamples::parse_memory_pages(Some("16")), Ok(16));
        assert_eq!(
            WasmIfLetGuardExamples::parse_memory_pages(Some("abc")),
            Err("无效的内存页数")
        );
        assert_eq!(WasmIfLetGuardExamples::parse_memory_pages(None), Ok(1));
    }

    #[test]
    fn test_parse_table_limit() {
        assert_eq!(
            WasmIfLetGuardExamples::parse_table_limit(Some("10000")),
            Ok(10000)
        );
        assert_eq!(
            WasmIfLetGuardExamples::parse_table_limit(Some("abc")),
            Err("无效的表大小限制")
        );
        assert_eq!(WasmIfLetGuardExamples::parse_table_limit(None), Ok(1000));
    }

    #[test]
    fn test_get_rust_196_wasm_info() {
        let info = get_rust_196_wasm_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}


// ==================== Rust 2024 Edition: unsafe extern blocks 安全 FFI ====================
//
// Rust 2024 Edition 引入了 `unsafe extern "C" { ... }` 语法，
// 将 FFI 声明块整体标记为 unsafe，符合 Rust 的安全哲学：
// 外部函数调用 inherently unsafe，应在调用点显式使用 `unsafe`。
//
// ## 语法对比
// ```rust,ignore
// // Rust 2021 及之前
// extern "C" {
//     fn strlen(s: *const c_char) -> usize;
// }
// // 调用时：unsafe { strlen(ptr) }
//
// // Rust 2024 Edition
// unsafe extern "C" {
//     fn strlen(s: *const c_char) -> usize;
// }
// // 调用时仍需：unsafe { strlen(ptr) }
// // 区别：声明本身明确表达了"这是不安全的接口"
// ```

// 标准 C 库函数声明（Rust 2024 语法）
//
// `unsafe extern "C"` 明确表示这些函数来自外部不安全代码，
// 调用者必须负责满足前置条件（如有效指针、正确内存布局等）。
#[cfg(not(target_arch = "wasm32"))]
unsafe extern "C" {
    /// 计算 C 字符串长度（以 null 结尾）
    ///
    /// # Safety
    /// - `s` 必须指向以 null 结尾的有效 C 字符串
    /// - 内存必须可读取直至 null 终止符
    fn strlen(s: *const std::ffi::c_char) -> usize;

    /// 比较两个内存区域
    ///
    /// # Safety
    /// - `s1` 和 `s2` 必须各指向至少 `n` 字节的有效内存
    #[allow(dead_code)]
    fn memcmp(s1: *const std::ffi::c_void, s2: *const std::ffi::c_void, n: usize) -> i32;
}

/// 安全的 C 字符串长度包装函数
///
/// 将 unsafe FFI 调用封装在安全接口中，由封装函数负责前置条件检查。
#[cfg(not(target_arch = "wasm32"))]
pub fn safe_strlen(s: &std::ffi::CStr) -> usize {
    // 封装层保证了指针有效性，因此内部的 unsafe 块是合理的
    unsafe { strlen(s.as_ptr()) }
}

/// WASM 环境下模拟的 C 库函数（用于 host 编译测试）
#[cfg(target_arch = "wasm32")]
unsafe extern "C" {
    /// WASM host 提供的日志函数
    ///
    /// # Safety
    /// - `ptr` 必须指向 WASM 线性内存中的有效 UTF-8 字符串
    /// - `len` 必须正确表示字符串字节长度
    fn host_log(ptr: *const u8, len: usize);
}

/// WASM 内存缓冲区结构
///
/// 展示如何在 Rust 2024 中安全地声明和使用外部内存。
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct WasmBuffer {
    /// 线性内存中的指针
    pub ptr: *mut u8,
    /// 缓冲区容量
    pub capacity: usize,
    /// 已使用长度
    pub len: usize,
}

/// 与 JavaScript 交互的 WASM API 声明（Rust 2024 语法）
///
/// 当 WASM 模块需要调用 host 环境（JavaScript）提供的函数时，
/// 使用 `unsafe extern` 明确标记这些调用的不安全性质。
#[cfg(target_arch = "wasm32")]
unsafe extern "C" {
    /// 从 JavaScript 获取时间戳
    fn js_performance_now() -> f64;

    /// 向 JavaScript 发送消息
    ///
    /// # Safety
    /// - `ptr` 和 `len` 必须指向 WASM 内存中的有效 UTF-8 数据
    fn js_send_message(ptr: *const u8, len: usize);
}

/// 安全的 WASM host 时间戳获取（host 模拟版本）
#[cfg(not(target_arch = "wasm32"))]
pub fn safe_performance_now() -> f64 {
    // 在 host 环境下使用标准库替代
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_secs_f64()
        * 1000.0
}

/// 演示 unsafe extern blocks 特性
pub fn demonstrate_unsafe_extern_blocks() {
    println!("\n========================================");
    println!("   Rust 2024 Edition unsafe extern blocks 演示");
    println!("========================================\n");

    println!("--- 语法说明 ---");
    println!("Rust 2024: `unsafe extern \"C\" {{ fn foo(); }}`");
    println!("相比旧语法 `extern \"C\" {{ fn foo(); }}`，新语法更明确地表达了");
    println!("'此块中的所有声明都是 unsafe 的 FFI 接口'这一语义。");

    println!("\n--- WASM FFI 示例 ---");
    let now = safe_performance_now();
    println!("模拟 WASM host 时间戳: {:.2} ms", now);

    println!("\n--- 安全封装模式 ---");
    let c_string = std::ffi::CString::new("Hello, FFI!").unwrap();
    #[cfg(not(target_arch = "wasm32"))]
    {
        let len = safe_strlen(&c_string);
        println!("C 字符串长度（通过安全封装）: {}", len);
    }

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 unsafe extern blocks 特性信息
pub fn get_unsafe_extern_info() -> String {
    "Rust 2024 Edition unsafe extern blocks 特性:\n\
        - 语法: unsafe extern \"C\" { fn foo(); }\n\
        - 声明块整体标记为 unsafe，语义更清晰\n\
        - 与调用点的 unsafe { foo() } 形成双重明确\n\
        - 鼓励将 unsafe FFI 封装为安全 API\n\
        - 适用于 C 库绑定、WASM host 函数、系统调用"
        .to_string()
}

#[cfg(test)]
mod unsafe_extern_tests {
    use super::*;

    #[test]
    fn test_safe_performance_now() {
        let now = safe_performance_now();
        assert!(now > 0.0);
    }

    #[test]
    fn test_wasm_buffer_layout() {
        // 验证 WASM 缓冲区内存布局
        assert_eq!(std::mem::size_of::<WasmBuffer>(), 24);
    }

    #[test]
    fn test_get_unsafe_extern_info() {
        let info = get_unsafe_extern_info();
        assert!(info.contains("unsafe extern"));
        assert!(info.contains("2024"));
    }

    #[test]
    #[cfg(not(target_arch = "wasm32"))]
    fn test_safe_strlen() {
        let c_string = std::ffi::CString::new("Hello").unwrap();
        assert_eq!(safe_strlen(&c_string), 5);
    }
}
