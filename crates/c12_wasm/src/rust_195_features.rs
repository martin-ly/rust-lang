#![forbid(unsafe_code)]
#![allow(unexpected_cfgs)]

//! Rust 1.95 特性 —— WASM/WASI 场景实际可执行代码
//!
//! 本模块演示 Rust 1.95 在 WebAssembly 上下文中的六项重要稳定特性：
//!
//! | 特性 | 应用场景 |
//! |------|----------|
//! | `cfg_select!` | 编译时选择 WASI p1/p2、浏览器或原生实现 |
//! | `bool::TryFrom<{integer}>` | FFI 边界整数标志安全转换为 `bool` |
//! | `core::hint::cold_path` | WASM 错误路径分支预测优化 |
//! | `if let` guards | `match` 中处理 wasm-bindgen `Result`/`Option` 模式 |
//! | `core::range::RangeInclusive` | 端口范围、内存页范围验证 |
//! | `ControlFlow::is_break`/`is_continue` (const) | 编译期评估的提前退出模式 |

use core::range::RangeInclusive;
use std::ops::ControlFlow;

// =========================================================================
// 1. cfg_select! —— 编译时 WASM 目标平台选择
// =========================================================================

/// WASM 运行时环境分类
///
/// 用于在编译期根据目标三元组确定当前所处的 WASM 执行环境。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WasmRuntime {
    /// 浏览器环境（含 Deno 等 Web 兼容运行时）
    Browser,
    /// Node.js 环境
    NodeJs,
    /// WASI Preview 1（传统能力驱动模型）
    WasiPreview1,
    /// WASI Preview 2（组件模型）
    WasiPreview2,
    /// 纯 WASM，无宿主接口（`wasm32v1-none`）
    Standalone,
    /// 原生编译目标（非 WASM）
    Native,
}

/// 检测当前编译目标对应的 WASM 运行时环境
///
/// 使用 `cfg_select!` 在编译期进行类似 `match` 的配置选择，
/// 不产生任何运行时开销，替代传统的 `cfg-if` crate。
///
/// # 示例
/// ```
/// use c12_wasm::rust_195_features::detect_runtime;
/// let rt = detect_runtime();
/// ```
pub const fn detect_runtime() -> WasmRuntime {
    cfg_select! {
        target_env = "wasip1" => WasmRuntime::WasiPreview1,
        target_env = "wasip2" => WasmRuntime::WasiPreview2,
        target_arch = "wasm32" => WasmRuntime::Browser,
        _ => WasmRuntime::Native,
    }
}

/// 获取当前平台推荐的日志输出方式描述
///
/// 根据编译目标返回对应环境的日志策略说明。
pub fn platform_log_description() -> &'static str {
    cfg_select! {
        target_env = "wasip1" => "WASI P1: 使用 wasi::stdout 输出日志",
        target_env = "wasip2" => "WASI P2: 使用组件模型接口输出日志",
        target_arch = "wasm32" => "浏览器 WASM: 使用 web_sys::console 输出日志",
        _ => "原生目标: 使用 std::println! 输出日志",
    }
}

/// 获取当前平台可用的文件系统 API 描述
pub fn platform_fs_description() -> &'static str {
    cfg_select! {
        target_env = "wasip1" => "WASI P1 文件描述符 API",
        target_env = "wasip2" => "WASI P2 句柄类型 API",
        target_arch = "wasm32" => "浏览器 Storage API 或虚拟文件系统",
        _ => "原生 std::fs API",
    }
}

// 使用 `cfg_select!` 在项位置定义平台相关的函数实现。
cfg_select! {
    target_env = "wasip1" => {
        /// 模拟 WASI Preview 1 环境下的文件读取
        pub fn platform_read_file(path: &str) -> Result<String, &'static str> {
            Ok(format!("[WASI P1] 读取文件: {}", path))
        }
    }
    target_env = "wasip2" => {
        /// 模拟 WASI Preview 2 环境下的文件读取
        pub fn platform_read_file(path: &str) -> Result<String, &'static str> {
            Ok(format!("[WASI P2] 组件模型读取: {}", path))
        }
    }
    target_arch = "wasm32" => {
        /// 模拟浏览器 WASM 环境下的文件读取
        pub fn platform_read_file(path: &str) -> Result<String, &'static str> {
            Ok(format!("[Browser WASM] 获取资源: {}", path))
        }
    }
    _ => {
        /// 原生环境下的文件读取
        pub fn platform_read_file(path: &str) -> Result<String, &'static str> {
            std::fs::read_to_string(path).map_err(|_| "native read failed")
        }
    }
}

// =========================================================================
// 2. bool::TryFrom<{integer}> —— FFI 边界安全布尔转换
// =========================================================================

/// 将 WASM FFI 边界传入的 `u8` 标志安全转换为 `bool`
///
/// 在 WASM 与宿主环境（JavaScript、C）交互时，外部代码常以 `0`/`1`
/// 整数表示布尔值。Rust 1.95 之前需手动检查，现在通过
/// `bool::try_from` 在边界处获得类型安全，拒绝 `0` 和 `1` 以外的值。
///
/// # 参数
/// - `flag`: 外部传入的 `u8` 整数值
///
/// # 返回值
/// - `Ok(true)` 当且仅当 `flag == 1`
/// - `Ok(false)` 当且仅当 `flag == 0`
/// - `Err` 其他所有值
///
/// # 示例
/// ```
/// use c12_wasm::rust_195_features::ffi_bool_from_u8;
/// assert_eq!(ffi_bool_from_u8(1), Ok(true));
/// assert!(ffi_bool_from_u8(2).is_err());
/// ```
pub fn ffi_bool_from_u8(flag: u8) -> Result<bool, &'static str> {
    bool::try_from(flag).map_err(|_| "FFI bool flag must be 0 or 1")
}

/// 将 WASI 返回的 `i32` 状态码安全转换为 `bool`
///
/// 某些旧版 WASI 绑定以 `0` 表示成功、`1` 表示失败。
/// 若宿主环境错误地传入 `-1` 或 `2` 等值，此函数可立即捕获。
///
/// # 参数
/// - `status`: WASI 函数返回的 `i32` 状态码
pub fn wasi_status_to_bool(status: i32) -> Result<bool, &'static str> {
    bool::try_from(status).map_err(|_| "WASI status must be 0 (success) or 1 (failure)")
}

/// 批量转换 JS 回调返回的整数标志数组
///
/// 常用于处理从 JavaScript 批量传入的布尔标志，例如配置选项数组。
///
/// # 参数
/// - `flags`: 外部传入的 `u8` 数组
///
/// # 返回值
/// 全部转换成功时返回 `Ok(Vec<bool>)`，任一失败则返回 `Err`
pub fn parse_js_bool_flags(flags: &[u8]) -> Result<Vec<bool>, &'static str> {
    flags.iter().map(|&f| ffi_bool_from_u8(f)).collect()
}

/// 将单个 `u32` 标志转换为 `Option<bool>`
///
/// 将 `0`/`1` 映射为 `Some(false)`/`Some(true)`，其他值映射为 `None`。
pub fn ffi_bool_optional(flag: u32) -> Option<bool> {
    bool::try_from(flag).ok()
}

// =========================================================================
// 3. core::hint::cold_path —— WASM 错误路径分支预测优化
// =========================================================================

/// 验证 WASM 内存页请求，对错误路径标记 `cold_path`
///
/// 在 WASM 运行时中，内存分配成功（热路径）远比失败（冷路径）常见。
/// `cold_path` 提示编译器将错误分支置于远离热路径的位置，
/// 优化指令缓存与分支预测，尤其有利于体积敏感的 WASM 模块。
///
/// # 参数
/// - `requested`: 请求的内存页数（每页 64 KiB）
/// - `max_allowed`: 允许的最大页数
///
/// # 返回值
/// 验证通过返回请求页数，否则返回错误信息
pub fn validate_memory_pages(requested: u32, max_allowed: u32) -> Result<u32, &'static str> {
    if requested == 0 {
        core::hint::cold_path();
        return Err("requested memory pages cannot be zero");
    }
    if requested > max_allowed {
        core::hint::cold_path();
        return Err("requested memory pages exceed maximum allowed");
    }
    Ok(requested)
}

/// 验证 WASM 表（table）大小限制
///
/// WASM 表用于存储函数引用，过大的表会导致宿主环境资源耗尽。
///
/// # 参数
/// - `size`: 请求的表大小
/// - `limit`: 允许的最大大小
pub fn validate_table_size(size: u32, limit: u32) -> Result<u32, &'static str> {
    if size > limit {
        core::hint::cold_path();
        return Err("table size exceeds limit");
    }
    if size == 0 {
        core::hint::cold_path();
        return Err("table size cannot be zero");
    }
    Ok(size)
}

/// 解析并验证 WASM 数据段（data segment）大小
///
/// 数据段过大可能导致实例化时内存不足。
///
/// # 参数
/// - `size_bytes`: 数据段字节大小
/// - `max_bytes`: 允许的最大字节数
pub fn validate_data_segment(size_bytes: usize, max_bytes: usize) -> Result<usize, &'static str> {
    if size_bytes > max_bytes {
        core::hint::cold_path();
        return Err("data segment exceeds maximum size");
    }
    Ok(size_bytes)
}

/// 验证导入模块名称格式
///
/// 无效的导入名称通常意味着宿主环境配置错误，属于异常场景。
///
/// # 参数
/// - `name`: 导入模块名称
pub fn validate_import_name(name: &str) -> Result<&str, &'static str> {
    if name.is_empty() {
        core::hint::cold_path();
        return Err("import name cannot be empty");
    }
    if name.contains('\0') {
        core::hint::cold_path();
        return Err("import name cannot contain null bytes");
    }
    Ok(name)
}

// =========================================================================
// 4. if let guards —— match 表达式中的模式守卫
// =========================================================================

/// 使用 `if let` guards 解析来自 JavaScript 的可选值
///
/// 处理从 wasm-bindgen 传入的 `Option<&str>`，可能包含整数、
/// 空字符串或 `null`/`undefined`。`if let` guards 允许在单个
/// `match` 表达式中完成多层解构，避免嵌套 `if let`。
///
/// # 参数
/// - `value`: 从 JS 传入的可选字符串
///
/// # 返回值
/// 分类后的结果字符串或错误信息
///
/// # 示例
/// ```
/// use c12_wasm::rust_195_features::process_js_optional_value;
/// assert_eq!(
///     process_js_optional_value(Some("42")),
///     Ok(String::from("integer: 42"))
/// );
/// ```
pub fn process_js_optional_value(value: Option<&str>) -> Result<String, &'static str> {
    match value {
        Some(s) if let Ok(n) = s.parse::<i32>() => Ok(format!("integer: {}", n)),
        Some("") => Err("empty string received from JS"),
        Some(s) => Ok(format!("string: {}", s)),
        None => Err("null or undefined received from JS"),
    }
}

/// 解析 WASM 模块导入描述符
///
/// 导入描述符可能是数字索引（`"5"`）、模块名对（`"env:memory"`）
/// 或纯字符串。`if let` guards 使三种模式在同一条 `match` 中处理。
///
/// # 参数
/// - `desc`: 导入描述符字符串
pub fn parse_import_descriptor(desc: Option<&str>) -> Result<(String, u32), &'static str> {
    match desc {
        Some(s) if let Ok(index) = s.parse::<u32>() => Ok((String::from("by_index"), index)),
        Some(s) if s.contains(':') => {
            let parts: Vec<&str> = s.split(':').collect();
            if parts.len() == 2 {
                Ok((format!("{}::{}", parts[0], parts[1]), 0))
            } else {
                Err("invalid import descriptor format")
            }
        }
        Some(s) => Ok((s.to_string(), 0)),
        None => Err("missing import descriptor"),
    }
}

/// 处理批量 WASM 调用结果
///
/// 批量执行 WASM 导出函数后，使用 `if let` guards 对结果分类：
/// 非负成功值、负异常值、以及显式错误。
///
/// # 参数
/// - `results`: WASM 调用结果数组
///
/// # 返回值
/// `(成功值数组, 错误信息数组)`
pub fn process_batch_results(
    results: &[Result<i32, &'static str>],
) -> (Vec<i32>, Vec<&'static str>) {
    let mut successes = Vec::new();
    let mut errors = Vec::new();

    for result in results {
        match result {
            Ok(val) if *val >= 0 => successes.push(*val),
            Ok(_) => errors.push("negative value from WASM"),
            Err(msg) => errors.push(*msg),
        }
    }

    (successes, errors)
}

/// 解析 WASM 全局变量初始化值
///
/// 全局初始化值可能是整数、浮点数字面量或特殊标志字符串。
///
/// # 参数
/// - `input`: 初始化值字符串
pub fn parse_global_init(input: Option<&str>) -> Result<String, &'static str> {
    match input {
        Some(s) if let Ok(n) = s.parse::<i64>() => Ok(format!("i64.const {}", n)),
        Some(s) if let Ok(f) = s.parse::<f64>() => Ok(format!("f64.const {}", f)),
        Some("null") => Ok(String::from("ref.null")),
        Some(s) => Ok(format!("unknown: {}", s)),
        None => Err("missing global init value"),
    }
}

// =========================================================================
// 5. core::range::RangeInclusive —— 范围类型与验证
// =========================================================================

/// 验证端口范围是否有效
///
/// WASM 模块在需要网络功能时（如 WASI sockets）需指定合法的端口范围。
/// 使用 `core::range::RangeInclusive` 替代传统的 `ops::RangeInclusive`，
/// 获得更一致的范围类型支持。
///
/// # 参数
/// - `range`: 待验证的闭区间端口范围
///
/// # 返回值
/// 范围有效返回 `true`，否则返回 `false`
///
/// # 示例
/// ```
/// use c12_wasm::rust_195_features::is_valid_port_range;
/// use core::range::RangeInclusive;
/// assert!(is_valid_port_range(&(1..=1024).into()));
/// ```
pub fn is_valid_port_range(range: &RangeInclusive<u16>) -> bool {
    range.start > 0 && range.start <= range.last
}

/// 创建 WASM 内存页范围
///
/// 每页大小为 64 KiB。闭区间范围清晰表达起始页和结束页均包含在内。
///
/// # 参数
/// - `start`: 起始页索引
/// - `end`: 结束页索引（包含）
///
/// # 返回值
/// 表示内存页范围的 `RangeInclusive<usize>`
pub fn memory_page_range(start: usize, end: usize) -> RangeInclusive<usize> {
    (start..=end).into()
}

/// 检查数据段大小是否在允许范围内
///
/// # 参数
/// - `size`: 数据段字节大小
/// - `allowed`: 允许的闭区间范围
pub fn is_data_size_in_range(size: usize, allowed: &RangeInclusive<usize>) -> bool {
    allowed.contains(&size)
}

/// 将模块索引分批为连续的闭区间范围
///
/// 加载大量 WASM 模块时，按批次处理可降低峰值内存占用。
///
/// # 参数
/// - `total`: 模块总数
/// - `batch_size`: 每批最大模块数
///
/// # 返回值
/// 各批次的闭区间索引范围数组
pub fn batch_module_ranges(total: usize, batch_size: usize) -> Vec<RangeInclusive<usize>> {
    if batch_size == 0 || total == 0 {
        return Vec::new();
    }

    let mut ranges = Vec::new();
    let mut start = 0;

    while start < total {
        let end = (start + batch_size - 1).min(total - 1);
        ranges.push((start..=end).into());
        start = end + 1;
    }

    ranges
}

/// 获取指定闭区间范围内的所有端口号
///
/// 用于生成 WASI 网络配置中的允许端口列表。
///
/// # 参数
/// - `range`: 端口闭区间范围
///
/// # 返回值
/// 范围内所有端口号的向量
pub fn ports_in_range(range: &RangeInclusive<u16>) -> Vec<u16> {
    if range.start > range.last {
        return Vec::new();
    }
    (*range).into_iter().collect()
}

/// 获取内存页范围的描述信息
///
/// # 参数
/// - `range`: 内存页闭区间范围
///
/// # 返回值
/// `(起始页, 结束页, 总页数)`
pub fn memory_range_info(range: &RangeInclusive<usize>) -> (usize, usize, usize) {
    let start = range.start;
    let end = range.last;
    let pages = end.saturating_sub(start).saturating_add(1);
    (start, end, pages)
}

// =========================================================================
// 6. ControlFlow::is_break / is_continue (const) —— 常量流程控制
// =========================================================================

/// 在 WASM 导出表查找目标函数索引
///
/// 遍历导出名称列表，找到目标时以 `ControlFlow::Break(index)` 提前退出。
///
/// # 参数
/// - `exports`: 导出函数名称数组
/// - `target`: 目标函数名称
///
/// # 返回值
/// - `Break(index)` 如果找到
/// - `Continue(())` 如果未找到
pub fn find_export_index(exports: &[&str], target: &str) -> ControlFlow<usize, ()> {
    for (i, &export) in exports.iter().enumerate() {
        if export == target {
            return ControlFlow::Break(i);
        }
    }
    ControlFlow::Continue(())
}

/// 在常量上下文中检查 `ControlFlow` 是否为 `Break`
///
/// Rust 1.95 将 `ControlFlow::is_break` 稳定为 `const fn`，
/// 允许在编译期评估迭代器提前退出状态。
///
/// # 参数
/// - `cf`: 流程控制值
///
/// # 返回值
/// 若为 `Break` 变体返回 `true`
pub const fn is_break_const<T, U>(cf: &ControlFlow<T, U>) -> bool {
    cf.is_break()
}

/// 在常量上下文中检查 `ControlFlow` 是否为 `Continue`
///
/// # 参数
/// - `cf`: 流程控制值
///
/// # 返回值
/// 若为 `Continue` 变体返回 `true`
pub const fn is_continue_const<T, U>(cf: &ControlFlow<T, U>) -> bool {
    cf.is_continue()
}

/// 验证 WASM 内存页序列，遇到超限页面时提前退出
///
/// 批量验证导入的内存页索引，发现非法值立即返回其位置。
///
/// # 参数
/// - `pages`: 内存页索引数组
/// - `max_page`: 允许的最大页索引
///
/// # 返回值
/// - `Break(index)` 如果 `pages[index]` 超过限制
/// - `Continue(())` 如果全部合法
pub fn validate_page_sequence(pages: &[u32], max_page: u32) -> ControlFlow<usize, ()> {
    for (i, &page) in pages.iter().enumerate() {
        if page > max_page {
            return ControlFlow::Break(i);
        }
    }
    ControlFlow::Continue(())
}

/// 在导入函数列表中查找第一个匹配指定模块名的函数
///
/// # 参数
/// - `imports`: `(模块名, 函数名)` 数组
/// - `module`: 目标模块名
///
/// # 返回值
/// - `Break((索引, 函数名))` 如果找到
/// - `Continue(())` 如果未找到
pub fn find_import_by_module<'a>(
    imports: &'a [(&'a str, &'a str)],
    module: &str,
) -> ControlFlow<(usize, &'a str), ()> {
    for (i, &(mod_name, func_name)) in imports.iter().enumerate() {
        if mod_name == module {
            return ControlFlow::Break((i, func_name));
        }
    }
    ControlFlow::Continue(())
}

// =========================================================================
// 测试
// =========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // --- cfg_select! 测试 ---

    #[test]
    fn test_detect_runtime_native() {
        let rt = detect_runtime();
        // 在原生编译目标下应为 Native
        assert_eq!(rt, WasmRuntime::Native);
    }

    #[test]
    fn test_platform_log_description() {
        let desc = platform_log_description();
        assert!(!desc.is_empty());
    }

    #[test]
    fn test_platform_fs_description() {
        let desc = platform_fs_description();
        assert!(!desc.is_empty());
    }

    #[test]
    fn test_platform_read_file_native() {
        // 原生目标下读取不存在的文件应返回错误
        let result = platform_read_file("nonexistent_test_file.txt");
        assert!(result.is_err());
    }

    // --- bool::TryFrom<{integer}> 测试 ---

    #[test]
    fn test_ffi_bool_from_u8_zero() {
        assert_eq!(ffi_bool_from_u8(0), Ok(false));
    }

    #[test]
    fn test_ffi_bool_from_u8_one() {
        assert_eq!(ffi_bool_from_u8(1), Ok(true));
    }

    #[test]
    fn test_ffi_bool_from_u8_invalid() {
        assert!(ffi_bool_from_u8(2).is_err());
        assert!(ffi_bool_from_u8(255).is_err());
    }

    #[test]
    fn test_wasi_status_to_bool_success() {
        assert_eq!(wasi_status_to_bool(0), Ok(false));
    }

    #[test]
    fn test_wasi_status_to_bool_failure() {
        assert_eq!(wasi_status_to_bool(1), Ok(true));
    }

    #[test]
    fn test_wasi_status_to_bool_invalid() {
        assert!(wasi_status_to_bool(-1).is_err());
        assert!(wasi_status_to_bool(2).is_err());
    }

    #[test]
    fn test_parse_js_bool_flags_success() {
        let flags = vec![0, 1, 1, 0];
        let result = parse_js_bool_flags(&flags);
        assert_eq!(result, Ok(vec![false, true, true, false]));
    }

    #[test]
    fn test_parse_js_bool_flags_invalid() {
        let flags = vec![0, 2, 1];
        assert!(parse_js_bool_flags(&flags).is_err());
    }

    #[test]
    fn test_ffi_bool_optional_some() {
        assert_eq!(ffi_bool_optional(0), Some(false));
        assert_eq!(ffi_bool_optional(1), Some(true));
    }

    #[test]
    fn test_ffi_bool_optional_none() {
        assert_eq!(ffi_bool_optional(2), None);
        assert_eq!(ffi_bool_optional(99), None);
    }

    // --- core::hint::cold_path 测试 ---

    #[test]
    fn test_validate_memory_pages_success() {
        assert_eq!(validate_memory_pages(4, 16), Ok(4));
        assert_eq!(validate_memory_pages(16, 16), Ok(16));
    }

    #[test]
    fn test_validate_memory_pages_zero() {
        assert_eq!(
            validate_memory_pages(0, 16),
            Err("requested memory pages cannot be zero")
        );
    }

    #[test]
    fn test_validate_memory_pages_exceed() {
        assert_eq!(
            validate_memory_pages(17, 16),
            Err("requested memory pages exceed maximum allowed")
        );
    }

    #[test]
    fn test_validate_table_size_success() {
        assert_eq!(validate_table_size(100, 1000), Ok(100));
    }

    #[test]
    fn test_validate_table_size_zero() {
        assert_eq!(
            validate_table_size(0, 1000),
            Err("table size cannot be zero")
        );
    }

    #[test]
    fn test_validate_table_size_exceed() {
        assert_eq!(
            validate_table_size(1001, 1000),
            Err("table size exceeds limit")
        );
    }

    #[test]
    fn test_validate_data_segment_success() {
        assert_eq!(validate_data_segment(1024, 65536), Ok(1024));
    }

    #[test]
    fn test_validate_data_segment_exceed() {
        assert_eq!(
            validate_data_segment(65537, 65536),
            Err("data segment exceeds maximum size")
        );
    }

    #[test]
    fn test_validate_import_name_success() {
        assert_eq!(validate_import_name("env"), Ok("env"));
    }

    #[test]
    fn test_validate_import_name_empty() {
        assert_eq!(validate_import_name(""), Err("import name cannot be empty"));
    }

    #[test]
    fn test_validate_import_name_null() {
        assert_eq!(
            validate_import_name("en\0v"),
            Err("import name cannot contain null bytes")
        );
    }

    // --- if let guards 测试 ---

    #[test]
    fn test_process_js_optional_value_integer() {
        assert_eq!(
            process_js_optional_value(Some("42")),
            Ok(String::from("integer: 42"))
        );
    }

    #[test]
    fn test_process_js_optional_value_string() {
        assert_eq!(
            process_js_optional_value(Some("hello")),
            Ok(String::from("string: hello"))
        );
    }

    #[test]
    fn test_process_js_optional_value_empty() {
        assert_eq!(
            process_js_optional_value(Some("")),
            Err("empty string received from JS")
        );
    }

    #[test]
    fn test_process_js_optional_value_none() {
        assert_eq!(
            process_js_optional_value(None),
            Err("null or undefined received from JS")
        );
    }

    #[test]
    fn test_parse_import_descriptor_by_index() {
        assert_eq!(
            parse_import_descriptor(Some("5")),
            Ok((String::from("by_index"), 5))
        );
    }

    #[test]
    fn test_parse_import_descriptor_module() {
        assert_eq!(
            parse_import_descriptor(Some("env:memory")),
            Ok((String::from("env::memory"), 0))
        );
    }

    #[test]
    fn test_parse_import_descriptor_plain() {
        assert_eq!(
            parse_import_descriptor(Some("foo")),
            Ok((String::from("foo"), 0))
        );
    }

    #[test]
    fn test_parse_import_descriptor_none() {
        assert_eq!(
            parse_import_descriptor(None),
            Err("missing import descriptor")
        );
    }

    #[test]
    fn test_process_batch_results() {
        let results = vec![Ok(10), Ok(-1), Err("trap"), Ok(20)];
        let (successes, errors) = process_batch_results(&results);
        assert_eq!(successes, vec![10, 20]);
        assert_eq!(errors, vec!["negative value from WASM", "trap"]);
    }

    #[test]
    fn test_parse_global_init_i64() {
        assert_eq!(
            parse_global_init(Some("123")),
            Ok(String::from("i64.const 123"))
        );
    }

    #[test]
    fn test_parse_global_init_f64() {
        let result = parse_global_init(Some("3.14"));
        assert!(result.is_ok());
        let s = result.unwrap();
        assert!(s.starts_with("f64.const "));
    }

    #[test]
    fn test_parse_global_init_null() {
        assert_eq!(
            parse_global_init(Some("null")),
            Ok(String::from("ref.null"))
        );
    }

    #[test]
    fn test_parse_global_init_unknown() {
        assert_eq!(
            parse_global_init(Some("abc")),
            Ok(String::from("unknown: abc"))
        );
    }

    // --- core::range::RangeInclusive 测试 ---

    #[test]
    fn test_is_valid_port_range_valid() {
        assert!(is_valid_port_range(&(1..=1024).into()));
        assert!(is_valid_port_range(&(8080..=8080).into()));
    }

    #[test]
    fn test_is_valid_port_range_invalid() {
        assert!(!is_valid_port_range(&(0..=1024).into()));
    }

    #[test]
    fn test_memory_page_range() {
        let range = memory_page_range(1, 4);
        assert_eq!(range.start, 1);
        assert_eq!(range.last, 4);
    }

    #[test]
    fn test_is_data_size_in_range() {
        let range: RangeInclusive<usize> = (0..=65536).into();
        assert!(is_data_size_in_range(1024, &range));
        assert!(!is_data_size_in_range(65537, &range));
    }

    #[test]
    fn test_batch_module_ranges() {
        let ranges = batch_module_ranges(10, 3);
        assert_eq!(ranges.len(), 4);
        assert_eq!(ranges[0].start, 0);
        assert_eq!(ranges[0].last, 2);
        assert_eq!(ranges[3].start, 9);
        assert_eq!(ranges[3].last, 9);
    }

    #[test]
    fn test_batch_module_ranges_empty() {
        assert!(batch_module_ranges(0, 3).is_empty());
        assert!(batch_module_ranges(10, 0).is_empty());
    }

    #[test]
    fn test_ports_in_range() {
        let ports = ports_in_range(&(80..=82).into());
        assert_eq!(ports, vec![80, 81, 82]);
    }

    #[test]
    fn test_ports_in_range_empty() {
        let ports = ports_in_range(&(82..=80).into());
        assert!(ports.is_empty());
    }

    #[test]
    fn test_memory_range_info() {
        let range = memory_page_range(2, 5);
        assert_eq!(memory_range_info(&range), (2, 5, 4));
    }

    // --- ControlFlow 测试 ---

    #[test]
    fn test_find_export_index_found() {
        let exports = vec!["memory", "add", "sub"];
        let result = find_export_index(&exports, "add");
        assert!(is_break_const(&result));
        assert!(!is_continue_const(&result));
        if let ControlFlow::Break(i) = result {
            assert_eq!(i, 1);
        }
    }

    #[test]
    fn test_find_export_index_not_found() {
        let exports = vec!["memory", "add"];
        let result = find_export_index(&exports, "mul");
        assert!(!is_break_const(&result));
        assert!(is_continue_const(&result));
    }

    #[test]
    fn test_validate_page_sequence_success() {
        let pages = vec![1, 2, 3, 4];
        let result = validate_page_sequence(&pages, 10);
        assert!(is_continue_const(&result));
    }

    #[test]
    fn test_validate_page_sequence_break() {
        let pages = vec![1, 2, 15, 4];
        let result = validate_page_sequence(&pages, 10);
        assert!(is_break_const(&result));
        if let ControlFlow::Break(i) = result {
            assert_eq!(i, 2);
        }
    }

    #[test]
    fn test_find_import_by_module_found() {
        let imports = vec![("env", "memory"), ("env", "table"), ("wasi", "fd_write")];
        let result = find_import_by_module(&imports, "wasi");
        assert!(is_break_const(&result));
        if let ControlFlow::Break((i, name)) = result {
            assert_eq!(i, 2);
            assert_eq!(name, "fd_write");
        }
    }

    #[test]
    fn test_find_import_by_module_not_found() {
        let imports = vec![("env", "memory")];
        let result = find_import_by_module(&imports, "foo");
        assert!(is_continue_const(&result));
    }

    #[test]
    fn test_is_break_const_true() {
        const CF: ControlFlow<i32, ()> = ControlFlow::Break(42);
        assert!(is_break_const(&CF));
    }

    #[test]
    fn test_is_continue_const_true() {
        const CF: ControlFlow<i32, ()> = ControlFlow::Continue(());
        assert!(is_continue_const(&CF));
    }

    #[test]
    fn test_const_eval_control_flow() {
        const B: bool = {
            let cf: ControlFlow<i32, ()> = ControlFlow::Break(1);
            is_break_const(&cf)
        };
        assert!(B);

        const C: bool = {
            let cf: ControlFlow<i32, ()> = ControlFlow::Continue(());
            is_continue_const(&cf)
        };
        assert!(C);
    }
}
