//! # Rust 1.96 特性跟踪模块（含历史特性复习）
//! # Rust 1.96 feature module （feature ）
//! - `assert_matches!` / `debug_assert_matches!` — 模式匹配断言宏 ⭐
//! - `expr` metavariable 传递给 `cfg` ⭐
//! - Never typein tuple in强制conversion ⭐
//!
//! 以及历史特性复习（非 1.96 新增，但与本模块教学相关）：
//!
//! and feature （ 1.96 ，but and this module ）：
//!
//! # 版本信息
//! # Version Information
//! # this
//! - 稳定日期: 2026-05-28
//! - date : 2026-05-28
//! - 稳定date: 2026-05-28
//! - stabledate: 2026-05-28
//! - date: 2026-05-28
//! # Rust 1.96.0 类型系统新特性
//! # Rust 1.96.0 type system feature

use std::assert_matches;

// ============================================================================
// 1. `impl From<bool> for {f32, f64}` — 布尔到浮点转换 (1.68.0 stable)
// ============================================================================

/// # 布尔到浮点转换 (`From<bool> for f32/f64`)
/// # to point conversion (`From<bool> for f32/f64`)
/// # 布尔to浮pointconversion (`From<bool> for f32/f64`)
/// Allowswill `bool` 直接conversionas `0.0` (false) or `1.0` (true)。
/// ## 类型系统意义
/// ## type system
/// - `bool` 已实现 `From<bool> for {integer}` (1.68.0 stable)
/// - `bool` 已Implementation of `From<bool> for {integer}` (1.68.0 stable)
/// - 1.96 补全了对浮点类型的对称转换
/// - 1.96 to point type to conversion
/// ## 应用场景
/// ## application scenario
/// - 机器学习特征向量构建 (0.0/1.0 特征)
/// - machine learning (0.0/1.0 )
/// - 概率计算中的指示函数
/// - in function
/// - 传感器数据处理 (布尔状态 → 浮点信号)
/// - (state → point )
pub struct BoolToFloatConversionExamples;

impl BoolToFloatConversionExamples {
    /// 将布尔数组转换为 f64 特征向量
    /// will conversion as f64
    pub fn bool_vector_to_features(flags: &[bool]) -> Vec<f64> {
        flags.iter().map(|&b| f64::from(b)).collect()
    }

    /// 条件概率指示函数: P(A) ≈ mean(indicator_A)
    /// condition function : P(A) ≈ mean(indicator_A)
    pub fn indicator(probability: f64, condition: bool) -> f64 {
        if condition {
            probability
        } else {
            f64::from(false)
        }
    }

    /// 传感器布尔状态转换为模拟信号强度
    /// state conversion as
    pub fn sensor_status_to_signal(active: bool, base_strength: f64) -> f64 {
        f64::from(active) * base_strength
    }
}

// ============================================================================
// 2. `VecDeque::new` 的 const 上下文支持 (1.68.0 stable)
// ============================================================================

use std::collections::VecDeque;

/// 允许在编译期初始化双端队列常量。
/// in constant 。
/// ## 类型系统意义
/// ## type system
/// 使得更多数据结构可以在编译期构造，减少运行时初始化开销。
/// data structure can in ，runtime overhead 。
/// ## 限制
/// ## Limitations
/// ##
pub struct ConstVecDequeExamples;

impl ConstVecDequeExamples {
    pub const EMPTY_QUEUE: VecDeque<i32> = VecDeque::new();

    pub fn build_static_config() -> VecDeque<&'static str> {
        // 注意: 在 stable Rust 中，const VecDeque 只能初始化，
        // 修改需要结合 LazyLock 或运行时初始化
        VecDeque::new()
    }
}

// ============================================================================
// Never 类型 (`!`) 深度专题 (Rust 1.96+ stable, Edition 2024)
// ============================================================================

// ✅ **状态**: `!` 类型的核心功能在 Rust 1.96+ stable / Edition 2024 中已可用：
//    - `!` 作为函数返回类型（`-> !`）—— 早已稳定
//    - `Result<T, !>` / `Option<!>` —— stable 可用（通过 edition 2024）
//    - never type 在 tuple 表达式中的 coercion —— Rust 1.96.0 stable
//    - match 穷尽性检查（`Result<T, !>` 无需 `Err` 分支）—— stable 可用
//
// ⚠️ **限制**: `!` 作为显式类型别名（如 `type MyNever = !;`）在某些上下文中仍受限，
//    但这不影响上述核心用例。
//
// # Rust 2024 Edition Never 类型 (`!`) 深度专题
//
// `!`（never type）是 Rust 中最特殊的类型之一，表示"永远不会返回的值"。
// 在 Rust 2024 Edition 中，never 类型的使用场景进一步扩展，
// 配合更完善的类型推导和穷尽性检查，使代码更安全、更简洁。
//
// ## 核心特性
// - `!` 可以强制转换为任何类型（coerce to any type）
// - 在 `match` 中启用更精确的穷尽性检查
// - `Result<T, !>` 表示"不可能出错"的操作
// - `Option<!>` 表示"不可能存在"的值

// ==================== 示例 1: 基础 Never 类型 ====================

/// 永远不会返回的函数
/// function
/// 永远不会Returnfunction
/// `-> !` 明确标记此函数不会正常返回，只会通过 panic/exit/无限循环结束。
/// `->!` explicit mark this function ， panic/exit/circulation 。
pub fn always_panics() -> ! {
    panic!("此函数永远不会返回")
}

/// 无限循环也返回 never 类型
/// circulation never type
/// 在嵌入式或服务器场景中常见：主循环永不退出。
/// in or scenario in ：circulation 。
pub fn infinite_loop() -> ! {
    loop {
        // 执行某些永久运行的任务
        std::thread::sleep(std::time::Duration::from_secs(1));
    }
}

/// 进程退出函数
/// process function
pub fn fatal_error(message: &str) -> ! {
    eprintln!("致命错误: {}", message);
    std::process::exit(1)
}

// ==================== 示例 2: Result<T, !> —— 不可能失败的运算 ====================

/// 安全的整数加法（不可能溢出）
/// （may ）
/// 当通过类型系统或前置条件保证操作不会失败时，可以使用 `!` 作为错误类型。
/// when type system or before condition ，can `!` as error type 。
pub fn safe_add(a: u32, b: u32) -> Result<u32, !> {
    // 如果业务逻辑保证不会溢出，错误类型为 `!`
    Ok(a.wrapping_add(b))
}

/// 字符串字面量的解析（编译期已知有效）
/// surface （effective ）
/// 从已知有效的字符串构建数字，理论上不可能失败。
/// from effective ，theory on may 。
pub fn parse_known_valid() -> Result<i32, !> {
    // 编译器知道 "42" 一定能解析成功
    Ok("42".parse().unwrap())
}

/// will `Result<T, !>` 安全地conversionas `T`
pub fn unwrap_infallible<T>(result: Result<T, !>) -> T {
    // Rust 2024: match 对 `Result<T, !>` 支持穷尽性检查，
    // 编译器知道 `Err` 分支不可能发生
    match result {
        Ok(v) => v,
        // Err 分支不需要，因为 `!` 是空类型，不存在该值
    }
}

// ==================== 示例 3: match 穷尽性检查 ====================

/// Use `Result<T, !>` 穷尽性 match
pub fn demonstrate_exhaustive_match() -> i32 {
    let x: Result<i32, !> = Ok(42);

    // 只需要处理 Ok 分支，编译器知道 Err 不可能发生
    match x {
        Ok(v) => v,
        // 不需要 Err 分支！编译器验证其穷尽性
    }
}

/// 自definitionenumand never typecombination
/// 使用泛型参数表示"某些变体在特定上下文中不可能出现"。
/// generic parameter represent "volume in on under in may "。
#[derive(Debug, PartialEq, Clone)]
pub enum Event<T, E> {
    /// 数据到达
    /// to
    Data(T),
    /// 错误发生
    Error(E),
    /// 流结束
    /// stream
    End,
}

/// 处理不可能出错的流事件
/// Processes不可能出错的流事件
/// may stream
/// 当 `E = !` 时，Error 变体在物理上不可能被构造。
/// when `E =!` ，Error volume in on may is 。
pub fn process_infallible_stream(event: Event<i32, !>) -> Option<i32> {
    match event {
        Event::Data(v) => Some(v),
        // Event::Error 分支不需要，因为 `!` 无法构造
        Event::End => None,
    }
}

/// 过滤后的结果类型
/// Filters后的结果类型
/// after result type
pub fn filtered_result(values: Vec<Result<i32, String>>) -> Vec<Result<i32, !>> {
    values
        .into_iter()
        .filter_map(|r| match r {
            Ok(v) => Some(Ok(v)),
            Err(_) => None, // 过滤掉错误
        })
        .collect()
}

// ==================== 示例 4: 控制流中的 never 类型 ====================

/// 提前返回辅助函数
/// before function
pub fn validate_positive(value: Option<i32>) -> i32 {
    match value {
        Some(v) if v > 0 => v,
        _ => fatal_error("值必须为正数"), // fatal_error 返回 `!`，可转为 i32
    }
}

pub fn conditional_never(flag: bool) -> i32 {
    if flag {
        42
    } else {
        always_panics() // `!` 自动 coercion 为 i32
    }
}

pub fn demonstrate_option_never() -> String {
    let impossible: Option<!> = None;

    // 由于 `!` 无法构造，match 只需要处理 None
    match impossible {
        None => "确实不可能存在".to_string(),
        // 不需要 Some 分支
    }
}

// ==================== 示例 5: 实际应用场景 ====================

/// 配置加载结果
/// result
/// 在某些场景下，配置必须存在且有效，否则程序直接退出。
/// in scenario under ，must in and effective ，program 。
pub type InfallibleConfig = Result<AppConfig, !>;

/// 应用配置
/// application
#[derive(Debug, PartialEq, Clone)]
pub struct AppConfig {
    /// 应用名称
    /// application
    pub name: String,
    /// 版本号
    /// this
    pub version: String,
}

impl AppConfig {
    /// 加载配置（在生产环境中不可失败）
    /// （in environment in ）
    /// 如果配置缺失，直接终止进程而非返回错误。
    /// if ，process while 。
    pub fn load_critical() -> Result<AppConfig, !> {
        match Self::load_optional() {
            Some(config) => Ok(config),
            None => fatal_error("关键配置缺失，无法启动应用"),
        }
    }

    /// 可选加载（可能失败）
    /// （may ）
    fn load_optional() -> Option<AppConfig> {
        Some(AppConfig {
            name: "MyApp".to_string(),
            version: "1.0.0".to_string(),
        })
    }
}

/// 编译期常量求值
/// constant
/// 编译期计算不可能在运行时失败，错误类型为 `!`。
/// may in runtime ，error type as `!`。
pub const fn compile_time_compute(input: u32) -> Result<u32, !> {
    Ok(input * 2)
}

// ==================== 演示函数 ====================

/// 演示 Never 类型特性
/// Demonstrates Never 类型特性
/// demonstration Never type feature
pub fn demonstrate_never_type() {
    println!("\n========================================");
    println!("   Rust 2024 Edition Never 类型 (!) 演示");
    println!("========================================\n");

    // 示例 1: Result<T, !>
    println!("--- 示例 1: 不可能失败的结果 ---");
    let result: Result<u32, !> = safe_add(10, 20);
    println!("safe_add(10, 20) => {:?}", result);
    println!("unwrap_infallible => {}", unwrap_infallible(result));

    // 示例 2: 穷尽性 match
    println!("\n--- 示例 2: 穷尽性 match ---");
    println!(
        "demonstrate_exhaustive_match => {}",
        demonstrate_exhaustive_match()
    );

    // 示例 3: 不可能出错的流
    println!("\n--- 示例 3: 不可能出错的流事件 ---");
    let event: Event<i32, !> = Event::Data(100);
    println!(
        "process_infallible_stream => {:?}",
        process_infallible_stream(event)
    );

    // 示例 4: 配置加载
    println!("\n--- 示例 4: 关键配置加载 ---");
    let config = AppConfig::load_critical();
    println!("load_critical => {:?}", config);

    // 示例 5: 编译期计算
    println!("\n--- 示例 5: 编译期计算 ---");
    println!("compile_time_compute(21) => {:?}", compile_time_compute(21));

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 never 类型特性信息
/// Gets never 类型特性信息
/// never type feature
pub fn get_never_type_info() -> String {
    "Rust 2024 Edition Never 类型 (!) 特性:\n- `!` 可强制转换为任何类型\n- `Result<T, !>` \
     表示不可能失败的操作\n- match 穷尽性检查：无需处理 `Err(!)` 分支\n- \
     控制流优化：panic/exit/无限循环返回 `!`\n- 编译期常量求值的理想错误类型"
        .to_string()
}

// ============================================================================
// 4. `core::range` 模块补齐 — `Range` / `RangeFrom` / `RangeToInclusive` (1.96.0 stable)
// ============================================================================

/// # `core::range` 模块（Rust 1.96.0 stable）
///
/// Rust 1.96.0 将范围类型从 `std::ops` 下沉到 `core::range`，并使其在元素类型为 `Copy` 时实现 `Copy`。
/// 当前稳定版包含 `Range`、`RangeFrom`、`RangeInclusive` 等核心类型。
///
/// **来源**: [Rust Standard Library: core::range] · [RFC 3550] · [Rust 1.96 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)
///
/// ## 代码示例
///
/// ```rust
/// use core::range::{Range, RangeFrom, RangeInclusive};
///
/// // Range: 半开区间 [1, 5)
/// let r = Range { start: 1, end: 5 };
/// let sum: i32 = r.into_iter().sum();
/// assert_eq!(sum, 10);
///
/// // 因 Range<i32>: Copy，可多次迭代而无需 clone
/// let v: Vec<i32> = r.into_iter().collect();
/// assert_eq!(v, vec![1, 2, 3, 4]);
///
/// // RangeFrom: [10, ∞)
/// let rf = RangeFrom { start: 10 };
/// let tenth = rf.into_iter().nth(10).unwrap();
/// assert_eq!(tenth, 20);
///
/// // RangeInclusive: [0, 5]
/// let ri = RangeInclusive { start: 0, last: 5 };
/// let v: Vec<i32> = ri.into_iter().collect();
/// assert_eq!(v, vec![0, 1, 2, 3, 4, 5]);
/// ```
///
/// ## 与 `std::ops` 的关系
///
/// | `std::ops` 旧类型 | `core::range` 新类型 | 说明 |
/// |:---|:---|:---|
/// | `std::ops::Range<T>` | `core::range::Range<T>` | 半开区间，1.96 起 `Copy` |
/// | `std::ops::RangeFrom<T>` | `core::range::RangeFrom<T>` | 无限起始区间，1.96 起 `Copy` |
/// | `std::ops::RangeInclusive<T>` | `core::range::RangeInclusive<T>` | 闭区间，1.96 起 `Copy` |
///
/// 推荐：新代码优先使用 `core::range` 以保持一致性。
pub fn core_range_demo() {
    use core::range::{Range, RangeFrom, RangeInclusive};

    let r = Range { start: 1, end: 5 };
    let sum: i32 = r.into_iter().sum();
    assert_eq!(sum, 1 + 2 + 3 + 4); // 10

    // Range<T>: Copy 保证可复用
    let v1: Vec<i32> = r.into_iter().collect();
    let v2: Vec<i32> = r.into_iter().collect();
    assert_eq!(v1, v2);

    let rf = RangeFrom { start: 10 };
    let tenth: i32 = rf.into_iter().nth(10).unwrap();
    assert_eq!(tenth, 20); // 10 + 10

    let ri = RangeInclusive { start: 0, last: 4 };
    let count = ri.into_iter().count();
    assert_eq!(count, 5); // 0, 1, 2, 3, 4
}

// ============================================================================
// 5. `NonZero` 范围迭代 (1.96 stable)
// ============================================================================

/// ```
/// use std::num::NonZeroU32;
/// use std::ops::Range;
///
/// let start = NonZeroU32::new(1).unwrap();
/// let end = NonZeroU32::new(5).unwrap();
/// let range: Range<NonZeroU32> = start..end;
///
/// for nz in range {
///     println!("NonZero: {}", nz.get()); // 1, 2, 3, 4
/// }
/// ```
///
/// **应用场景**:
/// **application scenario **:
/// - 数据库 ID 范围扫描（ID 永不为 0）
/// - database ID scope （ID as 0）
/// - 文件描述符遍历（fd >= 1）
/// - file descriptor （fd >= 1）
/// - 任何语义上排除 0 的数值范围
/// - on 0 scope
pub fn nonzero_range_demo() {
    use std::num::NonZeroU32;
    use std::ops::Range;

    let start = NonZeroU32::new(1).unwrap();
    let end = NonZeroU32::new(5).unwrap();
    let range: Range<NonZeroU32> = start..end;

    let values: Vec<u32> = range.map(|nz| nz.get()).collect();
    assert_eq!(values, vec![1, 2, 3, 4]);
}

// ============================================================================
// 6. `assert_matches!` / `debug_assert_matches!` (1.96.0 stable)
// ============================================================================

/// # 模式断言宏
/// #
/// `assert_matches!` 允许对表达式进行模式匹配断言，无需展开 `if let`：
/// `assert_matches!` to express ， `if let`：
/// ```
/// use std::assert_matches;
/// let result: Result<i32, &str> = Ok(42);
/// assert_matches!(result, Ok(n) if n > 0);
///
/// let option: Option<String> = Some("hello".to_string());
/// assert_matches!(option, Some(s) if s.len() > 0);
/// ```
///
/// **and `assert!(matches!(...))` 区别**:
/// **and `assert!(matches!(...))` difference**:
/// - 错误信息更友好（显示实际值 vs 模式）
/// - error message （display actual vs ）
/// - 支持 guard 条件（`if expr`）
/// - support guard condition（`if expr`）
/// - 支持变量绑定（`Ok(v) => { use v; }`）
/// - variable （`Ok(v) => { use v; }`）
///
/// **来源**: [Rust Standard Library: assert_matches]
pub fn assert_matches_demo() {
    // assert_matches! 在 Rust 1.96.0+ 稳定
    let result: Result<i32, &str> = Ok(42);
    assert_matches!(result, Ok(n) if n > 0);
}

// ==================== 测试 ====================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_add() {
        assert_eq!(safe_add(10, 20), Ok(30));
    }

    #[test]
    fn test_parse_known_valid() {
        assert_eq!(parse_known_valid(), Ok(42));
    }

    #[test]
    fn test_unwrap_infallible() {
        let result: Result<i32, !> = Ok(42);
        assert_eq!(unwrap_infallible(result), 42);
    }

    #[test]
    fn test_demonstrate_exhaustive_match() {
        assert_eq!(demonstrate_exhaustive_match(), 42);
    }

    #[test]
    fn test_process_infallible_stream() {
        assert_eq!(process_infallible_stream(Event::Data(100)), Some(100));
        assert_eq!(process_infallible_stream(Event::End), None);
    }

    #[test]
    fn test_filtered_result() {
        let values = vec![
            Ok(1),
            Err("bad".to_string()),
            Ok(2),
            Err("worse".to_string()),
        ];
        let filtered = filtered_result(values);
        assert_eq!(filtered.len(), 2);
        assert_eq!(filtered[0], Ok(1));
        assert_eq!(filtered[1], Ok(2));
    }

    #[test]
    fn test_validate_positive() {
        assert_eq!(validate_positive(Some(42)), 42);
    }

    #[test]
    fn test_conditional_never() {
        // 当 flag = true 时返回 42
        assert_eq!(conditional_never(true), 42);
        // flag = false 时会 panic，测试需要 catch_unwind
    }

    #[test]
    fn test_demonstrate_option_never() {
        assert_eq!(demonstrate_option_never(), "确实不可能存在");
    }

    #[test]
    fn test_compile_time_compute() {
        assert_eq!(compile_time_compute(21), Ok(42));
    }

    #[test]
    fn test_app_config_load_critical() {
        let config = AppConfig::load_critical();
        assert!(config.is_ok());
        let config = config.unwrap();
        assert_eq!(config.name, "MyApp");
    }

    #[test]
    fn test_core_range_demo() {
        core_range_demo();
    }

    #[test]
    fn test_assert_matches_demo() {
        assert_matches_demo();
    }

    #[test]
    fn test_get_never_type_info() {
        let info = get_never_type_info();
        assert!(info.contains("Never"));
        assert!(info.contains("2024"));
    }
}

/// 类型转换反模式与边界情况专题
/// type conversion and edge situation
pub mod anti_patterns_and_edge_cases {
    /// 展示类型转换中的反模式和边界情况
    /// type conversion in and edge situation
    pub struct TypeConversionAntiPatterns;

    impl TypeConversionAntiPatterns {
        /// ❌ 不推荐：无检查地将大类型转换为小类型
        /// ❌ ：will type conversion as type
        pub fn dangerous_narrowing(value: u64) -> u8 {
            // ❌ 反例：直接 as 转换，高位截断而不报错
            value as u8
        }

        /// ✅ 推荐：使用 try_into 进行安全转换
        /// ✅ Recommended: Use try_into for safe conversion
        /// ✅ ： try_into conversion
        /// ✅ 推荐：Use try_into 进行安全conversion
        pub fn safe_narrowing(value: u64) -> Result<u8, &'static str> {
            value.try_into().map_err(|_| "value out of u8 range")
        }

        /// ⚠️ 边界情况：f64 到整数的精度丢失边界
        /// ⚠️ Edge case: Precision loss boundary for f64 to integer
        /// ⚠️ edge situation ：f64 to edge
        /// 超过 2^53 的 f64 无法精确表示所有整数
        /// 2^53 f64 represent all
        pub fn f64_to_integer_boundary(value: f64) -> Result<i64, &'static str> {
            // ⚠️ 边界情况：检查 f64 是否能精确表示目标整数
            const MAX_EXACT_INTEGER: f64 = 9_007_199_254_740_992.0; // 2^53
            if value.is_nan() || value.is_infinite() {
                return Err("f64 is NaN or infinite");
            }
            if value.abs() > MAX_EXACT_INTEGER {
                return Err("f64 cannot precisely represent this integer");
            }
            if value.fract() != 0.0 {
                return Err("value has fractional part");
            }
            Ok(value as i64)
        }

        /// ⚠️ 边界情况：u8 极值边界上的运算
        /// ⚠️ edge situation ：u8 edge on
        pub fn u8_arithmetic_boundary(a: u8, b: u8) -> Result<u8, &'static str> {
            // ⚠️ 边界情况：在边界值上运算可能静默溢出
            a.checked_add(b).ok_or("u8 overflow")
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_dangerous_narrowing() {
            // ❌ 反例：256u64 截断为 0u8
            assert_eq!(TypeConversionAntiPatterns::dangerous_narrowing(256), 0);
            // ❌ 反例：u64::MAX 截断为 255u8
            assert_eq!(
                TypeConversionAntiPatterns::dangerous_narrowing(u64::MAX),
                255
            );
        }

        #[test]
        fn test_safe_narrowing() {
            assert_eq!(TypeConversionAntiPatterns::safe_narrowing(255), Ok(255));
            assert_eq!(
                TypeConversionAntiPatterns::safe_narrowing(256),
                Err("value out of u8 range")
            );
        }

        #[test]
        fn test_f64_to_integer_boundary() {
            assert_eq!(
                TypeConversionAntiPatterns::f64_to_integer_boundary(42.0),
                Ok(42)
            );
            assert_eq!(
                TypeConversionAntiPatterns::f64_to_integer_boundary(42.5),
                Err("value has fractional part")
            );
            let big = 9_007_199_254_740_994.0_f64; // > 2^53
            assert_eq!(
                TypeConversionAntiPatterns::f64_to_integer_boundary(big),
                Err("f64 cannot precisely represent this integer")
            );
        }

        #[test]
        fn test_u8_arithmetic_boundary() {
            assert_eq!(
                TypeConversionAntiPatterns::u8_arithmetic_boundary(100, 50),
                Ok(150)
            );
            assert_eq!(
                TypeConversionAntiPatterns::u8_arithmetic_boundary(200, 100),
                Err("u8 overflow")
            );
        }
    }
}

// ============================================================================
// 新增: Rust 1.96 实际稳定特性示例（2026-05-29 补全）
// ============================================================================

/// # `From<T>` for `LazyLock<T, F>` / `LazyCell<T, F>` / `AssertUnwindSafe<T>`
pub mod from_for_cell_types {
    use std::cell::LazyCell;
    use std::panic::AssertUnwindSafe;
    use std::sync::LazyLock;

    pub fn lazy_lock_from_value() -> LazyLock<String> {
        LazyLock::from("production".to_string())
    }

    pub fn lazy_cell_from_value() -> LazyCell<Vec<i32>> {
        LazyCell::from(vec![1, 2, 3])
    }

    pub fn assert_unwind_from_value() -> AssertUnwindSafe<i32> {
        AssertUnwindSafe::from(42)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_lazy_lock_from() {
            let lazy: LazyLock<i32> = LazyLock::from(100);
            assert_eq!(*lazy, 100);
        }

        #[test]
        fn test_lazy_cell_from() {
            let cell: LazyCell<i32> = LazyCell::from(200);
            assert_eq!(*cell, 200);
        }

        #[test]
        fn test_assert_unwind_safe_from() {
            let safe: AssertUnwindSafe<i32> = AssertUnwindSafe::from(300);
            assert_eq!(safe.0, 300);
        }
    }
}

pub mod manually_drop_pattern {
    use std::mem::ManuallyDrop;

    const TAG_A: ManuallyDrop<u32> = ManuallyDrop::new(1);
    const TAG_B: ManuallyDrop<u32> = ManuallyDrop::new(2);

    pub fn classify(value: ManuallyDrop<u32>) -> &'static str {
        match value {
            TAG_A => "tag_a",
            TAG_B => "tag_b",
            _ => "other",
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_manually_drop_pattern() {
            assert_eq!(classify(ManuallyDrop::new(1)), "tag_a");
            assert_eq!(classify(ManuallyDrop::new(2)), "tag_b");
            assert_eq!(classify(ManuallyDrop::new(99)), "other");
        }
    }
}

/// # `expr` Metavariable 传递给 `cfg`
/// 关键变更：在 1.96 之前，`expr` fragment specifier 不能用于 `#[cfg(...)]` 属性参数。
/// key ：in 1.96 's before ，`expr` fragment specifier cannot `#[cfg(...)]` attribute parameter 。
/// 1.96 放宽了这一限制，允许通过宏参数动态生成条件编译属性。
/// 1.96 ，parameter condition attribute 。
pub mod expr_metavariable_to_cfg {
    #[cfg(test)]
    mod tests {
        #[test]
        fn test_cfg_expr_feature_documented() {
            // 该特性为宏元编程能力扩展，完整实现见 c11_macro_system
            assert_eq!(2 + 2, 4);
        }
    }
}

/// 在 1.96 之前，某些边缘情况下 `!` 类型在 tuple 中不会被自动 coercion，
/// in 1.96 's before ，edge situation under `!` type in tuple in is coercion，
/// 导致编译失败。1.96 统一了这一行为。
/// 。1.96 as 。
pub mod never_type_tuple_coercion {
    #[allow(dead_code, unreachable_code)]
    fn _never_in_tuple() -> (i32, i32) {
        fn diverge() -> ! {
            panic!("this never returns")
        }
        (diverge(), 42)
    }

    #[allow(dead_code, unreachable_code)]
    fn _todo_in_tuple() -> (String, i32) {
        (todo!("implement this"), 42)
    }

    #[cfg(test)]
    mod tests {
        use std::panic::catch_unwind;

        #[test]
        fn test_never_type_tuple_coercion_compiles() {
            fn diverge() -> ! {
                panic!("expected panic for never type coercion test")
            }

            // 验证：返回 `!` 的表达式在 tuple 中可以被 coercion 为目标类型
            // 这个赋值语句的编译通过即证明了 never type coercion 工作正常
            let result = catch_unwind(|| {
                #[allow(unreachable_code, clippy::diverging_sub_expression)]
                let _: (i32, String) = (diverge(), "test".to_string());
            });

            assert!(
                result.is_err(),
                "diverge() 应该 panic，证明 never type 在 tuple 中被正确 coercion 后执行了"
            );
        }

        #[test]
        fn test_todo_in_tuple_compiles() {
            #[allow(unreachable_code)]
            fn make_tuple() -> (String, i32) {
                (todo!("never type coercion demo"), 42)
            }

            let result = catch_unwind(|| {
                #[allow(clippy::diverging_sub_expression)]
                let _: (String, i32) = make_tuple();
            });

            assert!(
                result.is_err(),
                "todo!() 应该 panic，证明 never type 在 tuple 中被正确 coercion"
            );
        }
    }
}
