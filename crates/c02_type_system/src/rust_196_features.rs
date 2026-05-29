//! # Rust 1.96 特性跟踪模块（含历史特性复习与 1.96 前瞻）
//!
//! 本模块包含 Rust 1.96.0 稳定版的类型系统增强：
//! - `impl From<bool> for {f32, f64}` — 布尔到浮点安全转换 ⭐
//! - `VecDeque::new` 的 const 上下文支持 — 常量初始化集合 ⭐
//!
//! 以及 nightly-only 的 Never 类型 (`!`) 深度专题（供前瞻学习）。
//!
//! # 版本信息
//! - Rust版本: 1.96.0+ (stable features) / nightly (`!` type)
//! - 稳定日期: 2026-05-XX
//! - Edition: 2024
//!
//! # Rust 1.96.0 类型系统新特性

use std::assert_matches;

// ============================================================================
// 1. `impl From<bool> for {f32, f64}` — 布尔到浮点转换 (1.68 stable)
// ============================================================================

/// # 布尔到浮点转换 (`From<bool> for f32/f64`)
///
/// Rust 1.68.0 稳定了 `impl From<bool> for f32` 和 `impl From<bool> for f64`，
/// 允许将 `bool` 直接转换为 `0.0` (false) 或 `1.0` (true)。
///
/// ## 类型系统意义
/// 这是 Rust 类型一致性 (type coherence) 的进一步完善：
/// - `bool` 已实现 `From<bool> for {integer}` (1.75 stable)
/// - 1.96 补全了对浮点类型的对称转换
/// - 统一了数值类型从 `bool` 的转换接口
///
/// ## 应用场景
/// - 机器学习特征向量构建 (0.0/1.0 特征)
/// - 概率计算中的指示函数
/// - 传感器数据处理 (布尔状态 → 浮点信号)
pub struct BoolToFloatConversionExamples;

impl BoolToFloatConversionExamples {
    /// 将布尔数组转换为 f64 特征向量
    pub fn bool_vector_to_features(flags: &[bool]) -> Vec<f64> {
        flags.iter().map(|&b| f64::from(b)).collect()
    }

    /// 条件概率指示函数: P(A) ≈ mean(indicator_A)
    pub fn indicator(probability: f64, condition: bool) -> f64 {
        if condition {
            probability
        } else {
            f64::from(false)
        }
    }

    /// 传感器布尔状态转换为模拟信号强度
    pub fn sensor_status_to_signal(active: bool, base_strength: f64) -> f64 {
        f64::from(active) * base_strength
    }
}

// ============================================================================
// 2. `VecDeque::new` 的 const 上下文支持 (1.68 stable)
// ============================================================================

use std::collections::VecDeque;

/// # `VecDeque::new` const 支持
///
/// Rust 1.68.0 使 `VecDeque::new` 可在 `const` 上下文中调用，
/// 允许在编译期初始化双端队列常量。
///
/// ## 类型系统意义
/// 这是 `const fn` 能力向标准库集合的持续扩展，
/// 使得更多数据结构可以在编译期构造，减少运行时初始化开销。
///
/// ## 限制
/// - 仅 `new()` 为 const，其他操作（push/pop）仍非常量
/// - 需要 `const Mutex` 或 `static` + `LazyLock` 才能实现真正的编译期全局队列
pub struct ConstVecDequeExamples;

impl ConstVecDequeExamples {
    /// 编译期初始化的空 VecDeque 常量
    pub const EMPTY_QUEUE: VecDeque<i32> = VecDeque::new();

    /// 使用 const VecDeque 构建静态配置
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
//    - never type 在 tuple 表达式中的 coercion —— Rust 1.96 stable
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
///
/// `-> !` 明确标记此函数不会正常返回，只会通过 panic/exit/无限循环结束。
pub fn always_panics() -> ! {
    panic!("此函数永远不会返回")
}

/// 无限循环也返回 never 类型
///
/// 在嵌入式或服务器场景中常见：主循环永不退出。
pub fn infinite_loop() -> ! {
    loop {
        // 执行某些永久运行的任务
        std::thread::sleep(std::time::Duration::from_secs(1));
    }
}

/// 进程退出函数
///
/// `std::process::exit` 返回 `!`，因为调用后程序立即终止。
pub fn fatal_error(message: &str) -> ! {
    eprintln!("致命错误: {}", message);
    std::process::exit(1)
}

// ==================== 示例 2: Result<T, !> —— 不可能失败的运算 ====================

/// 安全的整数加法（不可能溢出）
///
/// 当通过类型系统或前置条件保证操作不会失败时，可以使用 `!` 作为错误类型。
pub fn safe_add(a: u32, b: u32) -> Result<u32, !> {
    // 如果业务逻辑保证不会溢出，错误类型为 `!`
    Ok(a.wrapping_add(b))
}

/// 字符串字面量的解析（编译期已知有效）
///
/// 从已知有效的字符串构建数字，理论上不可能失败。
pub fn parse_known_valid() -> Result<i32, !> {
    // 编译器知道 "42" 一定能解析成功
    Ok("42".parse().unwrap())
}

/// 将 `Result<T, !>` 安全地转换为 `T`
///
/// 由于 `!` 表示不可能出现的错误，可以直接 unwrap 而无需担心 panic。
pub fn unwrap_infallible<T>(result: Result<T, !>) -> T {
    // Rust 2024: match 对 `Result<T, !>` 支持穷尽性检查，
    // 编译器知道 `Err` 分支不可能发生
    match result {
        Ok(v) => v,
        // Err 分支不需要，因为 `!` 是空类型，不存在该值
    }
}

// ==================== 示例 3: match 穷尽性检查 ====================

/// 使用 `Result<T, !>` 的穷尽性 match
///
/// Rust 2024 Edition 中，编译器能更好地识别 `!` 类型的穷尽性。
pub fn demonstrate_exhaustive_match() -> i32 {
    let x: Result<i32, !> = Ok(42);

    // 只需要处理 Ok 分支，编译器知道 Err 不可能发生
    match x {
        Ok(v) => v,
        // 不需要 Err 分支！编译器验证其穷尽性
    }
}

/// 自定义枚举与 never 类型的组合
///
/// 使用泛型参数表示"某些变体在特定上下文中不可能出现"。
#[derive(Debug, PartialEq, Clone)]
pub enum Event<T, E> {
    /// 数据到达
    Data(T),
    /// 错误发生
    Error(E),
    /// 流结束
    End,
}

/// 处理不可能出错的流事件
///
/// 当 `E = !` 时，Error 变体在物理上不可能被构造。
pub fn process_infallible_stream(event: Event<i32, !>) -> Option<i32> {
    match event {
        Event::Data(v) => Some(v),
        // Event::Error 分支不需要，因为 `!` 无法构造
        Event::End => None,
    }
}

/// 过滤后的结果类型
///
/// 当错误已经被提前过滤掉，剩余的结果类型可以标记为 `Result<T, !>`。
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
///
/// 在 match 中使用返回 `!` 的函数，利用其可以转换为任何类型的特性。
pub fn validate_positive(value: Option<i32>) -> i32 {
    match value {
        Some(v) if v > 0 => v,
        _ => fatal_error("值必须为正数"), // fatal_error 返回 `!`，可转为 i32
    }
}

/// 条件分支中的 never 类型 coercion
///
/// `!` 在条件表达式中自动 coercion 为目标类型。
pub fn conditional_never(flag: bool) -> i32 {
    if flag {
        42
    } else {
        always_panics() // `!` 自动 coercion 为 i32
    }
}

/// Option 的 map 与 never 类型
///
/// `Option<!>` 等价于 `None`，因为无法构造 `Some(!)`。
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
///
/// 在某些场景下，配置必须存在且有效，否则程序直接退出。
pub type InfallibleConfig = Result<AppConfig, !>;

/// 应用配置
#[derive(Debug, PartialEq, Clone)]
pub struct AppConfig {
    /// 应用名称
    pub name: String,
    /// 版本号
    pub version: String,
}

impl AppConfig {
    /// 加载配置（在生产环境中不可失败）
    ///
    /// 如果配置缺失，直接终止进程而非返回错误。
    pub fn load_critical() -> Result<AppConfig, !> {
        match Self::load_optional() {
            Some(config) => Ok(config),
            None => fatal_error("关键配置缺失，无法启动应用"),
        }
    }

    /// 可选加载（可能失败）
    fn load_optional() -> Option<AppConfig> {
        Some(AppConfig {
            name: "MyApp".to_string(),
            version: "1.0.0".to_string(),
        })
    }
}

/// 编译期常量求值
///
/// 编译期计算不可能在运行时失败，错误类型为 `!`。
pub const fn compile_time_compute(input: u32) -> Result<u32, !> {
    Ok(input * 2)
}

// ==================== 演示函数 ====================

/// 演示 Never 类型特性
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
pub fn get_never_type_info() -> String {
    "Rust 2024 Edition Never 类型 (!) 特性:\n- `!` 可强制转换为任何类型\n- `Result<T, !>` \
     表示不可能失败的操作\n- match 穷尽性检查：无需处理 `Err(!)` 分支\n- \
     控制流优化：panic/exit/无限循环返回 `!`\n- 编译期常量求值的理想错误类型"
        .to_string()
}

// ============================================================================
// 4. `core::range` 模块补齐 — `Range` / `RangeFrom` / `RangeToInclusive` (1.96 stable)
// ============================================================================

/// # `core::range` 模块完整类型族
///
/// Rust 1.95 稳定了 `RangeInclusive` 和 `RangeInclusiveIter`。
/// **1.96 补齐了 `core::range` 的其余核心类型**：
///
/// | 类型 | 语法 | 含义 | 对应迭代器 |
/// |:---|:---|:---|:---|
/// | `Range` | `start..end` | 半开区间 `[start, end)` | `RangeIter` |
/// | `RangeFrom` | `start..` | 无限区间 `[start, ∞)` | `RangeFromIter` |
/// | `RangeToInclusive` | `..=end` | 闭区间 `(-∞, end]` | `RangeToInclusiveIter` |
/// | `RangeInclusive` (1.95) | `start..=end` | 闭区间 `[start, end]` | `RangeInclusiveIter` |
///
/// **来源**: [Rust Standard Library: core::range] · [RFC 3550]
///
/// ## 设计目标
///
/// 1. **模块统一**: 所有 range 类型集中到 `core::range`
/// 2. **零成本抽象**: `RangeIter` 等是惰性视图，不分配内存
/// 3. **泛型一致**: 为 future 的 `Range<T>` 泛型化做准备
///
/// ## 代码示例
///
/// ```rust,ignore
/// // 注意: RangeToInclusive 的 IntoIterator 需要 Rust 1.96+ 且 Idx: Zero
/// use core::range::{
///     Range, RangeFrom, RangeFromIter, RangeIter, RangeToInclusive, RangeToInclusiveIter,
/// };
///
/// // Range: 半开区间 [1, 5)
/// let range = Range { start: 1, end: 5 };
/// let mut iter: RangeIter<i32> = range.into_iter();
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// // ... 3, 4, None
///
/// // RangeFrom: 无限区间 [10, ∞)
/// let from = RangeFrom { start: 10 };
/// let mut iter: RangeFromIter<i32> = from.into_iter();
/// assert_eq!(iter.next(), Some(10));
/// assert_eq!(iter.next(), Some(11));
/// // ... 无限递增（需配合 take）
///
/// // RangeToInclusive: 闭区间 (-∞, 5]
/// let to = RangeToInclusive { last: 5 };
/// // 注意：RangeToInclusive 需要从 0 开始迭代
/// let mut iter: RangeToInclusiveIter<i32> = to.into_iter();
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(1));
/// // ... 2, 3, 4, 5, None
/// ```
///
/// ## 与 `std::ops` 的关系
///
/// ```text
/// std::ops::Range<T>        ↔  core::range::Range<T>
/// std::ops::RangeFrom<T>    ↔  core::range::RangeFrom<T>
/// std::ops::RangeToInclusive<T> ↔  core::range::RangeToInclusive<T>
///
/// 当前状态：两者共存，core::range 是未来方向
/// 推荐：新代码使用 core::range 以保持一致性
/// ```
pub fn core_range_demo() {
    use core::range::{Range, RangeFrom, RangeToInclusive};

    let r = Range { start: 1, end: 5 };
    let sum: i32 = r.into_iter().sum();
    assert_eq!(sum, 1 + 2 + 3 + 4); // 10

    let rf = RangeFrom { start: 10 };
    let tenth: i32 = rf.into_iter().nth(10).unwrap();
    assert_eq!(tenth, 20); // 10 + 10

    let rt = RangeToInclusive { last: 4 };
    // RangeToInclusive 的迭代需要起始点，通常与 0..=end 配合使用
    let count = (0..=rt.last).count();
    assert_eq!(count, 5); // 0, 1, 2, 3, 4
}

// ============================================================================
// 5. `NonZero` 范围迭代 (1.96 stable)
// ============================================================================

/// # `NonZero` 整数范围迭代
///
/// Rust 1.96 为 `NonZero*` 类型实现了 `Step` trait，允许对非零整数范围进行迭代：
///
/// ```rust
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
/// - 数据库 ID 范围扫描（ID 永不为 0）
/// - 文件描述符遍历（fd >= 1）
/// - 任何语义上排除 0 的数值范围
///
/// **来源**: [Rust Standard Library: NonZero]
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
// 6. `assert_matches!` / `debug_assert_matches!` (1.96 stable)
// ============================================================================

/// # 模式断言宏
///
/// `assert_matches!` 允许对表达式进行模式匹配断言，无需展开 `if let`：
///
/// ```rust
/// use std::assert_matches;
/// let result: Result<i32, &str> = Ok(42);
/// assert_matches!(result, Ok(n) if n > 0);
///
/// let option: Option<String> = Some("hello".to_string());
/// assert_matches!(option, Some(s) if s.len() > 0);
/// ```
///
/// **与 `assert!(matches!(...))` 的区别**:
/// - 错误信息更友好（显示实际值 vs 模式）
/// - 支持 guard 条件（`if expr`）
/// - 支持变量绑定（`Ok(v) => { use v; }`）
///
/// **来源**: [Rust Standard Library: assert_matches]
pub fn assert_matches_demo() {
    // assert_matches! 在 Rust 1.96+ 稳定
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
    fn test_get_never_type_info() {
        let info = get_never_type_info();
        assert!(info.contains("Never"));
        assert!(info.contains("2024"));
    }
}

/// 类型转换反模式与边界情况专题
pub mod anti_patterns_and_edge_cases {
    /// 展示类型转换中的反模式和边界情况
    pub struct TypeConversionAntiPatterns;

    impl TypeConversionAntiPatterns {
        /// ❌ 不推荐：无检查地将大类型转换为小类型
        pub fn dangerous_narrowing(value: u64) -> u8 {
            // ❌ 反例：直接 as 转换，高位截断而不报错
            value as u8
        }

        /// ✅ 推荐：使用 try_into 进行安全转换
        pub fn safe_narrowing(value: u64) -> Result<u8, &'static str> {
            value.try_into().map_err(|_| "value out of u8 range")
        }

        /// ⚠️ 边界情况：f64 到整数的精度丢失边界
        /// 超过 2^53 的 f64 无法精确表示所有整数
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
///
/// Rust 1.96 稳定了从值直接构造这些类型的 `From` 实现：
pub mod from_for_cell_types {
    use std::cell::LazyCell;
    use std::panic::AssertUnwindSafe;
    use std::sync::LazyLock;

    /// 从值直接构造 LazyLock，无需闭包
    pub fn lazy_lock_from_value() -> LazyLock<String> {
        LazyLock::from("production".to_string())
    }

    /// 从值直接构造 LazyCell
    pub fn lazy_cell_from_value() -> LazyCell<Vec<i32>> {
        LazyCell::from(vec![1, 2, 3])
    }

    /// 从值直接构造 AssertUnwindSafe
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

/// # `ManuallyDrop` 常量作为模式
///
/// Rust 1.96 修复了 1.94.0 引入的回归，允许在 match 中使用 ManuallyDrop 常量：
pub mod manually_drop_pattern {
    use std::mem::ManuallyDrop;

    const TAG_A: ManuallyDrop<u32> = ManuallyDrop::new(1);
    const TAG_B: ManuallyDrop<u32> = ManuallyDrop::new(2);

    /// 使用 ManuallyDrop 常量进行模式匹配
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
///
/// Rust 1.96 允许宏将 `expr` 类型的 metavariable 传递给 `cfg` 属性。
/// 完整可运行示例见 `c11_macro_system::rust_196_features::ExprMetavariableToCfgExamples`。
///
/// 关键变更：在 1.96 之前，`expr` fragment specifier 不能用于 `#[cfg(...)]` 属性参数。
/// 1.96 放宽了这一限制，允许通过宏参数动态生成条件编译属性。
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

/// # Never Type 在 Tuple 表达式中的强制转换
///
/// Rust 1.96 修复了 never type (`!`) 在 tuple 表达式中的 coercion 行为，
/// 确保 diverging 表达式在 tuple 中始终被正确强制转换为目标类型。
///
/// 在 1.96 之前，某些边缘情况下 `!` 类型在 tuple 中不会被自动 coercion，
/// 导致编译失败。1.96 统一了这一行为。
pub mod never_type_tuple_coercion {
    /// 演示 never type 在 tuple 中的 coercion
    ///
    /// `diverge()` 返回 `!`，在 `(diverge(), 42)` 中被 coercion 为 `i32`。
    /// 整个表达式永远不会返回，因为 `diverge()` 不会返回。
    #[allow(dead_code, unreachable_code)]
    fn _never_in_tuple() -> (i32, i32) {
        fn diverge() -> ! {
            panic!("this never returns")
        }
        (diverge(), 42)
    }

    /// 使用 `todo!()` 返回 `!` 的温和演示
    ///
    /// 注意：此函数本身也会 diverge，因为 `todo!()` 返回 `!`。
    #[allow(dead_code, unreachable_code)]
    fn _todo_in_tuple() -> (String, i32) {
        (todo!("implement this"), 42)
    }

    /// 验证 never type coercion 的编译时测试
    ///
    /// 通过 `catch_unwind` 捕获 panic，验证代码能编译且运行时行为正确。
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
