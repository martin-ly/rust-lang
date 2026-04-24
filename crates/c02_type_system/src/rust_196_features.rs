//! # Rust 2024 Edition Never 类型 (`!`) 深度专题
//!
//! `!`（never type）是 Rust 中最特殊的类型之一，表示"永远不会返回的值"。
//! 在 Rust 2024 Edition 中，never 类型的使用场景进一步扩展，
//! 配合更完善的类型推导和穷尽性检查，使代码更安全、更简洁。
//!
//! ## 核心特性
//! - `!` 可以强制转换为任何类型（coerce to any type）
//! - 在 `match` 中启用更精确的穷尽性检查
//! - `Result<T, !>` 表示"不可能出错"的操作
//! - `Option<!>` 表示"不可能存在"的值

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
    println!("demonstrate_exhaustive_match => {}", demonstrate_exhaustive_match());

    // 示例 3: 不可能出错的流
    println!("\n--- 示例 3: 不可能出错的流事件 ---");
    let event: Event<i32, !> = Event::Data(100);
    println!("process_infallible_stream => {:?}", process_infallible_stream(event));

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
    "Rust 2024 Edition Never 类型 (!) 特性:\n\
        - `!` 可强制转换为任何类型\n\
        - `Result<T, !>` 表示不可能失败的操作\n\
        - match 穷尽性检查：无需处理 `Err(!)` 分支\n\
        - 控制流优化：panic/exit/无限循环返回 `!`\n\
        - 编译期常量求值的理想错误类型"
        .to_string()
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
        let values = vec![Ok(1), Err("bad".to_string()), Ok(2), Err("worse".to_string())];
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
