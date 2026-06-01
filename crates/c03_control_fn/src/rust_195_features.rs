//! Rust 1.95.0 控制流新特性实现模块
//! Rust 1.95.0 stream feature module
//! # 版本信息
//! # this
//! - 稳定日期: 2026-04-16
//! - date : 2026-04-16
//! - 稳定date: 2026-04-16
//! - date: 2026-04-16
//! # 参考
//! # reference
//! - [RFC 3637: Guard Patterns](https://rust-lang.github.io/rfcs/3637-guard-patterns.html)

use std::ops::ControlFlow;

// ============================================================================
// 1. if let guards on match arms
// ============================================================================

/// # `if let` Guards 深度解析
/// # `if let` Guards 深度Parse
/// ## 概念定义
/// ## concept definition
/// 无需额outside `match` 嵌套or `if` 语句。它will**模式守卫 (guard)** and
/// **let 绑定** 合二为一。
/// **let ** as 。
/// ## 语法形式
/// ##
///     pattern if let Some(inner) = expr2 => { ... }
///     //     ^^^^^^^^^^^^^^^^^^^^^^^^^^^ if let guard
/// }
/// ```
///
/// ## Wikipedia 概念对齐
/// ## 对比：传统方式 vs if let guard
/// ## to ：way vs if let guard
/// ## to比：传统way vs if let guard
/// | 维度 | 传统嵌套 match | if let guard (1.95.0+) |
/// | dimension | 传统嵌套 match | if let guard (1.95.0+) |
/// | 嵌套层级 | 2+ 层 | 1 层 |
/// | | 2+ | 1 |
/// | 可读性 | 较差（箭头型缩进） | 优秀（扁平化） |
/// | | （） | （） |
/// | 编译器优化 | 一般 | 更优（单一决策树） |
/// | optimization | | （tree ） |
/// | 错误信息 | 分散在多分支 | 集中在一处 |
/// | error message | dispersion in | in in |
/// | 穷尽检查 | 需手动覆盖所有组合 | 更自然的穷尽模式 |
/// | | all combination | |
/// ## 反例 / 限制
/// ## /
/// - 不能用于 `if let` 表达式本身（仅用于 `match` arms）
/// - cannot `if let` express this （ `match` arms）
/// - and `let chains` (1.88+) 不同：`let chains` Used for `if` condition，`if let` guards Used for `match` arms
pub struct IfLetGuardExamples;

impl IfLetGuardExamples {
    /// 基础示例：解析可选字符串为整数
    /// foundation example ：as
    /// 传统方式需要嵌套 match 或 if-let-inside-match。
    pub fn parse_priority_traditional(input: Option<&str>) -> Result<u8, &'static str> {
        match input {
            Some(s) => match s.parse::<u8>() {
                Ok(p) if p <= 100 => Ok(p),
                Ok(_) => Err("优先级超出范围"),
                Err(_) => Err("无效的优先级格式"),
            },
            None => Err("未指定优先级"),
        }
    }

    /// Use if let guard 扁平化版this
    /// 注意：`if let Ok(p) = s.parse::<u8>()` 直接在 match arm 上完成解析和绑定。
    /// ：`if let Ok(p) = s.parse::<u8>()` in match arm on and 。
    pub fn parse_priority_modern(input: Option<&str>) -> Result<u8, &'static str> {
        match input {
            Some(s) if let Ok(p) = s.parse::<u8>() => {
                if p <= 100 {
                    Ok(p)
                } else {
                    Err("优先级超出范围")
                }
            }
            Some(_) => Err("无效的优先级格式"),
            None => Err("未指定优先级"),
        }
    }

    pub fn parse_priority_fully_flat(input: Option<&str>) -> Result<u8, &'static str> {
        match input {
            Some(s)
                if let Ok(p) = s.parse::<u8>()
                    && p <= 100 =>
            {
                Ok(p)
            }
            Some(s) if let Ok(_) = s.parse::<u8>() => Err("优先级超出范围"),
            Some(_) => Err("无效的优先级格式"),
            None => Err("未指定优先级"),
        }
    }

    pub fn transition_state(state: ConnectionState, event: NetworkEvent) -> ConnectionState {
        match (state, event) {
            // 从 Connecting 状态，如果收到 ConnectSuccess 且 session_id 有效，进入 Connected
            (
                ConnectionState::Connecting { attempt: _ },
                NetworkEvent::ConnectSuccess { session_id },
            ) if let Some(valid_id) = validate_session(&session_id) => ConnectionState::Connected {
                session_id: valid_id,
            },

            // 连接失败但可重试
            (ConnectionState::Connecting { attempt }, NetworkEvent::ConnectFailed)
                if attempt < 3 =>
            {
                ConnectionState::Connecting {
                    attempt: attempt + 1,
                }
            }

            // 连接失败且超过重试次数
            (ConnectionState::Connecting { .. }, NetworkEvent::ConnectFailed) => {
                ConnectionState::Error {
                    code: 1001,
                    message: "Max retry exceeded".to_string(),
                }
            }

            // 断开连接后回到 Idle
            (ConnectionState::Connected { .. }, NetworkEvent::Disconnect) => ConnectionState::Idle,

            // 其他组合：状态不变
            (state, _) => state,
        }
    }

    /// 错误处理扁平化：`Result<Option<T>>` 解包
    /// error handling ：`Result<Option<T>>`
    pub fn evaluate_task_result<T>(result: Result<Option<T>, &'static str>) -> &'static str
    where
        T: std::fmt::Display,
    {
        match result {
            Ok(Some(value)) if value.to_string() == "0" => "任务成功完成",
            Ok(Some(_)) => "任务完成但有警告",
            Ok(None) => "任务结果为空",
            Err(e) if e.contains("timeout") => "任务执行超时",
            Err(_) => "任务执行失败",
        }
    }

    /// 多字段组合 guard：配置解析
    /// field combination guard：
    pub fn parse_config_entry(key: &str, value: &str) -> ConfigValue {
        match (key, value) {
            ("timeout", v)
                if let Ok(ms) = v.parse::<u64>()
                    && ms > 0
                    && ms <= 300_000 =>
            {
                ConfigValue::Timeout(std::time::Duration::from_millis(ms))
            }
            ("threads", v)
                if let Ok(n) = v.parse::<usize>()
                    && n > 0
                    && n <= 64 =>
            {
                ConfigValue::Threads(n)
            }
            ("enabled", v) if let Ok(b) = v.parse::<bool>() => ConfigValue::Enabled(b),
            ("level", v) if let Ok(l) = v.parse::<LogLevel>() => ConfigValue::LogLevel(l),
            _ => ConfigValue::Invalid(format!("无法解析 {}={}", key, value)),
        }
    }
}

/// 状态机处理：网络连接状态转换
/// state machine ：network state conversion
#[derive(Debug, Clone, PartialEq)]
pub enum ConnectionState {
    Idle,
    Connecting { attempt: u32 },
    Connected { session_id: String },
    Error { code: u32, message: String },
}

pub enum NetworkEvent {
    ConnectSuccess { session_id: String },
    ConnectFailed,
    Disconnect,
    DataReceived(Vec<u8>),
}

/// 配置值类型
/// type
#[derive(Debug, Clone, PartialEq)]
pub enum ConfigValue {
    Timeout(std::time::Duration),
    Threads(usize),
    Enabled(bool),
    LogLevel(LogLevel),
    Invalid(String),
}

/// 日志级别
/// level
/// 日志level
#[derive(Debug, Clone, PartialEq)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

impl std::str::FromStr for LogLevel {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "debug" => Ok(LogLevel::Debug),
            "info" => Ok(LogLevel::Info),
            "warn" => Ok(LogLevel::Warn),
            "error" => Ok(LogLevel::Error),
            _ => Err(()),
        }
    }
}

/// 验证 session ID（辅助函数）
/// session ID（function ）
/// Verify session ID（辅助function）
fn validate_session(id: &str) -> Option<String> {
    if id.len() >= 8 && id.chars().all(|c| c.is_ascii_alphanumeric() || c == '-') {
        Some(id.to_string())
    } else {
        None
    }
}

// ============================================================================
// 2. bool: TryFrom<{integer}>
// ============================================================================

/// ## 概念定义
/// ## concept definition
/// ## Wikipedia 概念对齐
/// - **Type Conversion**: 显式、可失败typeconversion，符合 Rust 显式哲学
/// ## 反例 / 常见错误
/// ## /
/// - **不要用 `!= 0`**：虽然惯用，但丢失了语义明确性，且对负数行为不直观
/// - ** `!= 0`**：，but explicit ，and to as
/// ## 设计决策树
/// ## design tree
pub struct BoolTryFromExamples;

impl BoolTryFromExamples {
    /// 基础示例：配置解析
    /// foundation example ：
    pub fn parse_flag(value: i32) -> Result<bool, &'static str> {
        match bool::try_from(value) {
            Ok(b) => Ok(b),
            Err(_) => Err("布尔值必须是 0 或 1"),
        }
    }

    /// 与 `u8` 一起使用
    /// and `u8`
    /// and `u8` 一起Use
    pub fn decode_protocol_flag(byte: u8) -> Result<bool, std::num::TryFromIntError> {
        bool::try_from(byte)
    }

    /// 在迭代器中批量转换
    /// in in conversion
    pub fn convert_flags(inputs: &[i32]) -> Vec<Result<bool, std::num::TryFromIntError>> {
        inputs.iter().copied().map(bool::try_from).collect()
    }

    /// 显式处理 0/1 语义 vs 非零语义
    /// 0/1 vs
    /// 当只需要"非零即真"时，显式使用 `!= 0` 并注释说明。
    /// when ""， `!= 0` and explain 。
    pub fn strict_vs_loose(input: i32) -> (Result<bool, &'static str>, bool) {
        let strict = bool::try_from(input).map_err(|_| "必须是 0 或 1");
        let loose = input != 0; // 明确：任意非零值视为 true
        (strict, loose)
    }
}

// ============================================================================
// 3. ControlFlow::is_break / is_continue (const 稳定)
// ============================================================================

/// ## 概念
/// ## concept
/// - `Break(B)`：终止，携带值 B
/// - `Break(B)`：， B
/// - `Continue(C)`：继续，携带值 C
/// - `Continue(C)`：， C
/// - `Continue(C)`：Continue，携带值 C
pub struct ControlFlowConstExamples;

impl ControlFlowConstExamples {
    pub const fn const_example() -> (bool, bool) {
        let break_val: ControlFlow<i32, ()> = ControlFlow::Break(42);
        let continue_val: ControlFlow<i32, ()> = ControlFlow::Continue(());

        // 这些调用在 const 上下文中是合法的（1.95+）
        (break_val.is_break(), continue_val.is_continue())
    }

    /// 在编译期计算中使用
    /// in in
    pub const COMPILE_TIME_CHECK: bool = {
        let result = ControlFlow::<(), ()>::Break(());
        result.is_break() // true
    };

    pub fn find_first_negative(numbers: &[i32]) -> Option<usize> {
        let result = numbers.iter().enumerate().try_fold((), |_, (idx, &n)| {
            if n < 0 {
                ControlFlow::Break(idx)
            } else {
                ControlFlow::Continue(())
            }
        });

        match result {
            ControlFlow::Break(idx) => Some(idx),
            ControlFlow::Continue(()) => None,
        }
    }
}

// ============================================================================
// 测试
// ============================================================================

// ============================================================================
// 3. cfg_select! 宏（Rust 1.95.0 稳定）
// ============================================================================

/// # `cfg_select!` 宏
/// ## 语法
/// ##
///     condition => { expression }
///     _ => { fallback_expression }
/// }
/// ```
///
/// ## 与 `cfg!` 的区别
/// ## and `cfg!`
/// ## and `cfg!` 区别
/// | 特性 | `cfg!` | `cfg_select!` |
/// | 返回值 | `bool` | 任意表达式 |
/// | return value | `bool` | express |
/// | 分支 | 无（仅判断） | 多分支选择 |
/// | | （） | |
/// | 使用场景 | 运行时条件判断 | 编译期代码/值选择 |
/// | scenario | runtime condition | / |
pub struct CfgSelectExamples;

impl CfgSelectExamples {
    pub fn path_separator() -> &'static str {
        std::cfg_select! {
            windows => "\\",
            unix => "/",
            _ => "/",
        }
    }

    pub fn line_ending() -> &'static str {
        std::cfg_select! {
            windows => "\r\n",
            _ => "\n",
        }
    }

    pub fn cache_line_size() -> usize {
        std::cfg_select! {
            target_arch = "x86_64" => 64,
            target_arch = "aarch64" => 64,
            target_arch = "riscv64" => 64,
            _ => 32,
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_if_let_guard_parse_priority() {
        assert_eq!(
            IfLetGuardExamples::parse_priority_modern(Some("50")),
            Ok(50)
        );
        assert_eq!(
            IfLetGuardExamples::parse_priority_modern(Some("150")),
            Err("优先级超出范围")
        );
        assert_eq!(
            IfLetGuardExamples::parse_priority_modern(Some("abc")),
            Err("无效的优先级格式")
        );
        assert_eq!(
            IfLetGuardExamples::parse_priority_modern(None),
            Err("未指定优先级")
        );
    }

    #[test]
    fn test_if_let_guard_fully_flat() {
        assert_eq!(
            IfLetGuardExamples::parse_priority_fully_flat(Some("42")),
            Ok(42)
        );
        assert_eq!(
            IfLetGuardExamples::parse_priority_fully_flat(Some("255")),
            Err("优先级超出范围")
        );
    }

    #[test]
    fn test_if_let_guard_state_machine() {
        let state = ConnectionState::Connecting { attempt: 1 };
        let event = NetworkEvent::ConnectSuccess {
            session_id: "valid-1234".to_string(),
        };
        let new_state = IfLetGuardExamples::transition_state(state, event);
        assert!(matches!(new_state, ConnectionState::Connected { .. }));

        let state = ConnectionState::Connecting { attempt: 1 };
        let event = NetworkEvent::ConnectSuccess {
            session_id: "short".to_string(), // 无效 ID
        };
        let new_state = IfLetGuardExamples::transition_state(state, event);
        // 无效 session_id 导致状态不变（fallback 到 (state, _) => state）
        assert!(matches!(new_state, ConnectionState::Connecting { .. }));
    }

    #[test]
    fn test_bool_try_from() {
        assert_eq!(bool::try_from(0i32), Ok(false));
        assert_eq!(bool::try_from(1i32), Ok(true));
        assert!(bool::try_from(2i32).is_err());
        assert!(bool::try_from(-1i32).is_err());
    }

    #[test]
    fn test_control_flow_const() {
        assert_eq!(ControlFlowConstExamples::const_example(), (true, true));
        assert!(ControlFlowConstExamples::COMPILE_TIME_CHECK);
    }

    #[test]
    fn test_find_first_negative() {
        assert_eq!(
            ControlFlowConstExamples::find_first_negative(&[1, 2, -3, 4]),
            Some(2)
        );
        assert_eq!(
            ControlFlowConstExamples::find_first_negative(&[1, 2, 3]),
            None
        );
    }
}

// ============================================================================
// Real Rust 1.95 Features — Control Flow, Functions
// ============================================================================

/// Demonstrates real Rust 1.95 features related to control flow and functions.
pub struct RealRust195Features;

impl RealRust195Features {
    /// `if let` guards in match arms (Rust 1.95)
    pub fn parse_with_if_let_guard(input: Result<Option<i32>, &str>) -> i32 {
        match input {
            Ok(Some(n)) if n > 0 => n,
            Ok(Some(0)) => 0,
            Ok(Some(_)) => -1,
            Ok(None) => 0,
            Err(msg) if msg.contains("empty") => -100,
            Err(_) => -1,
        }
    }

    /// `ControlFlow::map_break` (Rust 1.95)
    pub fn control_flow_transform() -> ControlFlow<i32, ()> {
        let flow: ControlFlow<i32, ()> = ControlFlow::Break(42);
        flow.map_break(|e: i32| e * 2)
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_parse_with_if_let_guard() {
        assert_eq!(
            RealRust195Features::parse_with_if_let_guard(Ok(Some(10))),
            10
        );
        assert_eq!(RealRust195Features::parse_with_if_let_guard(Ok(Some(0))), 0);
        assert_eq!(
            RealRust195Features::parse_with_if_let_guard(Ok(Some(-5))),
            -1
        );
        assert_eq!(RealRust195Features::parse_with_if_let_guard(Ok(None)), 0);
        assert_eq!(
            RealRust195Features::parse_with_if_let_guard(Err("empty input")),
            -100
        );
        assert_eq!(
            RealRust195Features::parse_with_if_let_guard(Err("other")),
            -1
        );
    }

    #[test]
    fn test_control_flow_transform() {
        let result = RealRust195Features::control_flow_transform();
        assert!(matches!(result, ControlFlow::Break(84)));
    }
}
