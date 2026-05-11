//! Rust 1.95.0 控制流新特性实现模块
//!
//! 本模块展示了 Rust 1.95.0 在控制流方面的关键增强，包括：
//! - `if let` guards on match arms ⭐
//! - `bool: TryFrom<{integer}>`
//! - `ControlFlow::is_break` / `is_continue` (const 稳定)
//!
//! # 版本信息
//! - Rust版本: 1.95.0
//! - 稳定日期: 2026-04-16
//! - Edition: 2024
//!
//! # 参考
//! - [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)
//! - [RFC 3637: Guard Patterns](https://rust-lang.github.io/rfcs/3637-guard-patterns.html)

use std::ops::ControlFlow;

// ============================================================================
// 1. if let guards on match arms
// ============================================================================

/// # `if let` Guards 深度解析
///
/// ## 概念定义
/// `if let` guard 允许在 `match` 的 arm 上直接进行嵌套模式匹配和条件判断，
/// 无需额外的 `match` 嵌套或 `if` 语句。它将**模式守卫 (guard)** 和
/// **let 绑定** 合二为一。
///
/// ## 语法形式
/// ```ignore
/// match expr {
///     pattern if let Some(inner) = expr2 => { ... }
///     //     ^^^^^^^^^^^^^^^^^^^^^^^^^^^ if let guard
/// }
/// ```
///
/// ## Wikipedia 概念对齐
/// - **Guarded Command**: 由 Edsger Dijkstra 提出，`if let` guard 是其在 Rust 中的具体实现
/// - **Pattern Matching**: 函数式编程核心概念，guard 扩展了模式表达力
///
/// ## 对比：传统方式 vs if let guard
///
/// | 维度 | 传统嵌套 match | if let guard (1.95+) |
/// |------|--------------|---------------------|
/// | 嵌套层级 | 2+ 层 | 1 层 |
/// | 可读性 | 较差（箭头型缩进） | 优秀（扁平化） |
/// | 编译器优化 | 一般 | 更优（单一决策树） |
/// | 错误信息 | 分散在多分支 | 集中在一处 |
/// | 穷尽检查 | 需手动覆盖所有组合 | 更自然的穷尽模式 |
///
/// ## 反例 / 限制
/// - `if let` guard 中的绑定在 arm 右侧**不可见**（与常规 guard 相同）
/// - 不能用于 `if let` 表达式本身（仅用于 `match` arms）
/// - 与 `let chains` (1.88+) 不同：`let chains` 用于 `if` 条件，`if let` guards 用于 `match` arms
pub struct IfLetGuardExamples;

impl IfLetGuardExamples {
    /// 基础示例：解析可选字符串为整数
    ///
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

    /// 使用 if let guard 的扁平化版本
    ///
    /// 注意：`if let Ok(p) = s.parse::<u8>()` 直接在 match arm 上完成解析和绑定。
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

    /// 更进一步的扁平化：将范围检查也纳入 guard
    ///
    /// 这里展示了 `if let` guard 与常规 guard (`&&`) 的组合使用。
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
    ///
    /// 这是 Rust 中常见的"嵌套 Result-Option"场景，`if let` guard 使其清晰可读。
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
    ///
    /// 展示了 `if let` guard 与元组解构、多个条件组合的强大能力。
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
///
/// 在实际系统中，`if let` guard 极大地简化了状态机中的条件转换。
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
#[derive(Debug, Clone, PartialEq)]
pub enum ConfigValue {
    Timeout(std::time::Duration),
    Threads(usize),
    Enabled(bool),
    LogLevel(LogLevel),
    Invalid(String),
}

/// 日志级别
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

/// # `bool: TryFrom<{integer}>` 解析
///
/// ## 概念定义
/// Rust 1.95.0 稳定了 `bool` 对所有整数类型的 `TryFrom` 实现：
/// - `0` → `Ok(false)`
/// - `1` → `Ok(true)`
/// - 其他 → `Err(TryFromIntError)`
///
/// ## Wikipedia 概念对齐
/// - **Type Conversion**: 显式、可失败的类型转换，符合 Rust 的显式哲学
/// - **Boolean Algebra**: George Boole 提出的二值逻辑，0/1 映射是其在计算中的自然表示
///
/// ## 反例 / 常见错误
/// - **不要用 `as bool`**：Rust 不允许 `as` 转换整数到 bool（防止 C/C++ 的隐式转换陷阱）
/// - **不要用 `!= 0`**：虽然惯用，但丢失了语义明确性，且对负数行为不直观
/// - **不要用 `match`**：`TryFrom` 提供了标准、可组合的错误处理路径
///
/// ## 设计决策树
/// ```text
/// 需要将整数转为 bool?
/// ├── 值域已约束为 0/1? → bool::try_from(n)
/// ├── 需要任意非零为 true? → n != 0（显式文档说明）
/// └── 需要位级语义? → 保持为整数，不要转 bool
/// ```
pub struct BoolTryFromExamples;

impl BoolTryFromExamples {
    /// 基础示例：配置解析
    pub fn parse_flag(value: i32) -> Result<bool, &'static str> {
        match bool::try_from(value) {
            Ok(b) => Ok(b),
            Err(_) => Err("布尔值必须是 0 或 1"),
        }
    }

    /// 与 `u8` 一起使用
    pub fn decode_protocol_flag(byte: u8) -> Result<bool, std::num::TryFromIntError> {
        bool::try_from(byte)
    }

    /// 在迭代器中批量转换
    pub fn convert_flags(inputs: &[i32]) -> Vec<Result<bool, std::num::TryFromIntError>> {
        inputs.iter().copied().map(bool::try_from).collect()
    }

    /// 显式处理 0/1 语义 vs 非零语义
    ///
    /// 当协议要求严格的 0/1 时，使用 `try_from`；
    /// 当只需要"非零即真"时，显式使用 `!= 0` 并注释说明。
    pub fn strict_vs_loose(input: i32) -> (Result<bool, &'static str>, bool) {
        let strict = bool::try_from(input).map_err(|_| "必须是 0 或 1");
        let loose = input != 0; // 明确：任意非零值视为 true
        (strict, loose)
    }
}

// ============================================================================
// 3. ControlFlow::is_break / is_continue (const 稳定)
// ============================================================================

/// # `ControlFlow` 判别方法（const 上下文）
///
/// Rust 1.95.0 将 `ControlFlow::is_break` 和 `ControlFlow::is_continue`
/// 在 const 上下文中稳定化。这使得在编译期计算中也能使用 `ControlFlow`。
///
/// ## 概念
/// `ControlFlow<B, C>` 是 Rust 标准库中表示**提前终止**或**继续**的类型：
/// - `Break(B)`：终止，携带值 B
/// - `Continue(C)`：继续，携带值 C
///
/// 它是 `try_fold`、`try_for_each` 等函数的基础。
pub struct ControlFlowConstExamples;

impl ControlFlowConstExamples {
    /// const 上下文中检查 ControlFlow 状态
    pub const fn const_example() -> (bool, bool) {
        let break_val: ControlFlow<i32, ()> = ControlFlow::Break(42);
        let continue_val: ControlFlow<i32, ()> = ControlFlow::Continue(());

        // 这些调用在 const 上下文中是合法的（1.95+）
        (break_val.is_break(), continue_val.is_continue())
    }

    /// 在编译期计算中使用
    pub const COMPILE_TIME_CHECK: bool = {
        let result = ControlFlow::<(), ()>::Break(());
        result.is_break() // true
    };

    /// 与 try_fold 结合：提前终止的搜索
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
///
/// `cfg_select!` 是 Rust 1.95.0 稳定的新宏，提供编译期条件选择，
/// 功能类似于流行的 `cfg-if` crate，但语法更直观。
///
/// ## 语法
/// ```ignore
/// cfg_select! {
///     condition => { expression }
///     _ => { fallback_expression }
/// }
/// ```
///
/// ## 与 `cfg!` 的区别
/// | 特性 | `cfg!` | `cfg_select!` |
/// |------|--------|---------------|
/// | 返回值 | `bool` | 任意表达式 |
/// | 分支 | 无（仅判断） | 多分支选择 |
/// | 使用场景 | 运行时条件判断 | 编译期代码/值选择 |
pub struct CfgSelectExamples;

impl CfgSelectExamples {
    /// 使用 `cfg_select!` 选择平台特定的路径分隔符
    pub fn path_separator() -> &'static str {
        std::cfg_select! {
            windows => "\\",
            unix => "/",
            _ => "/",
        }
    }

    /// 使用 `cfg_select!` 选择平台特定的换行符
    pub fn line_ending() -> &'static str {
        std::cfg_select! {
            windows => "\r\n",
            _ => "\n",
        }
    }

    /// 使用 `cfg_select!` 选择架构特定的缓存行大小
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
        assert_eq!(RealRust195Features::parse_with_if_let_guard(Ok(Some(10))), 10);
        assert_eq!(RealRust195Features::parse_with_if_let_guard(Ok(Some(0))), 0);
        assert_eq!(RealRust195Features::parse_with_if_let_guard(Ok(Some(-5))), -1);
        assert_eq!(RealRust195Features::parse_with_if_let_guard(Ok(None)), 0);
        assert_eq!(
            RealRust195Features::parse_with_if_let_guard(Err("empty input")),
            -100
        );
        assert_eq!(RealRust195Features::parse_with_if_let_guard(Err("other")), -1);
    }

    #[test]
    fn test_control_flow_transform() {
        let result = RealRust195Features::control_flow_transform();
        assert!(matches!(result, ControlFlow::Break(84)));
    }
}
