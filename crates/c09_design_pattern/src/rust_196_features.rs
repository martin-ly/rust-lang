//! # Rust 1.96.0 特性 — 设计模式
//! **历史稳定 patch**: Rust 1.96.1（基于 Rust 1.96.0 特性集）
//! # Rust 1.96.0/1.96.1 features design pattern
//!
//! Rust 1.96.0/1.96.1 为设计模式实现带来的核心稳定特性：
//! Rust 1.96.0/1.96.1 as design core feature ：
//!
//! - **`LazyLock::from(value)`**: 单例模式中的惰性初始化构造
//! - **`LazyLock::from(value)`**: singleton in
//! - **`assert_matches!`**: 状态机模式的状态断言测试
//! - **`assert_matches!`**: state machinepatternstatus test
//! - **`ManuallyDrop` 常量模式**: 在模式匹配中使用 `ManuallyDrop` 常量
//! - **`ManuallyDrop` constant **: in in `ManuallyDrop` constant

use std::mem::ManuallyDrop;
use std::sync::LazyLock;

// ==================== LazyLock::from 在单例模式中的应用 ====================

/// 使用 LazyLock::from 实现单例配置
/// use LazyLock::from implementationsingle configuration
///
/// `LazyLock::from(value)` 允许直接从一个已知的值创建 `LazyLock`，
/// `LazyLock::from(value)` from `LazyLock`，
/// 适用于配置已预计算的单例场景。
/// singleton scenario 。
pub struct SingletonConfig {
    value: LazyLock<String>,
}

impl SingletonConfig {
    /// 从已知值创建单例配置
    pub fn from_value(value: String) -> Self {
        Self {
            value: LazyLock::from(value),
        }
    }

    /// 获取配置值
    /// Get configurationvalue
    pub fn get(&self) -> &str {
        &self.value
    }
}

/// 使用 LazyLock::from 实现线程安全的单例计数器描述
pub struct SingletonCounter {
    description: LazyLock<String>,
}

impl SingletonCounter {
    pub fn new(desc: &str) -> Self {
        Self {
            description: LazyLock::from(desc.to_string()),
        }
    }

    pub fn description(&self) -> &str {
        &self.description
    }
}

// ==================== assert_matches! 在状态机模式测试中的应用 ====================

/// 状态机状态枚举
/// state machine state enum
#[derive(Debug, Clone, PartialEq)]
pub enum ConnectionState {
    Disconnected,
    Connecting,
    Connected { address: String },
    Failed { reason: String },
}

/// 状态机转换
/// state machine conversion
pub fn transition(state: ConnectionState, event: &str) -> ConnectionState {
    match (state, event) {
        (ConnectionState::Disconnected, "connect") => ConnectionState::Connecting,
        (ConnectionState::Connecting, "ok") => ConnectionState::Connected {
            address: String::from("127.0.0.1"),
        },
        (ConnectionState::Connecting, "fail") => ConnectionState::Failed {
            reason: String::from("timeout"),
        },
        (ConnectionState::Connected { .. }, "disconnect") => ConnectionState::Disconnected,
        (current, _) => current,
    }
}

// ==================== ManuallyDrop 常量在模式中的应用 ====================

/// 使用 ManuallyDrop 常量作为模式匹配标记
/// ManuallyDrop constant as mark
///
/// Rust 1.96 允许在模式匹配中使用 `ManuallyDrop` 常量。
/// Rust 1.96 in in `ManuallyDrop` constant 。
pub struct MarkerType<T> {
    value: ManuallyDrop<T>,
}

impl MarkerType<i32> {
    /// 特殊标记值常量
    /// mark constant
    pub const SPECIAL: ManuallyDrop<i32> = ManuallyDrop::new(42);

    /// 创建新的标记类型
    /// Create new type
    pub fn new(value: i32) -> Self {
        Self {
            value: ManuallyDrop::new(value),
        }
    }

    /// 检查是否为特殊标记值
    pub fn is_special(&self) -> bool {
        matches!(self.value, Self::SPECIAL)
    }

    /// 使用模式匹配处理特殊标记
    pub fn process(&self) -> &'static str {
        match self.value {
            Self::SPECIAL => "special_marker",
            _ => "regular",
        }
    }
}

/// 使用 ManuallyDrop 常量模式进行类型标记
/// ManuallyDrop constant type mark
pub enum TaggedValue {
    Int(ManuallyDrop<i32>),
    Text(ManuallyDrop<String>),
}

impl TaggedValue {
    /// 默认整数标记常量
    pub const DEFAULT_INT: ManuallyDrop<i32> = ManuallyDrop::new(0);

    /// 匹配默认标记
    /// mark
    pub fn is_default_int(&self) -> bool {
        matches!(self, TaggedValue::Int(Self::DEFAULT_INT))
    }
}

// ==================== 演示函数 ====================

/// 演示 Rust 1.96 设计模式特性
/// demonstration Rust 1.96 design feature
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 设计模式特性演示");
    println!("========================================\n");

    println!("--- LazyLock::from 单例模式 ---");
    let config = SingletonConfig::from_value(String::from("production"));
    println!("config = {}", config.get());

    println!("\n--- assert_matches! 状态机测试 ---");
    let state = ConnectionState::Connecting;
    let next = transition(state, "ok");
    println!("transition(Connecting, ok) = {:?}", next);

    println!("\n--- ManuallyDrop 常量模式 ---");
    let marker = MarkerType::new(42);
    println!("marker(42).is_special() = {}", marker.is_special());
    println!("marker(42).process() = {}", marker.process());

    let regular = MarkerType::new(100);
    println!("marker(100).process() = {}", regular.process());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
/// Get featuresinformation
pub fn get_rust_196_pattern_info() -> String {
    "Rust 1.96.0 设计模式特性:\n- LazyLock::from(value) 用于单例模式直接构造\n- assert_matches! \
     用于状态机模式断言测试\n- ManuallyDrop 常量可作为模式匹配使用"
        .to_string()
}

#[cfg(test)]
mod tests {
    use std::assert_matches;

    use super::*;

    #[test]
    fn test_singleton_config() {
        let config = SingletonConfig::from_value(String::from("test"));
        assert_eq!(config.get(), "test");
    }

    #[test]
    fn test_singleton_counter() {
        let counter = SingletonCounter::new("requests");
        assert_eq!(counter.description(), "requests");
    }

    #[test]
    fn test_state_machine_transitions() {
        let disconnected = ConnectionState::Disconnected;

        let connecting = transition(disconnected, "connect");
        assert_matches!(connecting, ConnectionState::Connecting);

        let connected = transition(connecting.clone(), "ok");
        assert_matches!(connected, ConnectionState::Connected { .. });
        assert_matches!(&connected, ConnectionState::Connected { address } if address == "127.0.0.1");

        let disconnected2 = transition(connected, "disconnect");
        assert_matches!(disconnected2, ConnectionState::Disconnected);

        let failed = transition(connecting, "fail");
        assert_matches!(failed, ConnectionState::Failed { reason } if reason == "timeout");
    }

    #[test]
    fn test_manually_drop_special_pattern() {
        let special = MarkerType::new(42);
        assert!(special.is_special());
        assert_eq!(special.process(), "special_marker");

        let regular = MarkerType::new(0);
        assert!(!regular.is_special());
        assert_eq!(regular.process(), "regular");
    }

    #[test]
    fn test_tagged_value_default() {
        let default = TaggedValue::Int(ManuallyDrop::new(0));
        assert!(default.is_default_int());

        let other = TaggedValue::Int(ManuallyDrop::new(5));
        assert!(!other.is_default_int());
    }

    #[test]
    fn test_get_rust_196_pattern_info() {
        let info = get_rust_196_pattern_info();
        assert!(info.contains("LazyLock::from"));
        assert!(info.contains("assert_matches!"));
    }
}
