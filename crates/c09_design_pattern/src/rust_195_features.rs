//! Rust 1.95 特性 —— 设计模式场景
//! Rust 1.95 feature —— design scenario
//!
//! # 概述
//! # Overview
//!
//! Rust 1.95 为设计模式实现带来的增强：
//! Rust 1.95 as design ：
//! - **`cfg_select!`** — 跨平台抽象工厂
//! - **`cfg_select!`** — platform factory
//! - **`Atomic*::update`** — 单例模式的并发初始化
//! - **`Atomic*::update`** — singleton concurrency
//! - **`if let` guards** — 状态机模式的条件转换
//! - **`if let` guards** — state machine condition conversion
//! - **`cold_path`** — 错误处理路径优化
//! - **`cold_path`** errorhandlingpath optimization

use std::sync::atomic::{AtomicUsize, Ordering};

// ============================================================================
// 1. cfg_select! — 跨平台抽象工厂
// ============================================================================

/// # 抽象工厂模式（跨平台）
/// # factory （platform ）
///
/// `cfg_select!` 在编译期选择平台特定的实现，零运行时开销。
/// `cfg_select!` in platform ，runtime overhead 。
pub struct PlatformAbstractFactory;

impl PlatformAbstractFactory {
    /// 创建平台特定的线程池大小推荐值
    pub const DEFAULT_THREAD_POOL_SIZE: usize = cfg_select! {
        target_os = "linux" => 8,
        target_os = "macos" => 4,
        target_os = "windows" => 8,
        _ => 2,
    };

    /// 文件路径分隔符
    pub const PATH_SEPARATOR: char = cfg_select! {
        target_os = "windows" => '\\',
        _ => '/',
    };

    /// 换行符序列
    /// sequence
    pub const LINE_ENDING: &'static str = cfg_select! {
        target_os = "windows" => "\r\n",
        _ => "\n",
    };
}

// ============================================================================
// 2. Atomic*::update — 单例/对象池并发控制
// ============================================================================

/// # 并发设计模式中的原子操作
/// # concurrentdesignpatternatomic operation
///
/// 对象池、连接池等模式中的原子计数。
pub struct ConcurrentPatternExamples;

impl ConcurrentPatternExamples {
    /// 对象池引用计数（装饰器模式中的包装计数）
    /// to reference counting （decorator in ）
    pub fn pool_borrow_count_increment(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Acquire, Ordering::Relaxed, |old| old + 1)
    }

    /// 对象池引用计数递减
    /// to reference counting
    pub fn pool_borrow_count_decrement(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Release, Ordering::Relaxed, |old| {
            old.saturating_sub(1)
        })
    }

    /// 尝试获取对象池中的对象（享元模式）
    /// to in to （flyweight ）
    pub fn try_acquire_from_pool(counter: &AtomicUsize, max_size: usize) -> Result<usize, usize> {
        counter.try_update(Ordering::Acquire, Ordering::Relaxed, |current| {
            if current < max_size {
                Some(current + 1)
            } else {
                None
            }
        })
    }

    /// 观察者模式：原子事件计数器递增
    pub fn event_notify(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1)
    }
}

// ============================================================================
// 3. if let guards — 状态机模式
// ============================================================================

/// # 状态机设计模式
/// # state machinedesign pattern
///
/// `if let` guards 简化了状态机的条件转换逻辑。
/// `if let` guards state machine condition conversion 。
pub struct StateMachinePatternExamples;

impl StateMachinePatternExamples {
    /// 订单状态机转换
    /// state machine conversion
    pub fn order_state_transition(
        state: &str,
        event: &str,
        payment_ok: bool,
    ) -> Option<&'static str> {
        match (state, event) {
            ("created", "pay") if payment_ok => Some("paid"),
            ("created", "cancel") => Some("cancelled"),
            ("paid", "ship") => Some("shipped"),
            ("shipped", "deliver") => Some("delivered"),
            ("delivered", "return") if payment_ok => Some("returned"),
            _ => None,
        }
    }

    /// 命令模式：条件执行
    pub fn execute_command(
        cmd: &str,
        args: Option<&str>,
        authorized: bool,
    ) -> Result<(), &'static str> {
        match (cmd, args) {
            ("delete", Some(_)) if authorized => Ok(()),
            ("delete", Some(_)) => Err("unauthorized"),
            ("read", Some(_)) => Ok(()),
            ("write", Some(_)) if authorized => Ok(()),
            _ => Err("invalid command"),
        }
    }
}

// ============================================================================
// 4. cold_path — 异常路径优化
// ============================================================================

/// # 设计模式中的异常路径
/// # designpattern path
///
/// 错误处理、验证失败等罕见路径。
/// error handling 、etc. 。
pub struct PatternColdPathExamples;

impl PatternColdPathExamples {
    /// 访问者模式：未处理的类型为冷路径
    pub fn visit_supported_type(ty: &str) -> Result<(), &'static str> {
        match ty {
            "int" | "float" | "string" | "bool" => Ok(()),
            _ => {
                std::hint::cold_path();
                Err("unsupported type")
            }
        }
    }

    /// 策略模式：策略验证失败为冷路径
    pub fn validate_strategy(name: &str) -> bool {
        match name {
            "round_robin" | "least_conn" | "ip_hash" => true,
            _ => {
                std::hint::cold_path();
                false
            }
        }
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_platform_factory() {
        const { assert!(PlatformAbstractFactory::DEFAULT_THREAD_POOL_SIZE >= 2) };
    }

    #[test]
    fn test_pool_acquire() {
        let counter = AtomicUsize::new(0);
        assert!(ConcurrentPatternExamples::try_acquire_from_pool(&counter, 5).is_ok());
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        counter.store(5, Ordering::Relaxed);
        assert!(ConcurrentPatternExamples::try_acquire_from_pool(&counter, 5).is_err());
    }

    #[test]
    fn test_order_state_machine() {
        assert_eq!(
            StateMachinePatternExamples::order_state_transition("created", "pay", true),
            Some("paid")
        );
        assert_eq!(
            StateMachinePatternExamples::order_state_transition("created", "pay", false),
            None
        );
        assert_eq!(
            StateMachinePatternExamples::order_state_transition("paid", "ship", true),
            Some("shipped")
        );
    }

    #[test]
    fn test_command_pattern() {
        assert!(StateMachinePatternExamples::execute_command("read", Some("file"), false).is_ok());
        assert!(StateMachinePatternExamples::execute_command("delete", Some("file"), true).is_ok());
        assert!(
            StateMachinePatternExamples::execute_command("delete", Some("file"), false).is_err()
        );
    }

    #[test]
    fn test_strategy_validation() {
        assert!(PatternColdPathExamples::validate_strategy("round_robin"));
        assert!(!PatternColdPathExamples::validate_strategy("unknown"));
    }
}

// ============================================================================
// 5. RealRust195Features — AsyncFn strategy pattern + ControlFlow::map_continue
// ============================================================================

use std::ops::ControlFlow;

/// # 真实 Rust 1.95 特性演示
/// # real Rust 1.95 feature demonstration
///
/// 展示 `AsyncFn` 在策略模式中的应用以及 `ControlFlow::map_continue` 的访问者模式。
/// `AsyncFn` in strategy in application and `ControlFlow::map_continue` visitor 。
pub struct RealRust195Features;

impl RealRust195Features {
    /// 使用 `AsyncFn` 实现异步策略模式
    /// use `AsyncFn` implementationasync pattern
    ///
    /// `async |x| x * 2` 闭包实现了 `AsyncFn` trait，可作为策略注入。
    /// `async |x| x * 2` `AsyncFn` trait，as strategy 。
    pub async fn async_strategy_pattern() -> i32 {
        run_strategy(async |x: i32| -> i32 { x * 2 }, 21).await
    }

    /// 使用 `ControlFlow::map_continue` 实现访问者模式
    /// use `ControlFlow::map_continue` implementation pattern
    /// in in to `Continue` conversion 。
    pub fn control_flow_visitor() -> ControlFlow<&'static str, i32> {
        let intermediate = ControlFlow::Continue(5);
        intermediate.map_continue(|v| v + 10)
    }
}

async fn run_strategy<F>(strategy: F, input: i32) -> i32
where
    F: AsyncFn(i32) -> i32,
{
    strategy(input).await
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_async_strategy_pattern() {
        let result = futures::executor::block_on(RealRust195Features::async_strategy_pattern());
        assert_eq!(result, 42);
    }

    #[test]
    fn test_control_flow_visitor() {
        assert_eq!(
            RealRust195Features::control_flow_visitor(),
            ControlFlow::Continue(15)
        );
    }
}
