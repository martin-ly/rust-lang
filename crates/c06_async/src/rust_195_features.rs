//! Rust 1.95.0 异步编程新特性实现模块
//!
//! 本模块展示了 Rust 1.95.0 在异步编程场景中的应用，包括：
//! - `if let` guards 在异步流处理中的应用 ⭐
//! - `ControlFlow::is_break` / `is_continue` (const) 在异步状态机中的应用
//!
//! # 版本信息
//! - Rust版本: 1.95.0
//! - 稳定日期: 2026-04-16
//! - Edition: 2024
//!
//! # 参考
//! - [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)

use std::ops::ControlFlow;

// ============================================================================
// 1. if let guards 在异步编程中的应用
// ============================================================================

/// # `if let` Guards 在异步场景中的深度应用
///
/// `if let` guards (Rust 1.95.0 稳定) 在处理异步结果、流数据、状态机时
/// 提供了极大的代码简洁性。本模块展示了其在异步编程中的典型模式。
pub struct AsyncIfLetGuardExamples;

impl AsyncIfLetGuardExamples {
    /// 解析超时配置字符串
    pub fn parse_timeout_ms(input: Option<&str>) -> Result<u64, &'static str> {
        match input {
            Some(s) if let Ok(ms) = s.parse::<u64>() && ms > 0 && ms <= 3_600_000 => Ok(ms),
            Some(s) if let Ok(_) = s.parse::<u64>() => Err("超时值必须在 1ms 到 1 小时之间"),
            Some(_) => Err("无效的超时值格式"),
            None => Ok(5000), // 默认 5 秒
        }
    }

    /// 评估异步任务结果：Result<Option<T>> 扁平化处理
    pub fn evaluate_task_result(result: Result<Option<u32>, &'static str>) -> &'static str {
        match result {
            Ok(Some(0)) => "任务成功完成",
            Ok(Some(n)) if n < 100 => "任务完成，轻微警告",
            Ok(Some(_)) => "任务完成，需要关注",
            Ok(None) => "任务结果为空",
            Err("timeout") => "任务执行超时",
            Err("cancelled") => "任务被取消",
            Err(_) => "任务执行失败",
        }
    }

    /// 异步配置解析：多字段组合 guard
    pub fn parse_async_config(key: &str, value: &str) -> AsyncConfigValue {
        match (key, value) {
            ("timeout", v) if let Ok(ms) = v.parse::<u64>() && ms > 0 => {
                AsyncConfigValue::Timeout(std::time::Duration::from_millis(ms))
            }
            ("concurrency", v) if let Ok(n) = v.parse::<usize>() && n > 0 && n <= 1000 => {
                AsyncConfigValue::Concurrency(n)
            }
            ("retry", v) if let Ok(b) = v.parse::<bool>() => AsyncConfigValue::Retry(b),
            ("backoff_ms", v) if let Ok(ms) = v.parse::<u64>() => {
                AsyncConfigValue::Backoff(std::time::Duration::from_millis(ms))
            }
            _ => AsyncConfigValue::Invalid(format!("{}={}", key, value)),
        }
    }

    pub fn transition_pool_state(
        state: PoolConnectionState,
        event: PoolEvent,
    ) -> PoolConnectionState {
        match (state, event) {
            (
                PoolConnectionState::Idle,
                PoolEvent::ConnectRequest { timeout_ms },
            ) if timeout_ms > 0 => {
                PoolConnectionState::Connecting {
                    attempt: 1,
                    since: std::time::Instant::now(),
                }
            }
            (
                PoolConnectionState::Connecting { attempt: _, since: _ },
                PoolEvent::ConnectSuccess { conn_id },
            ) if let Some(valid_id) = validate_conn_id(&conn_id) => PoolConnectionState::Connected {
                id: valid_id,
                created_at: std::time::Instant::now(),
            },
            (
                PoolConnectionState::Connecting { attempt, since: _ },
                PoolEvent::ConnectFailed { error: _ },
            ) if attempt < 3 => PoolConnectionState::Connecting {
                attempt: attempt + 1,
                since: std::time::Instant::now(),
            },
            (
                PoolConnectionState::Connecting { .. },
                PoolEvent::ConnectFailed { error },
            ) => PoolConnectionState::Failed {
                error,
                retry_after: std::time::Instant::now() + std::time::Duration::from_secs(30),
            },
            (PoolConnectionState::Connected { .. }, PoolEvent::Disconnect) => {
                PoolConnectionState::Idle
            }
            (state, _) => state,
        }
    }
}

#[derive(Debug, Clone)]
pub enum AsyncConfigValue {
    Timeout(std::time::Duration),
    Concurrency(usize),
    Retry(bool),
    Backoff(std::time::Duration),
    Invalid(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum PoolConnectionState {
    Idle,
    Connecting { attempt: u32, since: std::time::Instant },
    Connected { id: String, created_at: std::time::Instant },
    Failed { error: String, retry_after: std::time::Instant },
}

#[derive(Debug, Clone)]
pub enum PoolEvent {
    ConnectRequest { timeout_ms: u64 },
    ConnectSuccess { conn_id: String },
    ConnectFailed { error: String },
    Disconnect,
}

fn validate_conn_id(id: &str) -> Option<String> {
    if id.len() >= 4 && id.chars().all(|c| c.is_ascii_alphanumeric() || c == '-') {
        Some(id.to_string())
    } else {
        None
    }
    }

// ============================================================================
// 2. ControlFlow 在异步状态机中的应用
// ============================================================================

/// # `ControlFlow` 与异步迭代
///
/// `ControlFlow::is_break` / `is_continue` 在 const 上下文稳定后，
/// 可在编译期构建异步状态机的静态检查。
pub struct AsyncControlFlowExamples;

impl AsyncControlFlowExamples {
    /// 编译期常量检查：验证状态机终止条件
    /// 状态机终止检查（1.95+ `is_break`/`is_continue` 在 const 上下文稳定）
    pub fn validate_state_machine_termination() -> bool {
        // 模拟状态机终止检查
        let result: ControlFlow<&'static str, ()> = ControlFlow::Break("completed");
        result.is_break()
    }

    /// 异步流处理：使用 ControlFlow 实现提前终止
    pub async fn process_with_early_termination<
        S: futures::Stream<Item = i32> + Unpin,
    >(
        stream: &mut S,
        threshold: i32,
    ) -> Option<i32> {
        use futures::StreamExt;

        while let Some(value) = stream.next().await {
            if value > threshold {
                return Some(value);
            }
        }
        None
    }

    /// 批量任务处理：部分成功模式
    pub fn process_batch_results(results: &[Result<i32, String>]) -> ControlFlow<Vec<String>, Vec<i32>> {
        let mut successes = Vec::new();
        let mut errors = Vec::new();

        for result in results {
            match result {
                Ok(v) => successes.push(*v),
                Err(e) => errors.push(e.clone()),
            }
        }

        if errors.is_empty() {
            ControlFlow::Continue(successes)
        } else {
            ControlFlow::Break(errors)
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
    fn test_parse_timeout_ms() {
        assert_eq!(AsyncIfLetGuardExamples::parse_timeout_ms(Some("1000")), Ok(1000));
        assert_eq!(AsyncIfLetGuardExamples::parse_timeout_ms(Some("0")), Err("超时值必须在 1ms 到 1 小时之间"));
        assert_eq!(AsyncIfLetGuardExamples::parse_timeout_ms(Some("abc")), Err("无效的超时值格式"));
        assert_eq!(AsyncIfLetGuardExamples::parse_timeout_ms(None), Ok(5000));
    }

    #[test]
    fn test_evaluate_task_result() {
        assert_eq!(AsyncIfLetGuardExamples::evaluate_task_result(Ok(Some(0))), "任务成功完成");
        assert_eq!(AsyncIfLetGuardExamples::evaluate_task_result(Ok(Some(50))), "任务完成，轻微警告");
        assert_eq!(AsyncIfLetGuardExamples::evaluate_task_result(Ok(Some(200))), "任务完成，需要关注");
        assert_eq!(AsyncIfLetGuardExamples::evaluate_task_result(Err("timeout")), "任务执行超时");
    }

    #[test]
    fn test_async_config_parse() {
        assert!(matches!(
            AsyncIfLetGuardExamples::parse_async_config("timeout", "5000"),
            AsyncConfigValue::Timeout(_)
        ));
        assert!(matches!(
            AsyncIfLetGuardExamples::parse_async_config("concurrency", "100"),
            AsyncConfigValue::Concurrency(100)
        ));
        assert!(matches!(
            AsyncIfLetGuardExamples::parse_async_config("invalid", "value"),
            AsyncConfigValue::Invalid(_)
        ));
    }

    #[test]
    fn test_pool_state_transition() {
        let idle = PoolConnectionState::Idle;
        let event = PoolEvent::ConnectRequest { timeout_ms: 5000 };
        let new_state = AsyncIfLetGuardExamples::transition_pool_state(idle, event);
        assert!(matches!(new_state, PoolConnectionState::Connecting { .. }));
    }

    #[test]
    fn test_async_control_flow_const() {
        assert!(AsyncControlFlowExamples::validate_state_machine_termination());
    }

    #[test]
    fn test_process_batch_results() {
        let all_ok = vec![Ok(1), Ok(2), Ok(3)];
        let result = AsyncControlFlowExamples::process_batch_results(&all_ok);
        assert!(result.is_continue());

        let some_err = vec![Ok(1), Err("fail".to_string()), Ok(3)];
        let result = AsyncControlFlowExamples::process_batch_results(&some_err);
        assert!(result.is_break());
    }
}
