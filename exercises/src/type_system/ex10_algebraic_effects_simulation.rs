//! # 练习 10: 代数效应模拟 / Exercise 10: Algebraic Effects Simulation
//!
//! **难度 / Difficulty**: Hard  
//! **考点 / Focus**: 用枚举和解释器模拟代数效应与处理器（无语言原生支持）
//!   Simulate algebraic effects and handlers with enums and an interpreter
//!   (no native effect support).
//!
//! ## 题目描述 / Problem Description
//!
//! Rust 目前没有用户可定义的代数效应；本练习用 `enum` + 解释器模拟
//! “抛出/捕获”效应处理器，理解 `async`/`try`/`gen` 等关键字效应的
//! 共同结构。
//! Rust has no user-defined algebraic effects yet; this exercise simulates
//! "throw/catch" handlers with an enum and a small interpreter to understand
//! the common structure behind `async`/`try`/`gen` keyword effects.
//!
//! ## 对应概念 / Related Concepts
//!
//! - `concept/04_formal/07_concurrency_semantics/04_algebraic_effects.md`
//! - `concept/07_future/02_preview_features/01_effects_system.md`

/// 模拟的效应标签 / Simulated effect labels
#[derive(Debug, Clone, PartialEq)]
pub enum Label {
    /// 失败效应 / Failure effect
    Failure,
    /// 日志效应 / Log effect
    Log(String),
}

/// 计算结果：正常值 或 暂停并等待处理器的效应 / Computation result: value or suspended effect
#[derive(Debug, Clone, PartialEq)]
pub enum Effect<T> {
    /// 正常返回 / Normal return
    Done(T),
    /// 触发效应：携带标签和恢复默认值 / Perform effect: label and default resume value
    Perform { label: Label, default: T },
}

/// 安全除法：除零时触发 `Failure` 效应 / Safe division: triggers `Failure` on divide-by-zero
pub fn checked_divide(a: i32, b: i32) -> Effect<i32> {
    if b == 0 {
        Effect::Perform {
            label: Label::Failure,
            default: 0,
        }
    } else {
        Effect::Done(a / b)
    }
}

/// 序列化两个可能触发效应的计算 / Sequence two effectful computations
///
/// 处理器视角：先跑第一个；若触发效应则原样向上冒泡 / Handler view: run first; bubble up effects.
pub fn and_then<T>(first: Effect<T>, f: impl FnOnce(T) -> Effect<T>) -> Effect<T> {
    match first {
        Effect::Done(v) => f(v),
        effect => effect,
    }
}

/// 解释器：遇到 `Failure` 返回默认值，遇到 `Log` 继续执行 / Interpreter: handle Failure, continue on Log
pub fn handle<T>(comp: Effect<T>, on_failure: impl FnOnce() -> T) -> T {
    match comp {
        Effect::Done(v) => v,
        Effect::Perform { label, default } => match label {
            Label::Failure => on_failure(),
            // 日志等可恢复效应：用默认值继续 / resumable effect: continue with default
            _ => default,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checked_divide_normal() {
        assert_eq!(checked_divide(10, 2), Effect::Done(5));
    }

    #[test]
    fn test_checked_divide_by_zero_performs_effect() {
        assert_eq!(
            checked_divide(10, 0),
            Effect::Perform {
                label: Label::Failure,
                default: 0,
            }
        );
    }

    #[test]
    fn test_and_then_chains_success() {
        let comp = and_then(checked_divide(20, 4), |x| checked_divide(x, 2));
        assert_eq!(comp, Effect::Done(2));
    }

    #[test]
    fn test_and_then_bubbles_failure() {
        let comp = and_then(checked_divide(20, 4), |x| checked_divide(x, 0));
        assert_eq!(
            comp,
            Effect::Perform {
                label: Label::Failure,
                default: 0,
            }
        );
    }

    #[test]
    fn test_handle_failure() {
        let comp = and_then(checked_divide(20, 4), |x| checked_divide(x, 0));
        assert_eq!(handle(comp, || -1), -1);
    }

    #[test]
    fn test_handle_success() {
        assert_eq!(handle(checked_divide(20, 4), || -1), 5);
    }

    #[test]
    fn test_log_is_resumable() {
        let log_effect = Effect::Perform {
            label: Label::Log("checkpoint".into()),
            default: 42,
        };
        assert_eq!(handle(log_effect, || -1), 42);
    }
}
