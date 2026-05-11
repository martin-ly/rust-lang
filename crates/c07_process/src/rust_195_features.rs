//! Rust 1.95 特性 —— 进程管理场景
//!
//! # 概述
//!
//! Rust 1.95 在进程管理和系统编程方面的增强：
//! - **`Atomic*::update`/`try_update`** — 进程间共享计数器（如信号量）
//! - **`core::hint::cold_path`** — fork/spawn 失败路径优化
//! - **`if let` guards** — 进程状态转换条件匹配
//! - **`cfg_select!`** — 跨平台进程创建标志

use std::sync::atomic::{AtomicI32, AtomicUsize, Ordering};

// ============================================================================
// 1. Atomic*::update — 进程间共享状态
// ============================================================================

/// # 进程间原子操作
///
/// 在多进程环境中（如通过共享内存），原子操作是协调的基础。
pub struct ProcessAtomicExamples;

impl ProcessAtomicExamples {
    /// 子进程计数器递增（用于进程池管理）
    pub fn fork_child_counter(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::SeqCst, Ordering::Relaxed, |old| old + 1)
    }

    /// 子进程计数器递减
    pub fn reap_child_counter(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::SeqCst, Ordering::Relaxed, |old| old.saturating_sub(1))
    }

    /// 信号量 P 操作（尝试获取资源）
    pub fn semaphore_try_acquire(sem: &AtomicI32) -> Result<i32, i32> {
        sem.try_update(Ordering::Acquire, Ordering::Relaxed, |value| {
            if value > 0 {
                Some(value - 1)
            } else {
                None
            }
        })
    }

    /// 信号量 V 操作（释放资源）
    pub fn semaphore_release(sem: &AtomicI32) -> i32 {
        sem.update(Ordering::Release, Ordering::Relaxed, |value| value + 1)
    }

    /// 共享内存引用计数（用于 mmap 区域生命周期）
    pub fn shm_ref_count_increment(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::SeqCst, Ordering::SeqCst, |old| old + 1)
    }
}

// ============================================================================
// 2. cold_path — 进程错误路径优化
// ============================================================================

/// # 进程创建错误路径优化
///
/// fork/spawn 失败在正常运行中应该是极少数情况。
pub struct ProcessColdPathExamples;

impl ProcessColdPathExamples {
    /// 处理 spawn 结果：失败路径为冷
    pub fn handle_spawn_result<T>(result: Result<T, std::io::Error>) -> Option<T> {
        match result {
            Ok(handle) => Some(handle),
            Err(_e) => {
                std::hint::cold_path();
                None
            }
        }
    }

    /// 处理 waitpid 结果：异常子进程状态为冷
    pub fn handle_wait_status(status: std::process::ExitStatus) -> Result<(), &'static str> {
        if status.success() {
            Ok(())
        } else {
            std::hint::cold_path();
            Err("child process exited with non-zero status")
        }
    }
}

// ============================================================================
// 3. if let guards — 进程状态机
// ============================================================================

/// # 进程生命周期状态机
///
/// 使用 `if let` guards 处理进程状态转换。
pub struct ProcessStateMachineExamples;

impl ProcessStateMachineExamples {
    /// 进程池状态转换
    pub fn pool_state_transition(
        current: &str,
        event: &str,
        active_count: &AtomicUsize,
    ) -> Option<&'static str> {
        match (current, event) {
            ("idle", "spawn") if active_count.load(Ordering::Relaxed) < 8 => Some("spawning"),
            ("spawning", "ready") => Some("running"),
            ("running", "exit") => Some("reaping"),
            ("running", "kill") => Some("terminating"),
            ("reaping", "confirmed") => Some("idle"),
            _ => None,
        }
    }

    /// 信号处理：仅对特定状态转发信号
    pub fn route_signal(pid: Option<u32>, signal: i32, running: bool) -> bool {
        matches!((pid, signal), (Some(_), sig) if sig > 0 && running)
    }
}

// ============================================================================
// 4. cfg_select! — 跨平台进程创建
// ============================================================================

/// # 跨平台进程管理抽象
///
/// `cfg_select!` 提供了进程创建和管理相关的平台差异抽象。
pub struct ProcessCfgSelectExamples;

impl ProcessCfgSelectExamples {
    /// 进程栈大小推荐值（平台特定）
    pub const DEFAULT_STACK_SIZE: usize = cfg_select! {
        target_os = "linux" => 8 * 1024 * 1024,     // 8 MB
        target_os = "macos" => 8 * 1024 * 1024,     // 8 MB
        target_os = "windows" => 1024 * 1024,   // 1 MB
        _ => 2 * 1024 * 1024,
    };

    /// 最大进程数软限制推荐值
    pub const MAX_PROCESSES_RECOMMENDED: usize = cfg_select! {
        target_os = "linux" => 32768,
        target_os = "macos" => 2666,
        target_os = "windows" => 10000,
        _ => 1024,
    };

    /// 是否支持 fork()
    pub const HAS_FORK: bool = cfg_select! {
        target_family = "unix" => true,
        target_family = "windows" => false,
        _ => false,
    };
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_child_counter() {
        let counter = AtomicUsize::new(0);
        ProcessAtomicExamples::fork_child_counter(&counter);
        assert_eq!(counter.load(Ordering::Relaxed), 1);

        ProcessAtomicExamples::reap_child_counter(&counter);
        assert_eq!(counter.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn test_semaphore() {
        let sem = AtomicI32::new(2);
        assert!(ProcessAtomicExamples::semaphore_try_acquire(&sem).is_ok());
        assert!(ProcessAtomicExamples::semaphore_try_acquire(&sem).is_ok());
        assert!(ProcessAtomicExamples::semaphore_try_acquire(&sem).is_err());

        ProcessAtomicExamples::semaphore_release(&sem);
        assert!(ProcessAtomicExamples::semaphore_try_acquire(&sem).is_ok());
    }

    #[test]
    fn test_pool_state_transition() {
        let count = AtomicUsize::new(0);
        assert_eq!(
            ProcessStateMachineExamples::pool_state_transition("idle", "spawn", &count),
            Some("spawning")
        );
        assert_eq!(
            ProcessStateMachineExamples::pool_state_transition("unknown", "spawn", &count),
            None
        );
    }

    #[test]
    fn test_cfg_select_process_limits() {
        const { assert!(ProcessCfgSelectExamples::DEFAULT_STACK_SIZE >= 1024 * 1024) };
        const { assert!(ProcessCfgSelectExamples::MAX_PROCESSES_RECOMMENDED > 0) };
    }
}


// ============================================================================
// Real Rust 1.95 Features — Process, FFI, performance
// ============================================================================

use std::ffi::CStr;

/// # Real Rust 1.95 Features
///
/// Demonstrates `c"..."` C strings, `const {}`, and `if let` guards.
pub struct RealRust195Features;

impl RealRust195Features {
    /// C string literal demonstration
    pub fn c_string_literal_demo() -> &'static CStr {
        c"hello"
    }

    /// `const {}` block to compute buffer size at compile time
    pub fn const_block_buffer_size() -> usize {
        const { 1024 * std::mem::size_of::<u64>() }
    }

    /// Parse a protocol string using `if let` guard
    pub fn parse_protocol_with_guard(input: &str) -> &'static str {
        match input.split_once(':') {
            Some(("http", port_str)) if let Ok(80) = port_str.parse::<u16>() => "HTTP standard",
            Some(("https", port_str)) if let Ok(443) = port_str.parse::<u16>() => "HTTPS standard",
            Some(("http" | "https", _)) => "HTTP variant",
            Some(("ftp", port_str)) if let Ok(21) = port_str.parse::<u16>() => "FTP standard",
            Some(("ftp", _)) => "FTP variant",
            _ => "unknown protocol",
        }
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_c_string_literal() {
        let cstr = RealRust195Features::c_string_literal_demo();
        assert_eq!(cstr, CStr::from_bytes_with_nul(b"hello\0").unwrap());
    }

    #[test]
    fn test_const_block_buffer_size() {
        assert_eq!(RealRust195Features::const_block_buffer_size(), 1024 * 8);
    }

    #[test]
    fn test_parse_protocol_with_guard() {
        assert_eq!(RealRust195Features::parse_protocol_with_guard("http:80"), "HTTP standard");
        assert_eq!(RealRust195Features::parse_protocol_with_guard("https:443"), "HTTPS standard");
        assert_eq!(RealRust195Features::parse_protocol_with_guard("http:8080"), "HTTP variant");
        assert_eq!(RealRust195Features::parse_protocol_with_guard("ftp:21"), "FTP standard");
        assert_eq!(RealRust195Features::parse_protocol_with_guard("ftp:1000"), "FTP variant");
        assert_eq!(RealRust195Features::parse_protocol_with_guard("ssh:22"), "unknown protocol");
    }
}
