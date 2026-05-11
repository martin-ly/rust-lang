//! Rust 1.95.0 线程与并发新特性实现模块
//!
//! 本模块展示了 Rust 1.95.0 在线程与并发编程方面的关键增强：
//! - `AtomicPtr::update` / `try_update` ⭐
//! - `AtomicBool::update` / `try_update` ⭐
//! - `Atomic*::update` / `try_update` (整数类型) ⭐
//! - `core::hint::cold_path` ⭐
//! - `thread::scope` TLS 析构函数交互文档更新
//!
//! # 版本信息
//! - Rust版本: 1.95.0
//! - 稳定日期: 2026-04-16
//! - Edition: 2024
//!
//! # 参考
//! - [Rust 1.95.0 Release Notes](https://releases.rs/docs/1.95.0/)

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicUsize, Ordering};
use std::thread;

// ============================================================================
// 1. Atomic*::update / try_update
// ============================================================================

/// # `Atomic*::update` / `try_update` 深度解析
///
/// ## 概念定义
/// Rust 1.95.0 为所有原子类型稳定了 `update` 和 `try_update` 方法：
/// - `update(f)`: 读取当前值，应用 `f` 得到新值，CAS 循环直到成功
/// - `try_update(f)`: 同上，但如果 `f` 返回 `Err`，则中止并返回错误
///
/// 这是对传统 `fetch_update` 方法的补充，提供了更简洁的函数式 API。
///
/// ## Wikipedia 概念对齐
/// - **Compare-and-Swap (CAS)**: 原子操作的基石，`update` 是 CAS 循环的高阶抽象
/// - **Lock-free Algorithm**: 无锁编程范式，原子更新是核心原语
///
/// ## 对比：传统方式 vs update
///
/// | 维度 | `fetch_update` (旧) | `update` / `try_update` (1.95+) |
/// |------|-------------------|-------------------------------|
/// | 返回值 | `Result<T, T>` (成功返回旧值) | 直接返回新值 |
/// | 错误处理 | 需手动处理 `CompareExchangeError` | `try_update` 天然支持 `Result` |
/// | 语义清晰度 | 较模糊（成功/失败返回不同类型） | 明确：成功→新值，失败→错误 |
/// | 函数式风格 | 较弱 | 强（直接传入闭包） |
///
/// ## 决策树
/// ```text
/// 需要原子更新值？
/// ├── 更新必定成功？ → update(closure)
/// ├── 更新可能失败（需前置条件检查）？ → try_update(closure)
/// ├── 需要旧值？ → fetch_update (保留旧 API)
/// └── 仅需简单加减？ → fetch_add / fetch_sub
/// ```
///
/// ## 反例 / 限制
/// - `update` 内部是 CAS 循环，如果闭包执行时间过长或竞争激烈，可能导致**活锁 (livelock)**
/// - 闭包可能被调用多次（CAS 失败重试），因此闭包必须是**无副作用的纯函数**
/// - `try_update` 中返回 `Err` 不会回滚已执行的闭包副作用
pub struct AtomicUpdateExamples;

impl AtomicUpdateExamples {
    /// 基础示例：原子计数器递增（使用 update）
    ///
    /// 对比 `fetch_add`：当更新逻辑较复杂时，`update` 更优雅。
    pub fn atomic_counter_update(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1)
    }

    /// 条件更新：仅当值满足条件时才更新（try_update）
    ///
    /// 展示了 `try_update` 的强大能力：原子性条件更新。
    pub fn try_increment_if_even(counter: &AtomicI32) -> Result<i32, i32> {
        counter.try_update(Ordering::SeqCst, Ordering::SeqCst, |old| {
            if old % 2 == 0 { Some(old + 1) } else { None }
        })
    }

    /// 原子指针更新：CAS 循环简化
    ///
    /// `AtomicPtr::update` 极大地简化了指针级别的原子操作。
    pub fn update_shared_config<T>(ptr: &AtomicPtr<T>, updater: impl Fn(&T) -> T) -> *mut T {
        ptr.update(Ordering::Acquire, Ordering::Relaxed, |old_ptr| {
            // SAFETY: 假设 old_ptr 是有效的，且我们拥有更新权
            let old_ref = unsafe { &*old_ptr };
            let new_value = updater(old_ref);
            Box::into_raw(Box::new(new_value))
        })
    }

    /// AtomicBool 的条件翻转
    ///
    /// 仅当当前为 `false` 时设为 `true`（一次性触发）。
    pub fn try_set_flag(flag: &AtomicBool) -> Result<bool, bool> {
        flag.try_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
            if current { None } else { Some(true) }
        })
    }

    /// 指数退避：结合 update 与线程休眠
    ///
    /// 展示了 `update` 在并发算法中的实际应用。
    pub fn exponential_backoff_attempt(attempts: &AtomicUsize) -> usize {
        let attempt = attempts.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1);
        let delay_ms = 2usize.pow(attempt.min(10) as u32);
        thread::sleep(std::time::Duration::from_millis(delay_ms as u64));
        attempt
    }
}

// ============================================================================
// ConnectionState: 用于原子状态机的枚举
// ============================================================================

/// 状态机转换：原子状态更新
///
/// 使用 `try_update` 实现线程安全的状态机转换。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionState {
    Idle = 0,
    Connecting = 1,
    Connected = 2,
    Closing = 3,
    Closed = 4,
}

impl AtomicUpdateExamples {
    pub fn try_transition_state(
        state: &AtomicUsize,
        from: ConnectionState,
        to: ConnectionState,
    ) -> Result<usize, usize> {
        state.try_update(Ordering::Acquire, Ordering::Relaxed, |current| {
            if current == from as usize {
                Some(to as usize)
            } else {
                None
            }
        })
    }
}

// ============================================================================
// ConcurrentStats: 并发统计
// ============================================================================

/// 并发统计：使用 update 累加复杂指标
///
/// 在并发场景下安全地更新复合统计值。
pub struct ConcurrentStats {
    total_requests: AtomicUsize,
    total_errors: AtomicUsize,
}

impl ConcurrentStats {
    pub fn new() -> Self {
        Self {
            total_requests: AtomicUsize::new(0),
            total_errors: AtomicUsize::new(0),
        }
    }

    pub fn record_request(&self, is_error: bool) {
        self.total_requests
            .update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1);
        if is_error {
            self.total_errors
                .update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1);
        }
    }

    pub fn snapshot(&self) -> (usize, usize) {
        (
            self.total_requests.load(Ordering::Relaxed),
            self.total_errors.load(Ordering::Relaxed),
        )
    }
}

impl Default for ConcurrentStats {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 2. core::hint::cold_path
// ============================================================================

/// # `core::hint::cold_path` 解析
///
/// ## 概念定义
/// `cold_path` 是一个编译器提示，告诉优化器：当前代码路径**极少执行**（冷路径）。
/// 编译器会据此进行代码布局优化，将冷路径移到远离热路径的位置，
/// 改善指令缓存 (I-cache) 利用率。
///
/// ## Wikipedia 概念对齐
/// - **Branch Prediction**: CPU 推测执行机制，`cold_path` 帮助编译器生成对预测器友好的代码
/// - **Profile-guided Optimization (PGO)**: 基于执行频率的优化，`cold_path` 是手动 PGO 提示
///
/// ## 对比
///
/// | 方式 | 语义 | 稳定性 | 适用场景 |
/// |------|------|--------|---------|
/// | `cold_path` (1.95+) | 明确标记冷路径 | 标准库稳定 | 错误处理、panic、边界检查失败 |
/// | `std::intrinsics::unlikely` | 暗示布尔表达式为假 | 不稳定 (intrinsic) | 条件分支 |
/// | `#[cold]` 属性 | 标记函数为冷 | 已稳定 | 整个函数 |
/// | `LLVM __builtin_expect` | 底层编译器提示 | C/FFI | 底层优化 |
///
/// ## 决策树
/// ```text
/// 有极少执行的错误/边界路径？
/// ├── 整个函数极少调用？ → #[cold]
/// ├── 函数内某分支极少命中？ → cold_path()
/// └── 布尔条件极少为真？ → unlikely() (unstable)
/// ```
///
/// ## 反例 / 误用
/// - **不要滥用**：标记非冷路径为冷会导致分支预测失败，降低性能
/// - **不要与 IO/睡眠混用**：IO 已经是慢路径，`cold_path` 对延迟无帮助
/// - **不要替代错误处理**：它只是优化提示，不改变语义
pub struct ColdPathExamples;

impl ColdPathExamples {
    /// 基础示例：错误处理路径标记为冷
    pub fn parse_or_default(input: &str) -> i32 {
        match input.parse::<i32>() {
            Ok(value) => value,
            Err(_) => {
                // 解析失败是异常情况，标记为冷路径
                std::hint::cold_path();
                0 // 默认值
            }
        }
    }

    /// 并发场景：锁竞争失败路径
    pub fn try_lock_with_cold_hint<T>(
        lock: &std::sync::Mutex<T>,
    ) -> Option<std::sync::MutexGuard<'_, T>> {
        match lock.try_lock() {
            Ok(guard) => Some(guard),
            Err(_) => {
                // 锁竞争在低开销下应少见
                std::hint::cold_path();
                None
            }
        }
    }

    /// 状态机：非法状态转换
    pub fn state_transition_safe(current: ConnectionState, event: &str) -> ConnectionState {
        match (current, event) {
            (ConnectionState::Idle, "connect") => ConnectionState::Connecting,
            (ConnectionState::Connecting, "success") => ConnectionState::Connected,
            (ConnectionState::Connected, "disconnect") => ConnectionState::Idle,
            _ => {
                // 非法转换在正确程序中不应发生
                std::hint::cold_path();
                current // 保持不变
            }
        }
    }

    /// 与 `#[cold]` 属性函数结合使用
    ///
    /// 当整个错误处理函数都是冷路径时，优先使用 `#[cold]`；
    /// 当只有某条分支是冷路径时，使用 `cold_path()`。
    #[cold]
    fn handle_fatal_error() -> ! {
        eprintln!("Fatal error occurred");
        std::process::exit(1);
    }

    pub fn check_invariant(condition: bool) {
        if !condition {
            // 不变量违反是程序 bug，在正确执行中永不发生
            std::hint::cold_path();
            Self::handle_fatal_error();
        }
    }
}

// ============================================================================
// 3. thread::scope TLS 析构函数交互
// ============================================================================

/// # `thread::scope` 与 TLS (Thread Local Storage) 析构
///
/// Rust 1.95.0 更新了 `thread::scope` 的文档，明确了 `join` 与 TLS 析构函数的交互：
/// - `thread::scope` 返回前会**等待所有线程完成**
/// - 但 TLS 析构函数**可能**在 scope 返回后才执行（取决于平台实现）
/// - 因此不应在 scope 外部依赖 TLS 中的数据
///
/// ## Wikipedia 概念对齐
/// - **Thread-local Storage**: 线程私有存储，线程退出时析构
/// - **RAII (Resource Acquisition Is Initialization)**: TLS 析构是 RAII 的线程级扩展
///
/// ## 最佳实践
/// 1. 在 `thread::scope` 内通过 `join` 或共享引用获取结果
/// 2. 不要依赖 TLS 数据在 scope 外部的可用性
/// 3. 使用 `Arc`/`Mutex` 等显式共享机制替代 TLS 跨线程通信
pub struct ScopeTlsExamples;

impl ScopeTlsExamples {
    /// 安全示例：通过共享引用而非 TLS 传递结果
    pub fn safe_scope_pattern() -> i32 {
        let result = Arc::new(AtomicI32::new(0));

        thread::scope(|s| {
            let result_clone = Arc::clone(&result);
            s.spawn(move || {
                // 安全：通过原子变量共享结果
                result_clone.store(42, Ordering::Relaxed);
            });
        });

        // scope 返回时，线程已 join，但 TLS 析构顺序不确定
        // 然而 Arc/Atomic 不依赖 TLS，因此安全
        result.load(Ordering::Relaxed)
    }

    /// TLS 在 scope 中的正确使用
    ///
    /// TLS 仅用于线程内部状态，不跨线程暴露。
    pub fn tls_inside_scope() {
        thread_local! {
            static COUNTER: std::cell::Cell<i32> = const { std::cell::Cell::new(0) };
        }

        thread::scope(|s| {
            s.spawn(|| {
                COUNTER.with(|c| {
                    c.set(c.get() + 1);
                    println!("Thread-local counter: {}", c.get());
                });
            });

            s.spawn(|| {
                COUNTER.with(|c| {
                    c.set(c.get() + 100);
                    println!("Thread-local counter: {}", c.get());
                });
            });
        });

        // 注意：主线程的 TLS 不受影响，各线程 TLS 独立
    }
}

// ============================================================================
// 测试
// ============================================================================

// ============================================================================
// cfg_select! 宏 — 编译时平台选择 (Rust 1.95 stable)
// ============================================================================

/// # `cfg_select!` 宏
///
/// `cfg_select!` 是 Rust 1.95.0 稳定的编译时条件选择宏。
/// 在线程编程中，可用于编译期选择平台相关的线程栈大小默认值。
pub struct CfgSelectThreadExamples;

impl CfgSelectThreadExamples {
    /// 平台相关的默认线程栈大小 (bytes)
    pub const DEFAULT_STACK_SIZE: usize = cfg_select! {
        target_os = "linux" => { 2 * 1024 * 1024 }
        target_os = "macos" => { 2 * 1024 * 1024 }
        target_os = "windows" => { 1024 * 1024 }
        _ => { 512 * 1024 }
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_update_counter() {
        let counter = AtomicUsize::new(0);
        let new_val = AtomicUpdateExamples::atomic_counter_update(&counter);
        // update 返回旧值（类似 fetch_add）
        assert_eq!(new_val, 0);
        assert_eq!(counter.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn test_try_update_even() {
        let counter = AtomicI32::new(4);
        let result = AtomicUpdateExamples::try_increment_if_even(&counter);
        // try_update 成功时返回 Ok(旧值)，counter 被更新为新值
        assert_eq!(result, Ok(4));
        assert_eq!(counter.load(Ordering::Relaxed), 5);

        let counter = AtomicI32::new(5);
        let result = AtomicUpdateExamples::try_increment_if_even(&counter);
        // try_update 失败时返回 Err(当前值)
        assert_eq!(result, Err(5));
    }

    #[test]
    fn test_state_transition() {
        let state = AtomicUsize::new(ConnectionState::Idle as usize);

        let result = AtomicUpdateExamples::try_transition_state(
            &state,
            ConnectionState::Idle,
            ConnectionState::Connecting,
        );
        assert!(result.is_ok());

        let fail = AtomicUpdateExamples::try_transition_state(
            &state,
            ConnectionState::Idle,
            ConnectionState::Connected,
        );
        assert!(fail.is_err());
    }

    #[test]
    fn test_atomic_bool_try_update() {
        let flag = AtomicBool::new(false);
        // try_update 成功时返回 Ok(旧值 false)
        assert_eq!(AtomicUpdateExamples::try_set_flag(&flag), Ok(false));
        // flag 已被设为 true；再次尝试返回 Err(当前值 true)
        assert_eq!(AtomicUpdateExamples::try_set_flag(&flag), Err(true));
    }

    #[test]
    fn test_concurrent_stats() {
        let stats = Arc::new(ConcurrentStats::new());

        let handles: Vec<_> = (0..10)
            .map(|i| {
                let s = Arc::clone(&stats);
                thread::spawn(move || {
                    s.record_request(i % 3 == 0); // 1/3 是错误
                })
            })
            .collect();

        for h in handles {
            h.join().unwrap();
        }

        let (requests, errors) = stats.snapshot();
        assert_eq!(requests, 10);
        assert_eq!(errors, 4); // 0, 3, 6, 9
    }

    #[test]
    fn test_cold_path_parse() {
        assert_eq!(ColdPathExamples::parse_or_default("42"), 42);
        assert_eq!(ColdPathExamples::parse_or_default("invalid"), 0);
    }

    #[test]
    fn test_safe_scope_pattern() {
        assert_eq!(ScopeTlsExamples::safe_scope_pattern(), 42);
    }

    #[test]
    fn test_tls_inside_scope() {
        ScopeTlsExamples::tls_inside_scope();
        // 只要不出错即通过
    }
}


// ============================================================================
// Real Rust 1.95 Features — Concurrency, threads, lock-free
// ============================================================================

/// # Real Rust 1.95 Features
///
/// Demonstrates `&raw const`, `unsafe_op_in_unsafe_fn`, and `const {}` blocks.
pub struct RealRust195Features;

impl RealRust195Features {
    /// `const {}` block to compute alignment at compile time
    pub fn const_block_align_demo() -> usize {
        const { std::mem::align_of::<usize>() }
    }

    /// Safe raw reference to a packed struct field using `&raw const`
    pub fn safe_raw_ref_in_packed() -> u32 {
        #[repr(C, packed)]
        struct Packed {
            a: u8,
            b: u32,
        }

        let p = Packed { a: 1, b: 0xDEADBEEF };
        // SAFETY: &raw const avoids creating an intermediate unaligned reference
        let raw = &raw const p.b;
        // SAFETY: read via raw pointer from a valid local
        unsafe { std::ptr::read_unaligned(raw) }
    }

    /// Rust 2024 `unsafe_op_in_unsafe_fn` lint demonstration
    ///
    /// Even inside an `unsafe fn`, `unsafe` operations must be wrapped
    /// in explicit `unsafe {}` blocks.
    ///
    /// # Safety
    ///
    /// `counter` must be a valid, properly aligned pointer to an `AtomicU32`.
    pub unsafe fn rust_2024_atomic_unsafe_fn(counter: *mut std::sync::atomic::AtomicU32) -> u32 {
        unsafe { (*counter).fetch_add(1, std::sync::atomic::Ordering::Relaxed) }
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_const_block_align() {
        assert_eq!(RealRust195Features::const_block_align_demo(), std::mem::align_of::<usize>());
    }

    #[test]
    fn test_safe_raw_ref_in_packed() {
        assert_eq!(RealRust195Features::safe_raw_ref_in_packed(), 0xDEADBEEF);
    }

    #[test]
    fn test_rust_2024_atomic_unsafe_fn() {
        let mut value = std::sync::atomic::AtomicU32::new(10);
        let result = unsafe { RealRust195Features::rust_2024_atomic_unsafe_fn(&mut value) };
        assert_eq!(result, 10);
        assert_eq!(value.load(std::sync::atomic::Ordering::Relaxed), 11);
    }
}
