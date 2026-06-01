//! - `Atomic*::update` / `try_update` (整数类型) ⭐
//! - `Atomic*::update` / `try_update` (integertype) ⭐
//! - `Atomic*::update` / `try_update` (整数type) ⭐
//! - `Atomic*::update` / `try_update` (integertype) ⭐
//! - `thread::scope` TLS 析构函数交互文档更新
//! - `thread::scope` TLS destructor
//! # 版本信息
//! # Version Information
//! # this
//! - 稳定日期: 2026-04-16
//! - Stabilization date: 2026-04-16
//! - date : 2026-04-16
//! - 稳定date: 2026-04-16
//! - stabledate: 2026-04-16
//! - date: 2026-04-16
//! # 参考
//! # References
//! # reference

use std::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

// ============================================================================
// 1. Atomic*::update / try_update
// ============================================================================

/// # `Atomic*::update` / `try_update` 深度解析
/// # Deep Dive into `Atomic*::update` / `try_update`
/// # `Atomic*::update` / `try_update` 深度Parse
/// ## 概念定义
/// ## Concept Definition
/// ## concept definition
/// - `update(f)`: 读取当前值，应用 `f` 得到新值，CAS 循环直到成功
/// - `update(f)`: when before ，application `f` to ，CAS circulation to
/// - `try_update(f)`: 同上，但如果 `f` 返回 `Err`，则中止并返回错误
/// - `try_update(f)`: on ，but if `f` `Err`，in and
/// ## Wikipedia 概念对齐
/// ## Wikipedia Concept Alignment
/// ## 对比：传统方式 vs update
/// ## to ：way vs update
/// ## to比：传统way vs update
/// | 维度 | `fetch_update` (旧) | `update` / `try_update` (1.95+) |
/// | dimension | `fetch_update` (旧) | `update` / `try_update` (1.95+) |
/// | 返回值 | `Result<T, T>` (成功返回旧值) | 直接返回新值 |
/// | return value | `Result<T, T>` () | |
/// | 语义清晰度 | 较模糊（成功/失败返回不同类型） | 明确：成功→新值，失败→错误 |
/// | clear | vague （/type ） | explicit ：→，→ |
/// | 函数式风格 | 较弱 | 强（直接传入闭包） |
/// | functional | | （） |
/// ## 决策树
/// ## tree
/// ## 决策tree
/// ## tree
/// 需要原子更新值？
/// ？
/// ├── 更新必定成功？ → update(closure)
/// ├── 更新可能失败（需前置条件检查）？ → try_update(closure)
/// ├── may （before condition ）？ → try_update(closure)
/// ├── 需要旧值？ → fetch_update (保留旧 API)
/// ├── ？ → fetch_update ( API)
/// └── 仅需简单加减？ → fetch_add / fetch_sub
/// ## 反例 / 限制
/// ## Counter-examples / Limitations
/// ## /
/// - 闭包可能被调用多次（CAS 失败重试），因此闭包必须是**无副作用的纯函数**
/// - may is （CAS ），therefore must **role function **
pub struct AtomicUpdateExamples;

impl AtomicUpdateExamples {
    /// 基础示例：原子计数器递增（使用 update）
    /// foundation example ：atomic counter （ update）
    /// 对比 `fetch_add`：当更新逻辑较复杂时，`update` 更优雅。
    /// to `fetch_add`：when complex ，`update` 。
    pub fn atomic_counter_update(counter: &AtomicUsize) -> usize {
        counter.update(Ordering::Relaxed, Ordering::Relaxed, |old| old + 1)
    }

    /// 条件更新：仅当值满足条件时才更新（try_update）
    /// condition ：when condition （try_update）
    pub fn try_increment_if_even(counter: &AtomicI32) -> Result<i32, i32> {
        counter.try_update(Ordering::SeqCst, Ordering::SeqCst, |old| {
            if old % 2 == 0 {
                Some(old + 1)
            } else {
                None
            }
        })
    }

    /// 原子指针更新：CAS 循环简化
    /// atomic pointer ：CAS circulation
    pub fn update_shared_config<T>(ptr: &AtomicPtr<T>, updater: impl Fn(&T) -> T) -> *mut T {
        ptr.update(Ordering::Acquire, Ordering::Relaxed, |old_ptr| {
            // SAFETY: 假设 old_ptr 是有效的，且我们拥有更新权
            let old_ref = unsafe { &*old_ptr };
            let new_value = updater(old_ref);
            Box::into_raw(Box::new(new_value))
        })
    }

    /// 仅whenwhenbeforeas `false` 时设as `true`（一次性触发）。
    pub fn try_set_flag(flag: &AtomicBool) -> Result<bool, bool> {
        flag.try_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
            if current {
                None
            } else {
                Some(true)
            }
        })
    }

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
/// state machine conversion ：state
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
/// concurrency ： update complex indicator
/// 在并发场景下安全地更新复合统计值。
/// in concurrency scenario under 。
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
/// ## 概念定义
/// ## Concept Definition
/// ## concept definition
/// 编译器会据此进行代码布局优化，将冷路径移到远离热路径的位置，
/// this layout optimization ，will to position ，
/// 改善指令缓存 (I-cache) 利用率。
/// (I-cache) 。
/// ## Wikipedia 概念对齐
/// ## Wikipedia Concept Alignment
/// ## 对比
/// ## Comparison
/// ## to
/// ## to比
/// ## to
/// | 方式 | 语义 | 稳定性 | 适用场景 |
/// | way | | | scenario |
/// | `cold_path` (1.95+) | 明确标记冷路径 | 标准库稳定 | 错误处理、panic、边界检查失败 |
/// | `cold_path` (1.95+) | explicit mark | standard library | error handling 、panic、edge |
/// | `LLVM __builtin_expect` | 底层编译器提示 | C/FFI | 底层优化 |
/// | `LLVM __builtin_expect` | hint | C/FFI | optimization |
/// | `LLVM __builtin_expect` | 底层编译器hint | C/FFI | 底层optimization |
/// ## 决策树
/// ## tree
/// ## 决策tree
/// ## tree
/// 有极少执行的错误/边界路径？
/// /edge ？
/// ├── 整个函数极少调用？ → `#[cold]`
/// ├── function ？ → `#[cold]`
/// ├── 函数内某分支极少命中？ → cold_path()
/// ├── function inside in ？ → cold_path()
/// ## 反例 / 误用
/// ## /
/// - **不要滥用**：标记非冷路径为冷会导致分支预测失败，降低性能
/// - ****：mark as branch prediction ，performance
/// - **不要替代错误处理**：它只是优化提示，不改变语义
/// - **error handling **：optimization hint ，
pub struct ColdPathExamples;

impl ColdPathExamples {
    /// 基础示例：错误处理路径标记为冷
    /// foundation example ：error handling mark as
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
    /// concurrency scenario ：lock
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
    /// state machine ：state conversion
    /// state machine：非法stateconversion
    /// state machine：illegalstateconversion
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

/// # `thread::scope` and TLS (Thread Local Storage) 析构
/// - `thread::scope` 返回前会**等待所有线程完成**
/// - `thread::scope` before **etc. all thread **
/// - 但 TLS 析构函数**可能**在 scope 返回后才执行（取决于平台实现）
/// - but TLS destructor **may **in scope after （platform ）
/// ## Wikipedia 概念对齐
/// ## Wikipedia Concept Alignment
/// - **Thread-local Storage**: 线程私有存储，线程退出时析构
/// - **Thread-local Storage**: thread ，thread
/// ## 最佳实践
/// ##
/// 1. 在 `thread::scope` 内通过 `join` 或共享引用获取结果
/// 1. in `thread::scope` inside `join` or reference result
/// 3. 使用 `Arc`/`Mutex` 等显式共享机制替代 TLS 跨线程通信
/// 3. `Arc`/`Mutex` etc. mechanism TLS thread communication
pub struct ScopeTlsExamples;

impl ScopeTlsExamples {
    /// 安全示例：通过共享引用而非 TLS 传递结果
    /// example ：reference while TLS result
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

    /// TLS in scope in正确Use
    /// TLS in scope incorrectUse
    /// TLS 仅用于线程内部状态，不跨线程暴露。
    /// TLS thread inside state ，thread expose 。
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
/// 在线程编程中，可用于编译期选择平台相关的线程栈大小默认值。
/// in thread in ，platform thread stack 。
pub struct CfgSelectThreadExamples;

impl CfgSelectThreadExamples {
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

        let p = Packed {
            a: 1,
            b: 0xDEADBEEF,
        };
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
        assert_eq!(
            RealRust195Features::const_block_align_demo(),
            std::mem::align_of::<usize>()
        );
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
