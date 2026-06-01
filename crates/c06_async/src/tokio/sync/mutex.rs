//! Tokio 异步互斥锁（Mutex）详解
//! Tokio async mutex （Mutex）
//!
//! 本模块展示了如何在 Tokio 异步运行时中使用 `tokio::sync::Mutex`。
//! This module demonstrates Tokio asyncruntimeuse `tokio::sync::Mutex`
//! 异步 Mutex 是异步编程中保护共享数据的重要工具。
//! async Mutex async in important tool 。
//!
//! ## 核心概念
//! ## Core Concepts
//!
//! ### tokio::sync::Mutex vs std::sync::Mutex
//! - **std::sync::Mutex**: 同步互斥锁，会阻塞线程
//! - **std::sync::Mutex**: synchronous mutex ，thread
//! - **tokio::sync::Mutex**: 异步互斥锁，会挂起任务而不阻塞线程
//! - **tokio::sync::Mutex**: async mutex ，task while thread
//! - **优势**: 异步 Mutex 不会阻塞整个线程，其他任务可以继续执行
//! - **strength **: async Mutex thread ，its task can
//!
//! ### Arc + Mutex 模式
//! ### Arc + Mutex pattern
//! - `Arc`: reference counting ，task ownership
//! - `Mutex`: 提供内部可变性，确保数据访问的安全性
//! - `Mutex`: inside ，
//! - 组合使用：`Arc<Mutex<T>>` 是异步编程中的经典模式
//! - use`Arc<Mutex<T>>` asyncclassic pattern
//!
//! ## 使用场景
//! ## Usage Scenarios
//!
//! 1. **共享计数器**: 多个任务同时修改同一个计数器
//! 1. ****: task
//! 2. **共享缓存**: 多个任务读写同一个缓存
//! 2. ****: task
//! 3. **共享状态**: 维护应用程序的全局状态
//! 3. **sharedstatus**: applicationglobal status
//! 4. **资源池**: 管理有限的资源（如数据库连接）
//! 4. ****: （database ）
//!
//! ## 注意事项
//! ## Notes
//!
//! - 避免长时间持有锁，防止死锁
//! - time lock ，lock
//! - 考虑使用 RwLock 如果读操作比写操作多
//! - RwLock if
//! - 锁的粒度要合适，不要过度锁定
//! - lock ，lock
//!
//! ## 使用示例
//! ## Usage Examples
//!
//! ```no_run
//! use c06_async::tokio::sync::mutex_test01;
//!
//! #[tokio::main]
//! async fn main() {
//!     mutex_test01().await;
//! }
//! ```
use std::sync::Arc;
use tokio::sync::Mutex;

/// 演示异步 Mutex 的基本用法
/// demonstration async Mutex this
///
/// 这个函数展示了如何使用 `tokio::sync::Mutex` 来保护共享数据。
/// function `tokio::sync::Mutex` 。
/// 多个异步任务同时访问和修改同一个计数器，展示异步锁的工作原理。
/// async task and ，async lock 。
///
/// # 实现原理
/// # Implementation Principle
///
/// ## 数据保护
/// ##
/// - 使用 `Arc<Mutex<i32>>` 模式共享数据
/// - use `Arc<Mutex<i32>>` patternshared data
/// - `Arc` 提供多所有权，`Mutex` 提供互斥访问
/// - `Arc` ownership ，`Mutex`
/// - 确保同一时间只有一个任务可以修改数据
/// - timehastaskcan data
///
/// ## 异步特性
/// ## Async Features
/// - `lock().await` 是异步操作，不会阻塞线程
/// - `lock().await` async ，thread
/// - 当锁被其他任务持有时，当前任务会被挂起
/// - when lock is its task ，when before task is
/// - 锁释放后，挂起的任务会被自动唤醒
/// - lock after ，task is
///
/// ## 任务并发
/// ## task concurrency
/// - 10 个并发任务同时尝试增加计数器
/// - 10 concurrency task
/// - 每个任务都会获取锁，增加计数器，然后释放锁
/// - task lock ，，then lock
/// - 最终计数器应该等于任务数量（10）
/// - ultimately should etc. task quantity （10）
///
/// # 执行流程
/// # Execution Flow
/// 1. 创建共享的计数器（初始值为 0）
/// 1. （as 0）
/// 2. 启动 10 个并发任务，每个任务都会增加计数器
/// 2. 10 concurrency task ，task
/// 3. 等待所有任务完成
/// 3. etc. all task
/// 4. 验证最终结果
/// 4. verifyfinal result
///
/// # 示例
/// # Examples
/// ```no_run
/// use c06_async::tokio::sync::mutex_test01;
///
/// #[tokio::main]
/// async fn main() {
///     mutex_test01().await;
///     // 输出: Result: 10
/// }
/// ```
///
/// # 性能特点
/// # performance point
/// - 异步锁不会阻塞线程，提高并发性能
/// - asyncthreadhighconcurrent performance
/// - 适合高并发场景下的数据保护
/// - concurrency scenario under
/// - 相比同步锁，可以处理更多的并发任务
/// - synchronous lock ，can concurrency task
///
/// 测试异步 Mutex
/// Test async Mutex
pub async fn mutex_test01() {
    // 创建一个 Arc 包裹的 Mutex，内部数据为 0
    // Arc 允许在多个任务之间共享所有权
    // Mutex 提供互斥访问，确保数据安全
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    // 启动 10 个并发任务，每个任务都会增加计数器
    for _ in 0..10 {
        // 克隆 Arc 引用，以便在多个任务中共享
        let counter_clone = Arc::clone(&counter);

        // 使用 tokio::spawn 启动异步任务
        let handle = tokio::spawn(async move {
            // 获取锁，这是一个异步操作
            // 如果锁被其他任务持有，当前任务会被挂起
            let mut num = counter_clone.lock().await;

            // 修改共享数据（增加计数器）
            *num += 1;

            // 锁在 num 离开作用域时自动释放
        });

        handles.push(handle);
    }

    // 等待所有任务完成
    // 这确保了所有任务都完成了对计数器的修改
    for handle in handles {
        handle.await.expect("等待任务完成不应失败");
    }

    // 获取最终结果并打印
    // 由于所有任务都已完成，这里获取锁应该立即成功
    println!("Result: {}", *counter.lock().await); // 输出: Result: 10
}
