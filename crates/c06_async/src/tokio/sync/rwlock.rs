//! Tokio 异步读写锁（RwLock）详解
//! Tokio async rwlock （RwLock）
//!
//! 本模块展示了如何使用 `tokio::sync::RwLock` 在异步环境中实现读写锁。
//! This module demonstrates use `tokio::sync::RwLock` asyncimplementation
//! 读写锁允许多个读取操作并发执行，但写入操作是独占的，从而提高读多写少场景的性能。
//! rwlock concurrency ，but ，thereby scenario performance 。
//!
//! ## 核心概念
//! ## Core Concepts
//!
//! ### 读写锁的特性
//! ### rwlock feature
//! - **读锁（共享锁）**: 多个任务可以同时获取读锁，允许并发读取
//! - **lock （lock ）**: task can lock ，concurrency
//! - **写锁（排他锁）**: 只有一个任务可以获取写锁，写入期间阻止所有其他操作
//! - ****: hastaskcangethas operation
//! - **互斥性**: 读锁和写锁不能同时存在
//! - ****: lock and lock cannot in
//!
//! ### 异步特性
//! ### async feature
//! - `read().await`: 异步获取读锁，不会阻塞线程
//! - `read().await`: async lock ，thread
//! - `write().await`: 异步获取写锁，不会阻塞线程
//! - `write().await`: async lock ，thread
//! - 锁获取失败时，任务会被挂起而不是阻塞
//! - lock ，task is while
//!
//! ## 使用场景
//! ## Usage Scenarios
//!
//! 1. **读多写少**: 频繁读取但偶尔写入的数据
//! 1. **multiplefew**: data
//! 2. **配置数据**: 运行时配置的读取和更新
//! 2. ****: runtime and
//! 3. **缓存系统**: 缓存的读取和更新
//! 3. **system **: and
//! 4. **共享状态**: 应用程序状态的读取和修改
//! 4. **state **: application program state and
//!
//! ## 性能优势
//! ## performance strength
//!
//! - **并发读取**: 多个读操作可以同时进行
//! - **concurrency **: can
//! - **减少竞争**: 相比 Mutex，读操作之间不会相互阻塞
//! - ****: Mutex，'s
//! - **适合读多写少**: 在读操作远多于写操作时性能更好
//! - ****: in performance
//!
//! ## 注意事项
//! ## Notes
//!
//! - 写锁会阻塞所有读锁，要避免长时间持有写锁
//! - lock all lock ，time lock
//! - 读锁之间是兼容的，可以并发获取
//! - lock 's ，can concurrency
//! - 写锁是排他的，同时只能有一个
//! - lock ，
//! - 避免读锁升级为写锁，可能导致死锁
//! - lock as lock ，may lock
//!
//! ## 使用示例
//! ## Usage Examples
//!
//! ```no_run
//! use c06_async::tokio::sync::rwlock_test01;
//!
//! #[tokio::main]
//! async fn main() {
//!     rwlock_test01().await;
//! }
//! ```
use std::sync::Arc;
use tokio::sync::RwLock;

/// 演示异步读写锁的基本用法
/// demonstration async rwlock this
///
/// 这个函数展示了如何使用 `tokio::sync::RwLock` 来保护共享数据。
/// function `tokio::sync::RwLock` 。
/// 多个任务并发读取数据，一个任务负责写入数据，展示读写锁的工作原理。
/// task concurrency ，task ，rwlock 。
///
/// # 实现原理
/// # Implementation Principle
///
/// ## 读写分离
/// ## read-write splitting
/// - 读锁：多个任务可以同时获取，允许并发读取
/// - lock ：task can ，concurrency
/// - 写锁：独占访问，获取时会阻止所有其他操作
/// - exclusivegethas operation
/// - 自动释放：锁在离开作用域时自动释放
/// - ：lock in role domain
///
/// ## 异步特性
/// ## Async Features
/// - `read().await` 和 `write().await` 是异步操作
/// - `read().await` `write().await` async operation
/// - lock ，task is while thread
/// - 锁可用时，任务自动恢复执行
/// - lock ，task
///
/// ## 并发控制
/// ## concurrent control
/// - 5 个读任务可以并发执行
/// - 5 task can concurrency
/// - 1 个写任务独占访问
/// - 1 task
/// - 读写操作不会相互干扰
/// -
///
/// # 执行流程
/// # Execution Flow
/// 1. 创建共享数据（初始值为 [1, 2, 3]）
/// 1. （as [1, 2, 3]）
/// 2. 启动 5 个并发读任务，获取读锁并读取数据
/// 2. 5 concurrenttaskget data
/// 3. 启动 1 个写任务，获取写锁并修改数据
/// 3. 1 taskget data
/// 4. 等待所有任务完成
/// 4. etc. all task
///
/// # 示例
/// # Examples
/// ```no_run
/// use c06_async::tokio::sync::rwlock_test01;
///
/// #[tokio::main]
/// async fn main() {
///     rwlock_test01().await;
///     // 可能的输出:
///     // may :
///     // Read data: [1, 2, 3]
///     // Read data: [1, 2, 3]
///     // Read data: [1, 2, 3]
///     // Data modified
///     // Read data: [1, 2, 3]
///     // Read data: [1, 2, 3]
/// }
/// ```
///
/// # 性能特点
/// # performance point
/// - 读操作可以并发执行，提高读取性能
/// - operationcanconcurrentexecutionhigh performance
/// - 写操作独占访问，确保数据一致性
/// - ，consistency
/// - 适合读多写少的场景
/// - scenario
/// - 相比 Mutex，在读密集场景下性能更好
/// - Mutex，in scenario under performance
///
/// 测试 RwLock
/// Test RwLock
pub async fn rwlock_test01() {
    // 创建一个 Arc 包裹的 RwLock，内部数据为一个 Vec
    // Arc 提供多所有权，RwLock 提供读写锁功能
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 启动多个异步任务进行并发读取
    let mut read_handles = vec![];
    for _ in 0..5 {
        let data_clone = Arc::clone(&data);
        let handle = tokio::spawn(async move {
            // 获取读锁，这是一个异步操作
            // 多个读锁可以同时存在，不会相互阻塞
            let read_guard = data_clone.read().await;

            // 读取共享数据
            println!("Read data: {:?}", *read_guard);

            // 读锁在 read_guard 离开作用域时自动释放
        });
        read_handles.push(handle);
    }

    // 启动一个异步任务进行写入
    let data_clone = Arc::clone(&data);
    let write_handle = tokio::spawn(async move {
        // 获取写锁，这是一个异步操作
        // 写锁是独占的，获取时会阻止所有读锁和其他写锁
        let mut write_guard = data_clone.write().await;

        // 修改共享数据
        write_guard.push(4);
        println!("Data modified");

        // 写锁在 write_guard 离开作用域时自动释放
    });

    // 等待所有任务完成
    let _ = tokio::join!(
        write_handle,
        // 等待所有读取任务完成
        futures::future::join_all(read_handles)
    );
}
