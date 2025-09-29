//! Tokio 异步读写锁（RwLock）详解
//! 
//! 本模块展示了如何使用 `tokio::sync::RwLock` 在异步环境中实现读写锁。
//! 读写锁允许多个读取操作并发执行，但写入操作是独占的，从而提高读多写少场景的性能。
//! 
//! ## 核心概念
//! 
//! ### 读写锁的特性
//! - **读锁（共享锁）**: 多个任务可以同时获取读锁，允许并发读取
//! - **写锁（排他锁）**: 只有一个任务可以获取写锁，写入期间阻止所有其他操作
//! - **互斥性**: 读锁和写锁不能同时存在
//! 
//! ### 异步特性
//! - `read().await`: 异步获取读锁，不会阻塞线程
//! - `write().await`: 异步获取写锁，不会阻塞线程
//! - 锁获取失败时，任务会被挂起而不是阻塞
//! 
//! ## 使用场景
//! 
//! 1. **读多写少**: 频繁读取但偶尔写入的数据
//! 2. **配置数据**: 运行时配置的读取和更新
//! 3. **缓存系统**: 缓存的读取和更新
//! 4. **共享状态**: 应用程序状态的读取和修改
//! 
//! ## 性能优势
//! 
//! - **并发读取**: 多个读操作可以同时进行
//! - **减少竞争**: 相比 Mutex，读操作之间不会相互阻塞
//! - **适合读多写少**: 在读操作远多于写操作时性能更好
//! 
//! ## 注意事项
//! 
//! - 写锁会阻塞所有读锁，要避免长时间持有写锁
//! - 读锁之间是兼容的，可以并发获取
//! - 写锁是排他的，同时只能有一个
//! - 避免读锁升级为写锁，可能导致死锁
//! 
//! ## 使用示例
//! 
//! ```rust
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
/// 
/// 这个函数展示了如何使用 `tokio::sync::RwLock` 来保护共享数据。
/// 多个任务并发读取数据，一个任务负责写入数据，展示读写锁的工作原理。
/// 
/// # 实现原理
/// 
/// ## 读写分离
/// - 读锁：多个任务可以同时获取，允许并发读取
/// - 写锁：独占访问，获取时会阻止所有其他操作
/// - 自动释放：锁在离开作用域时自动释放
/// 
/// ## 异步特性
/// - `read().await` 和 `write().await` 是异步操作
/// - 锁获取失败时，任务被挂起而不是阻塞线程
/// - 锁可用时，任务自动恢复执行
/// 
/// ## 并发控制
/// - 5 个读任务可以并发执行
/// - 1 个写任务独占访问
/// - 读写操作不会相互干扰
/// 
/// # 执行流程
/// 1. 创建共享数据（初始值为 [1, 2, 3]）
/// 2. 启动 5 个并发读任务，获取读锁并读取数据
/// 3. 启动 1 个写任务，获取写锁并修改数据
/// 4. 等待所有任务完成
/// 
/// # 示例
/// ```rust
/// use c06_async::tokio::sync::rwlock_test01;
/// 
/// #[tokio::main]
/// async fn main() {
///     rwlock_test01().await;
///     // 可能的输出:
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
/// - 读操作可以并发执行，提高读取性能
/// - 写操作独占访问，确保数据一致性
/// - 适合读多写少的场景
/// - 相比 Mutex，在读密集场景下性能更好
#[allow(unused)]
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
