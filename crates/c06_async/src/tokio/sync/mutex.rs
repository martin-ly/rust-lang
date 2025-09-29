//! Tokio 异步互斥锁（Mutex）详解
//! 
//! 本模块展示了如何在 Tokio 异步运行时中使用 `tokio::sync::Mutex`。
//! 异步 Mutex 是异步编程中保护共享数据的重要工具。
//! 
//! ## 核心概念
//! 
//! ### tokio::sync::Mutex vs std::sync::Mutex
//! - **std::sync::Mutex**: 同步互斥锁，会阻塞线程
//! - **tokio::sync::Mutex**: 异步互斥锁，会挂起任务而不阻塞线程
//! - **优势**: 异步 Mutex 不会阻塞整个线程，其他任务可以继续执行
//! 
//! ### Arc + Mutex 模式
//! - `Arc`: 原子引用计数，允许多个任务共享所有权
//! - `Mutex`: 提供内部可变性，确保数据访问的安全性
//! - 组合使用：`Arc<Mutex<T>>` 是异步编程中的经典模式
//! 
//! ## 使用场景
//! 
//! 1. **共享计数器**: 多个任务同时修改同一个计数器
//! 2. **共享缓存**: 多个任务读写同一个缓存
//! 3. **共享状态**: 维护应用程序的全局状态
//! 4. **资源池**: 管理有限的资源（如数据库连接）
//! 
//! ## 注意事项
//! 
//! - 避免长时间持有锁，防止死锁
//! - 考虑使用 RwLock 如果读操作比写操作多
//! - 锁的粒度要合适，不要过度锁定
//! 
//! ## 使用示例
//! 
//! ```rust
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
/// 
/// 这个函数展示了如何使用 `tokio::sync::Mutex` 来保护共享数据。
/// 多个异步任务同时访问和修改同一个计数器，展示异步锁的工作原理。
/// 
/// # 实现原理
/// 
/// ## 数据保护
/// - 使用 `Arc<Mutex<i32>>` 模式共享数据
/// - `Arc` 提供多所有权，`Mutex` 提供互斥访问
/// - 确保同一时间只有一个任务可以修改数据
/// 
/// ## 异步特性
/// - `lock().await` 是异步操作，不会阻塞线程
/// - 当锁被其他任务持有时，当前任务会被挂起
/// - 锁释放后，挂起的任务会被自动唤醒
/// 
/// ## 任务并发
/// - 10 个并发任务同时尝试增加计数器
/// - 每个任务都会获取锁，增加计数器，然后释放锁
/// - 最终计数器应该等于任务数量（10）
/// 
/// # 执行流程
/// 1. 创建共享的计数器（初始值为 0）
/// 2. 启动 10 个并发任务，每个任务都会增加计数器
/// 3. 等待所有任务完成
/// 4. 验证最终结果
/// 
/// # 示例
/// ```rust
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
/// - 异步锁不会阻塞线程，提高并发性能
/// - 适合高并发场景下的数据保护
/// - 相比同步锁，可以处理更多的并发任务
#[allow(unused)]
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
        handle.await.unwrap();
    }

    // 获取最终结果并打印
    // 由于所有任务都已完成，这里获取锁应该立即成功
    println!("Result: {}", *counter.lock().await); // 输出: Result: 10
}
