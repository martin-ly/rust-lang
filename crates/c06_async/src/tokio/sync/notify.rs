//! Tokio 异步通知机制（Notify）详解
//! Tokio async mechanism （Notify）
//!
//! 本模块展示了如何使用 `tokio::sync::Notify` 在异步任务之间进行协调和同步。
//! This module demonstrates use `tokio::sync::Notify` asynctasksynchronous
//! Notify 是一种轻量级的通知机制，非常适合实现条件变量和任务协调。
//! Notify mechanism ，condition variable and task 。
//!
//! ## 核心概念
//! ## Core Concepts
//!
//! ### Notify 的工作原理
//! ### Notify
//! - **等待通知**: 任务调用 `notified().await` 进入等待状态
//! - ****: task `notified().await` status
//! - **发送通知**: 其他任务调用 `notify_one()` 或 `notify_waiters()` 发送通知
//! - ****: its task `notify_one()` or `notify_waiters()`
//! - **任务唤醒**: 等待的任务收到通知后继续执行
//! - **task **: etc. task to after
//!
//! ### 主要方法
//! ### method
//! - `notified()`: 返回一个 Future，等待通知
//! - `notified()`: Future，etc.
//! - `notify_one()`: 唤醒一个等待的任务
//! - `notify_one()`: etc. task
//! - `notify_waiters()`: 唤醒所有等待的任务
//! - `notify_waiters()`: all etc. task
//!
//! ## 使用场景
//! ## Usage Scenarios
//!
//! 1. **条件变量**: 等待某个条件满足
//! 1. **condition variable **: etc. condition
//! 2. **任务协调**: 在任务之间传递信号
//! 2. **task **: in task 's
//! 3. **生产者-消费者**: 通知消费者有新数据
//! 4. **启动同步**: 等待所有组件准备就绪
//! 4. **synchronous **: etc. all
//! 5. **优雅关闭**: 通知任务停止运行
//! 5. ****: task Run
//!
//! ## 与其他同步原语的比较
//! ## rather than synchronous
//!
//! - **vs Mutex**: Notify 不保护数据，只用于信号传递
//! - **vs Mutex**: Notify ，
//! - **vs Channel**: Notify 更轻量，不需要传递数据
//! - **vs Channel**: Notify need data
//! - **vs Barrier**: Notify 支持一对一和一对多通知
//! - **vs Barrier**: Notify to and to
//!
//! ## 注意事项
//! ## Notes
//!
//! - Notify 不传递数据，只传递信号
//! - Notify ，
//! - 如果通知在等待之前发送，通知会丢失
//! - if in etc. 's before ，
//! - 适合实现简单的等待-通知模式
//! - implementationsingle- pattern
//!
//! ## 使用示例
//! ## Usage Examples
//!
//! ```no_run
//! use c06_async::tokio::sync::notify_test01;
//!
//! #[tokio::main]
//! async fn main() {
//!     notify_test01().await;
//! }
//! ```
use std::sync::Arc;
use tokio::sync::Notify;

/// 演示 Notify 的基本用法
/// demonstration Notify this
///
/// 这个函数展示了如何使用 `tokio::sync::Notify` 来实现任务间的通知机制。
/// function `tokio::sync::Notify` task mechanism 。
/// 一个任务等待通知，另一个任务在完成工作后发送通知。
/// task etc. ，task in after 。
///
/// # 实现原理
/// # Implementation Principle
///
/// ## 通知机制
/// ## mechanism
/// - 使用 `Arc<Notify>` 在任务间共享通知器
/// - `Arc<Notify>` in task
/// - 等待任务调用 `notified().await` 进入等待状态
/// - task `notified().await` status
/// - 通知任务调用 `notify_one()` 唤醒等待的任务
/// - task `notify_one()` etc. task
///
/// ## 异步特性
/// ## Async Features
/// - `notified().await` 是异步操作，不会阻塞线程
/// - `notified().await` async ，thread
/// - 等待期间，其他任务可以继续执行
/// - etc. ，its task can
/// - 收到通知后，任务自动恢复执行
/// - to after ，task
///
/// ## 任务协调
/// ## task
/// - 两个任务并发执行：等待任务和通知任务
/// - task concurrency ：etc. task and task
/// - 通知任务完成工作后发送通知
/// - task after
/// - 等待任务收到通知后继续执行
/// - etc. task to after
///
/// # 执行流程
/// # Execution Flow
/// 1. 创建 Notify 实例并包装在 Arc 中
/// 1. Notify and in Arc in
/// 2. 启动等待任务，调用 `notified().await`
/// 2. etc. task ， `notified().await`
/// 3. 启动通知任务，模拟工作后调用 `notify_one()`
/// 3. task ，after `notify_one()`
/// 4. 等待两个任务都完成
/// 4. etc. task
///
/// # 示例
/// # Examples
/// ```no_run
/// use c06_async::tokio::sync::notify_test01;
///
/// #[tokio::main]
/// async fn main() {
///     notify_test01().await;
///     // 输出:
///     // :
///     // Waiting for notification...
///     // Sending notification...
///     // Received notification!
/// }
/// ```
///
/// # 应用场景
/// # application scenario
/// - 等待外部事件（如文件变化、网络连接）
/// - etc. outside （、network ）
/// - 实现生产者-消费者模式
/// - implementation- pattern
/// - 任务启动同步
/// - task synchronous
/// - 优雅关闭机制
/// - excellent mechanism
///
/// 测试 Notify
/// Test Notify
pub async fn notify_test01() {
    // 创建一个 Notify 实例并包装在 Arc 中
    // Arc 允许在多个任务之间共享 Notify
    let notify = Arc::new(Notify::new());

    // 克隆 Notify 的 Arc 引用，以便在等待任务中使用
    let notify_clone = Arc::clone(&notify);

    // 启动等待任务：等待通知
    let waiting_task = tokio::spawn(async move {
        println!("Waiting for notification...");

        // 等待通知，这是一个异步操作
        // 如果通知还没发送，当前任务会被挂起
        // 如果通知已经发送，会立即返回
        notify_clone.notified().await;

        println!("Received notification!");
    });

    // 启动通知任务：完成工作后发送通知
    let notifying_task = tokio::spawn(async move {
        // 模拟一些异步工作（如网络请求、文件处理等）
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

        println!("Sending notification...");

        // 发送通知，唤醒一个等待的任务
        // 如果有多个任务在等待，只唤醒其中一个
        notify.notify_one();
    });

    // 等待两个任务都完成
    // tokio::join! 会并发等待多个 Future
    let _ = tokio::join!(waiting_task, notifying_task);
}
