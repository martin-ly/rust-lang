//! Future 状态机和调度机制详解
//! 
//! 在 Rust 中，Future 的状态机和调度机制是理解异步编程的关键。
//! 本模块提供了对这两个概念的全面示例和解释。
//! 
//! ## Future 状态机模型
//! 
//! Future 的状态机模型允许异步操作在不同的状态之间转换：
//! - **Pending**: 表示计算尚未完成，可能需要等待某些条件
//! - **Ready**: 表示计算已完成，并且可以返回结果
//! 
//! ## 调度机制
//! 
//! 调度机制负责管理 Future 的执行：
//! - Rust 的异步运行时（如 Tokio 或 async-std）会在适当的时候调用 `poll` 方法
//! - 检查 Future 的状态并决定何时继续执行
//! - 使用 `Waker` 机制来通知运行时何时重新调度 Future
//! 
//! ## 核心概念
//! 
//! ### 1. Future Trait
//! ```rust
//! pub trait Future {
//!     type Output;
//!     fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
//! }
//! ```
//! 
//! ### 2. Poll 状态
//! ```rust
//! pub enum Poll<T> {
//!     Ready(T),
//!     Pending,
//! }
//! ```
//! 
//! ### 3. Context 和 Waker
//! - `Context` 提供对 `Waker` 的访问
//! - `Waker` 用于通知运行时重新调度 Future
//! 
//! ## 使用示例
//! 
//! ```rust
//! use c06_async::futures::*;
//! 
//! #[tokio::main]
//! async fn main() {
//!     // 演示手写 Future
//!     let result = demo_manual_future().await;
//!     println!("手动 Future 结果: {}", result);
//!     
//!     // 演示 Future 组合子
//!     let result = demo_future_combinators().await;
//!     println!("组合子结果: {}", result);
//! }
//! ```

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

/// 自定义 Future 实现示例
/// 
/// 这个结构体演示了如何手动实现 Future trait。
/// 它模拟了一个异步操作，可以处于两种状态：等待中或已完成。
/// 
/// # 字段说明
/// - `delay`: 模拟的延迟时间（实际实现中通常由运行时计时器处理）
/// - `state`: 当前状态，用于状态机转换
/// 
/// # 示例
/// ```rust
/// use c06_async::futures::demo_manual_future;
/// 
/// #[tokio::main]
/// async fn main() {
///     let result = demo_manual_future().await;
///     println!("Future 完成，结果: {}", result);
/// }
/// ```
#[allow(unused)]
pub struct MyFuture {
    /// 模拟的延迟时间
    pub delay: Duration,
    /// 当前状态
    pub state: State,
}

/// Future 的状态枚举
/// 
/// 这个枚举定义了 Future 可能处于的状态：
/// - `Pending`: 等待状态，表示操作尚未完成
/// - `Ready(i32)`: 就绪状态，包含操作结果
/// 
/// # 状态转换
/// 1. 初始状态通常是 `Pending`
/// 2. 当异步操作完成时，状态转换为 `Ready(result)`
/// 3. 一旦状态变为 `Ready`，Future 就不会再被轮询
#[allow(unused)]
pub enum State {
    /// 等待状态：操作尚未完成
    Pending,
    /// 就绪状态：操作完成，包含结果值
    Ready(i32),
}

/// 为 MyFuture 实现 Future trait
/// 
/// 这是 Future trait 的核心实现，展示了异步状态机的轮询机制。
/// 
/// # 实现细节
/// 
/// ## poll 方法的作用
/// - 运行时定期调用此方法来检查 Future 的状态
/// - 如果操作已完成，返回 `Poll::Ready(result)`
/// - 如果操作仍在进行，返回 `Poll::Pending`
/// 
/// ## 状态转换逻辑
/// 1. **Pending 状态**: 模拟异步操作，立即将状态转换为 Ready
/// 2. **Ready 状态**: 返回计算结果
/// 
/// ## Waker 机制
/// - 使用 `cx.waker().wake_by_ref()` 通知运行时重新调度
/// - 这确保了 Future 会在适当的时机被重新轮询
/// 
/// # 注意事项
/// - 这是一个简化的示例，实际实现中通常使用计时器或其他异步原语
/// - 真实的异步操作应该等待外部事件（如 I/O 完成、计时器到期等）
impl Future for MyFuture {
    /// Future 完成时返回的类型
    type Output = i32;

    /// 轮询 Future 的状态
    /// 
    /// # 参数
    /// - `self`: 被固定的 Future 引用
    /// - `cx`: 执行上下文，包含 Waker 等信息
    /// 
    /// # 返回值
    /// - `Poll::Ready(value)`: 操作完成，返回结果
    /// - `Poll::Pending`: 操作仍在进行，稍后重新轮询
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();

        match this.state {
            State::Pending => {
                // 模拟异步操作的处理
                // 在实际实现中，这里会检查外部条件或等待异步事件
                
                // 通知调度器：这个 Future 需要重新轮询
                // 这确保了即使状态立即改变，运行时也会正确处理
                cx.waker().wake_by_ref();
                
                // 模拟操作完成，更新状态为 Ready
                // 注意：这是简化的示例，实际中状态转换通常基于外部事件
                this.state = State::Ready(42);
                
                // 返回 Pending，让运行时知道需要重新轮询
                Poll::Pending
            }
            State::Ready(result) => {
                // 操作已完成，返回结果
                // 一旦返回 Ready，这个 Future 就不会再被轮询
                Poll::Ready(result)
            }
        }
    }
}

/// 演示手写 Future 的基本用法
/// 
/// 这个函数展示了如何使用自定义的 Future 实现。
/// 它创建了一个 MyFuture 实例并等待其完成。
/// 
/// # 返回值
/// 返回 Future 完成时的结果值（在这个例子中是 42）
/// 
/// # 示例
/// ```rust
/// use c06_async::futures::demo_manual_future;
/// 
/// #[tokio::main]
/// async fn main() {
///     let result = demo_manual_future().await;
///     println!("Future 完成，结果: {}", result);
/// }
/// ```
/// 
/// # 注意事项
/// - 这是一个教学示例，实际应用中很少需要手写 Future
/// - 大多数异步操作都使用标准库或第三方库提供的 Future 实现
pub async fn demo_manual_future() -> i32 {
    // 创建自定义 Future 实例
    // 注意：这里只是演示状态切换；真实延时应交给运行时计时器
    MyFuture {
        delay: Duration::from_millis(1),
        state: State::Pending,
    }
    .await
}

/// 演示 Future 组合子的高级用法
/// 
/// 这个函数展示了如何使用 futures 库提供的组合子来组合和操作多个 Future。
/// 包括：
/// - `map`: 转换 Future 的结果
/// - `select`: 同时等待多个 Future，返回最先完成的那个
/// 
/// # 组合子说明
/// 
/// ## map
/// - 将 Future 的结果通过函数进行转换
/// - 类似于 `Option::map` 或 `Result::map`
/// 
/// ## select
/// - 同时执行多个 Future，返回最先完成的结果
/// - 其他未完成的 Future 会被取消
/// - 返回 `Either<A, B>` 类型，表示哪个 Future 先完成
/// 
/// # 返回值
/// 返回组合操作的最终结果
/// 
/// # 示例
/// ```rust
/// use c06_async::futures::demo_future_combinators;
/// 
/// #[tokio::main]
/// async fn main() {
///     let result = demo_future_combinators().await;
///     println!("组合子操作结果: {}", result);
/// }
/// ```
pub async fn demo_future_combinators() -> i32 {
    use futures::{FutureExt, future};
    use tokio::time::sleep;

    // 演示 map 组合子：链式转换 Future 的结果
    let f1 = async { 21 };
    let result = f1.map(|x| x * 2).await; // 21 * 2 = 42

    // 演示 select 组合子：同时等待两个 Future，返回最先完成的
    let a = async {
        sleep(Duration::from_millis(10)).await; // 较慢的任务
        1
    };
    let b = async {
        sleep(Duration::from_millis(5)).await; // 较快的任务
        2
    };
    
    // 固定 Future 以便进行 select 操作
    // pin_mut! 宏确保 Future 在内存中的位置不变
    futures::pin_mut!(a);
    futures::pin_mut!(b);
    
    // 执行 select 操作，返回最先完成的 Future 及其结果
    let first_done = future::select(a, b).await;
    
    // 处理 select 的结果
    let faster_value = match first_done {
        future::Either::Left((va, _)) => {
            // Future A 先完成，va 是 A 的结果，_ 是未完成的 B
            va
        }
        future::Either::Right((vb, _)) => {
            // Future B 先完成，vb 是 B 的结果，_ 是未完成的 A
            vb
        }
    };

    // 返回组合结果：42 + 2 = 44（因为 B 更快完成）
    result + faster_value
}
