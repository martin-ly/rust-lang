//! 异步流（Stream）处理详解
//! async stream （Stream）
//!
//! 本模块展示了 Rust 中异步流（Stream）的概念和用法。
//! This module demonstrates Rust in async stream （Stream）concept and 。
//! Stream 是异步编程中处理连续数据的重要抽象，类似于同步编程中的迭代器。
//! Stream async in important ，similar to synchronous in 。
//!
//! ## 核心概念
//! ## core concept
//!
//! ### Stream Trait
//! ```ignore
//! use std::pin::Pin;
//! use std::task::{Context, Poll};
//!
//! pub trait Stream {
//!     type Item;
//!     fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
//! }
//! ```
//!
//! ### Stream vs Iterator
//! - **Iterator**: 同步的，阻塞式获取下一个元素
//! - **Iterator**: synchronous ，under element
//! - **Stream**: 异步的，非阻塞式获取下一个元素
//! - **Stream**: async ，under element
//! - **应用场景**: Stream 适合处理网络数据流、文件流、事件流等
//! - **application scenario **: Stream network stream 、stream 、stream etc.
//!
//! ## 主要特性
//! ## main feature
//!
//! ### 1. 自定义 Stream 实现
//! ### 1. definition Stream
//! - 展示如何实现 Stream trait
//! - Stream trait
//! - 基于计时器的时间序列流
//! - time sequence stream
//! - 状态管理和生命周期控制
//! - state and lifetime
//!
//! ### 2. Stream 组合子
//! ### 2. Stream combination
//! - `map`: 转换流中的每个元素
//! - `map`: conversion stream in element
//! - `filter`: 过滤流中的元素
//! - `filter`: stream in element
//! - `take`: 限制流中元素的数量
//! - `take`: stream in element quantity
//! - `collect`: 收集所有元素到集合中
//! - `collect`: all element to set in
//!
//! ### 3. 并发处理
//! ### 3. concurrency
//! - `buffer_unordered`: 并发处理流中的元素
//! - `buffer_unordered`: concurrency stream in element
//! - 限制并发数量，避免资源耗尽
//! - concurrency quantity ，
//!
//! ## 使用示例
//! ## example
//!
//! ```no_run
//! use c06_async::streams::*;
//! use std::time::Duration;
//!
//! #[tokio::main]
//! async fn main() {
//!     // 演示基本组合子
//!     // demonstration this combination
//!     let result = demo_basic_combinators(10).await;
//!     println!("组合子结果: {:?}", result);
//!     
//!     // 演示时间流
//!     // demonstration time stream
//!     let ticks = demo_tick_stream(5, Duration::from_millis(100)).await;
//!     println!("时间流结果: {:?}", ticks);
//! }
//! ```
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

use futures::{Stream, StreamExt, stream};
use tokio::time::{Interval, interval};

/// 基于计时器的自定义 Stream 实现
/// definition Stream
///
/// 这个结构体演示了如何实现 Stream trait 来创建一个自定义的异步流。
/// struct demonstration Stream trait definition async stream 。
/// 它基于 `tokio::time::Interval` 来生成定期的计时事件。
/// `tokio::time::Interval` 。
///
/// # 字段说明
/// # field explain
/// - `interval`: Tokio 的计时器间隔，用于定期触发
/// - `interval`: Tokio ，
/// - `remaining`: 剩余要产生的计时次数
/// - `remaining`:
/// - `counter`: 当前计时器的计数值
/// - `counter`: when before
///
/// # 工作原理
/// #
/// 1. 创建时设置总的计时次数和间隔时间
/// 1. and time
/// 2. 每次 `poll_next` 被调用时，等待下一次计时器触发
/// 2. `poll_next` is ，etc. under
/// 3. 计时器触发时，返回当前的计数值
/// 3. ，when before
/// 4. 当达到设定的次数时，流结束（返回 `None`）
/// 4. when to ，stream （ `None`）
///
/// # 示例
/// # example
/// ```no_run
/// use c06_async::streams::TickStream;
/// use futures::StreamExt;
/// use std::time::Duration;
///
/// #[tokio::main]
/// async fn main() {
///     let mut stream = TickStream::new(5, Duration::from_millis(100));
///     while let Some(tick) = stream.next().await {
///         println!("计时: {}", tick);
///     }
/// }
/// ```
pub struct TickStream {
    /// Tokio 计时器间隔
    /// Tokio
    interval: Interval,
    /// 剩余要产生的计时次数
    remaining: u64,
    /// 当前计数值
    /// when before
    counter: u64,
}

impl TickStream {
    /// 创建一个新的计时流
    /// stream
    ///
    /// # 参数
    /// # parameter
    /// - `ticks`: 总共要产生的计时次数
    /// - `ticks`:
    /// - `period`: 每次计时的间隔时间
    /// - `period`: time
    ///
    /// # 返回值
    /// # return value
    /// 返回一个新的 `TickStream` 实例
    /// `TickStream`
    ///
    /// # 示例
    /// # example
    /// ```no_run
    /// use c06_async::streams::TickStream;
    /// use std::time::Duration;
    ///
    /// let stream = TickStream::new(10, Duration::from_millis(500));
    /// ```
    pub fn new(ticks: u64, period: Duration) -> Self {
        Self {
            interval: interval(period),
            remaining: ticks,
            counter: 0,
        }
    }
}

/// 为 TickStream 实现 Stream trait
///
/// 这是 Stream trait 的核心实现，展示了异步流的轮询机制。
/// Stream trait core ，async stream mechanism 。
///
/// # 实现细节
/// #
///
/// ## poll_next 方法的作用
/// ## poll_next method role
/// - 运行时定期调用此方法来获取流中的下一个元素
/// - runtime this method stream in under element
/// - 如果流已结束，返回 `Poll::Ready(None)`
/// - if stream ， `Poll::Ready(None)`
/// - 如果有新元素，返回 `Poll::Ready(Some(item))`
/// - 如果暂时没有元素但流未结束，返回 `Poll::Pending`
/// - if temporary element but stream ， `Poll::Pending`
///
/// ## 状态管理
/// ## state
/// 1. **检查剩余次数**: 如果 `remaining == 0`，流结束
/// 1. ****: if `remaining == 0`，stream
/// 2. **等待计时器**: 使用 `interval.poll_tick()` 等待下一次触发
/// 2. **etc. **: `interval.poll_tick()` etc. under
/// 3. **更新状态**: 计时器触发时，更新计数器和剩余次数
/// 3. **state **: ，and
/// 4. **返回元素**: 返回当前的计数值
/// 4. **element **: when before
///
/// # 生命周期
/// # lifetime
/// - 创建时设置总次数和间隔
/// - and
/// - 每次轮询等待计时器触发
/// - etc.
/// - 达到设定次数后自动结束
/// - to after
impl Stream for TickStream {
    /// 流中元素的类型
    /// stream in element type
    type Item = u64;

    /// 轮询流中的下一个元素
    /// stream in under element
    ///
    /// # 参数
    /// # parameter
    /// - `self`: 被固定的 Stream 引用
    /// - `self`: is Stream reference
    /// - `cx`: 执行上下文，包含 Waker 等信息
    /// - `cx`: on under ， Waker etc.
    ///
    /// # 返回值
    /// # return value
    /// - `Poll::Ready(Some(item))`: 有新的元素可用
    /// - `Poll::Ready(None)`: 流已结束，没有更多元素
    /// - `Poll::Ready(None)`: stream ，element
    /// - `Poll::Pending`: 暂时没有元素，稍后重新轮询
    /// - `Poll::Pending`: temporary element ，after
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();

        // 检查是否还有剩余的计时次数
        if this.remaining == 0 {
            // 流已结束，返回 None
            return Poll::Ready(None);
        }

        // 等待计时器的下一次触发
        match Pin::new(&mut this.interval).poll_tick(cx) {
            Poll::Pending => {
                // 计时器还没到时间，返回 Pending
                Poll::Pending
            }
            Poll::Ready(_) => {
                // 计时器触发了，更新状态并返回计数值
                this.remaining -= 1; // 减少剩余次数
                this.counter += 1; // 增加计数器

                // 返回当前的计数值
                Poll::Ready(Some(this.counter))
            }
        }
    }
}

/// 基于迭代器快速构造一个 Stream
/// fast Stream
///
/// 这个函数展示了如何从同步迭代器创建异步流。
/// function from synchronous async stream 。
/// `stream::iter` 是 futures 库提供的工具，可以将任何迭代器转换为 Stream。
/// `stream::iter` futures library tool ，can will conversion as Stream。
///
/// # 参数
/// # parameter
/// - `n`: 要生成的数字范围的上限（包含）
/// - `n`: scope on （）
///
/// # 返回值
/// # return value
/// 返回一个产生 1 到 n 数字的 Stream
/// 1 to n Stream
///
/// # 示例
/// # example
/// ```rust
/// use c06_async::streams::make_iter_stream;
/// use futures::StreamExt;
///
/// # async fn example() {
/// let mut stream = make_iter_stream(5);
/// // 会产生: 1, 2, 3, 4, 5
/// // : 1, 2, 3, 4, 5
/// while let Some(n) = stream.next().await {
///     println!("{}", n);
/// }
/// # }
/// ```
pub fn make_iter_stream(n: u32) -> impl Stream<Item = u32> {
    stream::iter(1..=n)
}

/// 演示 Stream 组合子的链式操作
/// demonstration Stream combination
///
/// 这个函数展示了如何使用 Stream 的组合子来对数据流进行变换和过滤。
/// function Stream combination to stream transformation and 。
/// 组合子可以链式调用，形成数据处理的流水线。
/// combination can ，pipeline 。
///
/// # 组合子说明
/// # combination explain
///
/// ## map
/// - 对流中的每个元素应用转换函数
/// - to stream in element application conversion function
/// - 类似于 `Iterator::map`
///
/// ## filter
/// - 根据条件过滤流中的元素
/// - according to condition stream in element
/// - 只保留满足条件的元素
/// - condition element
///
/// ## take
/// - 限制流中元素的数量
/// - stream in element quantity
/// - 类似于 `Iterator::take`
///
/// ## collect
/// - 将流中的所有元素收集到集合中
/// - will stream in all element to set in
/// - 类似于 `Iterator::collect`
///
/// # 参数
/// # parameter
/// - `n`: 输入流的元素数量
/// - `n`: stream element quantity
///
/// # 返回值
/// # return value
/// 经过变换和过滤后的结果向量
/// transformation and after result
///
/// # 处理流程
/// # process
/// 1. 生成 1 到 n 的数字流
/// 1. 1 to n stream
/// 2. 每个数字乘以 2
/// 2. 2
/// 3. 过滤出能被 3 整除的数字
/// 3. is 3
/// 4. 最多取 5 个元素
/// 4. at most 5 element
/// 5. 收集到向量中
/// 5. to in
///
/// # 示例
/// # example
/// ```no_run
/// use c06_async::streams::demo_basic_combinators;
///
/// #[tokio::main]
/// async fn main() {
///     let result = demo_basic_combinators(10).await;
///     println!("结果: {:?}", result);
///     // 可能的输出: [6, 12, 18, 24, 30]
///     // may : [6, 12, 18, 24, 30]
/// }
/// ```
pub async fn demo_basic_combinators(n: u32) -> Vec<u32> {
    make_iter_stream(n)
        .map(|x| x * 2)                    // 每个数字乘以 2
        .filter(|x| futures::future::ready(x % 3 == 0))  // 过滤能被 3 整除的
        .take(5)                           // 最多取 5 个元素
        .collect::<Vec<_>>()               // 收集到向量中
        .await
}

/// 演示并发流处理
/// demonstration concurrency stream
///
/// 这个函数展示了如何使用 `buffer_unordered` 来并发处理流中的元素。
/// function `buffer_unordered` concurrency stream in element 。
/// 这对于处理大量异步操作（如网络请求）非常有用。
/// to async （network ）useful 。
///
/// # 并发处理策略
/// # concurrency strategy
///
/// ## buffer_unordered
/// - 并发处理流中的多个元素
/// - concurrency stream in element
/// - 不保证处理顺序（unordered）
/// - order （unordered）
/// - 可以设置并发数量限制
/// - can concurrency quantity
///
/// ## 使用场景
/// ## scenario
/// - 批量网络请求
/// - network
/// - 文件处理
/// -
/// - 数据库查询
/// - database
///
/// # 参数
/// # parameter
/// - `urls`: 要请求的 URL 列表
/// - `urls`: URL
///
/// # 返回值
/// # return value
/// 每个 URL 请求的结果向量（成功时包含响应长度，失败时包含错误）
/// URL result （，）
///
/// # 示例
/// # example
/// ```no_run
/// use c06_async::streams::demo_buffer_unordered;
///
/// #[tokio::main]
/// async fn main() {
///     let urls = vec![
///         "https://example.com".to_string(),
///         "https://httpbin.org/get".to_string(),
///     ];
///     let results = demo_buffer_unordered(urls).await;
///     for result in results {
///         match result {
///             Ok(len) => println!("响应长度: {}", len),
///             Err(e) => println!("请求失败: {}", e),
///         }
///     }
/// }
/// ```
pub async fn demo_buffer_unordered(urls: Vec<String>) -> Vec<Result<usize, reqwest::Error>> {
    let client = reqwest::Client::new();

    // 将 URL 列表转换为异步操作的流
    let futs = stream::iter(urls.into_iter().map(|u| {
        let c = client.clone();
        async move {
            // 发起 HTTP GET 请求
            let resp = c.get(u).send().await?;
            // 读取响应体
            let text = resp.text().await?;
            // 返回响应长度
            Ok::<usize, reqwest::Error>(text.len())
        }
    }));

    // 使用 buffer_unordered 限制并发数量为 4
    // 这样可以避免同时发起过多请求，防止资源耗尽
    futs.buffer_unordered(4).collect::<Vec<_>>().await
}

/// 演示自定义 TickStream 的使用
/// demonstration definition TickStream
///
/// 这个函数展示了如何消费自定义的 TickStream。
/// function definition TickStream。
/// 它会等待指定次数的计时器触发，并收集所有计数值。
/// etc. ，and all 。
///
/// # 参数
/// # parameter
/// - `ticks`: 要产生的计时次数
/// - `ticks`:
/// - `period`: 每次计时的间隔时间
/// - `period`: time
///
/// # 返回值
/// # return value
/// 包含所有计数值的向量
/// all
///
/// # 示例
/// # example
/// ```no_run
/// use c06_async::streams::demo_tick_stream;
/// use std::time::Duration;
///
/// #[tokio::main]
/// async fn main() {
///     let ticks = demo_tick_stream(3, Duration::from_millis(100)).await;
///     println!("计时结果: {:?}", ticks);
///     // 输出: [1, 2, 3]
///     // : [1, 2, 3]
/// }
/// ```
pub async fn demo_tick_stream(ticks: u64, period: Duration) -> Vec<u64> {
    let s = TickStream::new(ticks, period);
    s.collect::<Vec<_>>().await
}
