/*
消息传递:
    关注如何在不同线程之间传递消息，通常通过通道（channel）实现。
    通道（channel）是 Rust 提供的一种用于线程间通信的机制。
*/

use std::sync::mpsc;
use std::thread;

// 定义一个通用的消息类型
trait Message: Send + 'static {}

impl Message for String {}
impl Message for i32 {}

#[allow(unused)]
struct Worker<T: Message> {
    sender: mpsc::Sender<T>,
}

impl<T: Message> Worker<T> {
    fn new(sender: mpsc::Sender<T>) -> Self {
        Worker { sender }
    }

    fn send_message(&self, msg: T) {
        self.sender.send(msg).unwrap();
    }
}

#[allow(unused)]
fn message_passing() {
    let (tx, rx) = mpsc::channel();

    // 创建一个工作线程
    let worker = Worker::new(tx);
    thread::spawn(move || {
        // 发送字符串消息
        worker.send_message("Hello, world!".to_string());
        // 发送整数消息
        worker.send_message(42.to_string());

        // 发送完消息后，Sender 会被丢弃
    });

    // 接收消息
    for received in rx {
        println!("Received: {:?}", received);
    }

    // 当所有 Sender 被丢弃后，Receiver 会返回 None
    println!("Channel closed.");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_message_passing01() {
        message_passing();
    }
}

// === Async trait + GATs 事件流（背压 + 取消）示例 ===
use std::future::Future;

pub trait AsyncEventHandler<E: ?Sized> {
    type Ref<'a>
    where
        E: 'a,
        Self: 'a;

    /// 使用关联类型返回 Future，避免在公有 trait 中使用 `async fn`
    type Fut<'a>: Future<Output = ()> + 'a
    where
        E: 'a,
        Self: 'a;

    fn on_event<'a>(&'a self, event: Self::Ref<'a>) -> Self::Fut<'a>;
}

pub struct StringEventHandler;

impl AsyncEventHandler<String> for StringEventHandler {
    type Ref<'a> = &'a String where String: 'a;

    type Fut<'a> = std::pin::Pin<Box<dyn std::future::Future<Output = ()> + 'a>>
    where
        String: 'a,
        Self: 'a;

    fn on_event<'a>(&'a self, event: Self::Ref<'a>) -> Self::Fut<'a> {
        std::boxed::Box::pin(async move {
            // 纯演示：模拟处理
            let _ = event.len();
        })
    }
}

/// 简易异步事件总线（带背压与取消）
pub mod async_bus {
    use super::*;
    use std::future::Future;
    use std::pin::Pin;

    /// 面向 String 事件的简化总线，避免复杂的关联类型约束
    pub struct EventBusString {
        handler: StringEventHandler,
    }

    /// 泛型事件总线：适用于 Ref<'a> = &'a E 的处理器
    pub struct EventBusGeneric<H, E> {
        pub handler: H,
        _marker: core::marker::PhantomData<E>,
    }

    /// 背压策略（顺序驱动下的语义模拟）
    #[derive(Clone, Copy)]
    pub enum BackpressureStrategy {
        /// 丢弃最旧：仅处理最近的 N 条（由 caller 控制切片大小）
        DropOldest,
        /// 阻塞（顺序驱动下等价于逐条处理，无丢弃）
        Block,
        /// 批量聚合：按批处理，批内顺序消费
        Batch(usize),
    }

    /// 统一事件总线接口：以关联 Future 的形式提供异步 API
    pub trait EventBus<E> {
        type Fut<'a>: Future<Output = ()> + 'a
        where
            Self: 'a,
            E: 'a;

        fn run_with_backpressure<'a>(&'a self, events: &'a [E]) -> Self::Fut<'a>;
        fn run_until_cancel<'a>(&'a self, events: &'a [E], cancel: bool) -> Self::Fut<'a>;
        fn run_with_strategy<'a>(&'a self, events: &'a [E], strategy: BackpressureStrategy) -> Self::Fut<'a>;
        fn run_with_timeout_like<'a>(&'a self, events: &'a [E], max_events: usize) -> Self::Fut<'a>;
    }

    impl EventBusString {
        pub fn new(handler: StringEventHandler) -> Self {
            Self { handler }
        }

        /// 推送事件（顺序 await 处理，模拟背压：顺序消费）
        pub async fn run_with_backpressure(&self, events: &[String]) {
            for e in events {
                self.handler.on_event(e).await;
            }
        }

        /// 处理事件，遇到取消信号则提前返回
        pub async fn run_until_cancel(&self, events: &[String], cancel: bool) {
            for e in events {
                if cancel { break; }
                self.handler.on_event(e).await;
            }
        }

        /// 依据背压策略处理事件
        pub async fn run_with_strategy(&self, events: &[String], strategy: BackpressureStrategy) {
            match strategy {
                BackpressureStrategy::Block => {
                    for e in events {
                        self.handler.on_event(e).await;
                    }
                }
                BackpressureStrategy::DropOldest => {
                    // 仅处理尾部 1/2（示例策略：保留最新一半），避免实现内部缓冲
                    let half = events.len() / 2;
                    for e in &events[half..] {
                        self.handler.on_event(e).await;
                    }
                }
                BackpressureStrategy::Batch(batch_size) => {
                    let mut idx = 0;
                    while idx < events.len() {
                        let end = (idx + batch_size).min(events.len());
                        for e in &events[idx..end] {
                            self.handler.on_event(e).await;
                        }
                        idx = end;
                    }
                }
            }
        }

        /// 带超时取消（顺序驱动的计数截止模拟）
        /// max_events 作为超时阈值的无运行时近似（处理达到阈值即视为超时）。
        pub async fn run_with_timeout_like(&self, events: &[String], max_events: usize) {
            for (count, e) in events.iter().enumerate() {
                if count >= max_events { break; }
                self.handler.on_event(e).await;
            }
        }

    }

    impl EventBus<String> for EventBusString {
        type Fut<'a> = Pin<Box<dyn Future<Output = ()> + 'a>> where Self: 'a;

        fn run_with_backpressure<'a>(&'a self, events: &'a [String]) -> Self::Fut<'a> {
            Box::pin(self.run_with_backpressure(events))
        }

        fn run_until_cancel<'a>(&'a self, events: &'a [String], cancel: bool) -> Self::Fut<'a> {
            Box::pin(self.run_until_cancel(events, cancel))
        }

        fn run_with_strategy<'a>(&'a self, events: &'a [String], strategy: BackpressureStrategy) -> Self::Fut<'a> {
            Box::pin(self.run_with_strategy(events, strategy))
        }

        fn run_with_timeout_like<'a>(&'a self, events: &'a [String], max_events: usize) -> Self::Fut<'a> {
            Box::pin(self.run_with_timeout_like(events, max_events))
        }
    }

    impl<H, E> EventBusGeneric<H, E>
        where
            H: AsyncEventHandler<E>,
            for<'a> H::Ref<'a>: From<&'a E>,
        {
            pub fn new(handler: H) -> Self {
                Self { handler, _marker: core::marker::PhantomData }
            }

            pub async fn run_with_backpressure(&self, events: &[E]) {
                for e in events {
                    let r: H::Ref<'_> = <H::Ref<'_> as core::convert::From<&E>>::from(e);
                    self.handler.on_event(r).await;
                }
            }

            pub async fn run_until_cancel(&self, events: &[E], cancel: bool) {
                for e in events {
                    if cancel { break; }
                    let r: H::Ref<'_> = <H::Ref<'_> as core::convert::From<&E>>::from(e);
                    self.handler.on_event(r).await;
                }
            }

            pub async fn run_with_strategy(&self, events: &[E], strategy: BackpressureStrategy) {
                match strategy {
                    BackpressureStrategy::Block => {
                        for e in events {
                            let r: H::Ref<'_> = <H::Ref<'_> as core::convert::From<&E>>::from(e);
                            self.handler.on_event(r).await;
                        }
                    }
                    BackpressureStrategy::DropOldest => {
                        let half = events.len() / 2;
                        for e in &events[half..] {
                            let r: H::Ref<'_> = <H::Ref<'_> as core::convert::From<&E>>::from(e);
                            self.handler.on_event(r).await;
                        }
                    }
                    BackpressureStrategy::Batch(batch_size) => {
                        let mut idx = 0;
                        while idx < events.len() {
                            let end = (idx + batch_size).min(events.len());
                            for e in &events[idx..end] {
                                let r: H::Ref<'_> = <H::Ref<'_> as core::convert::From<&E>>::from(e);
                                self.handler.on_event(r).await;
                            }
                            idx = end;
                        }
                    }
                }
            }

            pub async fn run_with_timeout_like(&self, events: &[E], max_events: usize) {
                for (count, e) in events.iter().enumerate() {
                    if count >= max_events { break; }
                    let r: H::Ref<'_> = <H::Ref<'_> as core::convert::From<&E>>::from(e);
                    self.handler.on_event(r).await;
                }
            }
        }
    }

    impl<H, E> self::async_bus::EventBus<E> for self::async_bus::EventBusGeneric<H, E>
    where
        H: AsyncEventHandler<E>,
        for<'a> H::Ref<'a>: From<&'a E>,
    {
        type Fut<'a> = std::pin::Pin<Box<dyn std::future::Future<Output = ()> + 'a>> where Self: 'a, E: 'a;

        fn run_with_backpressure<'a>(&'a self, events: &'a [E]) -> Self::Fut<'a> {
            std::boxed::Box::pin(self.run_with_backpressure(events))
        }

        fn run_until_cancel<'a>(&'a self, events: &'a [E], cancel: bool) -> Self::Fut<'a> {
            std::boxed::Box::pin(self.run_until_cancel(events, cancel))
        }

        fn run_with_strategy<'a>(&'a self, events: &'a [E], strategy: self::async_bus::BackpressureStrategy) -> Self::Fut<'a> {
            std::boxed::Box::pin(self.run_with_strategy(events, strategy))
        }

        fn run_with_timeout_like<'a>(&'a self, events: &'a [E], max_events: usize) -> Self::Fut<'a> {
            std::boxed::Box::pin(self.run_with_timeout_like(events, max_events))
        }
    }

#[cfg(test)]
mod async_bus_tests {
    use super::async_bus::*;
    use super::StringEventHandler;
    use super::AsyncEventHandler;

    // 轻量 block_on：无外部运行时依赖，仅用于验证异步流程可执行
    fn block_on<F: core::future::Future>(mut fut: F) -> F::Output {
        use core::pin::Pin;
        use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

        fn dummy_raw_waker() -> RawWaker {
            fn no_op(_: *const ()) {}
            fn clone(_: *const ()) -> RawWaker { dummy_raw_waker() }
            static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
            RawWaker::new(core::ptr::null(), &VTABLE)
        }

        let waker = unsafe { Waker::from_raw(dummy_raw_waker()) };
        let mut cx = Context::from_waker(&waker);
        let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
        loop {
            match fut.as_mut().poll(&mut cx) {
                Poll::Ready(output) => break output,
                Poll::Pending => {}
            }
        }
    }

    fn sample_events(n: usize) -> Vec<String> {
        (0..n).map(|i| format!("e{}", i)).collect()
    }

    #[test]
    fn test_run_with_backpressure() {
        let bus = EventBusString::new(StringEventHandler);
        let events = sample_events(8);
        block_on(bus.run_with_backpressure(&events));
    }

    #[test]
    fn test_run_until_cancel() {
        let bus = EventBusString::new(StringEventHandler);
        let events = sample_events(10);
        // 取消为 false：应完整遍历
        block_on(bus.run_until_cancel(&events, false));
        // 取消为 true：应立即返回
        block_on(bus.run_until_cancel(&events, true));
    }

    #[test]
    fn test_run_with_strategy_variants() {
        let bus = EventBusString::new(StringEventHandler);
        let events = sample_events(9);
        block_on(bus.run_with_strategy(&events, BackpressureStrategy::Block));
        block_on(bus.run_with_strategy(&events, BackpressureStrategy::DropOldest));
        block_on(bus.run_with_strategy(&events, BackpressureStrategy::Batch(4)));
    }

    #[test]
    fn test_run_with_timeout_like() {
        let bus = EventBusString::new(StringEventHandler);
        let events = sample_events(7);
        block_on(bus.run_with_timeout_like(&events, 3));
        block_on(bus.run_with_timeout_like(&events, 10));
    }

    struct PassthroughHandler;

    impl AsyncEventHandler<String> for PassthroughHandler {
        type Ref<'a> = &'a String where String: 'a;
        type Fut<'a> = std::pin::Pin<Box<dyn std::future::Future<Output = ()> + 'a>> where Self: 'a, String: 'a;
        fn on_event<'a>(&'a self, event: Self::Ref<'a>) -> Self::Fut<'a> {
            std::boxed::Box::pin(async move {
                let _ = event.len();
            })
        }
    }

    #[test]
    fn test_generic_bus_basic() {
        let bus = EventBusGeneric::<PassthroughHandler, String>::new(PassthroughHandler);
        let events = sample_events(5);
        block_on(bus.run_with_backpressure(&events));
        block_on(bus.run_until_cancel(&events, false));
        block_on(bus.run_with_strategy(&events, BackpressureStrategy::Batch(2)));
        block_on(bus.run_with_timeout_like(&events, 3));
    }
}