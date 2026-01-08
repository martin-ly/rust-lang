//! Event Bus Demo
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **事件总线 (Event Bus)**: 发布-订阅模式的实现，用于解耦事件发布者和订阅者
//!   - **属性**: 事件发布、事件订阅、异步处理、背压处理
//!   - **关系**: 与观察者模式、发布-订阅模式相关
//!
//! ### 思维导图
//!
//! ```text
//! 事件总线演示
//! │
//! ├── 事件发布
//! │   └── 发布事件
//! ├── 事件订阅
//! │   └── 订阅事件
//! ├── 异步处理
//! │   └── 异步执行
//! └── 背压处理
//!     ├── DropOldest
//!     ├── Block
//!     └── Batch
//! ```

use c09_design_pattern::concurrency::message_passing::define::async_bus::{EventBusString, BackpressureStrategy};
use c09_design_pattern::concurrency::message_passing::define::StringEventHandler;

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
            Poll::Ready(v) => break v,
            Poll::Pending => {}
        }
    }
}

fn main() {
    let bus = EventBusString::new(StringEventHandler);
    let events: Vec<String> = (0..5).map(|i| format!("demo-{}", i)).collect();
    // 背压（顺序消费）
    block_on(bus.run_with_backpressure(&events));
    // 取消（立即返回）
    block_on(bus.run_until_cancel(&events, true));
    // 策略：Block/DropOldest/Batch
    block_on(bus.run_with_strategy(&events, BackpressureStrategy::Block));
    block_on(bus.run_with_strategy(&events, BackpressureStrategy::DropOldest));
    block_on(bus.run_with_strategy(&events, BackpressureStrategy::Batch(2)));
    // 超时近似（处理上限）
    block_on(bus.run_with_timeout_like(&events, 3));
    println!("event_bus_demo: done");
}
