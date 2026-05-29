//! 异步 Trait 演示
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **异步 Trait**: 在 Trait 中定义异步方法的模式
//!   - **属性**: async fn in traits、异步方法、Trait实现
//!   - **关系**: 与异步编程、Trait系统相关
//!
//! ### 思维导图
//!
//! ```text
//! 异步 Trait 演示
//! │
//! ├── Trait 定义
//! │   └── async fn
//! ├── Trait 实现
//! │   └── 异步方法实现
//! └── 使用
//!     └── 异步调用
//! ```
use c09_design_pattern::concurrency::asynchronous::native_async_trait::{EchoProcessor, run_demo};

fn block_on<F: core::future::Future>(mut fut: F) -> F::Output {
    use core::pin::Pin;
    use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

    fn dummy_raw_waker() -> RawWaker {
        fn no_op(_: *const ()) {}
        fn clone(_: *const ()) -> RawWaker {
            dummy_raw_waker()
        }
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

fn main() {
    let p = EchoProcessor;
    let out = block_on(run_demo(&p));
    println!("async_trait_demo: {}", out);
}
