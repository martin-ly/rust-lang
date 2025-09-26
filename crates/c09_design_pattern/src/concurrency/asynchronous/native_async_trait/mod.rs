//! 原生 async fn in trait 示例（Rust 1.90 / Edition 2024）

#[allow(unused)]
pub trait AsyncProcessor: Send + Sync {
    async fn process(&self, input: &str) -> String;
}

#[allow(unused)]
pub struct EchoProcessor;

impl AsyncProcessor for EchoProcessor {
    async fn process(&self, input: &str) -> String {
        // 模拟异步工作：无需运行时，这里只示意
        format!("echo:{}", input)
    }
}

#[allow(unused)]
pub async fn run_demo<P: AsyncProcessor>(p: &P) -> String {
    p.process("demo").await
}

#[cfg(feature = "tokio-bench")]
pub mod tokio_demo {
    use super::*;

    pub struct DelayProcessor;

    impl AsyncProcessor for DelayProcessor {
        async fn process(&self, input: &str) -> String {
            use tokio::time::{sleep, Duration};
            sleep(Duration::from_millis(5)).await;
            format!("delay:{}", input)
        }
    }

    #[tokio::test]
    async fn test_tokio_delay_processor() {
        let p = DelayProcessor;
        let out = p.process("x").await;
        assert_eq!(out, "delay:x");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // 纯 async 测试无需外部 runtime：使用简单的 block_on 辅助
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

    #[test]
    fn test_native_async_trait_echo() {
        let p = EchoProcessor;
        let out = block_on(run_demo(&p));
        assert_eq!(out, "echo:demo");
    }
}


