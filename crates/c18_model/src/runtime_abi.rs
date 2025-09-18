//! 统一运行时能力抽象（草案，不引入具体运行时依赖）
//!
//! 目标：在不绑定 Tokio/async-std/smol 等运行时时，抽象出最小能力面，
//! 便于在上层实现结构化并发、取消、超时、背压与可观测性的一致策略。

use core::future::Future;
use core::time::Duration;

/// 任务生成与阻塞任务网关
pub trait Spawner {
    type JoinHandle<T: 'static>: Future<Output = T> + Send + 'static;

    fn spawn<F, T>(&self, fut: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static;

    fn spawn_blocking<F, T>(&self, f: F) -> Self::JoinHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static;
}

/// 计时能力：sleep 与 timeout
pub trait Timer {
    type SleepFuture: Future<Output = ()> + Send + 'static;

    fn sleep(&self, dur: Duration) -> Self::SleepFuture;
}

/// 取消令牌：可克隆、可观察
pub trait CancellationToken: Clone + Send + Sync + 'static {
    type Cancelled<'a>: Future<Output = ()> + Send
    where
        Self: 'a;

    fn is_cancelled(&self) -> bool;
    fn cancelled(&self) -> Self::Cancelled<'_>;
}

/// 有界通道（最小能力）
pub trait Channel<T>: Send + Sync + 'static {
    type Sender: Send + Sync + Clone + 'static;
    type Receiver: Send + Sync + 'static;

    fn bounded(capacity: usize) -> (Self::Sender, Self::Receiver);
}

/// 可观测性：为 future 附加 trace 上下文（草案接口）
pub trait Instrument {
    fn instrument<Fut>(self, fut: Fut) -> Fut
    where
        Self: Sized,
        Fut: Future;
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::pin::Pin;
    use core::task::{Context, Poll};
    use std::boxed::Box;

    struct DummySpawner;
    impl Spawner for DummySpawner {
        type JoinHandle<T> = Pin<Box<dyn Future<Output = T> + Send + 'static>> where T: 'static;
        fn spawn<F, T>(&self, _fut: F) -> Self::JoinHandle<T>
        where
            F: Future<Output = T> + Send + 'static,
            T: Send + 'static,
        {
            Box::pin(_fut)
        }
        fn spawn_blocking<F, T>(&self, _f: F) -> Self::JoinHandle<T>
        where
            F: FnOnce() -> T + Send + 'static,
            T: Send + 'static,
        {
            Box::pin(async move { _f() })
        }
    }

    struct Ready;
    impl Future for Ready {
        type Output = ();
        fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> { Poll::Ready(()) }
    }

    struct DummyTimer;
    impl Timer for DummyTimer {
        type SleepFuture = Ready;
        fn sleep(&self, _dur: Duration) -> Self::SleepFuture { Ready }
    }

    #[derive(Clone)]
    struct DummyCancel;
    impl CancellationToken for DummyCancel {
        type Cancelled<'a> = Ready where Self: 'a;
        fn is_cancelled(&self) -> bool { false }
        fn cancelled(&self) -> Self::Cancelled<'_> { Ready }
    }

    struct DummyChan;
    impl<T> Channel<T> for DummyChan {
        type Sender = ();
        type Receiver = ();
        fn bounded(_capacity: usize) -> (Self::Sender, Self::Receiver) { ((), ()) }
    }

    struct DummyInstr;
    impl Instrument for DummyInstr {
        fn instrument<Fut>(self, fut: Fut) -> Fut where Fut: Future { fut }
    }

    #[test]
    fn abi_traits_compile_with_dummy_impls() {
        let _sp = DummySpawner;
        let _tm = DummyTimer;
        let _ct = DummyCancel;
        let _ = <DummyChan as Channel<u8>>::bounded(1);
        let _ = DummyInstr.instrument(Ready);
    }
}