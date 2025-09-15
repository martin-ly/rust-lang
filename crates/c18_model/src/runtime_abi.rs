//! 统一运行时能力抽象（占位，不引入具体运行时依赖）
//!
//! 目标：在不绑定 Tokio/async-std/smol 等运行时时，抽象出最小能力面，
//! 便于在上层实现结构化并发、取消、超时、背压与可观测性的一致策略。

use core::future::Future;
use core::time::Duration;

/// 任务生成与阻塞任务网关
pub trait Spawner {
    type JoinHandle<T>: Future<Output = T> + Send + 'static;

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

/// 可观测性：为 future 附加 trace 上下文（占位）
pub trait Instrument {
    fn instrument<Fut>(self, fut: Fut) -> Fut
    where
        Self: Sized,
        Fut: Future;
}


