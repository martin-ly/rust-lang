//! async-std 适配占位（仅在 feature = "async-std-adapter" 启用）
#![cfg(feature = "async-std-adapter")]

use core::future::Future;
use core::time::Duration;

use crate::runtime_abi::{CancellationToken as CancellationTokenTrait, Channel as ChannelTrait, Spawner, Timer};

pub struct AsyncStdSpawner;

impl Spawner for AsyncStdSpawner {
    type JoinHandle<T> = async_std::task::JoinHandle<T>;

    fn spawn<F, T>(&self, fut: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        async_std::task::spawn(fut)
    }

    fn spawn_blocking<F, T>(&self, f: F) -> Self::JoinHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        async_std::task::spawn_blocking(f)
    }
}

pub struct AsyncStdTimer;

impl Timer for AsyncStdTimer {
    type SleepFuture = async_std::future::Timeout<async_std::future::Ready<()>>;

    fn sleep(&self, dur: Duration) -> Self::SleepFuture {
        async_std::future::timeout(dur, async { () })
    }
}

#[derive(Clone, Default)]
pub struct AsyncStdCancellationToken(std::sync::Arc<std::sync::atomic::AtomicBool>);

impl AsyncStdCancellationToken {
    pub fn new() -> Self { Self(Default::default()) }
    pub fn cancel(&self) { self.0.store(true, std::sync::atomic::Ordering::SeqCst); }
}

impl CancellationTokenTrait for AsyncStdCancellationToken {
    type Cancelled<'a> = impl core::future::Future<Output = ()> + Send where Self: 'a;

    fn is_cancelled(&self) -> bool { self.0.load(std::sync::atomic::Ordering::SeqCst) }
    fn cancelled(&self) -> Self::Cancelled<'_> {
        // 轮询式等待（示例占位；工程中可用更优实现）
        let flag = self.0.clone();
        async move {
            while !flag.load(std::sync::atomic::Ordering::SeqCst) {
                async_std::task::yield_now().await;
            }
        }
    }
}

pub struct AsyncStdChannel;

impl<T: Send + 'static> ChannelTrait<T> for AsyncStdChannel {
    type Sender = async_channel::Sender<T>;
    type Receiver = async_channel::Receiver<T>;

    fn bounded(capacity: usize) -> (Self::Sender, Self::Receiver) {
        async_channel::bounded(capacity)
    }
}


