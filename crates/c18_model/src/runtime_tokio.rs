//! Tokio 适配占位（仅在 feature = "tokio-adapter" 启用）
#![cfg(feature = "tokio-adapter")]

use core::future::Future;
use core::time::Duration;

use crate::runtime_abi::{CancellationToken as CancellationTokenTrait, Channel as ChannelTrait, Spawner, Timer};

pub struct TokioSpawner;

impl Spawner for TokioSpawner {
    type JoinHandle<T> = tokio::task::JoinHandle<T>;

    fn spawn<F, T>(&self, fut: F) -> Self::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        tokio::spawn(fut)
    }

    fn spawn_blocking<F, T>(&self, f: F) -> Self::JoinHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        tokio::task::spawn_blocking(f)
    }
}

pub struct TokioTimer;

impl Timer for TokioTimer {
    type SleepFuture = tokio::time::Sleep;

    fn sleep(&self, dur: Duration) -> Self::SleepFuture {
        tokio::time::sleep(dur)
    }
}

#[derive(Clone)]
pub struct TokioCancellationToken(tokio_util::sync::CancellationToken);

impl TokioCancellationToken {
    pub fn new() -> Self {
        Self(tokio_util::sync::CancellationToken::new())
    }
    pub fn cancel(&self) {
        self.0.cancel();
    }
}

impl CancellationTokenTrait for TokioCancellationToken {
    type Cancelled<'a> = tokio_util::sync::WaitForCancellationFuture<'a> where Self: 'a;

    fn is_cancelled(&self) -> bool {
        self.0.is_cancelled()
    }

    fn cancelled(&self) -> Self::Cancelled<'_> {
        self.0.cancelled()
    }
}

pub struct TokioChannel;

impl<T: Send + 'static> ChannelTrait<T> for TokioChannel {
    type Sender = tokio::sync::mpsc::Sender<T>;
    type Receiver = tokio::sync::mpsc::Receiver<T>;

    fn bounded(capacity: usize) -> (Self::Sender, Self::Receiver) {
        tokio::sync::mpsc::channel(capacity)
    }
}


