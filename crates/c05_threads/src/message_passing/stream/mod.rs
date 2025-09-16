//! 将 `crossbeam_channel::Receiver<T>` 适配为可迭代流。
//! 注意：这是同步阻塞迭代器，适用于简单消费场景。

use crossbeam_channel::Receiver;
use std::thread::sleep;
use std::time::{Duration, Instant};

pub struct ReceiverStream<T> {
    receiver: Receiver<T>,
}

impl<T> ReceiverStream<T> {
    pub fn new(receiver: Receiver<T>) -> Self {
        Self { receiver }
    }

    /// 阻塞等待下一项（可能永远阻塞）
    pub fn next_blocking(&self) -> Option<T> {
        self.receiver.recv().ok()
    }

    /// 在给定超时时间内尝试获取下一项，超时返回 None
    pub fn next_once_with_timeout(&self, timeout: Duration) -> Option<T> {
        self.receiver.recv_timeout(timeout).ok()
    }

    /// 非阻塞尝试获取一项
    pub fn try_next(&self) -> Option<T> {
        self.receiver.try_recv().ok()
    }

    /// 消费 self，返回阻塞迭代器
    pub fn into_iter(self) -> ReceiverIntoIter<T> {
        ReceiverIntoIter {
            inner: self.receiver,
        }
    }

    /// 轻量 map 适配器：返回惰性迭代器
    pub fn map<U, F>(self, mut f: F) -> impl Iterator<Item = U>
    where
        F: FnMut(T) -> U,
    {
        self.into_iter().map(move |item| f(item))
    }

    /// 轻量 filter 适配器：返回惰性迭代器
    pub fn filter<F>(self, mut pred: F) -> impl Iterator<Item = T>
    where
        F: FnMut(&T) -> bool,
    {
        self.into_iter().filter(move |item| pred(item))
    }

    /// 最多获取 batch_size 条，使用 per_item_timeout 作为单次取元素超时
    pub fn next_batch_max(&self, batch_size: usize, per_item_timeout: Duration) -> Vec<T> {
        let mut out = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            if let Some(v) = self.next_once_with_timeout(per_item_timeout) {
                out.push(v);
            } else {
                break;
            }
        }
        out
    }

    /// 在总超时 total_timeout 内持续消费，单次取元素超时 per_item_timeout
    pub fn take_until_timeout(
        &self,
        total_timeout: Duration,
        per_item_timeout: Duration,
    ) -> Vec<T> {
        let start = Instant::now();
        let mut out = Vec::new();
        while start.elapsed() < total_timeout {
            if let Some(v) = self.next_once_with_timeout(per_item_timeout) {
                out.push(v);
            } else {
                break;
            }
        }
        out
    }

    /// 以近似速率限制生成迭代器（每个元素之间最小间隔 min_interval）
    pub fn rate_limit_iter(self, min_interval: Duration) -> impl Iterator<Item = T> {
        let mut last = Instant::now();
        self.into_iter().map(move |item| {
            let elapsed = last.elapsed();
            if elapsed < min_interval {
                sleep(min_interval - elapsed);
            }
            last = Instant::now();
            item
        })
    }

    /// 在最大等待窗口 max_wait 内凑批，至少 1 条，最多 batch_size 条
    pub fn next_batch_with_max_wait(&self, batch_size: usize, max_wait: Duration) -> Vec<T> {
        let mut out = Vec::with_capacity(batch_size);
        let start = Instant::now();
        // 第一个元素：立即尝试获取，若无则在窗口内等待一次
        if let Some(v) = self.try_next() {
            out.push(v);
        } else if let Some(v) = self.next_once_with_timeout(max_wait) {
            out.push(v);
        } else {
            return out; // 空批
        }
        // 后续元素：在剩余窗口内尽量多取
        while out.len() < batch_size {
            let elapsed = start.elapsed();
            if elapsed >= max_wait {
                break;
            }
            let remain = max_wait - elapsed;
            if let Some(v) = self.next_once_with_timeout(remain) {
                out.push(v);
            } else {
                break;
            }
        }
        out
    }
}

impl<T> From<Receiver<T>> for ReceiverStream<T> {
    fn from(receiver: Receiver<T>) -> Self {
        Self::new(receiver)
    }
}

pub struct ReceiverIntoIter<T> {
    inner: Receiver<T>,
}

impl<T> Iterator for ReceiverIntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.recv().ok()
    }
}

impl<T> Iterator for ReceiverStream<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.receiver.recv().ok()
    }
}
