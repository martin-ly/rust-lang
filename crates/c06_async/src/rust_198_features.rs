//! Rust 1.98 Nightly 前瞻 —— 异步迭代与生成器
//! Rust 1.98 Nightly front async generator
#![allow(clippy::incompatible_msrv)]

use std::async_iter::AsyncIterator;
use std::pin::Pin;
use std::task::{Context, Poll};

/// # Rust 1.98 Nightly 异步特性前瞻
/// # Rust 1.98 Nightly async feature before
///
/// 本模块展示 nightly 1.98 中的前沿异步特性：
/// This module demonstrates nightly 1.98 frontasyncfeatures
/// - `for await` 循环 — 原生异步迭代语法糖
/// - `for await` circulation — async
/// - `AsyncIterator` trait — 标准异步迭代器接口
/// - `AsyncIterator` trait standardasynciterator interface
/// - `gen` 块与异步流的结合
/// - `gen` and async stream
///
/// **⚠️ 需要 nightly Rust + `#![feature(async_iterator, async_for_loop)]`**
pub struct Rust198AsyncFeatures;

// ============================================================================
// AsyncIterator 手动实现
// ============================================================================

/// 计数异步迭代器：从 start 开始，每次产生下一个整数
pub struct CountingAsyncIter {
    current: i32,
    end: i32,
}

impl CountingAsyncIter {
    /// 创建新的计数异步迭代器
    /// Create new asynciterator
    pub fn new(start: i32, end: i32) -> Self {
        Self {
            current: start,
            end,
        }
    }
}

impl AsyncIterator for CountingAsyncIter {
    type Item = i32;

    fn poll_next(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        if this.current < this.end {
            let val = this.current;
            this.current += 1;
            Poll::Ready(Some(val))
        } else {
            Poll::Ready(None)
        }
    }
}

/// 异步迭代器包装器：对 item 应用变换函数
pub struct MapAsyncIter<I, F> {
    inner: I,
    f: F,
}

impl<I, F, T> AsyncIterator for MapAsyncIter<I, F>
where
    I: AsyncIterator,
    F: FnMut(I::Item) -> T,
{
    type Item = T;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // SAFETY: 我们不动 MapAsyncIter 的 pin，只获取内部字段
        let this = unsafe { self.get_unchecked_mut() };
        let inner = unsafe { Pin::new_unchecked(&mut this.inner) };
        match inner.poll_next(cx) {
            Poll::Ready(Some(item)) => Poll::Ready(Some((this.f)(item))),
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}

impl Rust198AsyncFeatures {
    /// 使用 `for await` 语法遍历异步迭代器并求和
    /// `for await` async and and
    ///
    /// `for await x in iter` 是 `while let Some(x) = iter.next().await` 的语法糖。
    pub async fn sum_async_iter(iter: impl AsyncIterator<Item = i32>) -> i32 {
        let mut sum = 0;
        for await x in iter {
            sum += x;
        }
        sum
    }

    /// 使用 `for await` 语法过滤并收集异步流
    /// `for await` and async stream
    pub async fn collect_even_async(iter: impl AsyncIterator<Item = i32>) -> Vec<i32> {
        let mut result = Vec::new();
        for await x in iter {
            if x % 2 == 0 {
                result.push(x);
            }
        }
        result
    }

    /// 创建一个异步计数流
    pub fn count_stream(start: i32, end: i32) -> CountingAsyncIter {
        CountingAsyncIter::new(start, end)
    }

    /// 对异步流进行映射变换
    /// to async stream transformation
    pub fn map_stream<I, F, T>(inner: I, f: F) -> MapAsyncIter<I, F>
    where
        I: AsyncIterator,
        F: FnMut(I::Item) -> T,
    {
        MapAsyncIter { inner, f }
    }

    /// 使用 `for await` 实现异步流式批处理
    /// use `for await` implementationasyncflow processing
    ///
    /// 从异步迭代器读取数据，当累积 `batch_size` 个元素时 yield 一批。
    /// from async ，when `batch_size` element yield 。
    pub async fn batch_process(
        iter: impl AsyncIterator<Item = i32>,
        batch_size: usize,
    ) -> Vec<Vec<i32>> {
        let mut batches = Vec::new();
        let mut current = Vec::with_capacity(batch_size);
        for await item in iter {
            current.push(item);
            if current.len() == batch_size {
                batches.push(std::mem::take(&mut current));
                current.reserve(batch_size);
            }
        }
        if !current.is_empty() {
            batches.push(current);
        }
        batches
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_sum_async_iter() {
        let stream = CountingAsyncIter::new(0, 5);
        let sum = Rust198AsyncFeatures::sum_async_iter(stream).await;
        assert_eq!(sum, 10); // 0+1+2+3+4
    }

    #[tokio::test]
    async fn test_collect_even_async() {
        let stream = CountingAsyncIter::new(0, 10);
        let evens = Rust198AsyncFeatures::collect_even_async(stream).await;
        assert_eq!(evens, vec![0, 2, 4, 6, 8]);
    }

    #[tokio::test]
    async fn test_map_stream() {
        let stream = CountingAsyncIter::new(1, 4);
        let mapped = Rust198AsyncFeatures::map_stream(stream, |x| x * 2);
        let sum = Rust198AsyncFeatures::sum_async_iter(mapped).await;
        assert_eq!(sum, 12); // (1*2)+(2*2)+(3*2) = 12
    }

    #[tokio::test]
    async fn test_batch_process() {
        let stream = CountingAsyncIter::new(0, 10);
        let batches = Rust198AsyncFeatures::batch_process(stream, 3).await;
        assert_eq!(
            batches,
            vec![vec![0, 1, 2], vec![3, 4, 5], vec![6, 7, 8], vec![9]]
        );
    }
}
