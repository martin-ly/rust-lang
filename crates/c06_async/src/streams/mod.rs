use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

use futures::{stream, Stream, StreamExt};
use tokio::time::{interval, Interval};

/// 一个简单的基于 `tokio::time::interval` 的自定义 Stream
pub struct TickStream {
    interval: Interval,
    remaining: u64,
    counter: u64,
}

impl TickStream {
    pub fn new(ticks: u64, period: Duration) -> Self {
        Self {
            interval: interval(period),
            remaining: ticks,
            counter: 0,
        }
    }
}

impl Stream for TickStream {
    type Item = u64;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        if this.remaining == 0 {
            return Poll::Ready(None);
        }

        match Pin::new(&mut this.interval).poll_tick(cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(_) => {
                this.remaining -= 1;
                this.counter += 1;
                Poll::Ready(Some(this.counter))
            }
        }
    }
}

/// 基于迭代器快速构造一个 Stream
pub fn make_iter_stream(n: u32) -> impl Stream<Item = u32> {
    stream::iter(1..=n)
}

/// 展示 Stream 组合子：map/filter/take
pub async fn demo_basic_combinators(n: u32) -> Vec<u32> {
    let items = make_iter_stream(n)
        .map(|x| x * 2)
        .filter(|x| futures::future::ready(x % 3 == 0))
        .take(5)
        .collect::<Vec<_>>()
        .await;
    items
}

/// 展示并发组合子：buffer_unordered
pub async fn demo_buffer_unordered(urls: Vec<String>) -> Vec<Result<usize, reqwest::Error>> {
    let client = reqwest::Client::new();
    let futs = stream::iter(urls.into_iter().map(|u| {
        let c = client.clone();
        async move {
            let resp = c.get(u).send().await?;
            let text = resp.text().await?;
            Ok::<usize, reqwest::Error>(text.len())
        }
    }));

    // 限流并发数，避免过高并发
    futs.buffer_unordered(4).collect::<Vec<_>>().await
}

/// 消费 TickStream 的示例
pub async fn demo_tick_stream(ticks: u64, period: Duration) -> Vec<u64> {
    let s = TickStream::new(ticks, period);
    s.collect::<Vec<_>>().await
}

