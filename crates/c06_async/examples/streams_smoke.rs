//! 运行方式：
//! Run way ：
use std::time::Duration;

#[tokio::main]
async fn main() {
    use tokio_stream::StreamExt;
    use tokio_stream::wrappers::IntervalStream;
    let interval = tokio::time::interval(Duration::from_millis(10));
    let mut s = IntervalStream::new(interval).take(5);
    let mut acc = 0u64;
    let mut i = 0u64;
    while s.next().await.is_some() {
        acc += i;
        i += 1;
    }
    println!("streams_smoke: acc={}", acc);
}
