//! 运行方式：
//! cargo run -p c06_async --example streams_smoke

use std::time::Duration;

#[tokio::main]
async fn main() {
    use tokio_stream::{wrappers::IntervalStream, StreamExt};
    let interval = tokio::time::interval(Duration::from_millis(10));
    let mut s = IntervalStream::new(interval).take(5);
    let mut acc = 0u64;
    let mut i = 0u64;
    while let Some(_) = s.next().await {
        acc += i;
        i += 1;
    }
    println!("streams_smoke: acc={}", acc);
}


