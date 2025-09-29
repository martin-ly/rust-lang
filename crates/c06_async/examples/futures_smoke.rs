//! 运行方式：
//! cargo run -p c06_async --example futures_smoke

use std::time::Duration;

#[tokio::main]
async fn main() {
    async fn task(dur: Duration, val: u32) -> u32 {
        tokio::time::sleep(dur).await;
        val
    }
    let vals = futures::future::join_all(vec![
        task(Duration::from_millis(10), 1),
        task(Duration::from_millis(20), 2),
        task(Duration::from_millis(5), 3),
    ]).await;
    let sum: u32 = vals.into_iter().sum();
    println!("futures_smoke: sum={}", sum);
}


