//! 运行方式：
//! cargo run -p c06_async --example tokio_smoke

use std::time::Duration;

#[tokio::main]
async fn main() {
    // 基本计时与 sleep
    let t0 = std::time::Instant::now();
    tokio::time::sleep(Duration::from_millis(50)).await;

    // JoinSet 并发执行
    let mut set = tokio::task::JoinSet::new();
    for i in 0..4u32 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis(10 * (i + 1) as u64)).await;
            i * i
        });
    }
    let mut sum = 0u32;
    while let Some(res) = set.join_next().await {
        sum += res.unwrap();
    }

    println!("tokio_smoke: elapsed={:?}, sum={}", t0.elapsed(), sum);
}


