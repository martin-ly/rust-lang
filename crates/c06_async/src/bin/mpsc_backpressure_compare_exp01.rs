use std::time::{Duration, Instant};

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    // 对比：bounded mpsc vs unbounded mpsc 在慢消费者下的表现
    let total = 200u32;

    // bounded
    let (tx_b, mut rx_b) = tokio::sync::mpsc::channel::<u32>(32);
    let start_b = Instant::now();
    let prod_b = tokio::spawn(async move {
        for i in 0..total { tx_b.send(i).await.unwrap(); }
    });
    let cons_b = tokio::spawn(async move {
        let mut cnt = 0u32;
        while let Some(_v) = rx_b.recv().await {
            cnt += 1;
            if cnt % 20 == 0 { tokio::time::sleep(Duration::from_millis(10)).await; }
            if cnt == total { break; }
        }
    });
    let _ = tokio::join!(prod_b, cons_b);
    let elapsed_b = start_b.elapsed();

    // unbounded
    let (tx_u, mut rx_u) = tokio::sync::mpsc::unbounded_channel::<u32>();
    let start_u = Instant::now();
    let prod_u = tokio::spawn(async move {
        for i in 0..total { tx_u.send(i).unwrap(); }
    });
    let cons_u = tokio::spawn(async move {
        let mut cnt = 0u32;
        while let Some(_v) = rx_u.recv().await {
            cnt += 1;
            if cnt % 20 == 0 { tokio::time::sleep(Duration::from_millis(10)).await; }
            if cnt == total { break; }
        }
    });
    let _ = tokio::join!(prod_u, cons_u);
    let elapsed_u = start_u.elapsed();

    println!("bounded elapsed: {:?}", elapsed_b);
    println!("unbounded elapsed: {:?}", elapsed_u);
}


