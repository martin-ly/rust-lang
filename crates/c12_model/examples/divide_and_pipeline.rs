#![allow(clippy::print_stdout)]

#[cfg(all(feature = "tokio-adapter"))]
#[tokio::main(flavor = "multi_thread")] 
async fn main() {
    use tokio::sync::{mpsc, broadcast};
    use tokio::task::JoinSet;

    // Stage 1: producer (divide)
    let (tx1, mut rx1) = mpsc::channel::<u64>(256);
    let (tx2, mut rx2) = mpsc::channel::<u64>(256);

    let prod = tokio::spawn({
        let tx1 = tx1.clone();
        async move {
            for i in 0..10000u64 { tx1.send(i).await.unwrap(); }
        }
    });

    // Stage 2: compute (parallel map) - use broadcast channel for multiple receivers
    let (tx_broadcast, _) = broadcast::channel::<u64>(256);
    let mut workers = JoinSet::new();
    
    // Forward from rx1 to broadcast
    let forward_task = tokio::spawn({
        let tx_broadcast = tx_broadcast.clone();
        async move {
            while let Some(v) = rx1.recv().await {
                let _ = tx_broadcast.send(v);
            }
        }
    });
    
    for _ in 0..8u64 {
        let tx2c = tx2.clone();
        let mut rx_bc = tx_broadcast.subscribe();
        workers.spawn(async move {
            while let Ok(v) = rx_bc.recv().await {
                let y = v.wrapping_mul(2);
                tx2c.send(y).await.ok();
            }
        });
    }
    drop(tx2);
    drop(tx1);

    // Stage 3: sink (aggregate)
    let sink = tokio::spawn(async move {
        let mut sum = 0u64;
        while let Some(v) = rx2.recv().await { sum = sum.wrapping_add(v); }
        sum
    });

    let _ = prod.await;
    let _ = forward_task.await;
    while workers.join_next().await.is_some() {}
    let sum = sink.await.unwrap();
    println!("divide_and_pipeline: sum={sum}");
}

#[cfg(not(all(feature = "tokio-adapter")))]
fn main() {
    eprintln!("Enable features: --features tokio-adapter\nExample: cargo run -p c12_model --example divide_and_pipeline --features tokio-adapter");
}


