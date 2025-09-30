#![allow(clippy::print_stdout)]

#[cfg(all(feature = "tokio-adapter"))]
#[tokio::main(flavor = "multi_thread")] 
async fn main() {
    use std::time::Duration;
    use tokio::{sync::mpsc, time};

    let capacity: usize = 64;
    let (tx, mut rx) = mpsc::channel::<u64>(capacity);

    // Producer: bursts faster than consumer
    let prod = tokio::spawn({
        let tx = tx.clone();
        async move {
            let mut sent = 0u64;
            for i in 0..10_000u64 {
                // Try fast path; if full, fallback to await send (backpressure)
                match tx.try_send(i) {
                    Ok(_) => sent += 1,
                    Err(_e) => {
                        // bounded backpressure: await send blocks producer
                        if tx.send(i).await.is_ok() {
                            sent += 1;
                        }
                    }
                }
                // bursty pattern
                if i % 100 == 0 { time::sleep(Duration::from_millis(1)).await; }
            }
            sent
        }
    });

    // Consumer: slower handler
    let cons = tokio::spawn(async move {
        let mut recv = 0u64;
        while let Some(_v) = rx.recv().await {
            recv += 1;
            // emulate work
            time::sleep(Duration::from_micros(200)).await;
            if recv >= 10_000 { break; }
        }
        recv
    });

    let (sent, recv) = tokio::join!(prod, cons);
    let sent = sent.unwrap();
    let recv = recv.unwrap();

    println!("bounded_backpressure: capacity={capacity} sent={sent} recv={recv} drop={}", sent.saturating_sub(recv));
}

#[cfg(not(all(feature = "tokio-adapter")))]
fn main() {
    eprintln!("Enable features: --features tokio-adapter\nExample: cargo run -p c12_model --example async_backpressure_bounded --features tokio-adapter");
}


