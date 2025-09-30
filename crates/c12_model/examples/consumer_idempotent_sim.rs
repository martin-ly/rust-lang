#![allow(clippy::print_stdout)]

#[cfg(all(feature = "tokio-adapter"))]
#[tokio::main(flavor = "multi_thread")] 
async fn main() {
    use std::collections::HashSet;
    use tokio::sync::{mpsc, Mutex};
    use std::sync::Arc;

    #[derive(Clone, Debug)]
    struct Msg { key: u64, payload: u64 }

    let (tx, mut rx) = mpsc::channel::<Msg>(1024);

    // Producer: duplicates to simulate at-least-once
    let prod = tokio::spawn({
        let tx = tx.clone();
        async move {
            for i in 0..5000u64 {
                let _ = tx.send(Msg { key: i, payload: i }).await;
                if i % 5 == 0 { let _ = tx.send(Msg { key: i, payload: i }).await; }
            }
        }
    });

    // Consumer with idempotency window
    let seen: Arc<Mutex<HashSet<u64>>> = Arc::new(Mutex::new(HashSet::new()));
    let mut ok = 0u64;
    while let Some(m) = rx.recv().await {
        let mut s = seen.lock().await;
        if s.insert(m.key) {
            ok = ok.wrapping_add(m.payload);
        } else {
            // duplicate -> skip
        }
    }
    let _ = prod.await;
    let unique_count = seen.lock().await.len();
    println!("consumer_idempotent_sim: ok_sum={ok} unique={unique_count}");
}

#[cfg(not(all(feature = "tokio-adapter")))]
fn main() {
    eprintln!("Enable features: --features tokio-adapter\nExample: cargo run -p c12_model --example consumer_idempotent_sim --features tokio-adapter");
}


