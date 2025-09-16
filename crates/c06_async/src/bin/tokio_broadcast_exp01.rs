#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let (tx, _rx) = tokio::sync::broadcast::channel::<u32>(16);
    // 三个订阅者
    let mut r1 = tx.subscribe();
    let mut r2 = tx.subscribe();
    let mut r3 = tx.subscribe();
    let h1 = tokio::spawn(async move {
        while let Ok(v) = r1.recv().await {
            println!("sub1 {v}");
        }
    });
    let h2 = tokio::spawn(async move {
        while let Ok(v) = r2.recv().await {
            println!("sub2 {v}");
        }
    });
    let h3 = tokio::spawn(async move {
        while let Ok(v) = r3.recv().await {
            println!("sub3 {v}");
        }
    });
    for i in 1..=5u32 {
        let _ = tx.send(i);
    }
    drop(tx);
    let _ = tokio::join!(h1, h2, h3);
}
