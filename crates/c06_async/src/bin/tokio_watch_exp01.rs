#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let (tx, mut rx) = tokio::sync::watch::channel(0u32);
    let h = tokio::spawn(async move {
        while rx.changed().await.is_ok() {
            let v = *rx.borrow();
            println!("watch got {v}");
            if v == 5 {
                break;
            }
        }
    });
    for i in 1..=5 {
        let _ = tx.send(i);
    }
    let _ = h.await;
}
