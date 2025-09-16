use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn main() {
    let (tx, rx) = tokio::sync::mpsc::channel::<u32>(128);
    // 生产者
    let prod = tokio::spawn(async move {
        for i in 0..100u32 {
            tx.send(i).await.unwrap();
        }
    });
    // 工作池
    let mut workers = Vec::new();
    // 将接收端放入 Arc<Mutex<_>> 以共享
    let shared = std::sync::Arc::new(tokio::sync::Mutex::new(rx));
    for id in 0..4u32 {
        let shared = std::sync::Arc::clone(&shared);
        workers.push(tokio::spawn(async move {
            loop {
                let v_opt = { shared.lock().await.recv().await };
                match v_opt {
                    Some(v) => {
                        tokio::time::sleep(Duration::from_millis(10)).await;
                        println!("worker#{id} -> {v}");
                    }
                    None => break,
                }
            }
        }));
    }
    let _ = tokio::join!(prod, futures::future::join_all(workers));
}
