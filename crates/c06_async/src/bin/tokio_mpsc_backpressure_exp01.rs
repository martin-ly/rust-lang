use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<u32>(4); // 小缓冲制造背压

    let prod = tokio::spawn(async move {
        for i in 0..12u32 {
            // send 在缓冲满时会等待，体现背压
            tx.send(i).await.unwrap();
            println!("sent {i}");
        }
    });

    let cons = tokio::spawn(async move {
        while let Some(v) = rx.recv().await {
            println!("recv {v}");
            tokio::time::sleep(Duration::from_millis(120)).await; // 慢消费
        }
    });

    let _ = tokio::join!(prod, cons);
}


