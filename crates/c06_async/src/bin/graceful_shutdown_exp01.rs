use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let (tx, mut rx) = tokio::sync::mpsc::channel::<()>(1);
    let worker = tokio::spawn(async move {
        loop {
            tokio::select! {
                Some(_) = rx.recv() => { println!("worker: shutdown signal"); break; }
                _ = tokio::time::sleep(Duration::from_millis(200)) => {
                    println!("worker: heartbeat");
                }
            }
        }
        println!("worker: cleanup done");
    });

    tokio::signal::ctrl_c().await.ok();
    let _ = tx.send(()).await;
    let _ = worker.await;
    println!("main: bye");
}
