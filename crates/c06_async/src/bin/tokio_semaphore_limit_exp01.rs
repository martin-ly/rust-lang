use std::sync::Arc;
use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    let sem = Arc::new(tokio::sync::Semaphore::new(3));
    let mut handles = Vec::new();
    for i in 0..10u32 {
        let sem = Arc::clone(&sem);
        handles.push(tokio::spawn(async move {
            let permit = sem.acquire().await.expect("acquire permit");
            println!("task {} got permit", i);
            tokio::time::sleep(Duration::from_millis(100)).await;
            drop(permit);
            println!("task {} done", i);
        }));
    }
    for h in handles { let _ = h.await; }
}


