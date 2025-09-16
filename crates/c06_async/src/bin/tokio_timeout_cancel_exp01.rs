use futures::future::{AbortHandle, Abortable};
use std::time::Duration;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    // 超时控制
    let work = async {
        tokio::time::sleep(Duration::from_millis(300)).await;
        42
    };
    match tokio::time::timeout(Duration::from_millis(200), work).await {
        Ok(v) => println!("finished: {}", v),
        Err(_) => println!("timeout hit"),
    }

    // 取消控制：使用 futures 的 AbortHandle/Abortable
    let (handle, reg) = AbortHandle::new_pair();
    let task = Abortable::new(
        async {
            tokio::time::sleep(Duration::from_secs(1)).await;
            println!("long job done");
        },
        reg,
    );
    let h = tokio::spawn(task);
    tokio::time::sleep(Duration::from_millis(100)).await;
    handle.abort();
    let _ = h.await;
    println!("aborted");
}
