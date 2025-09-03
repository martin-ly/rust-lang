use std::future::Future;
use std::time::Duration;
use futures::future::{AbortHandle, Abortable};

async fn with_timeout_cancel<F, T>(dur: Duration, fut: F) -> Option<T>
where
    F: Future<Output = T>,
{
    match tokio::time::timeout(dur, fut).await {
        Ok(v) => Some(v),
        Err(_) => None,
    }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    // 超时+取消 作用域：在作用域内注册一组任务，当超时触发时取消其余任务
    let (h, reg) = AbortHandle::new_pair();

    let t = tokio::spawn(Abortable::new(async {
        // 子任务 A
        let a = tokio::spawn(async {
            tokio::time::sleep(Duration::from_millis(150)).await;
            println!("A done");
        });
        // 子任务 B
        let b = tokio::spawn(async {
            tokio::time::sleep(Duration::from_millis(300)).await;
            println!("B done");
        });
        let _ = tokio::join!(a, b);
    }, reg));

    if with_timeout_cancel(Duration::from_millis(200), async { t.await }).await.is_none() {
        h.abort();
        println!("scope timeout -> cancelled");
    }
}


