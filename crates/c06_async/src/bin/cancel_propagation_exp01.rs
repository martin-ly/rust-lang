use futures::future::{AbortHandle, Abortable, Aborted};
use std::time::Duration;

async fn subtask(name: &'static str, delay_ms: u64) -> Result<(), ()> {
    tokio::time::sleep(Duration::from_millis(delay_ms)).await;
    println!("{} done", name);
    Ok(())
}

#[tokio::main]
async fn main() {
    // 通过 AbortHandle 模拟取消传播：一旦有错误，取消其它任务
    let (h1, reg1) = AbortHandle::new_pair();
    let (h2, reg2) = AbortHandle::new_pair();

    let t1 = tokio::spawn(Abortable::new(
        async move { subtask("t1", 300).await },
        reg1,
    ));

    let t2 = tokio::spawn(Abortable::new(
        async move {
            tokio::time::sleep(Duration::from_millis(120)).await;
            Err::<(), ()>(())
        },
        reg2,
    ));

    let r1 = t1;
    let r2 = t2;

    // 等待先返回者
    let first = futures::future::select(r1, r2).await;
    match first {
        futures::future::Either::Left((a, b)) => {
            if matches!(a, Ok(Ok(Err(()))) | Ok(Err(Aborted)) | Err(_)) {
                h2.abort();
            }
            let _ = b.await; // 等待另一边
        }
        futures::future::Either::Right((a, b)) => {
            if matches!(a, Ok(Ok(Err(()))) | Ok(Err(Aborted)) | Err(_)) {
                h1.abort();
            }
            let _ = b.await;
        }
    }
    println!("cancel propagated");
}
