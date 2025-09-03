use std::sync::Arc;
use std::time::Duration;
use tokio_stream::{StreamExt, wrappers::IntervalStream};

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn main() {
    // 以固定速率生成事件，窗口化批处理，并用 Semaphore 控制并发批量处理
    let ticker = tokio::time::interval(Duration::from_millis(20));
    let mut idx: u32 = 0;
    let stream = IntervalStream::new(ticker)
        .map(move |_| { idx += 1; idx - 1 })
        .take(100);

    let sem = Arc::new(tokio::sync::Semaphore::new(4));
    let mut s = stream;
    loop {
        let mut batch = Vec::with_capacity(10);
        let deadline = tokio::time::sleep(Duration::from_millis(100));
        tokio::pin!(deadline);
        while batch.len() < 10 {
            tokio::select! {
                _ = &mut deadline => { break; }
                v = s.next() => {
                    match v {
                        Some(x) => batch.push(x),
                        None => break,
                    }
                }
            }
        }
        if batch.is_empty() {
            break;
        }
        let permit = sem.clone().acquire_owned().await.unwrap();
        tokio::spawn(async move {
            let _p = permit;
            tokio::time::sleep(Duration::from_millis(60)).await;
            println!("processed batch: {:?}", batch);
        });
    }
}


