use async_channel::{bounded, Receiver, Sender};
use async_io::Timer;
use futures::{StreamExt};
use std::time::Duration;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    smol::block_on(async move {
        let (tx, rx) = bounded::<String>(1024);
        smol::spawn(producer(tx)).detach();
        consumer(rx).await?;
        Ok(())
    })
}

async fn producer(tx: Sender<String>) {
    for page in 1..=10u32 {
        let url = format!("https://httpbin.org/get?page={}", page);
        let _ = tx.send(url).await;
        Timer::after(Duration::from_millis(50)).await;
    }
}

async fn consumer(rx: Receiver<String>) -> anyhow::Result<()> {
    let client = surf::Client::new();
    let bodies = futures::stream::unfold(rx, |rx| async move {
        match rx.recv().await.ok() {
            Some(url) => Some((url, rx)),
            None => None,
        }
    })
    .map(|url| {
        let client = client.clone();
        async move { client.get(url).recv_string().await }
    })
    .buffer_unordered(8)
    .collect::<Vec<_>>()
    .await;

    println!("fetched {} pages", bodies.len());
    Ok(())
}


