use c06_async::tokio::sync::mpsc::channel::exp01::*;

#[tokio::main]
async fn main() {
    channel_exp01().await;
    channel_exp02().await;
    channel_exp03().await;
    channel_exp04().await;
    channel_exp05().await;
}

