use c06_async::tokio::sync::mpsc::channel::exp02::*;

#[tokio::main]
async fn main() {
    channel_exp11().await;
    channel_exp12().await;
}
