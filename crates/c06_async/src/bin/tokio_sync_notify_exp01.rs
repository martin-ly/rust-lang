use c06_async::tokio::sync::notify::*;

#[tokio::main]
async fn main() {
    notify_test01().await;
}

