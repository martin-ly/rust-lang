use c06_async::tokio::sync::mutex::*;

#[tokio::main]
async fn main() {
    mutex_test01().await;
}

