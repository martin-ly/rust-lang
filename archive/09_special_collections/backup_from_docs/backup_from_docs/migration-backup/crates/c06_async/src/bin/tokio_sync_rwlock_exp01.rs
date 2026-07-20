use c06_async::tokio::sync::rwlock::*;

#[tokio::main]
async fn main() {
    rwlock_test01().await;
}
