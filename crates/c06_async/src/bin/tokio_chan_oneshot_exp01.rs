use c06_async::tokio::sync::mpsc::oneshot::exp::*;

#[tokio::main]
async fn main() {
    oneshot_test01().await;
}


