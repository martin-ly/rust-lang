use c06_async::futures::future01::*;

use std::time::Duration;

#[tokio::main]
async fn main() {
    let my_future = MyFuture {
        delay: Duration::from_secs(2),
        state: State::Pending,
    };

    let result = my_future.await; // 等待 Future 完成
    println!("Future 完成，结果: {}", result);
}
