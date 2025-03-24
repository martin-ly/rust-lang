use c06_async::r#await::await01;

#[tokio::main]
async fn main() {
    println!("开始异步任务");
    let result = await01::async_text01().await;
    println!("异步任务完成，结果: {}", result);
}