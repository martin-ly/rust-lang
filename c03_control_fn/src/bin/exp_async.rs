use c03_control_fn::closure::r#async::*;
use std::time::Duration;
use tokio::time::sleep;


#[tokio::main]
async fn main() {
    // 使用 FnOnce 的闭包
    let once_closure = || {
        // 这里可以执行一些计算
        42
    };
    async_fn_once(once_closure).await;

    // 使用 FnMut 的闭包
    let mut count = 0;
    let mut_closure = || {
        count += 1;
        count
    };
    async_fn_mut(mut_closure).await;

    // 使用 Fn 的闭包
    let fn_closure = || {
        100
    };
    async_fn(fn_closure).await;

    // 模拟异步操作
    println!("Sleeping for 1 seconds...");
    sleep(Duration::from_secs(1)).await;
    println!("Awake!");
}
