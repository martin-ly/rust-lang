/*
在 Rust 中，async 和 await 是用于处理异步编程的关键字。
它们允许你编写非阻塞的代码，
使得程序在等待某些操作（如 I/O 操作）完成时可以继续执行其他任务。

定义与解释
async: 
    这个关键字用于定义一个异步函数或块。
    异步函数会返回一个实现了 Future trait 的值，
    这个值代表一个可能在将来完成的计算。
await: 
    这个关键字用于等待一个 Future 完成。
    使用 await 时，当前的异步任务会被挂起，直到所等待的 Future 完成。
*/

use tokio::time::sleep;
use std::time::Duration;


#[allow(unused)]
pub async fn async_text01() -> i32 {
    println!("开始异步任务");
    sleep(Duration::from_secs(1)).await; // 模拟异步操作
    println!("异步任务完成");
    42 // 返回结果
}

