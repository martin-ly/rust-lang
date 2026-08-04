/*
tokio 的 oneshot 是一种用于在异步编程中实现单次消息传递的机制。
它允许一个任务发送一个值到另一个任务，并且这个值只能被接收一次。
oneshot 通常用于在异步环境中进行简单的通信。

定义

tokio::sync::oneshot 提供了一种创建单次发送和接收的通道。
它由两个部分组成：发送者（sender）和接收者（receiver）。
发送者可以发送一个值，而接收者可以接收这个值。

解释

发送者（Sender）：
用于发送数据的部分。调用 send 方法将数据发送到接收者。
接收者（Receiver）：
用于接收数据的部分。调用 await 方法等待接收到数据。
*/

use tokio::sync::oneshot;

#[allow(unused)]
pub async fn oneshot_test01() {
    // 创建一个 oneshot 通道
    let (tx, rx) = oneshot::channel();

    // 启动一个异步任务
    tokio::spawn(async move {
        // 发送一个值
        let _ = tx.send("Hello, world!");
    });

    // 接收发送的值
    match rx.await {
        Ok(message) => println!("Received: {}", message),
        Err(_) => println!("The sender dropped the message"),
    }
}
