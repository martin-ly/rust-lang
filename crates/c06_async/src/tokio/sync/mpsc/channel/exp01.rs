/*
tokio::sync::mpsc 是 tokio 提供的多生产者单消费者（MPSC）通道，用于在异步任务之间传递消息。
它允许多个发送者（生产者）将消息发送到一个接收者（消费者），并且可以在异步环境中安全地使用。

定义

tokio::sync::mpsc 提供了一种异步通道，允许多个任务发送消息到一个任务。
它由发送者（Sender）和接收者（Receiver）组成。

解释

发送者（Sender）：用于发送消息的部分。可以通过调用 send 方法将消息发送到通道。
接收者（Receiver）：用于接收消息的部分。可以通过调用 recv 方法等待接收消息。

在 tokio::sync::mpsc 中，关闭通道的方式是通过丢弃发送者（Sender）来实现的。
当所有的发送者都被丢弃后，接收者（Receiver）将会收到 None，这表示通道已经关闭。

*/

use tokio::sync::mpsc;

#[allow(unused)]
pub async fn channel_exp01() {
    println!("channel_exp01");
    // 创建一个 MPSC 通道，缓冲区大小为 32
    let (tx, mut rx) = mpsc::channel(32);

    // 启动一个异步任务来发送消息
    tokio::spawn(async move {
        for i in 0..5 {
            if tx.send(i).await.is_err() {
                println!("Receiver dropped");
                return;
            }
            println!("Sent: {}", i);
        }
    });

    // 接收消息
    while let Some(message) = rx.recv().await {
        println!("Received: {}", message);
    }
}

#[allow(unused)]
pub async fn channel_exp02() {
    println!("channel_exp02");
    // 创建一个 MPSC 通道，缓冲区大小为 32
    let (tx, mut rx) = mpsc::channel(32);

    // 启动一个异步任务来发送消息
    tokio::spawn(async move {
        for i in 0..5 {
            if tx.send(i).await.is_err() {
                println!("Receiver dropped");
                return;
            }
            println!("Sent: {}", i);
        }
        // 发送完所有消息后，丢弃发送者以关闭通道
    });

    // 接收消息
    while let Some(message) = rx.recv().await {
        println!("Received: {}", message);
    }

    // 当所有发送者都被丢弃后，接收者将会收到 None
    println!("Channel closed");
}

#[allow(unused)]
pub async fn channel_exp03() {
    println!("channel_exp03");
    let (tx, mut rx) = mpsc::channel(32);
    let tx1 = tx.clone(); // 克隆发送者

    // 第一个发送者
    tokio::spawn(async move {
        for i in 0..3 {
            tx.send(i).await.unwrap();
            println!("Sender 1 sent: {}", i);
        }
    });

    // 第二个发送者
    tokio::spawn(async move {
        for i in 3..6 {
            tx1.send(i).await.unwrap();
            println!("Sender 2 sent: {}", i);
        }
    });

    // 接收者
    while let Some(message) = rx.recv().await {
        println!("Received: {}", message);
    }
}

#[allow(unused)]
pub async fn channel_exp04() {
    println!("channel_exp04");

    let (tx, mut rx) = mpsc::channel(2); // 缓冲区大小为 2

    // 启动发送者
    tokio::spawn(async move {
        for i in 0..5 {
            if tx.send(i).await.is_err() {
                println!("Receiver dropped");
                return;
            }
            println!("Sent: {}", i);
        }
    });

    // 启动接收者
    tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Received: {}", message);
            // 模拟处理时间
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        }
    });

    // 等待一段时间以观察阻塞情况
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}

#[allow(unused)]
pub async fn channel_exp05() {
    println!("channel_exp05");

    let (tx, mut rx) = mpsc::channel(32);

    // 启动接收者
    tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Received: {}", message);
        }
        println!("Channel closed");
    });

    // 启动发送者
    tokio::spawn(async move {
        // 发送一条消息
        tx.send(1).await.unwrap();
        println!("Sent: 1");
        // 模拟发送延迟
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        // 发送另一条消息
        tx.send(2).await.unwrap();
        println!("Sent: 2");
    });

    // 等待一段时间以观察接收者的阻塞情况
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}
