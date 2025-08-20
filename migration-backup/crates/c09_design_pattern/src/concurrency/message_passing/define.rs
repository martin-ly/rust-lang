/*
消息传递:
    关注如何在不同线程之间传递消息，通常通过通道（channel）实现。
    通道（channel）是 Rust 提供的一种用于线程间通信的机制。
*/

use std::sync::mpsc;
use std::thread;

// 定义一个通用的消息类型
trait Message: Send + 'static {}

impl Message for String {}
impl Message for i32 {}

#[allow(unused)]
struct Worker<T: Message> {
    sender: mpsc::Sender<T>,
}

impl<T: Message> Worker<T> {
    fn new(sender: mpsc::Sender<T>) -> Self {
        Worker { sender }
    }

    fn send_message(&self, msg: T) {
        self.sender.send(msg).unwrap();
    }
}

#[allow(unused)]
fn message_passing() {
    let (tx, rx) = mpsc::channel();

    // 创建一个工作线程
    let worker = Worker::new(tx);
    thread::spawn(move || {
        // 发送字符串消息
        worker.send_message("Hello, world!".to_string());
        // 发送整数消息
        worker.send_message(42.to_string());

        // 发送完消息后，Sender 会被丢弃
    });

    // 接收消息
    for received in rx {
        println!("Received: {:?}", received);
    }

    // 当所有 Sender 被丢弃后，Receiver 会返回 None
    println!("Channel closed.");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_message_passing01() {
        message_passing();
    }
}
