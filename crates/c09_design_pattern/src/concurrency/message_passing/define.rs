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

// === Async trait + GATs 事件流（背压 + 取消）示例 ===
pub trait AsyncEventHandler<E: ?Sized> {
    type Ref<'a>
    where
        E: 'a,
        Self: 'a;

    async fn on_event<'a>(&self, event: Self::Ref<'a>);
}

pub struct StringEventHandler;

impl AsyncEventHandler<String> for StringEventHandler {
    type Ref<'a> = &'a String where String: 'a;

    async fn on_event<'a>(&self, event: Self::Ref<'a>) {
        // 纯演示：模拟处理
        let _ = event.len();
    }
}

/// 简易异步事件总线（带背压与取消）
pub mod async_bus {
    use super::*;

    /// 面向 String 事件的简化总线，避免复杂的关联类型约束
    pub struct EventBusString {
        handler: StringEventHandler,
    }

    /// 背压策略（顺序驱动下的语义模拟）
    #[derive(Clone, Copy)]
    pub enum BackpressureStrategy {
        /// 丢弃最旧：仅处理最近的 N 条（由 caller 控制切片大小）
        DropOldest,
        /// 阻塞（顺序驱动下等价于逐条处理，无丢弃）
        Block,
        /// 批量聚合：按批处理，批内顺序消费
        Batch(usize),
    }

    impl EventBusString {
        pub fn new(handler: StringEventHandler) -> Self {
            Self { handler }
        }

        /// 推送事件（顺序 await 处理，模拟背压：顺序消费）
        pub async fn run_with_backpressure(&self, events: &[String]) {
            for e in events {
                self.handler.on_event(e).await;
            }
        }

        /// 处理事件，遇到取消信号则提前返回
        pub async fn run_until_cancel(&self, events: &[String], cancel: bool) {
            for e in events {
                if cancel { break; }
                self.handler.on_event(e).await;
            }
        }

        /// 依据背压策略处理事件
        pub async fn run_with_strategy(&self, events: &[String], strategy: BackpressureStrategy) {
            match strategy {
                BackpressureStrategy::Block => {
                    for e in events {
                        self.handler.on_event(e).await;
                    }
                }
                BackpressureStrategy::DropOldest => {
                    // 仅处理尾部 1/2（示例策略：保留最新一半），避免实现内部缓冲
                    let half = events.len() / 2;
                    for e in &events[half..] {
                        self.handler.on_event(e).await;
                    }
                }
                BackpressureStrategy::Batch(batch_size) => {
                    let mut idx = 0;
                    while idx < events.len() {
                        let end = (idx + batch_size).min(events.len());
                        for e in &events[idx..end] {
                            self.handler.on_event(e).await;
                        }
                        idx = end;
                    }
                }
            }
        }

        /// 带超时取消（顺序驱动的计数截止模拟）
        /// max_events 作为超时阈值的无运行时近似（处理达到阈值即视为超时）。
        pub async fn run_with_timeout_like(&self, events: &[String], max_events: usize) {
            let mut count = 0;
            for e in events {
                if count >= max_events { break; }
                self.handler.on_event(e).await;
                count += 1;
            }
        }
    }
}