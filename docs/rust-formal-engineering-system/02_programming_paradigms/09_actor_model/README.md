# Actor 模型理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [c05_threads/](../../../../crates/c05_threads/)、[c06_async/](../../../../crates/c06_async/)

[返回主索引](../../00_master_index.md)

---

## Actor 模型核心概念

Actor 模型是一种并发计算模型，其中：

- 每个 Actor 是一个独立的计算实体
- Actor 之间通过异步消息传递通信
- 每个 Actor 有自己的状态，不共享内存

### 基本 Actor 实现

```rust
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;

// 消息类型
enum Message {
    Increment,
    GetValue(Sender<usize>),
    Stop,
}

// Actor 结构
struct CounterActor {
    sender: Sender<Message>,
}

impl CounterActor {
    fn new() -> Self {
        let (sender, receiver) = channel::<Message>();

        thread::spawn(move || {
            let mut count = 0usize;

            while let Ok(msg) = receiver.recv() {
                match msg {
                    Message::Increment => count += 1,
                    Message::GetValue(reply) => {
                        let _ = reply.send(count);
                    }
                    Message::Stop => break,
                }
            }
        });

        Self { sender }
    }

    fn increment(&self) {
        let _ = self.sender.send(Message::Increment);
    }

    fn get_value(&self) -> usize {
        let (tx, rx) = channel();
        let _ = self.sender.send(Message::GetValue(tx));
        rx.recv().unwrap_or(0)
    }

    fn stop(&self) {
        let _ = self.sender.send(Message::Stop);
    }
}

// 使用示例
fn demo() {
    let actor = CounterActor::new();

    for _ in 0..10 {
        actor.increment();
    }

    println!("Count: {}", actor.get_value());  // 10
    actor.stop();
}
```

### 异步 Actor

```rust
use tokio::sync::mpsc::{channel, Sender, Receiver};

// 异步 Actor
struct AsyncActor {
    sender: Sender<AsyncMessage>,
}

enum AsyncMessage {
    Process(String),
    GetResult(Sender<String>),
}

impl AsyncActor {
    async fn run(mut receiver: Receiver<AsyncMessage>) {
        while let Some(msg) = receiver.recv().await {
            match msg {
                AsyncMessage::Process(data) => {
                    // 异步处理
                    println!("Processing: {}", data);
                }
                AsyncMessage::GetResult(reply) => {
                    let _ = reply.send("Done".to_string()).await;
                }
            }
        }
    }

    fn new() -> Self {
        let (sender, receiver) = channel(100);
        tokio::spawn(Self::run(receiver));
        Self { sender }
    }
}
```

## 相关 crates

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c05_threads | 线程并发实现 | [../../../../crates/c05_threads/](../../../../crates/c05_threads/) |
| c06_async | 异步并发实现 | [../../../../crates/c06_async/](../../../../crates/c06_async/) |
