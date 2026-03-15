# C06 异步原语练习

> 难度: 中级 | 预计时间: 60 分钟

---

## 🎯 练习目标

- 理解 Future 和 async/await
- 掌握 Tokio 运行时
- 理解并发原语

---

## 练习 1: 自定义 Future

实现一个简单的延迟 Future。

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

pub struct Delay {
    when: Instant,
}

impl Delay {
    pub fn new(duration: Duration) -> Self {
        Self {
            when: Instant::now() + duration,
        }
    }
}

impl Future for Delay {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if Instant::now() >= self.when {
            Poll::Ready(())
        } else {
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

#[tokio::main]
async fn main() {
    println!("Starting...");
    Delay::new(Duration::from_secs(1)).await;
    println!("Done!");
}
```

**任务**:

1. 实现一个带返回值的延迟 Future
2. 优化 polling 效率

---

## 练习 2: 并发任务管理

使用 JoinSet 管理多个并发任务。

```rust
use tokio::task::JoinSet;
use std::time::Duration;

#[tokio::main]
async fn main() {
    let mut set = JoinSet::new();

    for i in 0..5 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_millis(i * 100)).await;
            println!("Task {} completed", i);
            i * i
        });
    }

    while let Some(result) = set.join_next().await {
        match result {
            Ok(value) => println!("Got result: {}", value),
            Err(e) => println!("Task failed: {}", e),
        }
    }

    println!("All tasks completed");
}
```

**任务**:

1. 实现任务超时处理
2. 实现任务取消功能

<details>
<summary>超时处理答案</summary>

```rust
use tokio::task::JoinSet;
use tokio::time::{timeout, Duration};

#[tokio::main]
async fn main() {
    let mut set = JoinSet::new();

    for i in 0..5 {
        set.spawn(async move {
            tokio::time::sleep(Duration::from_secs(i as u64)).await;
            i * i
        });
    }

    while let Some(result) = set.join_next().await {
        match result {
            Ok(Ok(value)) => println!("Got result: {}", value),
            Ok(Err(e)) => println!("Task panicked: {}", e),
            Err(e) => println!("Task failed: {}", e),
        }
    }
}

// 带超时的版本
async fn run_with_timeout() {
    let result = timeout(
        Duration::from_secs(2),
        tokio::time::sleep(Duration::from_secs(5))
    ).await;

    match result {
        Ok(_) => println!("Completed in time"),
        Err(_) => println!("Timed out"),
    }
}
```

</details>

---

## 练习 3: Select 多路复用

使用 select! 同时等待多个异步操作。

```rust
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    let (tx1, mut rx1) = mpsc::channel(100);
    let (tx2, mut rx2) = mpsc::channel(100);

    tokio::spawn(async move {
        for i in 0..5 {
            tx1.send(format!("Channel 1: {}", i)).await.unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });

    tokio::spawn(async move {
        for i in 0..5 {
            tx2.send(format!("Channel 2: {}", i)).await.unwrap();
            sleep(Duration::from_millis(150)).await;
        }
    });

    loop {
        tokio::select! {
            Some(msg) = rx1.recv() => {
                println!("Received: {}", msg);
            }
            Some(msg) = rx2.recv() => {
                println!("Received: {}", msg);
            }
            else => break,
        }
    }
}
```

**任务**:

1. 添加优先级处理
2. 实现优雅关闭

---

## 📚 相关文档

- [C06 异步模块](../README.md)
- [Tokio 文档](https://tokio.rs/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
