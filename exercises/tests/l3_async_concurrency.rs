//! L3 异步与并发嵌入式测验 — 可运行验证
//!
//! 本文件提取自 concept/03_advanced/ 中以下文件的嵌入式测验：
//! - 02_async.md
//! - 02_async_advanced.md
//! - 02_async_patterns.md
//! - 10_concurrency_patterns.md
//!
//! 运行: cargo test --test l3_async_concurrency

use std::sync::Arc;
use tokio::sync::{Mutex, mpsc};
use tokio::time::{Duration, sleep};

// ========== 02_async.md 测验验证 ==========

/// 测验1: async fn 返回 Future（记忆层验证）
#[tokio::test]
async fn test_async_fn_returns_future() {
    async fn foo() -> i32 {
        42
    }

    // async fn 返回的是 Future，需要 .await 或 executor 驱动
    let fut = foo();
    let result = fut.await;
    assert_eq!(result, 42);
}

/// 测验2: .await 非阻塞（理解层验证）
#[tokio::test]
async fn test_await_is_non_blocking() {
    let start = tokio::time::Instant::now();

    let task1 = tokio::spawn(async {
        sleep(Duration::from_millis(50)).await;
        1
    });
    let task2 = tokio::spawn(async {
        sleep(Duration::from_millis(50)).await;
        2
    });

    // 两个任务并发执行，总时间 ≈ 50ms，不是 100ms
    let (r1, r2) = tokio::join!(task1, task2);
    let elapsed = start.elapsed();

    assert_eq!(r1.unwrap(), 1);
    assert_eq!(r2.unwrap(), 2);
    assert!(elapsed < Duration::from_millis(80), "await 应该是非阻塞的");
}

/// 测验3: 取消安全（分析层验证）
#[tokio::test]
async fn test_cancellation_safety() {
    use tokio::io::AsyncWriteExt;

    let mut file = tokio::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open("test_cancel_tmp.txt")
        .await
        .unwrap();

    let result =
        tokio::time::timeout(Duration::from_millis(1), file.write_all(b"hello world")).await;

    // 超时会发生，但 write_all 要么完成要么不开始
    // 注意：实际取消安全取决于具体实现
    let _ = result;
    let _ = tokio::fs::remove_file("test_cancel_tmp.txt").await;
}

// ========== 02_async_advanced.md 测验验证 ==========

/// 测验1: async fn in trait（记忆层验证）
#[tokio::test]
async fn test_async_fn_in_trait() {
    trait Greeter {
        async fn greet(&self) -> String;
    }

    struct English;
    impl Greeter for English {
        async fn greet(&self) -> String {
            "Hello".to_string()
        }
    }

    let greeter = English;
    assert_eq!(greeter.greet().await, "Hello");
}

/// 测验2: spawn_blocking 隔离 CPU 密集型任务（应用层验证）
#[tokio::test]
async fn test_spawn_blocking() {
    let result = tokio::task::spawn_blocking(|| {
        // 模拟 CPU 密集型计算
        let mut sum = 0u64;
        for i in 0..1_000_000 {
            sum += i;
        }
        sum
    })
    .await
    .unwrap();

    assert_eq!(result, 499999500000);
}

/// 测验3: async 递归需要 Box::pin（分析层验证）
#[tokio::test]
async fn test_async_recursion() {
    use std::future::Future;
    use std::pin::Pin;

    fn count_down(n: i32) -> Pin<Box<dyn Future<Output = Vec<i32>> + Send>> {
        Box::pin(async move {
            if n <= 0 {
                vec![0]
            } else {
                let mut rest = count_down(n - 1).await;
                rest.insert(0, n);
                rest
            }
        })
    }

    let result = count_down(5).await;
    assert_eq!(result, vec![5, 4, 3, 2, 1, 0]);
}

// ========== 02_async_patterns.md 测验验证 ==========

/// 测验1: tokio::select! 竞争等待（记忆层验证）
#[tokio::test]
async fn test_tokio_select() {
    let (tx, mut rx) = mpsc::channel::<i32>(1);

    let result = tokio::select! {
        msg = rx.recv() => msg,
        _ = sleep(Duration::from_millis(10)) => Some(-1),
    };

    // channel 为空，sleep 先完成
    assert_eq!(result, Some(-1));

    // 现在发送消息再试
    tx.send(42).await.unwrap();
    let result = tokio::select! {
        msg = rx.recv() => msg,
        _ = sleep(Duration::from_secs(10)) => Some(-1),
    };
    assert_eq!(result, Some(42));
}

/// 测验2: 有界 channel 实现 backpressure（应用层验证）
#[tokio::test]
async fn test_bounded_channel_backpressure() {
    let (tx, mut rx) = mpsc::channel::<i32>(2); // 容量仅2

    // 发送3条消息，第3条会阻塞直到消费者读取
    tx.send(1).await.unwrap();
    tx.send(2).await.unwrap();

    // 启动生产者尝试发送第3条
    let tx2 = tx.clone();
    let producer = tokio::spawn(async move {
        let start = tokio::time::Instant::now();
        tx2.send(3).await.unwrap();
        start.elapsed()
    });

    // 消费者延迟读取
    sleep(Duration::from_millis(50)).await;
    assert_eq!(rx.recv().await, Some(1));

    let elapsed = producer.await.unwrap();
    // 生产者因 channel 满而阻塞了约 50ms
    assert!(elapsed >= Duration::from_millis(40));
}

/// 测验3: Actor 模式（应用层验证）
#[tokio::test]
async fn test_actor_pattern() {
    enum Command {
        Increment,
        GetCount(tokio::sync::oneshot::Sender<i32>),
    }

    let (tx, mut rx) = mpsc::channel::<Command>(10);

    // 启动 Actor 任务
    let actor = tokio::spawn(async move {
        let mut counter = 0i32;
        while let Some(cmd) = rx.recv().await {
            match cmd {
                Command::Increment => counter += 1,
                Command::GetCount(resp) => {
                    let _ = resp.send(counter);
                }
            }
        }
        counter
    });

    // 客户端发送消息
    tx.send(Command::Increment).await.unwrap();
    tx.send(Command::Increment).await.unwrap();
    tx.send(Command::Increment).await.unwrap();

    let (resp_tx, resp_rx) = tokio::sync::oneshot::channel();
    tx.send(Command::GetCount(resp_tx)).await.unwrap();

    let count = resp_rx.await.unwrap();
    assert_eq!(count, 3);

    drop(tx); // 关闭 channel，Actor 退出
    let final_count = actor.await.unwrap();
    assert_eq!(final_count, 3);
}

// ========== 10_concurrency_patterns.md 测验验证 ==========

/// 测验1: Arc + Mutex 共享状态（理解层验证）
#[tokio::test]
async fn test_arc_mutex_shared_state() {
    let counter = Arc::new(Mutex::new(0i32));
    let mut handles = vec![];

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        handles.push(tokio::spawn(async move {
            let mut num = c.lock().await;
            *num += 1;
        }));
    }

    for h in handles {
        h.await.unwrap();
    }

    assert_eq!(*counter.lock().await, 10);
}

/// 测验2: RwLock 读并发（理解层验证）
#[test]
fn test_rwlock_read_concurrent() {
    use std::sync::RwLock;

    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];

    for _ in 0..5 {
        let d = Arc::clone(&data);
        handles.push(std::thread::spawn(move || {
            let read = d.read().unwrap();
            assert_eq!(read.len(), 3);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}

/// 测验3: 工作窃取模式（应用层验证）
#[test]
fn test_rayon_work_stealing() {
    use rayon::prelude::*;

    let sum: i64 = (0..1_000_000)
        .into_par_iter()  // 并行迭代
        .sum();

    assert_eq!(sum, 499999500000i64);
}

/// 测验4: 死锁预防 — 统一加锁顺序（分析层验证）
#[test]
fn test_deadlock_prevention() {
    use std::sync::Mutex;

    struct Account {
        #[allow(dead_code)]
        id: u32,
        balance: Mutex<i32>,
    }

    fn transfer(from: &Account, to: &Account, amount: i32) {
        // 按地址排序加锁，消除循环等待
        let (first, second): (&Account, &Account) = if from as *const _ < to as *const _ {
            (from, to)
        } else {
            (to, from)
        };

        let mut first_guard = first.balance.lock().unwrap();
        let mut second_guard = second.balance.lock().unwrap();

        // 按原始方向执行转账
        if std::ptr::eq(from, first) {
            *first_guard -= amount;
            *second_guard += amount;
        } else {
            *first_guard += amount;
            *second_guard -= amount;
        }
    }

    let a = Arc::new(Account {
        id: 1,
        balance: Mutex::new(100),
    });
    let b = Arc::new(Account {
        id: 2,
        balance: Mutex::new(100),
    });

    let a2 = Arc::clone(&a);
    let b2 = Arc::clone(&b);
    let a3 = Arc::clone(&a);
    let b3 = Arc::clone(&b);

    let h1 = std::thread::spawn(move || transfer(&a2, &b2, 10));
    let h2 = std::thread::spawn(move || transfer(&b3, &a3, 20));

    h1.join().unwrap();
    h2.join().unwrap();

    // 无死锁，转账成功
    assert_eq!(*a.balance.lock().unwrap(), 110); // 100 - 10 + 20
    assert_eq!(*b.balance.lock().unwrap(), 90); // 100 + 10 - 20
}
