//! L3 进阶嵌入式测验（quizzes/l3_advanced）
//!
//! 覆盖范围：异步进阶、并发模式、原子操作、内联汇编、无锁结构
//!
//! 运行: cargo test --test quizzes

use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier, mpsc};
use std::thread;

/// 测验 1：`tokio::select!` 竞速两个异步任务
#[tokio::test]
async fn test_tokio_select_race() {
    let fast = tokio::time::sleep(tokio::time::Duration::from_millis(10));
    let slow = tokio::time::sleep(tokio::time::Duration::from_millis(100));

    tokio::select! {
        _ = fast => {}
        _ = slow => panic!("slow should not win"),
    }
}

/// 测验 2：`FuturesUnordered` 并发执行多个 Future
#[tokio::test]
async fn test_futures_unordered() {
    use futures::StreamExt;
    use futures::stream::FuturesUnordered;

    let mut tasks = FuturesUnordered::new();
    for i in 0..3 {
        tasks.push(async move { i * i });
    }

    let mut results = Vec::new();
    while let Some(v) = tasks.next().await {
        results.push(v);
    }
    results.sort();
    assert_eq!(results, vec![0, 1, 4]);
}

/// 测验 3：`std::thread::scope`  scoped 线程借用栈数据
#[test]
fn test_scoped_threads_borrow_stack() {
    let mut data = [1, 2, 3, 4, 5];

    thread::scope(|s| {
        for d in &mut data {
            s.spawn(move || {
                *d *= 2;
            });
        }
    });

    assert_eq!(data, [2, 4, 6, 8, 10]);
}

/// 测验 4：Actor 模式 —— 通过 channel 串行处理消息
#[test]
fn test_actor_pattern_counter() {
    enum Msg {
        Inc,
        Get(std::sync::mpsc::Sender<usize>),
    }

    let (tx, rx) = mpsc::channel::<Msg>();

    thread::spawn(move || {
        let mut count = 0usize;
        for msg in rx {
            match msg {
                Msg::Inc => count += 1,
                Msg::Get(reply) => {
                    let _ = reply.send(count);
                }
            }
        }
    });

    for _ in 0..5 {
        tx.send(Msg::Inc).unwrap();
    }

    let (reply_tx, reply_rx) = mpsc::channel();
    tx.send(Msg::Get(reply_tx)).unwrap();
    assert_eq!(reply_rx.recv().unwrap(), 5);
}

/// 测验 5：CAS 循环实现无锁自增
#[test]
fn test_cas_loop_increment() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = Vec::new();

    for _ in 0..4 {
        let c = counter.clone();
        handles.push(thread::spawn(move || {
            for _ in 0..100 {
                loop {
                    let current = c.load(Ordering::Relaxed);
                    let next = current + 1;
                    if c.compare_exchange_weak(current, next, Ordering::Relaxed, Ordering::Relaxed)
                        .is_ok()
                    {
                        break;
                    }
                }
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
    assert_eq!(counter.load(Ordering::Relaxed), 400);
}

/// 测验 6：`fetch_add` 比 load+store 更适合并发计数
#[test]
fn test_atomic_fetch_add_race_safe() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = Vec::new();

    for _ in 0..4 {
        let c = counter.clone();
        handles.push(thread::spawn(move || {
            for _ in 0..100 {
                c.fetch_add(1, Ordering::Relaxed);
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
    assert_eq!(counter.load(Ordering::Relaxed), 400);
}

/// 测验 7：Barrier 同步多个线程
#[test]
fn test_barrier_synchronization() {
    let barrier = Arc::new(Barrier::new(4));
    let mut handles = Vec::new();

    for i in 0..4 {
        let b = barrier.clone();
        handles.push(thread::spawn(move || {
            // 所有线程到达 barrier 后才继续
            let _ = b.wait();
            i
        }));
    }

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    assert_eq!(results.iter().sum::<usize>(), 6);
}

/// 测验 8：Release-Acquire 内存序实现简单的线程间信号
#[test]
fn test_release_acquire_flag() {
    let ready = Arc::new(AtomicUsize::new(0));
    let data = Arc::new(AtomicUsize::new(0));

    let (r1, d1) = (ready.clone(), data.clone());
    let producer = thread::spawn(move || {
        d1.store(42, Ordering::Relaxed);
        r1.store(1, Ordering::Release);
    });

    let (r2, d2) = (ready, data);
    let consumer = thread::spawn(move || {
        while r2.load(Ordering::Acquire) == 0 {
            thread::yield_now();
        }
        d2.load(Ordering::Relaxed)
    });

    producer.join().unwrap();
    assert_eq!(consumer.join().unwrap(), 42);
}

/// 测验 9：无锁 Treiber 栈（单生产者单消费者简化版）
#[test]
fn test_lock_free_treiber_stack() {
    use std::ptr;
    use std::sync::atomic::{AtomicPtr, Ordering};

    struct Node<T> {
        value: T,
        next: *mut Node<T>,
    }

    struct Stack<T> {
        head: AtomicPtr<Node<T>>,
    }

    impl<T> Stack<T> {
        fn new() -> Self {
            Self {
                head: AtomicPtr::new(ptr::null_mut()),
            }
        }

        fn push(&self, value: T) {
            let new_node = Box::into_raw(Box::new(Node {
                value,
                next: ptr::null_mut(),
            }));
            loop {
                let head = self.head.load(Ordering::Relaxed);
                unsafe { (*new_node).next = head }
                if self
                    .head
                    .compare_exchange_weak(head, new_node, Ordering::Release, Ordering::Relaxed)
                    .is_ok()
                {
                    break;
                }
            }
        }

        fn pop(&self) -> Option<T> {
            loop {
                let head = self.head.load(Ordering::Acquire);
                if head.is_null() {
                    return None;
                }
                let next = unsafe { (*head).next };
                if self
                    .head
                    .compare_exchange_weak(head, next, Ordering::Release, Ordering::Relaxed)
                    .is_ok()
                {
                    let value = unsafe { Box::from_raw(head).value };
                    return Some(value);
                }
            }
        }
    }

    let stack = Arc::new(Stack::new());
    let s1 = stack.clone();
    let s2 = stack.clone();

    thread::scope(|scope| {
        scope.spawn(move || {
            for i in 0..5 {
                s1.push(i);
            }
        });
        scope.spawn(move || {
            for i in 5..10 {
                s2.push(i);
            }
        });
    });

    let mut collected = Vec::new();
    while let Some(v) = stack.pop() {
        collected.push(v);
    }
    collected.sort();
    assert_eq!(collected, (0..10).collect::<Vec<_>>());
}

/// 测验 10：异步超时取消
#[tokio::test]
async fn test_async_timeout_cancellation() {
    let never = tokio::time::sleep(tokio::time::Duration::from_secs(10));
    let result = tokio::time::timeout(tokio::time::Duration::from_millis(50), never).await;

    assert!(result.is_err(), "超时应当返回 Err");
}

/// 测验 11：使用 `Pin<Box<dyn Future>>` 存储异构 Future
#[tokio::test]
async fn test_pin_box_dyn_future() {
    let fut1: Pin<Box<dyn Future<Output = i32> + Send>> = Box::pin(async { 1 });
    let fut2: Pin<Box<dyn Future<Output = i32> + Send>> = Box::pin(async { 2 });

    let (a, b) = tokio::join!(fut1, fut2);
    assert_eq!(a + b, 3);
}

/// 测验 12：x86_64 内联汇编读取 `rdtsc`（仅在 x86_64 平台运行）
#[test]
#[cfg(target_arch = "x86_64")]
fn test_inline_asm_rdtsc_increases() {
    let t1: u64;
    let t2: u64;
    unsafe {
        std::arch::asm!(
            "rdtsc",
            out("rax") t1,
            out("rdx") _,
        );
        std::arch::asm!(
            "rdtsc",
            out("rax") t2,
            out("rdx") _,
        );
    }
    // rdtsc 通常单调递增；若被调度到不同核心可能有微小回退，
    // 因此这里只验证两次读取均为非零且大概率递增。
    assert!(t1 != 0);
    assert!(t2 != 0);
    assert!(t2 >= t1);
}
