//! 综合 Loom 并发测试 / Comprehensive Loom Concurrency Tests
//!
//! 本模块包含使用 Loom 进行的全面并发测试，确保并发代码的正确性。
//! This module contains comprehensive concurrency tests using Loom to ensure correctness of concurrent code.
//!
//! 在 Windows 上使用 4MB 栈以避免 loom 状态空间探索导致的栈溢出。
//! Uses 4MB stack on Windows to avoid stack overflow from loom's state space exploration.
//!
//! Windows 上 loom 状态空间探索易导致栈溢出，全部 loom 测试在 Windows 上默认忽略。
//! Run with `cargo test -p c05_threads --test loom_comprehensive -- --ignored` to run them.

use loom::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use loom::sync::{Arc, Condvar, Mutex};
use loom::thread;
use std::sync::mpsc;

/// 在较大栈上运行 loom 模型，避免 Windows 上栈溢出
fn loom_model<F, R>(f: F) -> R
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    const STACK_SIZE: usize = 4 * 1024 * 1024; // 4MB
    std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// 测试基本的原子操作 / Test basic atomic operations
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_atomic_operations() {
    loom_model(|| {
    loom::model(|| {
        let atomic = Arc::new(AtomicUsize::new(0));
        let atomic_clone1 = atomic.clone();
        let atomic_clone2 = atomic.clone();
        
        let t1 = thread::spawn(move || {
            atomic_clone1.fetch_add(1, Ordering::SeqCst);
        });
        
        let t2 = thread::spawn(move || {
            atomic_clone2.fetch_add(1, Ordering::SeqCst);
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
        
        assert_eq!(atomic.load(Ordering::SeqCst), 2);
    });
    });
}

/// 测试原子布尔值 / Test atomic boolean
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_atomic_boolean() {
    loom_model(|| {
    loom::model(|| {
        let flag = Arc::new(AtomicBool::new(false));
        let flag_clone1 = flag.clone();
        let flag_clone2 = flag.clone();
        
        let t1 = thread::spawn(move || {
            flag_clone1.store(true, Ordering::SeqCst);
        });
        
        let t2 = thread::spawn(move || {
            while !flag_clone2.load(Ordering::SeqCst) {
                // 忙等待 / Busy wait
            }
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
        
        assert!(flag.load(Ordering::SeqCst));
    });
    });
}

/// 测试互斥锁 / Test mutex
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_mutex() {
    loom_model(|| {
    loom::model(|| {
        let data = Arc::new(Mutex::new(0));
        let data_clone1 = data.clone();
        let data_clone2 = data.clone();
        
        let t1 = thread::spawn(move || {
            let mut value = data_clone1.lock().unwrap();
            *value += 1;
        });
        
        let t2 = thread::spawn(move || {
            let mut value = data_clone2.lock().unwrap();
            *value += 1;
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
        
        assert_eq!(*data.lock().unwrap(), 2);
    });
    });
}

/// 测试条件变量 / Test condition variable
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_condition_variable() {
    loom_model(|| {
    loom::model(|| {
        let pair = Arc::new((Mutex::new(false), Condvar::new()));
        let pair_clone = pair.clone();
        
        let t1 = thread::spawn(move || {
            let (lock, cvar) = &*pair_clone;
            let mut started = lock.lock().unwrap();
            *started = true;
            cvar.notify_one();
        });
        
        let t2 = thread::spawn(move || {
            let (lock, cvar) = &*pair;
            let mut started = lock.lock().unwrap();
            while !*started {
                started = cvar.wait(started).unwrap();
            }
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
    });
    });
}

/// 测试生产者-消费者模式 / Test producer-consumer pattern
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_producer_consumer() {
    loom_model(|| {
    loom::model(|| {
        let (tx, rx) = mpsc::channel();
        let tx_clone = tx.clone();
        
        let producer = thread::spawn(move || {
            for i in 0..10 {
                tx_clone.send(i).unwrap();
            }
        });
        
        let consumer = thread::spawn(move || {
            let mut received = 0;
            while let Ok(_) = rx.recv() {
                received += 1;
            }
            received
        });
        
        producer.join().unwrap();
        let received = consumer.join().unwrap();
        
        assert_eq!(received, 10);
    });
    });
}

/// 测试有界通道 / Test bounded channel
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_bounded_channel() {
    loom_model(|| {
    loom::model(|| {
        let (tx, rx) = mpsc::sync_channel(2);
        let tx_clone = tx.clone();
        
        let producer = thread::spawn(move || {
            for i in 0..5 {
                tx_clone.send(i).unwrap();
            }
        });
        
        let consumer = thread::spawn(move || {
            let mut received = 0;
            while let Ok(_) = rx.recv() {
                received += 1;
            }
            received
        });
        
        producer.join().unwrap();
        let received = consumer.join().unwrap();
        
        assert_eq!(received, 5);
    });
    });
}

/// 测试读写锁 / Test read-write lock
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_rwlock() {
    loom_model(|| {
    loom::model(|| {
        use loom::sync::RwLock;
        
        let data = Arc::new(RwLock::new(0));
        let data_clone = data.clone();
        
        let reader = thread::spawn(move || {
            let value = data_clone.read().unwrap();
            *value
        });
        
        let writer = thread::spawn(move || {
            let mut value = data.write().unwrap();
            *value += 1;
        });
        
        writer.join().unwrap();
        let read_value = reader.join().unwrap();
        
        assert_eq!(read_value, 1);
    });
    });
}

/// 测试屏障 / Test barrier
/// 在 Windows 上 loom Barrier 状态空间探索易导致栈溢出，暂时忽略
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom Barrier causes stack overflow on Windows")]
fn test_barrier() {
    loom_model(|| {
    loom::model(|| {
        use loom::sync::Barrier;
        
        let barrier = Arc::new(Barrier::new(2));
        let barrier_clone = barrier.clone();
        
        let t1 = thread::spawn(move || {
            barrier_clone.wait();
        });
        
        let t2 = thread::spawn(move || {
            barrier.wait();
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
    });
    });
}

/// 测试信号量 / Test semaphore
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_semaphore() {
    loom_model(|| {
    loom::model(|| {
        // 使用原子计数器模拟信号量 / Use atomic counter to simulate semaphore
        let semaphore = Arc::new(AtomicUsize::new(2));
        let semaphore_clone1 = semaphore.clone();
        let semaphore_clone2 = semaphore.clone();
        
        let t1 = thread::spawn(move || {
            // 获取许可 / Acquire permit
            while semaphore_clone1.compare_exchange(2, 1, Ordering::SeqCst, Ordering::SeqCst).is_err() {
                // 忙等待 / Busy wait
            }
            // 模拟工作 / Simulate work
            // 释放许可 / Release permit
            semaphore_clone1.fetch_add(1, Ordering::SeqCst);
        });
        
        let t2 = thread::spawn(move || {
            // 获取许可 / Acquire permit
            while semaphore_clone2.compare_exchange(1, 0, Ordering::SeqCst, Ordering::SeqCst).is_err() {
                // 忙等待 / Busy wait
            }
            // 模拟工作 / Simulate work
            // 释放许可 / Release permit
            semaphore_clone2.fetch_add(1, Ordering::SeqCst);
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
    });
    });
}

/// 测试复杂的并发场景 / Test complex concurrency scenario
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_complex_concurrency() {
    loom_model(|| {
    loom::model(|| {
        let shared_data = Arc::new(Mutex::new(Vec::new()));
        let counter = Arc::new(AtomicUsize::new(0));
        let done = Arc::new(AtomicBool::new(false));
        
        let mut handles = vec![];
        
        // 启动多个生产者 / Start multiple producers
        for i in 0..3 {
            let data_clone = shared_data.clone();
            let counter_clone = counter.clone();
            let done_clone = done.clone();
            
            let handle = thread::spawn(move || {
                for j in 0..10 {
                    let mut data = data_clone.lock().unwrap();
                    data.push(i * 10 + j);
                    counter_clone.fetch_add(1, Ordering::SeqCst);
                }
                
                if i == 2 {
                    done_clone.store(true, Ordering::SeqCst);
                }
            });
            
            handles.push(handle);
        }
        
        // 启动消费者 / Start consumer
        let data_clone = shared_data.clone();
        let counter_clone = counter.clone();
        let done_clone = done.clone();
        
        let consumer = thread::spawn(move || {
            let mut processed = 0;
            loop {
                if done_clone.load(Ordering::SeqCst) && 
                   counter_clone.load(Ordering::SeqCst) == processed {
                    break;
                }
                
                if let Ok(mut data) = data_clone.try_lock() {
                    if let Some(item) = data.pop() {
                        processed += 1;
                        // 处理项目 / Process item
                        black_box(item);
                    }
                }
            }
            processed
        });
        
        // 等待所有线程完成 / Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }
        
        let processed = consumer.join().unwrap();
        assert_eq!(processed, 30);
    });
    });
}

/// 测试死锁检测 / Test deadlock detection
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_deadlock_prevention() {
    loom_model(|| {
    loom::model(|| {
        let lock1 = Arc::new(Mutex::new(0));
        let lock2 = Arc::new(Mutex::new(0));
        
        let lock1_clone = lock1.clone();
        let lock2_clone = lock2.clone();
        
        let t1 = thread::spawn(move || {
            let _guard1 = lock1_clone.lock().unwrap();
            let _guard2 = lock2_clone.lock().unwrap();
        });
        
        let t2 = thread::spawn(move || {
            let _guard2 = lock2.lock().unwrap();
            let _guard1 = lock1.lock().unwrap();
        });
        
        t1.join().unwrap();
        t2.join().unwrap();
    });
    });
}

/// 测试内存顺序 / Test memory ordering
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_memory_ordering() {
    loom_model(|| {
    loom::model(|| {
        let data = Arc::new(AtomicUsize::new(0));
        let ready = Arc::new(AtomicBool::new(false));
        
        let data_clone = data.clone();
        let ready_clone = ready.clone();
        
        let writer = thread::spawn(move || {
            data_clone.store(42, Ordering::Release);
            ready_clone.store(true, Ordering::Release);
        });
        
        let reader = thread::spawn(move || {
            while !ready.load(Ordering::Acquire) {
                // 忙等待 / Busy wait
            }
            data.load(Ordering::Acquire)
        });
        
        writer.join().unwrap();
        let value = reader.join().unwrap();
        
        assert_eq!(value, 42);
    });
    });
}

/// 测试取消机制 / Test cancellation mechanism
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_cancellation() {
    loom_model(|| {
    loom::model(|| {
        let cancelled = Arc::new(AtomicBool::new(false));
        let cancelled_clone = cancelled.clone();
        
        let worker = thread::spawn(move || {
            let mut work_count = 0;
            while !cancelled_clone.load(Ordering::SeqCst) {
                work_count += 1;
                if work_count > 1000 {
                    break; // 防止无限循环 / Prevent infinite loop
                }
            }
            work_count
        });
        
        // 模拟取消 / Simulate cancellation
        cancelled.store(true, Ordering::SeqCst);
        
        let work_count = worker.join().unwrap();
        assert!(work_count > 0);
    });
    });
}

/// 测试超时机制 / Test timeout mechanism
#[test]
#[cfg_attr(target_os = "windows", ignore = "loom stack overflow on Windows")]
fn test_timeout() {
    loom_model(|| {
    loom::model(|| {
        let data = Arc::new(Mutex::new(0));
        let data_clone = data.clone();
        
        let worker = thread::spawn(move || {
            let _guard = data_clone.lock().unwrap();
            // 模拟长时间工作 / Simulate long work
            // 在 loom 中，我们使用 yield_now 而不是 sleep
            for _ in 0..100 {
                thread::yield_now();
            }
        });
        
        // 尝试获取锁，但设置超时 / Try to acquire lock with timeout
        let _result = data.try_lock();
        
        worker.join().unwrap();
        
        // 超时后应该能够获取锁 / Should be able to acquire lock after timeout
        let _guard = data.lock().unwrap();
    });
    });
}

/// 辅助函数：黑盒 / Helper function: black box
fn black_box<T>(x: T) -> T {
    x
}
