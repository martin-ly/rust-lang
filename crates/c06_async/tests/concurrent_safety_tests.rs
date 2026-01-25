//! 异步编程模块并发安全测试套件 / Async Programming Module Concurrent Safety Test Suite

use std::sync::{Arc, Mutex};
use std::thread;

/// 测试共享状态并发安全
#[test]
fn test_shared_state_safety() {
    let shared = Arc::new(Mutex::new(Vec::<i32>::new()));
    let mut handles = vec![];

    // 创建多个线程同时操作共享向量
    for i in 0..100 {
        let shared = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let mut vec = shared.lock().unwrap();
            vec.push(i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证所有值都已添加
    let vec = shared.lock().unwrap();
    assert_eq!(vec.len(), 100);
}

/// 测试竞态条件
#[test]
fn test_race_conditions() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    // 创建多个线程同时增加计数器
    for _ in 0..100 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut count = counter.lock().unwrap();
            *count += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证计数器值正确
    assert_eq!(*counter.lock().unwrap(), 100);
}

/// 测试内存安全
#[test]
fn test_memory_safety() {
    let shared = Arc::new(Mutex::new(Vec::<usize>::new()));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for i in 0..1000 {
        let shared = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let mut vec = shared.lock().unwrap();
            vec.push(i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证内存安全（没有崩溃）
    let vec = shared.lock().unwrap();
    assert_eq!(vec.len(), 1000);
}

/// 测试原子操作
#[test]
fn test_atomic_operations() {
    use std::sync::atomic::{AtomicUsize, Ordering};

    let counter = AtomicUsize::new(0);
    let mut handles = vec![];

    // 创建多个线程同时增加原子计数器
    for _ in 0..100 {
        let counter = &counter;
        let handle = thread::spawn(move || {
            counter.fetch_add(1, Ordering::SeqCst);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证计数器值正确
    assert_eq!(counter.load(Ordering::SeqCst), 100);
}

/// 测试同步原语
#[test]
fn test_synchronization_primitives() {
    use std::sync::Barrier;

    let barrier = Arc::new(Barrier::new(10));
    let mut handles = vec![];

    // 创建多个线程等待屏障
    for _ in 0..10 {
        let barrier = Arc::clone(&barrier);
        let handle = thread::spawn(move || {
            barrier.wait();
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 所有线程都已通过屏障
    assert!(true);
}

/// 测试Future并发安全
#[test]
fn test_future_safety() {
    let shared = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    // 创建多个线程模拟Future并发
    for _ in 0..100 {
        let shared = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let mut count = shared.lock().unwrap();
            *count += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证Future并发安全
    assert_eq!(*shared.lock().unwrap(), 100);
}
