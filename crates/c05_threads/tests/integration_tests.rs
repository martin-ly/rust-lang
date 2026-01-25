//! 线程模块集成测试套件 / Threads Module Integration Test Suite

use std::sync::{Arc, Mutex};
use std::thread;

/// 测试线程创建集成
#[test]
fn test_thread_creation_integration() {
    let handle = thread::spawn(|| {
        "Hello from thread"
    });
    
    let result = handle.join().unwrap();
    assert_eq!(result, "Hello from thread");
}

/// 测试线程间通信集成
#[test]
fn test_thread_communication_integration() {
    let shared = Arc::new(Mutex::new(0));
    let shared_clone = Arc::clone(&shared);
    
    let handle = thread::spawn(move || {
        let mut value = shared_clone.lock().unwrap();
        *value += 1;
    });
    
    handle.join().unwrap();
    assert_eq!(*shared.lock().unwrap(), 1);
}

/// 测试多线程协作集成
#[test]
fn test_multithreaded_cooperation_integration() {
    let shared = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let shared = Arc::clone(&shared);
        let handle = thread::spawn(move || {
            let mut value = shared.lock().unwrap();
            *value += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(*shared.lock().unwrap(), 10);
}

/// 测试线程同步集成
#[test]
fn test_thread_synchronization_integration() {
    use std::sync::Barrier;
    
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for _ in 0..3 {
        let barrier = Arc::clone(&barrier);
        let handle = thread::spawn(move || {
            barrier.wait();
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
    
    assert!(true); // 所有线程都已同步
}

/// 测试原子操作集成
#[test]
fn test_atomic_operations_integration() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            counter.fetch_add(1, Ordering::SeqCst);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    assert_eq!(counter.load(Ordering::SeqCst), 10);
}

/// 测试线程本地存储集成
#[test]
fn test_thread_local_storage_integration() {
    use std::cell::RefCell;
    use std::thread_local;
    
    thread_local! {
        static COUNTER: RefCell<usize> = RefCell::new(0);
    }
    
    COUNTER.with(|c| {
        *c.borrow_mut() += 1;
    });
    
    COUNTER.with(|c| {
        assert_eq!(*c.borrow(), 1);
    });
}
