//! 所有权和借用作用域模块并发安全测试套件 / Ownership and Borrowing Scope Module Concurrent Safety Test Suite

use c01_ownership_borrow_scope::scope::{ScopeManager, ScopeType};
use std::sync::{Arc, Mutex};
use std::thread;

/// 测试共享状态并发安全
#[test]
fn test_shared_state_safety() {
    let manager = Arc::new(Mutex::new(ScopeManager::new()));
    let mut handles = vec![];

    // 创建多个线程同时操作作用域管理器
    for i in 0..10 {
        let manager = Arc::clone(&manager);
        let handle = thread::spawn(move || {
            let mut mgr = manager.lock().unwrap();
            let scope_name = format!("thread_{}", i);
            mgr.enter_scope(scope_name, ScopeType::Block).unwrap();
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证所有作用域都已创建
    let mgr = manager.lock().unwrap();
    assert_eq!(mgr.get_scope_depth(), 10);
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
    let manager = Arc::new(Mutex::new(ScopeManager::new()));
    let mut handles = vec![];

    // 创建多个线程同时操作
    for i in 0..50 {
        let manager = Arc::clone(&manager);
        let handle = thread::spawn(move || {
            let mut mgr = manager.lock().unwrap();
            let scope_name = format!("scope_{}", i);
            mgr.enter_scope(scope_name, ScopeType::Block).unwrap();
            mgr.add_variable(format!("var_{}", i)).unwrap();
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    // 验证内存安全（没有崩溃）
    let mgr = manager.lock().unwrap();
    assert_eq!(mgr.get_scope_depth(), 50);
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
