//! 并发所有权专项测试
//!
//! 测试Rust并发编程中的所有权管理

use std::sync::{Arc, Mutex, RwLock, atomic::{AtomicUsize, Ordering}};
use std::thread;

// ============================================
// Send 和 Sync 基础
// ============================================

#[test]
fn test_arc_send_sync() {
    let data = Arc::new(vec![1, 2, 3]);
    let mut handles = vec![];
    
    for i in 0..5 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            assert_eq!(data[i], i + 1);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

#[test]
fn test_mutex_thread_safety() {
    let counter = Arc::new(Mutex::new(0usize));
    let mut handles = vec![];
    
    for _ in 0..100 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    assert_eq!(*counter.lock().unwrap(), 100);
}

#[test]
fn test_rwlock_multiple_readers() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));
    let mut handles = vec![];
    
    // 多个读线程
    for _ in 0..10 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            assert_eq!(read_guard.len(), 3);
        }));
    }
    
    // 一个写线程
    let data_write = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        let mut write_guard = data_write.write().unwrap();
        write_guard.push(4);
    }));
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    assert_eq!(data.read().unwrap().len(), 4);
}

// ============================================
// 作用域线程
// ============================================

#[test]
fn test_scoped_threads() {
    let data = vec![1, 2, 3, 4, 5];
    
    thread::scope(|s| {
        s.spawn(|| {
            let sum: i32 = data.iter().sum();
            assert_eq!(sum, 15);
        });
        
        s.spawn(|| {
            let first = data.first().unwrap();
            assert_eq!(*first, 1);
        });
    });  // 自动等待所有线程完成
    
    // data 仍然有效
    assert_eq!(data.len(), 5);
}

// ============================================
// 消息传递
// ============================================

#[test]
fn test_channel_ownership() {
    use std::sync::mpsc;
    
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        let data = String::from("hello from thread");
        tx.send(data).unwrap();
        // data 的所有权已转移，不能再使用
    });
    
    let received = rx.recv().unwrap();
    assert_eq!(received, "hello from thread");
}

#[test]
fn test_multiple_producers() {
    use std::sync::mpsc;
    
    let (tx, rx) = mpsc::channel();
    let mut handles = vec![];
    
    for i in 0..5 {
        let tx = tx.clone();
        handles.push(thread::spawn(move || {
            tx.send(i).unwrap();
        }));
    }
    
    // 关闭原始发送端
    drop(tx);
    
    let mut received = vec![];
    for msg in rx {
        received.push(msg);
    }
    
    received.sort();
    assert_eq!(received, vec![0, 1, 2, 3, 4]);
}

// ============================================
// 原子操作
// ============================================

#[test]
fn test_atomic_counter() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            for _ in 0..100 {
                counter.fetch_add(1, Ordering::Relaxed);
            }
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    assert_eq!(counter.load(Ordering::Relaxed), 1000);
}

// ============================================
// 死锁避免
// ============================================

#[test]
fn test_lock_ordering() {
    let lock1 = Arc::new(Mutex::new(1));
    let lock2 = Arc::new(Mutex::new(2));
    
    let t1 = {
        let (l1, l2) = (Arc::clone(&lock1), Arc::clone(&lock2));
        thread::spawn(move || {
            let _a = l1.lock().unwrap();
            thread::sleep(std::time::Duration::from_millis(10));
            let _b = l2.lock().unwrap();
        })
    };
    
    let t2 = {
        let (l1, l2) = (Arc::clone(&lock1), Arc::clone(&lock2));
        // 相同顺序获取锁，避免死锁
        thread::spawn(move || {
            let _a = l1.lock().unwrap();
            thread::sleep(std::time::Duration::from_millis(10));
            let _b = l2.lock().unwrap();
        })
    };
    
    t1.join().unwrap();
    t2.join().unwrap();
}

// ============================================
// 细粒度锁
// ============================================

#[test]
fn test_fine_grained_locks() {
    use std::sync::Mutex;
    
    let data: Vec<Mutex<i32>> = (0..10).map(|_| Mutex::new(0)).collect();
    let data = Arc::new(data);
    let mut handles = vec![];
    
    for i in 0..10 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut guard = data[i].lock().unwrap();
            *guard += i as i32;
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let sum: i32 = data.iter().map(|m| *m.lock().unwrap()).sum();
    assert_eq!(sum, 45);  // 0+1+2+...+9
}

// ============================================
// 线程局部存储
// ============================================

#[test]
fn test_thread_local() {
    use std::cell::Cell;
    
    thread_local! {
        static COUNTER: Cell<u32> = Cell::new(0);
    }
    
    COUNTER.with(|c| c.set(1));
    
    let handle = thread::spawn(|| {
        COUNTER.with(|c| {
            assert_eq!(c.get(), 0);  // 新线程，初始值
            c.set(2);
        });
    });
    
    handle.join().unwrap();
    
    COUNTER.with(|c| {
        assert_eq!(c.get(), 1);  // 原线程的值不受影响
    });
}

// ============================================
// 栅栏
// ============================================

#[test]
fn test_barrier() {
    use std::sync::Barrier;
    
    let barrier = Arc::new(Barrier::new(5));
    let mut handles = vec![];
    
    for i in 0..5 {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("Thread {} before barrier", i);
            b.wait();
            println!("Thread {} after barrier", i);
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
