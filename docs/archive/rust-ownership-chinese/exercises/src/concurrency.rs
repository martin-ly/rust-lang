//! 并发所有权模式
//!
//! 展示Rust在并发环境下的所有权管理

use std::sync::{Arc, Mutex, RwLock, mpsc};
use std::thread;
use std::time::Duration;

// ============================================
// Send与Sync基础
// ============================================

/// Send: 值可以在线程间转移所有权
/// Sync: 值可以在多个线程间共享引用（&T是Send）
///
/// # 形式语义
/// - T: Send ⟺ 所有权可跨线程转移
/// - T: Sync ⟺ &T: Send ⟺ 可安全多线程共享

#[derive(Debug)]
pub struct MyData {
    value: i32,
    name: String,
}
// MyData自动实现Send+Sync

/// 使用Arc替代Rc
pub fn arc_is_send() {
    let data = Arc::new(42);
    let data2 = Arc::clone(&data);
    
    thread::spawn(move || {
        println!("{}", data2);
    });
    
    println!("{}", data);
}

// ============================================
// 共享可变状态模式
// ============================================

pub struct SharedState {
    counter: i32,
    data: Vec<String>,
}

pub fn shared_mutable_state() {
    let state = Arc::new(Mutex::new(SharedState {
        counter: 0,
        data: vec![],
    }));
    
    let mut handles = vec![];
    
    for i in 0..5 {
        let state = Arc::clone(&state);
        let handle = thread::spawn(move || {
            let mut guard = state.lock().unwrap();
            guard.counter += 1;
            guard.data.push(format!("Thread {}", i));
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let final_state = state.lock().unwrap();
    println!("Counter: {}", final_state.counter);
}

/// 读写锁模式 - 读多写少场景
pub fn rwlock_pattern() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));
    
    let mut readers = vec![];
    for _ in 0..3 {
        let data = Arc::clone(&data);
        readers.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("Read: {:?}", *read_guard);
        }));
    }
    
    let data_writer = Arc::clone(&data);
    let writer = thread::spawn(move || {
        let mut write_guard = data_writer.write().unwrap();
        write_guard.push(6);
        println!("Written");
    });
    
    for r in readers {
        r.join().unwrap();
    }
    writer.join().unwrap();
}

// ============================================
// 消息传递模式
// ============================================

pub fn message_passing() {
    let (tx, rx) = mpsc::channel();
    
    thread::spawn(move || {
        for i in 0..5 {
            tx.send(format!("Message {}", i)).unwrap();
            thread::sleep(Duration::from_millis(10));
        }
    });
    
    for received in rx {
        println!("Received: {}", received);
    }
}

/// 多生产者单消费者
pub fn mpmc_pattern() {
    let (tx, rx) = mpsc::channel();
    
    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for j in 0..3 {
                tx.send((i, j)).unwrap();
            }
        });
    }
    
    drop(tx); // 关闭原始发送端
    
    for received in rx {
        println!("Received: {:?}", received);
    }
}

// ============================================
// 作用域线程
// ============================================

pub fn scoped_thread_pattern() {
    let data = vec![1, 2, 3, 4, 5];
    
    thread::scope(|s| {
        s.spawn(|| {
            println!("{:?}", &data);
        });
        s.spawn(|| {
            println!("Sum: {}", data.iter().sum::<i32>());
        });
    }); // 保证join
}

// ============================================
// 锁模式
// ============================================

/// 细粒度锁
pub struct FineGrainedCache {
    data: Vec<Mutex<String>>,
}

impl FineGrainedCache {
    pub fn new(size: usize) -> Self {
        let mut data = Vec::with_capacity(size);
        for _ in 0..size {
            data.push(Mutex::new(String::new()));
        }
        Self { data }
    }
    
    pub fn get(&self, idx: usize) -> Option<std::sync::MutexGuard<String>> {
        self.data.get(idx).map(|m| m.lock().unwrap())
    }
}

/// 死锁避免 - 锁顺序
pub fn deadlock_avoidance() {
    let lock1 = Arc::new(Mutex::new(1));
    let lock2 = Arc::new(Mutex::new(2));
    
    // 总是按相同顺序获取锁
    let t1 = {
        let (l1, l2) = (Arc::clone(&lock1), Arc::clone(&lock2));
        thread::spawn(move || {
            let _a = l1.lock().unwrap();
            let _b = l2.lock().unwrap();
            println!("Thread 1 acquired both locks");
        })
    };
    
    let t2 = {
        let (l1, l2) = (Arc::clone(&lock1), Arc::clone(&lock2));
        thread::spawn(move || {
            let _a = l1.lock().unwrap(); // 相同顺序
            let _b = l2.lock().unwrap();
            println!("Thread 2 acquired both locks");
        })
    };
    
    t1.join().unwrap();
    t2.join().unwrap();
}

// ============================================
// 测试
// ============================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_arc_send() {
        arc_is_send();
    }
    
    #[test]
    fn test_scoped_threads() {
        scoped_thread_pattern();
    }
    
    #[test]
    fn test_deadlock_avoidance() {
        deadlock_avoidance();
    }
}
