//! Mutex 同步模块
//!
//! 本模块演示Rust中Mutex的使用，包括：
//! - 基本Mutex使用
//! - 多线程共享状态
//! - 死锁预防
//! - 性能优化技巧

use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 基本Mutex使用示例
pub fn basic_mutex_usage() {
    println!("🔒 基本Mutex使用示例");

    let counter = Arc::new(Mutex::new(0));
    let mut handles = Vec::new();

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
            println!("  线程增加计数器到: {}", *num);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("  最终计数器值: {}", *counter.lock().unwrap());
}

/// 共享复杂数据结构
pub fn shared_complex_data() {
    println!("🔒 共享复杂数据结构示例");

    #[derive(Debug)]
    struct SharedData {
        users: Vec<String>,
        count: usize,
        #[allow(dead_code)]
        active: bool,
    }

    let shared_data = Arc::new(Mutex::new(SharedData {
        users: Vec::new(),
        count: 0,
        active: true,
    }));

    let mut handles = Vec::new();

    // 生产者线程
    for i in 0..3 {
        let data = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            let mut data = data.lock().unwrap();
            let user_name = format!("用户-{}", i);
            data.users.push(user_name);
            data.count += 1;
            println!("  添加用户，当前总数: {}", data.count);
        });
        handles.push(handle);
    }

    // 消费者线程
    for _ in 0..2 {
        let data = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            let data = data.lock().unwrap();
            println!("  读取数据: {:?}", *data);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let final_data = shared_data.lock().unwrap();
    println!("  最终数据: {:?}", *final_data);
}

/// 死锁预防示例
pub fn deadlock_prevention() {
    println!("🔒 死锁预防示例");

    let resource_a = Arc::new(Mutex::new(0));
    let resource_b = Arc::new(Mutex::new(0));

    // 正确的顺序：总是先锁A，再锁B
    let resource_a1 = Arc::clone(&resource_a);
    let resource_b1 = Arc::clone(&resource_b);
    let handle1 = thread::spawn(move || {
        let mut a = resource_a1.lock().unwrap();
        thread::sleep(Duration::from_millis(10)); // 模拟工作
        let mut b = resource_b1.lock().unwrap();

        *a += 1;
        *b += 1;
        println!("  线程1: A={}, B={}", *a, *b);
    });

    let resource_a2 = Arc::clone(&resource_a);
    let resource_b2 = Arc::clone(&resource_b);
    let handle2 = thread::spawn(move || {
        let mut a = resource_a2.lock().unwrap();
        thread::sleep(Duration::from_millis(10)); // 模拟工作
        let mut b = resource_b2.lock().unwrap();

        *a += 1;
        *b += 1;
        println!("  线程2: A={}, B={}", *a, *b);
    });

    handle1.join().unwrap();
    handle2.join().unwrap();

    println!("  死锁预防成功！");
}

/// 使用try_lock避免阻塞
pub fn try_lock_example() {
    println!("🔒 try_lock示例");

    let data = Arc::new(Mutex::new(42));
    let mut handles = Vec::new();

    for i in 0..5 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            // 尝试获取锁，如果失败则跳过
            if let Ok(mut value) = data.try_lock() {
                *value += i;
                println!("  线程{}成功获取锁，值: {}", i, *value);
                thread::sleep(Duration::from_millis(50));
            } else {
                println!("  线程{}无法获取锁，跳过", i);
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("  最终值: {}", *data.lock().unwrap());
}

/// 条件变量与Mutex结合使用
pub fn mutex_with_condition() {
    println!("🔒 Mutex与条件变量结合示例");

    use std::sync::Condvar;

    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let (lock, cvar) = &*pair;

    let pair_clone = Arc::clone(&pair);
    let (_lock_clone, _cvar_clone) = &*pair_clone;

    // 等待线程
    let waiter = thread::spawn(move || {
        let (lock, cvar) = &*pair_clone;
        let mut started = lock.lock().unwrap();
        while !*started {
            started = cvar.wait(started).unwrap();
        }
        println!("  等待线程被唤醒！");
    });

    // 通知线程
    thread::sleep(Duration::from_millis(100));
    {
        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();
        println!("  通知线程发送信号");
    }

    waiter.join().unwrap();
}

/// 性能优化：减少锁的持有时间
pub fn lock_optimization() {
    println!("🔒 锁优化示例");

    let data = Arc::new(Mutex::new(vec![0; 1000]));

    // 不好的做法：长时间持有锁
    let bad_handle = thread::spawn({
        let data = Arc::clone(&data);
        move || {
            let mut data = data.lock().unwrap();
            // 模拟长时间操作
            for i in 0..1000 {
                data[i] = i * 2;
                thread::sleep(Duration::from_micros(1));
            }
            println!("  不好的做法：长时间持有锁完成");
        }
    });

    // 好的做法：最小化锁持有时间
    let good_handle = thread::spawn({
        let data = Arc::clone(&data);
        move || {
            // 在锁外准备数据
            let mut temp_data = Vec::new();
            for i in 0..1000 {
                temp_data.push(i * 3);
                thread::sleep(Duration::from_micros(1));
            }

            // 只在需要时短暂持有锁
            {
                let mut data = data.lock().unwrap();
                for (i, &value) in temp_data.iter().enumerate() {
                    data[i] = value;
                }
            }
            println!("  好的做法：最小化锁持有时间完成");
        }
    });

    bad_handle.join().unwrap();
    good_handle.join().unwrap();
}

/// 自定义Mutex包装器
pub fn custom_mutex_wrapper() {
    println!("🔒 自定义Mutex包装器示例");

    use std::sync::atomic::{AtomicBool, Ordering};

    pub struct SmartMutex<T> {
        data: Mutex<T>,
        locked: AtomicBool,
    }

    impl<T> SmartMutex<T> {
        pub fn new(data: T) -> Self {
            Self {
                data: Mutex::new(data),
                locked: AtomicBool::new(false),
            }
        }

        pub fn lock(&self) -> std::sync::MutexGuard<'_, T> {
            self.locked.store(true, Ordering::SeqCst);
            self.data.lock().unwrap()
        }

        pub fn unlock(&self) {
            self.locked.store(false, Ordering::SeqCst);
        }

        pub fn is_locked(&self) -> bool {
            self.locked.load(Ordering::SeqCst)
        }
    }

    let smart_mutex = Arc::new(SmartMutex::new(42));

    let handle = thread::spawn({
        let smart_mutex = Arc::clone(&smart_mutex);
        move || {
            println!("  锁状态: {}", smart_mutex.is_locked());
            let value = smart_mutex.lock();
            println!("  锁状态: {}", smart_mutex.is_locked());
            println!("  值: {}", *value);
            smart_mutex.unlock();
            println!("  锁状态: {}", smart_mutex.is_locked());
        }
    });

    handle.join().unwrap();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_mutex_usage() {
        basic_mutex_usage();
    }

    #[test]
    fn test_shared_complex_data() {
        shared_complex_data();
    }

    #[test]
    fn test_deadlock_prevention() {
        deadlock_prevention();
    }

    #[test]
    fn test_try_lock_example() {
        try_lock_example();
    }

    #[test]
    fn test_mutex_with_condition() {
        mutex_with_condition();
    }

    #[test]
    fn test_lock_optimization() {
        lock_optimization();
    }

    #[test]
    fn test_custom_mutex_wrapper() {
        custom_mutex_wrapper();
    }
}
