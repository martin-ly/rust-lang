use std::sync::{Arc, Mutex};
use std::thread;

#[allow(unused)]
pub fn count_test() {
    // 创建一个 Arc 包裹的 Mutex，内部数据为 0
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        // 克隆 Arc，以便在多个线程中共享
        let counter_clone = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            // 锁定 Mutex，获取对数据的可变引用
            let mut num = counter_clone.lock().unwrap();
            *num += 1; // 增加计数器的值
        });
        handles.push(handle);
    }

    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }

    // 打印最终计数器的值
    println!("Result: {}", *counter.lock().unwrap()); // 输出: Result: 10
}
