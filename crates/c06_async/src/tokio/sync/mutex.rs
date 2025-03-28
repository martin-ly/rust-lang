
use tokio::sync::Mutex;
use std::sync::Arc;

#[allow(unused)]
pub async fn mutex_test01() {
    // 创建一个 Arc 包裹的 Mutex，内部数据为 0
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        // 克隆 Arc，以便在多个任务中共享
        let counter_clone = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            // 锁定 Mutex，获取对数据的可变引用
            let mut num = counter_clone.lock().await;
            *num += 1; // 增加计数器
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await.unwrap();
    }

    // 打印最终计数器的值
    println!("Result: {}", *counter.lock().await); // 输出: Result: 10
}
