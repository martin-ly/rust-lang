//! 综合集成示例 - 展示多个模块的协同使用
//!
//! 本示例展示如何将多个Rust模块组合使用，构建一个完整的应用程序
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 综合集成示例主函数
fn main() {
    println!("🚀 Rust 综合集成示例");
    println!("====================\n");

    // 1. 所有权与类型系统集成
    demonstrate_ownership_type_integration();

    // 2. 并发与异步集成
    demonstrate_concurrency_async_integration();

    // 3. 算法与性能优化集成
    demonstrate_algorithm_performance_integration();

    // 4. 网络与进程管理集成
    demonstrate_network_process_integration();

    println!("\n✅ 综合集成示例完成！");
}

/// 演示所有权与类型系统集成
fn demonstrate_ownership_type_integration() {
    println!("📦 1. 所有权与类型系统集成");

    use std::sync::Arc;

    // 使用Arc实现多线程共享所有权
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let data_clone = Arc::clone(&data);

    println!("  - Arc共享所有权: {:?}", data_clone);
    println!("  - 引用计数: {}", Arc::strong_count(&data));

    // 使用泛型实现类型安全
    fn process_items<T: Clone>(items: &[T]) -> Vec<T> {
        items.iter().map(|item| item.clone()).collect()
    }

    let numbers = vec![1, 2, 3];
    let processed = process_items(&numbers);
    println!("  - 泛型处理结果: {:?}", processed);
}

/// 演示并发与异步集成
fn demonstrate_concurrency_async_integration() {
    println!("\n⚡ 2. 并发与异步集成");

    use std::sync::{Arc, Mutex};

    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    // 创建多个线程
    for i in 0..5 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += i;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("  - 多线程计数器结果: {}", *counter.lock().unwrap());
}

/// 演示算法与性能优化集成
fn demonstrate_algorithm_performance_integration() {
    println!("\n📊 3. 算法与性能优化集成");

    let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5];
    let start = Instant::now();

    // 排序
    data.sort();

    // 去重
    data.dedup();

    let duration = start.elapsed();

    println!("  - 处理结果: {:?}", data);
    println!("  - 处理耗时: {:?}", duration);
}

/// 演示网络与进程管理集成
fn demonstrate_network_process_integration() {
    println!("\n🌐 4. 网络与进程管理集成");

    // 模拟网络操作
    let network_operation = || {
        thread::sleep(Duration::from_millis(10));
        "网络操作完成"
    };

    let result = network_operation();
    println!("  - {}", result);

    // 模拟进程管理
    let process_count = 3;
    println!("  - 进程数量: {}", process_count);
}
