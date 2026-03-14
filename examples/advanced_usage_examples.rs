//! 高级用法示例集合
//!
//! 本文件包含各种高级Rust用法示例，展示实际应用场景
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 高级所有权模式示例
pub fn advanced_ownership_example() {
    println!("📦 高级所有权模式示例");

    use std::rc::Rc;
    use std::sync::Arc;

    // 使用Rc实现单线程引用计数
    let rc_data = Rc::new(42);
    let rc_clone1 = Rc::clone(&rc_data);
    let rc_clone2 = Rc::clone(&rc_data);
    println!("  - Rc引用计数: {}", Rc::strong_count(&rc_data));

    // 使用Arc实现多线程引用计数
    let arc_data = Arc::new(42);
    let arc_clone = Arc::clone(&arc_data);
    println!("  - Arc引用计数: {}", Arc::strong_count(&arc_data));
}

/// 高级并发模式示例
pub fn advanced_concurrency_example() {
    println!("\n⚡ 高级并发模式示例");

    use std::sync::atomic::{AtomicUsize, Ordering};

    // 使用原子操作实现无锁计数器
    let counter = AtomicUsize::new(0);
    counter.fetch_add(1, Ordering::SeqCst);
    println!("  - 原子计数器值: {}", counter.load(Ordering::SeqCst));

    // 使用Barrier实现线程同步
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
    println!("  - 所有线程已同步");
}

/// 高级错误处理示例
pub fn advanced_error_handling_example() {
    println!("\n🛡️ 高级错误处理示例");

    // 使用Result进行错误处理
    fn divide(a: i32, b: i32) -> Result<i32, String> {
        if b == 0 {
            Err("Division by zero".to_string())
        } else {
            Ok(a / b)
        }
    }

    match divide(10, 2) {
        Ok(result) => println!("  - 除法结果: {}", result),
        Err(e) => println!("  - 错误: {}", e),
    }

    // 使用?操作符传播错误
    fn process() -> Result<i32, String> {
        let result = divide(10, 2)?;
        Ok(result * 2)
    }

    match process() {
        Ok(result) => println!("  - 处理结果: {}", result),
        Err(e) => println!("  - 错误: {}", e),
    }
}

/// 高级类型系统示例
pub fn advanced_type_system_example() {
    println!("\n🔧 高级类型系统示例");

    // 使用关联类型
    trait Container {
        type Item;
        fn get(&self) -> Self::Item;
    }

    struct IntContainer(i32);

    impl Container for IntContainer {
        type Item = i32;
        fn get(&self) -> Self::Item {
            self.0
        }
    }

    let container = IntContainer(42);
    println!("  - 容器值: {}", container.get());

    // 使用泛型约束
    fn process<T: Clone + std::fmt::Display>(item: T) -> T {
        println!("  - 处理项: {}", item);
        item.clone()
    }

    let result = process(42);
    println!("  - 处理结果: {}", result);
}

/// 高级性能优化示例
pub fn advanced_performance_example() {
    println!("\n⚡ 高级性能优化示例");

    use std::time::Instant;

    // 预分配容量
    let start = Instant::now();
    let mut vec = Vec::with_capacity(1000);
    for i in 0..1000 {
        vec.push(i);
    }
    let duration = start.elapsed();
    println!("  - 预分配向量耗时: {:?}", duration);

    // 使用迭代器链式操作
    let start = Instant::now();
    let sum: i32 = (0..1000)
        .filter(|&x| x % 2 == 0)
        .map(|x| x * 2)
        .sum();
    let duration = start.elapsed();
    println!("  - 迭代器链式操作耗时: {:?}", duration);
    println!("  - 结果: {}", sum);
}

/// Rust 1.94 特性示例
pub fn rust_194_features_example() {
    println!("\n🆕 Rust 1.94 特性示例");

    // array_windows 示例
    let data = [1, 2, 3, 4, 5];
    let sums: Vec<i32> = data.array_windows::<2>()
        .map(|&[a, b]| a + b)
        .collect();
    println!("  - array_windows 结果: {:?}", sums);

    // ControlFlow 示例
    use std::ops::ControlFlow;
    let items = vec![1, 2, -3, 4, 5];
    let result = items.iter().try_for_each(|&n| {
        if n < 0 { ControlFlow::Break(n) }
        else { ControlFlow::Continue(()) }
    });
    println!("  - ControlFlow 结果: {:?}", result.break_value());

    // 数学常量示例
    println!("  - 欧拉常数: {}", std::f64::consts::EULER_GAMMA);
    println!("  - 黄金比例: {}", std::f64::consts::GOLDEN_RATIO);
}

/// 主函数
fn main() {
    println!("🚀 Rust 高级用法示例集合");
    println!("======================\n");

    advanced_ownership_example();
    advanced_concurrency_example();
    advanced_error_handling_example();
    advanced_type_system_example();
    advanced_performance_example();
    rust_194_features_example();

    println!("\n✅ 所有高级用法示例完成！");
}
