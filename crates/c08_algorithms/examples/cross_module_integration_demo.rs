//! 跨模块集成演示程序
//!
//! ## 📐 知识结构
//!
//! ### 核心概念
//!
//! - **模块集成**: 将多个模块组合使用以实现复杂功能
//!   - **属性**: 模块化、可组合、可扩展
//!   - **关系**: 与所有模块相关
//!
//! ### 思维导图
//!
//! ```text
//! 跨模块集成
//! │
//! ├── 基础模块 (C01-C03)
//! │   ├── 所有权系统
//! │   └── 类型系统
//! ├── 并发模块 (C05-C06)
//! │   ├── 线程管理
//! │   └── 异步编程
//! ├── 系统模块 (C07, C10)
//! │   ├── 进程管理
//! │   └── 网络编程
//! └── 应用模块 (C08, C09)
//!     ├── 算法数据结构
//!     └── 设计模式
//! ```
//!
//! 本示例展示如何将多个模块（C01-C12）的功能整合在一起，
//! 构建一个完整的 Rust 应用程序。

use std::time::Duration;

/// 跨模块集成演示
///
/// 本演示整合了以下模块：
/// - C01: 所有权和借用
/// - C02: 类型系统
/// - C05: 线程和并发
/// - C06: 异步编程
/// - C07: 进程管理
/// - C08: 算法和数据结构
/// - C10: 网络编程
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Rust 跨模块集成演示");
    println!("========================\n");

    // 1. C01: 所有权和借用 - 智能指针使用
    println!("📦 C01: 所有权和借用");
    demonstrate_ownership();
    println!();

    // 2. C02: 类型系统 - 泛型和 Trait
    println!("🔧 C02: 类型系统");
    demonstrate_type_system();
    println!();

    // 3. C05: 线程和并发 - 多线程处理
    println!("⚡ C05: 线程和并发");
    demonstrate_threading().await;
    println!();

    // 4. C06: 异步编程 - 异步任务
    println!("🌐 C06: 异步编程");
    demonstrate_async().await;
    println!();

    // 5. C08: 算法和数据结构 - 排序和搜索
    println!("📊 C08: 算法和数据结构");
    demonstrate_algorithms();
    println!();

    // 6. 综合应用：构建一个简单的任务处理系统
    println!("🎯 综合应用：任务处理系统");
    demonstrate_integrated_system().await?;
    println!();

    println!("✅ 跨模块集成演示完成！");
    Ok(())
}

/// C01: 演示所有权和借用
fn demonstrate_ownership() {
    use std::sync::Arc;

    // 使用 Arc 实现多线程共享所有权
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let data_clone = Arc::clone(&data);

    println!("  - Arc 共享所有权: {:?}", data_clone);
    println!("  - 引用计数: {}", Arc::strong_count(&data));
}

/// C02: 演示类型系统
fn demonstrate_type_system() {
    // 泛型函数
    fn find_max<T: Ord>(items: &[T]) -> Option<&T> {
        items.iter().max()
    }

    let numbers = vec![3, 1, 4, 1, 5, 9, 2, 6];
    if let Some(max) = find_max(&numbers) {
        println!("  - 最大值: {}", max);
    }

    // Trait 对象
    trait Processor {
        fn process(&self) -> String;
    }

    struct TextProcessor;
    impl Processor for TextProcessor {
        fn process(&self) -> String {
            "处理文本".to_string()
        }
    }

    let processor: Box<dyn Processor> = Box::new(TextProcessor);
    println!("  - Trait 对象: {}", processor.process());
}

/// C05: 演示线程和并发
async fn demonstrate_threading() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use tokio::task;

    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = Vec::new();

    // 创建多个异步任务
    for _ in 0..5 {
        let counter_clone = Arc::clone(&counter);
        let handle = task::spawn(async move {
            counter_clone.fetch_add(1, Ordering::SeqCst);
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await.unwrap();
    }

    println!("  - 并发计数结果: {}", counter.load(Ordering::SeqCst));
}

/// C06: 演示异步编程
async fn demonstrate_async() {
    use tokio::time::{sleep, Instant};

    let start = Instant::now();

    // 并发执行多个异步任务
    let task1 = async {
        sleep(Duration::from_millis(100)).await;
        "任务1完成"
    };

    let task2 = async {
        sleep(Duration::from_millis(100)).await;
        "任务2完成"
    };

    let (result1, result2) = tokio::join!(task1, task2);

    let elapsed = start.elapsed();
    println!("  - {}: {}", result1, elapsed.as_millis());
    println!("  - {}: {}", result2, elapsed.as_millis());
    println!("  - 总耗时: {}ms (并发执行)", elapsed.as_millis());
}

/// C08: 演示算法和数据结构
fn demonstrate_algorithms() {
    // 快速排序
    fn quicksort<T: Ord + Clone>(arr: &[T]) -> Vec<T> {
        if arr.len() <= 1 {
            return arr.to_vec();
        }

        let pivot = &arr[0];
        let mut less = Vec::new();
        let mut equal = Vec::new();
        let mut greater = Vec::new();

        for item in arr {
            if item < pivot {
                less.push(item.clone());
            } else if item > pivot {
                greater.push(item.clone());
            } else {
                equal.push(item.clone());
            }
        }

        let mut result = quicksort(&less);
        result.extend(equal);
        result.extend(quicksort(&greater));
        result
    }

    let unsorted = vec![64, 34, 25, 12, 22, 11, 90];
    let sorted = quicksort(&unsorted);
    println!("  - 排序前: {:?}", unsorted);
    println!("  - 排序后: {:?}", sorted);

    // 二分搜索
    fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
        let mut left = 0;
        let mut right = arr.len();

        while left < right {
            let mid = left + (right - left) / 2;
            if arr[mid] == target {
                return Some(mid);
            } else if arr[mid] < target {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        None
    }

    let search_array = vec![11, 12, 22, 25, 34, 64, 90];
    if let Some(index) = binary_search(&search_array, 25) {
        println!("  - 找到 25 在索引: {}", index);
    }
}

/// 综合应用：任务处理系统
async fn demonstrate_integrated_system() -> Result<(), Box<dyn std::error::Error>> {
    use std::sync::Arc;
    use tokio::sync::Mutex;
    use tokio::time::{sleep, Duration};

    // 任务队列（使用 C05 的并发原语）
    let task_queue: Arc<Mutex<Vec<String>>> = Arc::new(Mutex::new(Vec::new()));

    // 生产者：添加任务
    let queue_clone = Arc::clone(&task_queue);
    let producer = tokio::spawn(async move {
        for i in 1..=5 {
            let mut queue = queue_clone.lock().await;
            queue.push(format!("任务 {}", i));
            println!("  - 生产者: 添加任务 {}", i);
            drop(queue);
            sleep(Duration::from_millis(100)).await;
        }
    });

    // 消费者：处理任务
    let queue_clone = Arc::clone(&task_queue);
    let consumer = tokio::spawn(async move {
        loop {
            let task = {
                let mut queue = queue_clone.lock().await;
                queue.pop()
            };

            if let Some(task) = task {
                println!("  - 消费者: 处理 {}", task);
                sleep(Duration::from_millis(200)).await;
            } else {
                sleep(Duration::from_millis(50)).await;
            }

            // 检查是否完成
            let queue = queue_clone.lock().await;
            if queue.is_empty() {
                break;
            }
        }
    });

    // 等待生产者和消费者完成
    tokio::try_join!(producer, consumer)?;

    println!("  - ✅ 任务处理系统运行完成");
    Ok(())
}
