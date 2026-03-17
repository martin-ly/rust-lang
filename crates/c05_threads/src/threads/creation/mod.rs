//! 线程创建模块
//!
//! 本模块演示Rust中线程的创建方法，包括：
//! 1) 基本线程创建
//! 2) 线程命名
//! 3) 线程栈大小设置
//! 4) 线程创建最佳实践
//! 5) 线程错误处理与结果传递（补充）
use std::thread;
use std::time::Duration;

/// 基本线程创建示例
pub fn basic_thread_creation() {
    println!("🔧 基本线程创建示例");

    // 创建线程
    let handle = thread::spawn(|| {
        println!("  子线程开始执行");
        thread::sleep(Duration::from_millis(100));
        println!("  子线程执行完成");
    });

    println!("  主线程等待子线程...");
    handle.join().expect("线程应成功完成");
    println!("  主线程继续执行");
}

/// 带参数的线程创建
pub fn thread_with_parameters() {
    println!("🔧 带参数的线程创建示例");

    let data = vec![1, 2, 3, 4, 5];

    let handle = thread::spawn(move || {
        println!("  子线程处理数据: {:?}", data);
        let sum: i32 = data.iter().sum();
        println!("  数据总和: {}", sum);
        sum
    });

    let result = handle.join().expect("线程应成功完成");
    println!("  主线程获得结果: {}", result);
}

/// 线程命名示例
pub fn named_threads() {
    println!("🔧 线程命名示例");

    let handle = thread::Builder::new()
        .name("worker-thread".to_string())
        .spawn(|| {
            let current_thread = thread::current();
            let name = current_thread.name().unwrap_or("unnamed");
            println!("  线程 '{}' 开始执行", name);
            thread::sleep(Duration::from_millis(50));
            println!("  线程 '{}' 执行完成", name);
        })
        .expect("线程创建不应失败");

    handle.join().expect("线程应成功完成");
}

/// 自定义栈大小的线程
pub fn custom_stack_size_thread() {
    println!("🔧 自定义栈大小线程示例");

    let handle = thread::Builder::new()
        .stack_size(1024 * 1024) // 1MB 栈大小
        .spawn(|| {
            println!("  大栈线程开始执行");
            // 这里可以执行需要大量栈空间的操作
            thread::sleep(Duration::from_millis(50));
            println!("  大栈线程执行完成");
        })
        .expect("线程创建不应失败");

    handle.join().unwrap();
}

/// 多线程并行执行
pub fn parallel_execution() {
    println!("🔧 多线程并行执行示例");

    let mut handles = Vec::new();

    for i in 0..5 {
        let handle = thread::spawn(move || {
            println!("  线程 {} 开始执行", i);
            thread::sleep(Duration::from_millis(100));
            println!("  线程 {} 执行完成", i);
            i * i
        });
        handles.push(handle);
    }

    // 等待所有线程完成
    for (i, handle) in handles.into_iter().enumerate() {
        let result = handle.join().expect("线程应成功完成");
        println!("  线程 {} 返回结果: {}", i, result);
    }
}

/// 线程创建最佳实践
pub fn thread_best_practices() {
    println!("🔧 线程创建最佳实践");

    // 1. 使用 move 闭包避免生命周期问题
    let data = [1, 2, 3, 4, 5];
    let handle = thread::spawn(move || data.iter().sum::<i32>());

    // 2. 合理设置线程数量
    let num_threads = 4; // 假设4个CPU核心
    println!("  CPU核心数: {}", num_threads);

    // 3. 使用线程池处理大量任务
    let mut handles = Vec::new();
    for i in 0..num_threads {
        let handle = thread::spawn(move || format!("线程-{}", i));
        handles.push(handle);
    }

    // 收集结果
    let results: Vec<String> = handles.into_iter().map(|h| h.join().expect("线程应成功完成")).collect();

    println!("  创建的线程: {:?}", results);

    let sum = handle.join().expect("线程应成功完成");
    println!("  数据处理结果: {}", sum);
}

/// 线程错误处理与结果传递（5）
/// - 在线程中使用 Result 进行显式错误返回
/// - 主线程 join 后匹配错误并处理
pub fn thread_error_handling_example() {
    println!("🔧 线程错误处理与结果传递示例");
    let handle = thread::spawn(|| -> Result<i32, &'static str> {
        // 模拟业务：可能失败
        let ok = true;
        if ok { Ok(100) } else { Err("业务失败") }
    });
    match handle.join() {
        Ok(Ok(v)) => println!("  成功: {}", v),
        Ok(Err(e)) => println!("  线程返回错误: {}", e),
        Err(_) => println!("  线程发生 panic"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_thread_creation() {
        basic_thread_creation();
    }

    #[test]
    fn test_thread_with_parameters() {
        thread_with_parameters();
    }

    #[test]
    fn test_named_threads() {
        named_threads();
    }

    #[test]
    fn test_custom_stack_size_thread() {
        custom_stack_size_thread();
    }

    #[test]
    fn test_parallel_execution() {
        parallel_execution();
    }

    #[test]
    fn test_thread_best_practices() {
        thread_best_practices();
    }

    #[test]
    fn test_thread_error_handling_example() {
        thread_error_handling_example();
    }
}
