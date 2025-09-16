//! 简化的演示模块
//!
//! 本模块提供了简化的演示功能，避免复杂的线程安全问题

use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 简化的演示功能
pub fn demonstrate_simple_features() {
    println!("=== 简化功能演示 ===");

    // 测试基础同步
    demonstrate_basic_sync();

    // 测试消息传递
    demonstrate_message_passing();

    // 测试性能基准
    demonstrate_performance_benchmark();
}

/// 基础同步演示
fn demonstrate_basic_sync() {
    println!("=== 基础同步演示 ===");

    let counter = Arc::new(Mutex::new(0));
    let iterations = 1000;
    let thread_count = 4;

    let start = Instant::now();
    let handles: Vec<_> = (0..thread_count)
        .map(|_| {
            let counter = counter.clone();
            thread::spawn(move || {
                for _ in 0..iterations / thread_count {
                    let mut count = counter.lock().unwrap();
                    *count += 1;
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }
    let duration = start.elapsed();

    let final_count = *counter.lock().unwrap();
    println!("最终计数: {}", final_count);
    println!("同步耗时: {:?}", duration);
    println!(
        "吞吐量: {:.2} ops/sec",
        final_count as f64 / duration.as_secs_f64()
    );
}

/// 消息传递演示
fn demonstrate_message_passing() {
    println!("=== 消息传递演示 ===");

    use crate::message_passing::priority_channels_simple::SimplePriorityChannel;

    let channel = Arc::new(SimplePriorityChannel::new());

    // 创建生产者线程
    let producer = {
        let channel = channel.clone();
        thread::spawn(move || {
            for i in 0..20 {
                let priority = if i % 3 == 0 { 1 } else { 2 };
                channel.send(priority, format!("消息 {}", i));
                thread::sleep(Duration::from_millis(1));
            }
        })
    };

    // 创建消费者线程
    let consumer = {
        let channel = channel.clone();
        thread::spawn(move || {
            for _ in 0..20 {
                if let Some(message) = channel.recv() {
                    println!("接收到: {}", message);
                }
            }
        })
    };

    producer.join().unwrap();
    consumer.join().unwrap();

    println!("消息传递完成");
}

/// 性能基准演示
fn demonstrate_performance_benchmark() {
    println!("=== 性能基准演示 ===");

    let iterations = 100000;
    let thread_count = 4;

    // 测试Mutex性能
    let mutex_counter = Arc::new(Mutex::new(0));
    let start = Instant::now();
    let handles: Vec<_> = (0..thread_count)
        .map(|_| {
            let counter = mutex_counter.clone();
            thread::spawn(move || {
                for _ in 0..iterations / thread_count {
                    let mut count = counter.lock().unwrap();
                    *count += 1;
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }
    let mutex_time = start.elapsed();

    println!("Mutex性能:");
    println!("  耗时: {:?}", mutex_time);
    println!(
        "  吞吐量: {:.2} ops/sec",
        iterations as f64 / mutex_time.as_secs_f64()
    );

    // 测试原子操作性能
    use std::sync::atomic::{AtomicUsize, Ordering};
    let atomic_counter = Arc::new(AtomicUsize::new(0));
    let start = Instant::now();
    let handles: Vec<_> = (0..thread_count)
        .map(|_| {
            let counter = atomic_counter.clone();
            thread::spawn(move || {
                for _ in 0..iterations / thread_count {
                    counter.fetch_add(1, Ordering::Relaxed);
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }
    let atomic_time = start.elapsed();

    println!("原子操作性能:");
    println!("  耗时: {:?}", atomic_time);
    println!(
        "  吞吐量: {:.2} ops/sec",
        iterations as f64 / atomic_time.as_secs_f64()
    );

    println!(
        "性能提升: {:.2}x",
        mutex_time.as_nanos() as f64 / atomic_time.as_nanos() as f64
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_sync() {
        let counter = Arc::new(Mutex::new(0));
        let handles: Vec<_> = (0..4)
            .map(|_| {
                let counter = counter.clone();
                thread::spawn(move || {
                    for _ in 0..100 {
                        let mut count = counter.lock().unwrap();
                        *count += 1;
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(*counter.lock().unwrap(), 400);
    }

    #[test]
    fn test_message_passing() {
        use crate::message_passing::priority_channels_simple::SimplePriorityChannel;

        let channel = SimplePriorityChannel::new();
        channel.send(1, "test");
        assert_eq!(channel.recv(), Some("test"));
    }
}
