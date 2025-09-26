//! 并发性能测试
//! 
//! 测试并发和并行处理的性能

use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Instant;

#[test]
fn test_thread_performance() {
    let data = Arc::new(vec![1, 2, 3, 4, 5]);
    let num_threads = 4;
    
    let start = Instant::now();
    
    let handles: Vec<_> = (0..num_threads)
        .map(|i| {
            let data = Arc::clone(&data);
            thread::spawn(move || {
                let sum: i32 = data.iter().sum();
                sum + i
            })
        })
        .collect();
    
    let results: Vec<i32> = handles
        .into_iter()
        .map(|h| h.join().unwrap())
        .collect();
    
    let duration = start.elapsed();
    
    assert_eq!(results.len(), num_threads);
    assert!(duration.as_millis() < 100);
}

#[test]
fn test_mutex_performance() {
    let counter = Arc::new(Mutex::new(0));
    let num_threads = 10;
    
    let start = Instant::now();
    
    let handles: Vec<_> = (0..num_threads)
        .map(|_| {
            let counter = Arc::clone(&counter);
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
    
    let duration = start.elapsed();
    let final_count = *counter.lock().unwrap();
    
    assert_eq!(final_count, 1000);
    assert!(duration.as_millis() < 500);
}

#[test]
fn test_parallel_processing() {
    let data: Vec<i32> = (0..10000).collect();
    
    // 串行处理
    let start = Instant::now();
    let serial_result: i32 = data.iter().map(|x| x * x).sum();
    let serial_time = start.elapsed();
    
    // 并行处理
    let start = Instant::now();
    let parallel_result: i32 = data
        .par_iter()
        .map(|x| x * x)
        .sum();
    let parallel_time = start.elapsed();
    
    assert_eq!(serial_result, parallel_result);
    // 并行处理应该更快（在某些情况下）
    println!("Serial time: {:?}, Parallel time: {:?}", serial_time, parallel_time);
}

#[test]
fn test_channel_performance() {
    let (tx, rx) = std::sync::mpsc::channel();
    let num_messages = 10000;
    
    let start = Instant::now();
    
    // 发送线程
    let sender = thread::spawn(move || {
        for i in 0..num_messages {
            tx.send(i).unwrap();
        }
    });
    
    // 接收线程
    let receiver = thread::spawn(move || {
        let mut received = 0;
        while let Ok(_) = rx.recv() {
            received += 1;
        }
        received
    });
    
    sender.join().unwrap();
    let received_count = receiver.join().unwrap();
    
    let duration = start.elapsed();
    
    assert_eq!(received_count, num_messages);
    assert!(duration.as_millis() < 1000);
}

#[test]
fn test_async_performance() {
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    let start = Instant::now();
    
    rt.block_on(async {
        let tasks: Vec<_> = (0..1000)
            .map(|i| {
                tokio::spawn(async move {
                    tokio::time::sleep(tokio::time::Duration::from_millis(1)).await;
                    i * 2
                })
            })
            .collect();
        
        let results: Vec<i32> = futures::future::join_all(tasks)
            .await
            .into_iter()
            .map(|r| r.unwrap())
            .collect();
        
        assert_eq!(results.len(), 1000);
    });
    
    let duration = start.elapsed();
    
    // 异步任务应该快速完成
    assert!(duration.as_millis() < 2000);
}

#[test]
fn test_lock_contention() {
    let shared_data = Arc::new(Mutex::new(Vec::new()));
    let num_threads = 5;
    let items_per_thread = 1000;
    
    let start = Instant::now();
    
    let handles: Vec<_> = (0..num_threads)
        .map(|thread_id| {
            let data = Arc::clone(&shared_data);
            thread::spawn(move || {
                for i in 0..items_per_thread {
                    let mut vec = data.lock().unwrap();
                    vec.push(thread_id * 1000 + i);
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let duration = start.elapsed();
    let final_data = shared_data.lock().unwrap();
    
    assert_eq!(final_data.len(), num_threads * items_per_thread);
    assert!(duration.as_millis() < 1000);
}

#[test]
fn test_memory_barrier_performance() {
    let data = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let num_threads = 10;
    
    let start = Instant::now();
    
    let handles: Vec<_> = (0..num_threads)
        .map(|_| {
            let data = Arc::clone(&data);
            thread::spawn(move || {
                for _ in 0..1000 {
                    data.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    let duration = start.elapsed();
    let final_value = data.load(std::sync::atomic::Ordering::SeqCst);
    
    assert_eq!(final_value, num_threads * 1000);
    assert!(duration.as_millis() < 500);
}

// 需要添加 rayon 依赖来支持并行迭代器
// 这里使用一个简化的实现
trait ParallelIterator {
    type Item;
    fn par_iter(self) -> Self;
    fn map<F, B>(self, f: F) -> Self where F: Fn(Self::Item) -> B;
    fn sum<S>(self) -> S where S: std::iter::Sum<Self::Item>;
}

impl<'a, T> ParallelIterator for &'a [T] {
    type Item = &'a T;
    
    fn par_iter(self) -> Self {
        self
    }
    
    fn map<F, B>(self, f: F) -> Self 
    where 
        F: Fn(Self::Item) -> B,
    {
        self // 简化实现
    }
    
    fn sum<S>(self) -> S 
    where 
        S: std::iter::Sum<Self::Item>,
    {
        self.iter().sum()
    }
}
