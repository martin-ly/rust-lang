//! Rust 1.90 特性演示模块 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`
//! 
//! 本模块展示 Rust 1.90 版本的新特性和改进，包括：
//! - 返回位置 impl Trait (RPITIT) 的改进
//! - 异步泛型函数的支持
//! - 共享状态的不同锁策略对比

use std::sync::{Arc, Mutex, RwLock};
use std::thread;

/// 数据结构体，用于演示迭代器管道
pub struct Data<T> {
    items: Vec<T>,
}

impl<T> Data<T> {
    /// 创建新的 Data 实例
    pub fn new(items: Vec<T>) -> Self {
        Self { items }
    }
    
    /// 返回迭代器管道，演示 RPITIT 特性
    pub fn pipeline(&self) -> impl Iterator<Item = T> + '_ 
    where 
        T: Clone,
    {
        self.items
            .iter()
            .filter(|_| {
                // 简单的过滤逻辑
                true
            })
            .map(|x| x.clone())
            .take(100) // 限制输出数量
    }
}

/// 装箱版本的迭代器管道，用于性能对比
pub fn boxed_pipeline<T>(items: &[T]) -> Box<dyn Iterator<Item = T> + '_>
where
    T: Clone,
{
    Box::new(
        items
            .iter()
            .filter(|_| true)
            .map(|x| x.clone())
            .take(100)
    )
}

/// 共享状态演示模块
pub mod shared_state_demo {
    use super::*;
    
    /// 使用 Mutex 的计数器演示
    pub fn mutex_counter(thread_count: usize, iterations: usize) -> i32 {
        let counter = Arc::new(Mutex::new(0));
        let handles: Vec<_> = (0..thread_count)
            .map(|_| {
                let counter = Arc::clone(&counter);
                thread::spawn(move || {
                    for _ in 0..iterations {
                        let mut count = counter.lock().unwrap();
                        *count += 1;
                    }
                })
            })
            .collect();
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        *counter.lock().unwrap()
    }
    
    /// 使用 RwLock 的累加器演示（读多写少场景）
    pub fn rwlock_accumulate(readers: usize, writers: usize, iterations: usize) -> i32 {
        let data = Arc::new(RwLock::new(0));
        let mut handles = Vec::new();
        
        // 启动读取线程
        for _ in 0..readers {
            let data = Arc::clone(&data);
            let handle = thread::spawn(move || {
                for _ in 0..iterations {
                    let _value = data.read().unwrap();
                    // 模拟读取操作
                }
            });
            handles.push(handle);
        }
        
        // 启动写入线程
        for _ in 0..writers {
            let data = Arc::clone(&data);
            let handle = thread::spawn(move || {
                for _ in 0..iterations {
                    let mut value = data.write().unwrap();
                    *value += 1;
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        *data.read().unwrap()
    }
}

/// 异步泛型函数演示
pub async fn async_add_generic<T>(a: T, b: T) -> T
where
    T: std::ops::Add<Output = T> + Copy,
{
    a + b
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_data_pipeline() {
        let data = Data::new(vec![1, 2, 3, 4, 5]);
        let result: Vec<i32> = data.pipeline().collect();
        assert_eq!(result.len(), 5);
    }
    
    #[test]
    fn test_boxed_pipeline() {
        let items = vec![1, 2, 3, 4, 5];
        let result: Vec<i32> = boxed_pipeline(&items).collect();
        assert_eq!(result.len(), 5);
    }
    
    #[test]
    fn test_mutex_counter() {
        let result = shared_state_demo::mutex_counter(4, 100);
        assert_eq!(result, 400);
    }
    
    #[test]
    fn test_rwlock_accumulate() {
        let result = shared_state_demo::rwlock_accumulate(8, 2, 50);
        assert_eq!(result, 100);
    }
    
    #[test]
    fn test_async_add_generic() {
        // 使用 futures::executor::block_on 来运行异步代码
        let result = futures::executor::block_on(async_add_generic(2u8, 3u8));
        assert_eq!(result, 5u8);
        
        let result = futures::executor::block_on(async_add_generic(10i32, 20i32));
        assert_eq!(result, 30i32);
    }
}
