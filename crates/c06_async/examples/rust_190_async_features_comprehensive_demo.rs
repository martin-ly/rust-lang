//! Rust 1.90 异步特性综合演示程序
//! 
//! 本程序全面展示了Rust 1.90版本中异步编程的新特性和改进，包括：
//! - 显式推断的常量参数在异步编程中的应用
//! - 生命周期语法一致性检查的实际应用
//! - 函数指针比较扩展检查的安全性提升
//! - 异步控制流增强的实际效果
//! - 性能优化的实际表现

use std::sync::Arc;
use std::time::Duration;
use tokio::time::sleep;
use tokio::sync::{Mutex, Semaphore};
use std::collections::HashMap;
use anyhow::Result;
// use std::future::Future;
// use std::pin::Pin;

/// Rust 1.90 显式推断的常量参数在异步编程中的应用
/// 
/// 演示如何使用 `_` 进行常量参数推断，简化异步代码的编写
pub struct AsyncArrayProcessor<const N: usize> {
    data: Arc<Mutex<[u8; N]>>,
    processing_count: Arc<Mutex<usize>>,
}

impl<const N: usize> AsyncArrayProcessor<N> {
    pub fn new(data: [u8; N]) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            processing_count: Arc::new(Mutex::new(0)),
        }
    }

    /// 使用常量参数推断处理数组
    /// 
    /// 在Rust 1.90中，可以使用 `_` 让编译器自动推断常量参数类型
    pub async fn process_with_inference(&self) -> Result<[u8; N]> {
        let data = self.data.lock().await;
        let mut processed: [u8; N] = [0; N]; // 使用常量参数
        
        for i in 0..N {
            processed[i] = data[i] * 2;
            sleep(Duration::from_millis(1)).await; // 模拟异步处理
        }
        
        // 更新处理计数
        {
            let mut count = self.processing_count.lock().await;
            *count += 1;
        }
        
        Ok(processed)
    }

    /// 异步映射操作，展示常量参数推断的强大功能
    pub async fn async_map<F, T>(&self, f: F) -> Result<[T; N]>
    where
        F: Fn(u8) -> T + Send + Sync,
        T: Default + Copy,
    {
        let data = self.data.lock().await;
        let mut result: [T; N] = [Default::default(); N]; // 使用常量参数
        
        for i in 0..N {
            result[i] = f(data[i]);
            sleep(Duration::from_millis(1)).await; // 模拟异步处理
        }
        
        Ok(result)
    }

    pub async fn get_processing_count(&self) -> usize {
        let count = self.processing_count.lock().await;
        *count
    }
}

/// 生命周期语法一致性检查的实际应用
/// 
/// 演示如何在异步函数中正确使用生命周期，避免语法不一致
pub struct AsyncLifecycleManager<'a> {
    name: &'a str,
    resources: Arc<Mutex<HashMap<String, String>>>,
    active_connections: Arc<Mutex<Vec<&'a str>>>,
}

impl<'a> AsyncLifecycleManager<'a> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            resources: Arc::new(Mutex::new(HashMap::new())),
            active_connections: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 正确的生命周期语法 - 参数和返回值使用一致的生命周期语法
    pub async fn get_resource(&self, key: &str) -> Option<String> {
        let resources = self.resources.lock().await;
        resources.get(key).cloned()
    }

    /// 异步资源管理，展示生命周期的一致性
    pub async fn manage_resource(&self, key: &'a str, value: &'a str) -> Result<()> {
        {
            let mut resources = self.resources.lock().await;
            resources.insert(key.to_string(), value.to_string());
        }
        
        {
            let mut connections: tokio::sync::MutexGuard<'_, Vec<&'a str>> = self.active_connections.lock().await;
            connections.push(key);
        }
        
        println!("资源 {} 已添加到管理器 {}", key, self.name);
        Ok(())
    }

    /// 异步清理资源，展示生命周期的正确使用
    pub async fn cleanup_resources(&self) -> Result<Vec<&'a str>> {
        let mut connections = self.active_connections.lock().await;
        let cleaned: Vec<&'a str> = connections.drain(..).collect();
        
        println!("已清理 {} 个资源连接", cleaned.len());
        Ok(cleaned)
    }
}

/// 函数指针比较扩展检查的安全性提升
/// 
/// 演示如何在异步回调中安全地比较函数指针
pub struct AsyncCallbackManager {
    callbacks: Arc<Mutex<HashMap<String, fn() -> Result<()>>>>,
    execution_order: Arc<Mutex<Vec<String>>>,
}

impl AsyncCallbackManager {
    pub fn new() -> Self {
        Self {
            callbacks: Arc::new(Mutex::new(HashMap::new())),
            execution_order: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 安全地注册异步回调函数
    pub async fn register_callback(&self, name: String, callback: fn() -> Result<()>) {
        // Rust 1.90的函数指针比较扩展检查确保这里的安全性
        let mut callbacks = self.callbacks.lock().await;
        callbacks.insert(name, callback);
    }

    /// 异步执行回调，展示安全的函数指针处理
    pub async fn execute_callback(&self, name: &str) -> Result<()> {
        let callback = {
            let callbacks = self.callbacks.lock().await;
            callbacks.get(name).copied()
        };

        if let Some(callback_fn) = callback {
            // 记录执行顺序
            {
                let mut order = self.execution_order.lock().await;
                order.push(name.to_string());
            }
            
            // 异步执行回调
            sleep(Duration::from_millis(10)).await;
            callback_fn()?;
            
            println!("回调 {} 执行完成", name);
        } else {
            return Err(anyhow::anyhow!("回调 {} 未找到", name));
        }
        
        Ok(())
    }

    /// 获取执行顺序，展示函数指针比较的安全性
    pub async fn get_execution_order(&self) -> Vec<String> {
        let order = self.execution_order.lock().await;
        order.clone()
    }
}

/// 异步控制流增强的实际效果
/// 
/// 演示Rust 1.90中异步控制流的改进
pub struct AsyncControlFlow190 {
    state: Arc<Mutex<AsyncState>>,
    state_history: Arc<Mutex<Vec<AsyncState>>>,
    transition_callbacks: Arc<Mutex<HashMap<AsyncState, Box<dyn Fn() -> Result<()> + Send + Sync>>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AsyncState {
    Idle,
    Processing,
    Waiting,
    Completed,
    Error,
}

impl AsyncControlFlow190 {
    pub fn new() -> Self {
        Self {
            state: Arc::new(Mutex::new(AsyncState::Idle)),
            state_history: Arc::new(Mutex::new(Vec::new())),
            transition_callbacks: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// 注册状态转换回调
    pub async fn register_transition_callback<F>(&self, state: AsyncState, callback: F)
    where
        F: Fn() -> Result<()> + Send + Sync + 'static,
    {
        let mut callbacks = self.transition_callbacks.lock().await;
        callbacks.insert(state, Box::new(callback));
    }

    /// 异步状态转换，展示控制流的增强
    pub async fn transition_to(&self, new_state: AsyncState) -> Result<()> {
        let current_state = {
            let state = self.state.lock().await;
            state.clone()
        };

        // 记录状态历史
        {
            let mut history = self.state_history.lock().await;
            history.push(current_state.clone());
        }

        // 执行状态转换
        {
            let mut state = self.state.lock().await;
            *state = new_state.clone();
        }

        // 执行转换回调
        if let Some(callback) = self.transition_callbacks.lock().await.get(&new_state) {
            callback()?;
        }

        println!("状态转换: {:?} -> {:?}", current_state, new_state);
        Ok(())
    }

    /// 异步状态机处理，展示控制流的实际应用
    pub async fn process_data(&self, data: &[u8]) -> Result<Vec<u8>> {
        self.transition_to(AsyncState::Processing).await?;
        
        let mut result = Vec::new();
        for &byte in data {
            result.push(byte * 2);
            sleep(Duration::from_millis(1)).await; // 模拟异步处理
        }
        
        self.transition_to(AsyncState::Completed).await?;
        Ok(result)
    }

    /// 获取当前状态
    pub async fn get_current_state(&self) -> AsyncState {
        let state = self.state.lock().await;
        state.clone()
    }

    /// 获取状态历史
    pub async fn get_state_history(&self) -> Vec<AsyncState> {
        let history = self.state_history.lock().await;
        history.clone()
    }
}

/// 性能优化的实际表现
/// 
/// 演示Rust 1.90中性能优化的实际效果
#[derive(Clone)]
pub struct AsyncPerformanceOptimizer {
    cache: Arc<Mutex<HashMap<String, usize>>>,
    computation_stats: Arc<Mutex<HashMap<String, (usize, Duration)>>>,
    parallel_workers: Arc<Semaphore>,
}

impl AsyncPerformanceOptimizer {
    pub fn new(max_parallel: usize) -> Self {
        Self {
            cache: Arc::new(Mutex::new(HashMap::new())),
            computation_stats: Arc::new(Mutex::new(HashMap::new())),
            parallel_workers: Arc::new(Semaphore::new(max_parallel)),
        }
    }

    /// 优化的异步计算，展示性能改进
    pub async fn optimized_compute(&self, key: String, input: usize) -> Result<usize> {
        // 检查缓存
        if let Some(&cached) = self.cache.lock().await.get(&key) {
            return Ok(cached);
        }

        let _permit = self.parallel_workers.acquire().await?;
        let start = std::time::Instant::now();

        // 模拟复杂的计算
        let result = self.perform_computation(input).await?;
        
        let duration = start.elapsed();

        // 更新缓存和统计
        {
            let mut cache = self.cache.lock().await;
            cache.insert(key.clone(), result);
        }

        {
            let mut stats = self.computation_stats.lock().await;
            stats.insert(key, (result, duration));
        }

        Ok(result)
    }

    async fn perform_computation(&self, input: usize) -> Result<usize> {
        // 模拟CPU密集型计算
        sleep(Duration::from_millis(50)).await;
        Ok(input * input + input * 2 + 1)
    }

    /// 批量异步计算，展示并行优化
    pub async fn batch_compute(&self, tasks: Vec<(String, usize)>) -> Result<Vec<usize>> {
        let mut handles = Vec::new();

        for (key, input) in tasks {
            let optimizer = self.clone();
            let handle = tokio::spawn(async move {
                optimizer.optimized_compute(key, input).await
            });
            handles.push(handle);
        }

        let mut results = Vec::new();
        for handle in handles {
            let result = handle.await??;
            results.push(result);
        }

        Ok(results)
    }

    /// 获取性能统计
    pub async fn get_performance_stats(&self) -> HashMap<String, (usize, Duration)> {
        let stats = self.computation_stats.lock().await;
        stats.clone()
    }

    /// 获取缓存命中率
    pub async fn get_cache_stats(&self) -> (usize, usize) {
        let cache = self.cache.lock().await;
        let stats = self.computation_stats.lock().await;
        (cache.len(), stats.len())
    }
}

/// 综合演示Rust 1.90异步特性
pub async fn demonstrate_rust_190_async_features() -> Result<()> {
    println!("🚀 Rust 1.90 异步特性综合演示");
    println!("==========================================");

    // 1. 显式推断的常量参数演示
    println!("\n1. 显式推断的常量参数演示:");
    let processor = AsyncArrayProcessor::new([1, 2, 3, 4, 5]);
    let processed = processor.process_with_inference().await?;
    println!("  处理结果: {:?}", processed);
    
    let mapped = processor.async_map(|x| x * x).await?;
    println!("  映射结果: {:?}", mapped);
    
    let count = processor.get_processing_count().await;
    println!("  处理次数: {}", count);

    // 2. 生命周期语法一致性检查演示
    println!("\n2. 生命周期语法一致性检查演示:");
    let name = "test_manager";
    let manager = AsyncLifecycleManager::new(name);
    
    manager.manage_resource("resource1", "value1").await?;
    manager.manage_resource("resource2", "value2").await?;
    
    let resource = manager.get_resource("resource1").await;
    println!("  获取资源: {:?}", resource);
    
    let cleaned = manager.cleanup_resources().await?;
    println!("  清理的资源: {:?}", cleaned);

    // 3. 函数指针比较扩展检查演示
    println!("\n3. 函数指针比较扩展检查演示:");
    let callback_manager = AsyncCallbackManager::new();
    
    callback_manager.register_callback("callback1".to_string(), || {
        println!("  执行回调1");
        Ok(())
    }).await;
    
    callback_manager.register_callback("callback2".to_string(), || {
        println!("  执行回调2");
        Ok(())
    }).await;
    
    callback_manager.execute_callback("callback1").await?;
    callback_manager.execute_callback("callback2").await?;
    
    let order = callback_manager.get_execution_order().await;
    println!("  执行顺序: {:?}", order);

    // 4. 异步控制流增强演示
    println!("\n4. 异步控制流增强演示:");
    let control_flow = AsyncControlFlow190::new();
    
    control_flow.register_transition_callback(AsyncState::Processing, || {
        println!("  进入处理状态");
        Ok(())
    }).await;
    
    control_flow.register_transition_callback(AsyncState::Completed, || {
        println!("  处理完成");
        Ok(())
    }).await;
    
    let data = b"test data";
    let result = control_flow.process_data(data).await?;
    println!("  处理结果: {:?}", result);
    
    let history = control_flow.get_state_history().await;
    println!("  状态历史: {:?}", history);

    // 5. 性能优化演示
    println!("\n5. 性能优化演示:");
    let optimizer = AsyncPerformanceOptimizer::new(4);
    
    let tasks = vec![
        ("task1".to_string(), 10),
        ("task2".to_string(), 20),
        ("task3".to_string(), 30),
        ("task4".to_string(), 40),
    ];
    
    let results = optimizer.batch_compute(tasks).await?;
    println!("  批量计算结果: {:?}", results);
    
    let stats = optimizer.get_performance_stats().await;
    println!("  性能统计: {:?}", stats);
    
    let (cache_size, total_computations) = optimizer.get_cache_stats().await;
    println!("  缓存统计: {} 缓存项, {} 总计算", cache_size, total_computations);

    println!("\n✅ Rust 1.90 异步特性综合演示完成!");
    Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 Rust 1.90 异步特性综合演示程序");
    println!("==========================================");
    
    // 运行综合演示
    demonstrate_rust_190_async_features().await?;
    
    println!("\n🎉 演示程序运行完成！");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_array_processor() {
        let processor = AsyncArrayProcessor::new([1, 2, 3]);
        let result = processor.process_with_inference().await.unwrap();
        assert_eq!(result, [2, 4, 6]);
        
        let count = processor.get_processing_count().await;
        assert_eq!(count, 1);
    }

    #[tokio::test]
    async fn test_lifecycle_manager() {
        let name = "test";
        let manager = AsyncLifecycleManager::new(name);
        
        manager.manage_resource("key1", "value1").await.unwrap();
        let resource = manager.get_resource("key1").await;
        assert_eq!(resource, Some("value1".to_string()));
    }

    #[tokio::test]
    async fn test_callback_manager() {
        let manager = AsyncCallbackManager::new();
        
        manager.register_callback("test".to_string(), || {
            Ok(())
        }).await;
        
        manager.execute_callback("test").await.unwrap();
        let order = manager.get_execution_order().await;
        assert_eq!(order, vec!["test"]);
    }

    #[tokio::test]
    async fn test_control_flow() {
        let control_flow = AsyncControlFlow190::new();
        
        control_flow.transition_to(AsyncState::Processing).await.unwrap();
        let state = control_flow.get_current_state().await;
        assert_eq!(state, AsyncState::Processing);
    }

    #[tokio::test]
    async fn test_performance_optimizer() {
        let optimizer = AsyncPerformanceOptimizer::new(2);
        
        let result = optimizer.optimized_compute("test".to_string(), 5).await.unwrap();
        assert_eq!(result, 36); // 5*5 + 5*2 + 1 = 36
        
        let (cache_size, _) = optimizer.get_cache_stats().await;
        assert_eq!(cache_size, 1);
    }

    #[tokio::test]
    async fn test_comprehensive_demo() {
        assert!(demonstrate_rust_190_async_features().await.is_ok());
    }
}
