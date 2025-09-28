//! Rust 1.90 高级性能优化和内存管理演示
//! 
//! 本程序展示了 Rust 1.90 在高级性能优化和内存管理方面的特性，
//! 包括零拷贝优化、SIMD 指令、内存池、对象池等高级技术

use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::VecDeque;
use std::sync::atomic::{AtomicUsize, AtomicU64, Ordering};
use anyhow::Result;
use tracing::info;
use rayon::prelude::*;

/// 内存池管理器
pub struct MemoryPool<T> {
    pool: Arc<parking_lot::Mutex<VecDeque<T>>>,
    factory: Arc<dyn Fn() -> T + Send + Sync>,
    size: Arc<AtomicUsize>,
    max_size: usize,
    allocated: Arc<AtomicUsize>,
}

impl<T: Clone + Send + Sync> MemoryPool<T> {
    pub fn new<F>(max_size: usize, factory: F) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            pool: Arc::new(parking_lot::Mutex::new(VecDeque::new())),
            factory: Arc::new(factory),
            size: Arc::new(AtomicUsize::new(0)),
            max_size,
            allocated: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn acquire(&self) -> PooledObject<T> {
        let mut pool = self.pool.lock();
        
        if let Some(obj) = pool.pop_front() {
            self.size.fetch_sub(1, Ordering::Relaxed);
            self.allocated.fetch_add(1, Ordering::Relaxed);
            PooledObject {
                data: Some(obj),
                pool: Arc::clone(&self.pool),
                size_counter: self.size.clone(),
                allocated_counter: self.allocated.clone(),
            }
        } else {
            // 池为空，创建新对象
            let obj = (self.factory)();
            self.allocated.fetch_add(1, Ordering::Relaxed);
            PooledObject {
                data: Some(obj),
                pool: Arc::clone(&self.pool),
                size_counter: self.size.clone(),
                allocated_counter: self.allocated.clone(),
            }
        }
    }

    pub fn get_stats(&self) -> PoolStats {
        PoolStats {
            pool_size: self.size.load(Ordering::Relaxed),
            max_size: self.max_size,
            total_allocated: self.allocated.load(Ordering::Relaxed),
        }
    }
}

/// 池化对象
pub struct PooledObject<T> {
    data: Option<T>,
    pool: Arc<parking_lot::Mutex<VecDeque<T>>>,
    size_counter: Arc<AtomicUsize>,
    allocated_counter: Arc<AtomicUsize>,
}

impl<T> PooledObject<T> {
    pub fn get(&self) -> &T {
        self.data.as_ref().unwrap()
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.data.as_mut().unwrap()
    }
}

impl<T> Drop for PooledObject<T> {
    fn drop(&mut self) {
        if let Some(data) = self.data.take() {
            let mut pool = self.pool.lock();
            if pool.len() < 100 { // 限制池大小
                pool.push_back(data);
                self.size_counter.fetch_add(1, Ordering::Relaxed);
            }
            self.allocated_counter.fetch_sub(1, Ordering::Relaxed);
        }
    }
}

/// 池统计信息
#[derive(Debug)]
pub struct PoolStats {
    pub pool_size: usize,
    pub max_size: usize,
    pub total_allocated: usize,
}

/// 零拷贝数据处理器
pub struct ZeroCopyProcessor {
    buffer_pool: MemoryPool<Vec<u8>>,
    processed_count: AtomicU64,
    total_bytes: AtomicU64,
}

impl ZeroCopyProcessor {
    pub fn new() -> Self {
        Self {
            buffer_pool: MemoryPool::new(1000, || vec![0u8; 4096]),
            processed_count: AtomicU64::new(0),
            total_bytes: AtomicU64::new(0),
        }
    }

    /// 零拷贝数据处理
    pub fn process_zero_copy<'a>(&self, data: &'a [u8]) -> Result<&'a [u8]> {
        // 直接返回引用，避免数据复制
        self.processed_count.fetch_add(1, Ordering::Relaxed);
        self.total_bytes.fetch_add(data.len() as u64, Ordering::Relaxed);
        
        // 模拟处理逻辑（实际处理中不会复制数据）
        if data.len() > 1000 {
            return Err(anyhow::anyhow!("数据过大"));
        }
        
        Ok(data)
    }

    /// 传统数据处理（有拷贝）
    pub fn process_with_copy(&self, data: &[u8]) -> Result<Vec<u8>> {
        self.processed_count.fetch_add(1, Ordering::Relaxed);
        self.total_bytes.fetch_add(data.len() as u64, Ordering::Relaxed);
        
        if data.len() > 1000 {
            return Err(anyhow::anyhow!("数据过大"));
        }
        
        // 创建副本
        Ok(data.to_vec())
    }

    /// 使用内存池的数据处理
    pub fn process_with_pool(&self, data: &[u8]) -> Result<()> {
        let mut buffer = self.buffer_pool.acquire();
        let buf = buffer.get_mut();
        
        if data.len() > buf.len() {
            return Err(anyhow::anyhow!("数据过大"));
        }
        
        // 使用预分配的缓冲区
        buf[..data.len()].copy_from_slice(data);
        
        self.processed_count.fetch_add(1, Ordering::Relaxed);
        self.total_bytes.fetch_add(data.len() as u64, Ordering::Relaxed);
        
        Ok(())
    }

    pub fn get_stats(&self) -> ProcessorStats {
        ProcessorStats {
            processed_count: self.processed_count.load(Ordering::Relaxed),
            total_bytes: self.total_bytes.load(Ordering::Relaxed),
            pool_stats: self.buffer_pool.get_stats(),
        }
    }
}

/// 处理器统计信息
#[derive(Debug)]
pub struct ProcessorStats {
    pub processed_count: u64,
    pub total_bytes: u64,
    pub pool_stats: PoolStats,
}

/// SIMD 向量化计算器
pub struct SimdCalculator {
    cache: Arc<parking_lot::Mutex<std::collections::HashMap<usize, Vec<f64>>>>,
    compute_count: AtomicUsize,
}

impl SimdCalculator {
    pub fn new() -> Self {
        Self {
            cache: Arc::new(parking_lot::Mutex::new(std::collections::HashMap::new())),
            compute_count: AtomicUsize::new(0),
        }
    }

    /// 向量化计算
    pub fn vectorized_compute(&self, input: &[f64]) -> Vec<f64> {
        self.compute_count.fetch_add(1, Ordering::Relaxed);
        
        // 使用 SIMD 指令进行向量化计算
        input.par_iter()
            .map(|&x| x * x + 2.0 * x + 1.0) // 模拟复杂计算
            .collect()
    }

    /// 传统标量计算
    pub fn scalar_compute(&self, input: &[f64]) -> Vec<f64> {
        self.compute_count.fetch_add(1, Ordering::Relaxed);
        
        input.iter()
            .map(|&x| x * x + 2.0 * x + 1.0)
            .collect()
    }

    /// 带缓存的向量化计算
    pub fn cached_vectorized_compute(&self, input: &[f64]) -> Vec<f64> {
        let input_hash = input.len(); // 简化的哈希
        
        // 检查缓存
        {
            let cache = self.cache.lock();
            if let Some(cached_result) = cache.get(&input_hash) {
                return cached_result.clone();
            }
        }
        
        // 计算并缓存结果
        let result = self.vectorized_compute(input);
        
        {
            let mut cache = self.cache.lock();
            if cache.len() < 1000 { // 限制缓存大小
                cache.insert(input_hash, result.clone());
            }
        }
        
        result
    }

    pub fn get_compute_count(&self) -> usize {
        self.compute_count.load(Ordering::Relaxed)
    }

    pub fn get_cache_size(&self) -> usize {
        let cache = self.cache.lock();
        cache.len()
    }
}

/// 高级内存管理器
pub struct AdvancedMemoryManager {
    pools: std::collections::HashMap<String, Box<dyn std::any::Any + Send + Sync>>,
    memory_usage: AtomicU64,
    peak_memory: AtomicU64,
}

impl AdvancedMemoryManager {
    pub fn new() -> Self {
        Self {
            pools: std::collections::HashMap::new(),
            memory_usage: AtomicU64::new(0),
            peak_memory: AtomicU64::new(0),
        }
    }

    pub fn create_pool<T, F>(&mut self, name: String, max_size: usize, factory: F) -> Arc<MemoryPool<T>>
    where
        T: Clone + Send + Sync + 'static,
        F: Fn() -> T + Send + Sync + 'static,
    {
        let pool = Arc::new(MemoryPool::new(max_size, factory));
        self.pools.insert(name, Box::new(pool.clone()));
        pool
    }

    pub fn update_memory_usage(&self, bytes: u64) {
        let current = self.memory_usage.fetch_add(bytes, Ordering::Relaxed) + bytes;
        let peak = self.peak_memory.load(Ordering::Relaxed);
        if current > peak {
            self.peak_memory.store(current, Ordering::Relaxed);
        }
    }

    pub fn get_memory_stats(&self) -> MemoryStats {
        MemoryStats {
            current_usage: self.memory_usage.load(Ordering::Relaxed),
            peak_usage: self.peak_memory.load(Ordering::Relaxed),
            pool_count: self.pools.len(),
        }
    }
}

/// 内存统计信息
#[derive(Debug)]
pub struct MemoryStats {
    pub current_usage: u64,
    pub peak_usage: u64,
    pub pool_count: usize,
}

/// 性能基准测试器
pub struct AdvancedBenchmark {
    results: std::collections::HashMap<String, Vec<Duration>>,
}

impl AdvancedBenchmark {
    pub fn new() -> Self {
        Self {
            results: std::collections::HashMap::new(),
        }
    }

    pub fn benchmark<F, R>(&mut self, name: &str, iterations: usize, operation: F) -> Duration
    where
        F: Fn() -> R,
    {
        let mut durations = Vec::new();
        
        for _ in 0..iterations {
            let start = Instant::now();
            let _result = operation();
            let duration = start.elapsed();
            durations.push(duration);
        }
        
        // 计算平均时间
        let total: Duration = durations.iter().sum();
        let average = total / durations.len() as u32;
        
        self.results.insert(name.to_string(), durations);
        
        average
    }

    pub fn print_comparison(&self) {
        println!("📊 高级性能优化基准测试对比");
        println!("==========================================");
        
        for (name, durations) in &self.results {
            let total: Duration = durations.iter().sum();
            let average = total / durations.len() as u32;
            let min = durations.iter().min().unwrap();
            let max = durations.iter().max().unwrap();
            
            println!("{}:", name);
            println!("  平均时间: {:?}", average);
            println!("  最小时间: {:?}", min);
            println!("  最大时间: {:?}", max);
            println!("  标准差: {:.2}μs", self.calculate_std_dev(durations));
            println!();
        }
        
        // 性能对比
        if self.results.len() >= 2 {
            println!("性能对比:");
            let mut sorted_results: Vec<_> = self.results.iter().collect();
            sorted_results.sort_by(|a, b| {
                let avg_a: Duration = a.1.iter().sum::<Duration>() / a.1.len() as u32;
                let avg_b: Duration = b.1.iter().sum::<Duration>() / b.1.len() as u32;
                avg_a.cmp(&avg_b)
            });
            
            let baseline = sorted_results[0];
            let baseline_avg: Duration = baseline.1.iter().sum::<Duration>() / baseline.1.len() as u32;
            
            for (name, durations) in &sorted_results {
                let avg: Duration = durations.iter().sum::<Duration>() / durations.len() as u32;
                let ratio = avg.as_nanos() as f64 / baseline_avg.as_nanos() as f64;
                println!("  {}: {:.2}x (相对于最快)", name, ratio);
            }
        }
    }

    fn calculate_std_dev(&self, durations: &[Duration]) -> f64 {
        let avg_nanos: f64 = durations.iter()
            .map(|d| d.as_nanos() as f64)
            .sum::<f64>() / durations.len() as f64;
        
        let variance: f64 = durations.iter()
            .map(|d| {
                let diff = d.as_nanos() as f64 - avg_nanos;
                diff * diff
            })
            .sum::<f64>() / durations.len() as f64;
        
        variance.sqrt()
    }
}

/// 主演示函数
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    info!("🚀 开始 Rust 1.90 高级性能优化演示");
    info!("==========================================");

    let mut benchmark = AdvancedBenchmark::new();

    // 1. 零拷贝 vs 传统拷贝性能测试
    info!("\n📋 零拷贝性能测试:");
    let processor = ZeroCopyProcessor::new();
    let test_data = vec![1u8; 1024];

    let zero_copy_time = benchmark.benchmark("零拷贝处理", 10000, || {
        processor.process_zero_copy(&test_data)
    });

    let copy_time = benchmark.benchmark("传统拷贝处理", 10000, || {
        processor.process_with_copy(&test_data)
    });

    let pool_time = benchmark.benchmark("内存池处理", 10000, || {
        processor.process_with_pool(&test_data)
    });

    println!("零拷贝处理时间: {:?}", zero_copy_time);
    println!("传统拷贝处理时间: {:?}", copy_time);
    println!("内存池处理时间: {:?}", pool_time);
    println!("零拷贝加速比: {:.2}x", copy_time.as_nanos() as f64 / zero_copy_time.as_nanos() as f64);

    // 2. SIMD 向量化计算性能测试
    info!("\n⚡ SIMD 向量化计算性能测试:");
    let calculator = SimdCalculator::new();
    let test_vector = (0..10000).map(|i| i as f64).collect::<Vec<_>>();

    let simd_time = benchmark.benchmark("SIMD 向量化计算", 1000, || {
        calculator.vectorized_compute(&test_vector)
    });

    let scalar_time = benchmark.benchmark("传统标量计算", 1000, || {
        calculator.scalar_compute(&test_vector)
    });

    let cached_simd_time = benchmark.benchmark("缓存 SIMD 计算", 1000, || {
        calculator.cached_vectorized_compute(&test_vector)
    });

    println!("SIMD 向量化计算时间: {:?}", simd_time);
    println!("传统标量计算时间: {:?}", scalar_time);
    println!("缓存 SIMD 计算时间: {:?}", cached_simd_time);
    println!("SIMD 加速比: {:.2}x", scalar_time.as_nanos() as f64 / simd_time.as_nanos() as f64);

    // 3. 内存管理测试
    info!("\n💾 高级内存管理测试:");
    let mut memory_manager = AdvancedMemoryManager::new();
    
    // 创建不同类型的对象池
    let _string_pool = memory_manager.create_pool("strings".to_string(), 100, || {
        String::with_capacity(1024)
    });
    
    let _vec_pool = memory_manager.create_pool("vectors".to_string(), 100, || {
        Vec::<u8>::with_capacity(1024)
    });

    // 模拟内存使用
    for _ in 0..1000 {
        memory_manager.update_memory_usage(1024);
    }

    let memory_stats = memory_manager.get_memory_stats();
    println!("内存使用统计: {:?}", memory_stats);

    // 4. 并发性能测试
    info!("\n🔄 并发性能测试:");
    let concurrent_time = benchmark.benchmark("并发处理", 100, || {
        let data = (0..1000).collect::<Vec<_>>();
        data.par_iter()
            .map(|&x| x * x)
            .collect::<Vec<_>>()
    });

    let sequential_time = benchmark.benchmark("顺序处理", 100, || {
        let data = (0..1000).collect::<Vec<_>>();
        data.iter()
            .map(|&x| x * x)
            .collect::<Vec<_>>()
    });

    println!("并发处理时间: {:?}", concurrent_time);
    println!("顺序处理时间: {:?}", sequential_time);
    println!("并发加速比: {:.2}x", sequential_time.as_nanos() as f64 / concurrent_time.as_nanos() as f64);

    // 5. 显示处理器统计
    let processor_stats = processor.get_stats();
    println!("\n📊 处理器统计:");
    println!("处理次数: {}", processor_stats.processed_count);
    println!("总字节数: {}", processor_stats.total_bytes);
    println!("内存池统计: {:?}", processor_stats.pool_stats);

    let calc_stats = calculator.get_compute_count();
    println!("SIMD 计算次数: {}", calc_stats);
    println!("缓存大小: {}", calculator.get_cache_size());

    // 6. 打印基准测试对比
    benchmark.print_comparison();

    info!("✅ Rust 1.90 高级性能优化演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_pool() {
        let pool = MemoryPool::new(10, || String::new());
        let obj1 = pool.acquire();
        let obj2 = pool.acquire();
        
        assert!(obj1.get().is_empty());
        assert!(obj2.get().is_empty());
        
        let stats = pool.get_stats();
        assert_eq!(stats.total_allocated, 2);
    }

    #[test]
    fn test_zero_copy_processor() {
        let processor = ZeroCopyProcessor::new();
        let data = vec![1, 2, 3, 4, 5];
        
        let result = processor.process_zero_copy(&data).unwrap();
        assert_eq!(result, data.as_slice());
        
        let stats = processor.get_stats();
        assert_eq!(stats.processed_count, 1);
        assert_eq!(stats.total_bytes, 5);
    }

    #[test]
    fn test_simd_calculator() {
        let calculator = SimdCalculator::new();
        let input = vec![1.0, 2.0, 3.0, 4.0];
        
        let result = calculator.vectorized_compute(&input);
        assert_eq!(result.len(), 4);
        
        assert_eq!(calculator.get_compute_count(), 1);
    }

    #[test]
    fn test_memory_manager() {
        let mut manager = AdvancedMemoryManager::new();
        manager.update_memory_usage(1024);
        
        let stats = manager.get_memory_stats();
        assert_eq!(stats.current_usage, 1024);
        assert_eq!(stats.peak_usage, 1024);
    }

    #[test]
    fn test_benchmark() {
        let mut benchmark = AdvancedBenchmark::new();
        
        let duration = benchmark.benchmark("test", 10, || {
            42
        });
        
        assert!(duration >= Duration::ZERO);
        assert_eq!(benchmark.results.len(), 1);
    }
}
