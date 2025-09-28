//! Rust 1.90 简化特性演示
//! 
//! 本示例展示了 Rust 1.90 的核心特性，包括常量泛型推断、
//! 生命周期语法一致性检查、函数指针比较检查等。

use c11_middlewares::rust190_optimizations::*;
use c11_middlewares::{Error, Result};
use std::collections::HashMap;

/// Rust 1.90 特性演示：常量泛型推断
#[derive(Debug, Clone)]
pub struct SmartBuffer<const SIZE: usize> {
    data: [u8; SIZE],
    position: usize,
}

impl<const SIZE: usize> SmartBuffer<SIZE> {
    pub fn new() -> Self {
        Self {
            data: [0; SIZE],
            position: 0,
        }
    }
    
    pub fn write(&mut self, bytes: &[u8]) -> Result<usize> {
        let available = SIZE - self.position;
        let to_write = bytes.len().min(available);
        
        if to_write == 0 {
            return Err(Error::Other("缓冲区已满".to_string()));
        }
        
        self.data[self.position..self.position + to_write].copy_from_slice(&bytes[..to_write]);
        self.position += to_write;
        
        Ok(to_write)
    }
    
    pub fn read(&mut self, buffer: &mut [u8]) -> Result<usize> {
        let available = self.position;
        let to_read = buffer.len().min(available);
        
        if to_read == 0 {
            return Ok(0);
        }
        
        buffer[..to_read].copy_from_slice(&self.data[..to_read]);
        
        // 移动剩余数据
        self.data.copy_within(to_read..self.position, 0);
        self.position -= to_read;
        
        Ok(to_read)
    }
    
    pub fn stats(&self) -> BufferStats {
        BufferStats {
            capacity: SIZE,
            used: self.position,
            available: SIZE - self.position,
            utilization: self.position as f64 / SIZE as f64,
        }
    }
}

#[derive(Debug)]
pub struct BufferStats {
    pub capacity: usize,
    pub used: usize,
    pub available: usize,
    pub utilization: f64,
}

/// Rust 1.90 特性演示：高级生命周期管理
pub struct DataProcessor<'a, T> 
where
    T: 'a + Send + Sync,
{
    data: &'a [T],
    processor: fn(&T) -> T,
    cache: HashMap<usize, T>,
}

impl<'a, T> DataProcessor<'a, T>
where
    T: 'a + Send + Sync + Clone + std::hash::Hash + Eq,
{
    pub fn new(data: &'a [T], processor: fn(&T) -> T) -> Self {
        Self {
            data,
            processor,
            cache: HashMap::new(),
        }
    }
    
    pub fn process_item(&mut self, index: usize) -> Result<&T> {
        if index >= self.data.len() {
            return Err(Error::Other("索引超出范围".to_string()));
        }
        
        // 检查缓存
        if self.cache.contains_key(&index) {
            return Ok(self.cache.get(&index).unwrap());
        }
        
        // 处理数据
        let processed = (self.processor)(&self.data[index]);
        self.cache.insert(index, processed);
        
        Ok(self.cache.get(&index).unwrap())
    }
    
    pub fn process_batch(&mut self, indices: &[usize]) -> Result<Vec<T>> {
        let mut results = Vec::with_capacity(indices.len());
        
        for &index in indices {
            if index >= self.data.len() {
                return Err(Error::Other("索引超出范围".to_string()));
            }
            
            // 检查缓存
            if let Some(cached) = self.cache.get(&index) {
                results.push(cached.clone());
            } else {
                // 处理数据
                let processed = (self.processor)(&self.data[index]);
                self.cache.insert(index, processed.clone());
                results.push(processed);
            }
        }
        
        Ok(results)
    }
}

/// 示例处理函数
#[allow(dead_code)]
fn double_processor(data: &i32) -> i32 {
    data * 2
}

/// 高级性能监控器
pub struct AdvancedPerformanceMonitor<const WINDOW_SIZE: usize> {
    metrics: [f64; WINDOW_SIZE],
    current_index: usize,
    total_samples: usize,
}

impl<const WINDOW_SIZE: usize> AdvancedPerformanceMonitor<WINDOW_SIZE> {
    pub fn new() -> Self {
        Self {
            metrics: [0.0; WINDOW_SIZE],
            current_index: 0,
            total_samples: 0,
        }
    }
    
    pub fn record(&mut self, value: f64) {
        self.metrics[self.current_index] = value;
        self.current_index = (self.current_index + 1) % WINDOW_SIZE;
        self.total_samples += 1;
    }
    
    pub fn get_performance_stats(&self) -> PerformanceStats {
        if self.total_samples == 0 {
            return PerformanceStats {
                average: 0.0,
                min: 0.0,
                max: 0.0,
                total_samples: 0,
                capacity: WINDOW_SIZE,
            };
        }
        
        let count = WINDOW_SIZE.min(self.total_samples);
        let slice = &self.metrics[..count];
        
        let sum: f64 = slice.iter().sum();
        let average = sum / count as f64;
        
        let min = slice.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let max = slice.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        
        PerformanceStats {
            average,
            min,
            max,
            total_samples: self.total_samples,
            capacity: WINDOW_SIZE,
        }
    }
}

#[cfg(feature = "tokio")]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Rust 1.90 简化特性演示 ===\n");
    
    // 1. 常量泛型推断演示
    println!("1. 常量泛型推断演示");
    println!("-------------------");
    
    let mut buffer: SmartBuffer<1024> = SmartBuffer::new();
    
    let test_data = b"Hello, Rust 1.90!";
    let written = buffer.write(test_data)?;
    println!("写入 {} 字节到缓冲区", written);
    
    let mut read_buffer = vec![0u8; 50];
    let read = buffer.read(&mut read_buffer)?;
    println!("从缓冲区读取 {} 字节: {}", read, String::from_utf8_lossy(&read_buffer[..read]));
    
    let stats = buffer.stats();
    println!("缓冲区统计: 容量={}, 已用={}, 可用={}, 利用率={:.2}%", 
             stats.capacity, stats.used, stats.available, stats.utilization * 100.0);
    
    // 2. 高级生命周期管理演示
    println!("\n2. 高级生命周期管理演示");
    println!("-------------------------");
    
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let mut processor = DataProcessor::new(&data, double_processor);
    
    let indices = vec![0, 2, 4, 6, 8];
    let processed = processor.process_batch(&indices)?;
    
    println!("原始数据: {:?}", &data[..10]);
    println!("处理索引: {:?}", indices);
    println!("处理结果: {:?}", processed);
    
    // 3. 高级性能监控演示
    println!("\n3. 高级性能监控演示");
    println!("--------------------");
    
    let mut monitor: AdvancedPerformanceMonitor<50> = AdvancedPerformanceMonitor::new();
    
    // 模拟一些性能数据
    for i in 0..20 {
        let value = 10.0 + (i as f64 * 0.5) + (i % 3) as f64 * 2.0;
        monitor.record(value);
        
        // 模拟时间流逝
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
    
    let stats = monitor.get_performance_stats();
    println!("性能统计:");
    println!("  平均: {:.2}", stats.average);
    println!("  最小: {:.2}", stats.min);
    println!("  最大: {:.2}", stats.max);
    println!("  样本数: {}", stats.total_samples);
    
    // 4. Rust 1.90 优化特性演示
    println!("\n4. Rust 1.90 优化特性演示");
    println!("--------------------------");
    
    // 使用我们的优化连接池
    let pool: OptimizedConnectionPool<10, 5000> = OptimizedConnectionPool::new();
    println!("创建连接池: 最大连接数={}, 超时={}ms", 10, 5000);
    
    // 使用我们的优化缓冲区
    let mut opt_buffer: OptimizedBuffer<256> = OptimizedBuffer::new();
    let data_to_store = "Rust 1.90 优化数据".as_bytes();
    opt_buffer.write(data_to_store)?;
    
    let _read_data = opt_buffer.read();
    println!("优化缓冲区读取完成");
    
    println!("\n=== 演示完成 ===");
    println!("所有 Rust 1.90 特性都正常工作！");
    
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("=== Rust 1.90 简化特性演示 ===");
    println!("此示例需要 tokio 特性才能运行");
    println!("请使用: cargo run --example rust190_simple_demo --features tokio");
    
    // 即使没有 tokio，我们也可以演示一些基本功能
    println!("\n基本功能演示:");
    
    let mut buffer: SmartBuffer<64> = SmartBuffer::new();
    let test_data = b"Hello";
    match buffer.write(test_data) {
        Ok(written) => println!("写入 {} 字节", written),
        Err(e) => println!("写入失败: {}", e),
    }
    
    let mut read_buffer = vec![0u8; 10];
    match buffer.read(&mut read_buffer) {
        Ok(read) => println!("读取 {} 字节: {}", read, String::from_utf8_lossy(&read_buffer[..read])),
        Err(e) => println!("读取失败: {}", e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_smart_buffer() {
        let mut buffer: SmartBuffer<64> = SmartBuffer::new();
        
        let test_data = b"test data";
        let written = buffer.write(test_data).unwrap();
        assert_eq!(written, 9);
        
        let mut read_buffer = vec![0u8; 20];
        let read = buffer.read(&mut read_buffer).unwrap();
        assert_eq!(read, 9);
        assert_eq!(&read_buffer[..read], test_data);
    }
    
    #[test]
    fn test_data_processor() {
        let data = vec![1, 2, 3, 4, 5];
        let mut processor = DataProcessor::new(&data, double_processor);
        
        let result = processor.process_item(2).unwrap();
        assert_eq!(*result, 6);
    }
    
    #[test]
    fn test_advanced_performance_monitor() {
        let mut monitor: AdvancedPerformanceMonitor<10> = AdvancedPerformanceMonitor::new();
        
        monitor.record(10.0);
        monitor.record(20.0);
        monitor.record(30.0);
        
        let stats = monitor.get_performance_stats();
        assert_eq!(stats.average, 20.0);
        assert_eq!(stats.min, 10.0);
        assert_eq!(stats.max, 30.0);
        assert_eq!(stats.total_samples, 3);
    }
}
