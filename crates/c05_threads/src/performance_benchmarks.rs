//! 多线程性能基准测试模块
//! 
//! 本模块提供全面的多线程性能测试，包括：
//! - 线程池性能对比
//! - 无锁数据结构性能测试
//! - 并发算法性能基准
//! - 内存分配性能测试

use std::time::{Duration, Instant};
use std::sync::{Arc, Mutex};
use std::thread;
use std::sync::atomic::{AtomicUsize, Ordering};
use rayon::prelude::*;

use super::advanced_concurrency::{
    HighPerformanceThreadPool,
    LockFreeRingBuffer,
    LockFreeStack,
    parallel_reduce,
    parallel_map,
};

// ============================================================================
// 性能测试配置
// ============================================================================

/// 性能测试配置
#[derive(Debug, Clone)]
pub struct BenchmarkConfig {
    pub data_size: usize,
    pub thread_counts: Vec<usize>,
    pub iterations: usize,
    pub warmup_iterations: usize,
}

impl Default for BenchmarkConfig {
    fn default() -> Self {
        Self {
            data_size: 1_000_000,
            thread_counts: vec![1, 2, 4, 8, 16],
            iterations: 10,
            warmup_iterations: 3,
        }
    }
}

/// 性能测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub name: String,
    pub thread_count: usize,
    pub avg_time_ms: f64,
    pub min_time_ms: f64,
    pub max_time_ms: f64,
    pub throughput: f64,
    pub speedup: f64,
}

// ============================================================================
// 线程池性能对比测试
// ============================================================================

/// 线程池性能对比测试
pub fn benchmark_thread_pools(config: &BenchmarkConfig) -> Vec<BenchmarkResult> {
    let mut results = Vec::new();
    
    // 准备测试数据
    let data: Vec<i32> = (0..config.data_size).collect();
    
    for &thread_count in &config.thread_counts {
        // 测试标准线程池
        let result = benchmark_standard_thread_pool(&data, thread_count, config);
        results.push(result);
        
        // 测试高性能线程池
        let result = benchmark_high_performance_thread_pool(&data, thread_count, config);
        results.push(result);
        
        // 测试Rayon线程池
        let result = benchmark_rayon_thread_pool(&data, thread_count, config);
        results.push(result);
    }
    
    results
}

/// 标准线程池性能测试
fn benchmark_standard_thread_pool(
    data: &[i32],
    thread_count: usize,
    config: &BenchmarkConfig,
) -> BenchmarkResult {
    let mut times = Vec::new();
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        process_data_standard_threads(data, thread_count);
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        process_data_standard_threads(data, thread_count);
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "标准线程池".to_string(),
        thread_count,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: config.data_size as f64 / avg_time * 1000.0,
        speedup: if thread_count == 1 { 1.0 } else { 
            times[0] / avg_time 
        },
    }
}

/// 高性能线程池性能测试
fn benchmark_high_performance_thread_pool(
    data: &[i32],
    thread_count: usize,
    config: &BenchmarkConfig,
) -> BenchmarkResult {
    let mut times = Vec::new();
    let pool = HighPerformanceThreadPool::new(thread_count);
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        process_data_high_performance_thread_pool(&pool, data);
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        process_data_high_performance_thread_pool(&pool, data);
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "高性能线程池".to_string(),
        thread_count,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: config.data_size as f64 / avg_time * 1000.0,
        speedup: if thread_count == 1 { 1.0 } else { 
            times[0] / avg_time 
        },
    }
}

/// Rayon线程池性能测试
fn benchmark_rayon_thread_pool(
    data: &[i32],
    thread_count: usize,
    config: &BenchmarkConfig,
) -> BenchmarkResult {
    let mut times = Vec::new();
    
    // 设置Rayon线程池大小
    rayon::ThreadPoolBuilder::new()
        .num_threads(thread_count)
        .build_global()
        .unwrap();
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        process_data_rayon(data);
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        process_data_rayon(data);
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "Rayon线程池".to_string(),
        thread_count,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: config.data_size as f64 / avg_time * 1000.0,
        speedup: if thread_count == 1 { 1.0 } else { 
            times[0] / avg_time 
        },
    }
}

// ============================================================================
// 数据处理函数
// ============================================================================

/// 使用标准线程处理数据
fn process_data_standard_threads(data: &[i32], thread_count: usize) -> Vec<i32> {
    let chunk_size = (data.len() + thread_count - 1) / thread_count;
    let data = Arc::new(data.to_vec());
    let results = Arc::new(Mutex::new(vec![0; data.len()]));
    
    let handles: Vec<_> = (0..thread_count)
        .map(|i| {
            let data = Arc::clone(&data);
            let results = Arc::clone(&results);
            
            thread::spawn(move || {
                let start = i * chunk_size;
                let end = std::cmp::min(start + chunk_size, data.len());
                
                if start < end {
                    let chunk = &data[start..end];
                    let processed_chunk: Vec<i32> = chunk.iter()
                        .map(|&x| x * 2 + 1)
                        .collect();
                    
                    let mut results = results.lock().unwrap();
                    for (j, &value) in processed_chunk.iter().enumerate() {
                        results[start + j] = value;
                    }
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    Arc::try_unwrap(results).unwrap().into_inner().unwrap()
}

/// 使用高性能线程池处理数据
fn process_data_high_performance_thread_pool(
    pool: &HighPerformanceThreadPool,
    data: &[i32],
) -> Vec<i32> {
    let chunk_size = (data.len() + 4 - 1) / 4; // 假设4个工作线程
    let mut results = vec![0; data.len()];
    
    let tasks: Vec<Box<dyn FnOnce() + Send + 'static>> = (0..4)
        .map(|i| {
            let data = data.to_vec();
            let start = i * chunk_size;
            let end = std::cmp::min(start + chunk_size, data.len());
            
            Box::new(move || {
                let chunk = &data[start..end];
                let processed_chunk: Vec<i32> = chunk.iter()
                    .map(|&x| x * 2 + 1)
                    .collect();
                
                (start, processed_chunk)
            })
        })
        .collect();
    
    let task_results = pool.execute_batch(tasks);
    
    for (start, processed_chunk) in task_results {
        let end = std::cmp::min(start + processed_chunk.len(), results.len());
        results[start..end].copy_from_slice(&processed_chunk[..end-start]);
    }
    
    results
}

/// 使用Rayon处理数据
fn process_data_rayon(data: &[i32]) -> Vec<i32> {
    data.par_iter()
        .map(|&x| x * 2 + 1)
        .collect()
}

// ============================================================================
// 无锁数据结构性能测试
// ============================================================================

/// 无锁数据结构性能测试
pub fn benchmark_lock_free_structures(config: &BenchmarkConfig) -> Vec<BenchmarkResult> {
    let mut results = Vec::new();
    
    // 测试无锁环形缓冲区
    let result = benchmark_lock_free_ring_buffer(config);
    results.push(result);
    
    // 测试无锁栈
    let result = benchmark_lock_free_stack(config);
    results.push(result);
    
    // 测试标准Mutex保护的数据结构
    let result = benchmark_mutex_structures(config);
    results.push(result);
    
    results
}

/// 无锁环形缓冲区性能测试
fn benchmark_lock_free_ring_buffer(config: &BenchmarkConfig) -> BenchmarkResult {
    let mut times = Vec::new();
    let buffer = LockFreeRingBuffer::new(config.data_size);
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        for i in 0..config.data_size {
            let _ = buffer.try_push(i);
        }
        for _ in 0..config.data_size {
            let _ = buffer.try_pop();
        }
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        for i in 0..config.data_size {
            let _ = buffer.try_push(i);
        }
        for _ in 0..config.data_size {
            let _ = buffer.try_pop();
        }
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "无锁环形缓冲区".to_string(),
        thread_count: 1,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: (config.data_size * 2) as f64 / avg_time * 1000.0,
        speedup: 1.0,
    }
}

/// 无锁栈性能测试
fn benchmark_lock_free_stack(config: &BenchmarkConfig) -> BenchmarkResult {
    let mut times = Vec::new();
    let stack = LockFreeStack::new(config.data_size);
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        for i in 0..config.data_size {
            let _ = stack.push(i);
        }
        for _ in 0..config.data_size {
            let _ = stack.pop();
        }
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        for i in 0..config.data_size {
            let _ = stack.push(i);
        }
        for _ in 0..config.data_size {
            let _ = stack.pop();
        }
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "无锁栈".to_string(),
        thread_count: 1,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: (config.data_size * 2) as f64 / avg_time * 1000.0,
        speedup: 1.0,
    }
}

/// Mutex保护的数据结构性能测试
fn benchmark_mutex_structures(config: &BenchmarkConfig) -> BenchmarkResult {
    let mut times = Vec::new();
    let data = Arc::new(Mutex::new(Vec::new()));
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        for i in 0..config.data_size {
            data.lock().unwrap().push(i);
        }
        for _ in 0..config.data_size {
            data.lock().unwrap().pop();
        }
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        for i in 0..config.data_size {
            data.lock().unwrap().push(i);
        }
        for _ in 0..config.data_size {
            data.lock().unwrap().pop();
        }
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "Mutex保护的数据结构".to_string(),
        thread_count: 1,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: (config.data_size * 2) as f64 / avg_time * 1000.0,
        speedup: 1.0,
    }
}

// ============================================================================
// 并发算法性能测试
// ============================================================================

/// 并发算法性能测试
pub fn benchmark_concurrent_algorithms(config: &BenchmarkConfig) -> Vec<BenchmarkResult> {
    let mut results = Vec::new();
    let data: Vec<i32> = (0..config.data_size).collect();
    
    for &thread_count in &config.thread_counts {
        // 测试并发归约
        let result = benchmark_parallel_reduce(&data, thread_count, config);
        results.push(result);
        
        // 测试并发映射
        let result = benchmark_parallel_map(&data, thread_count, config);
        results.push(result);
        
        // 测试Rayon并行算法
        let result = benchmark_rayon_algorithms(&data, thread_count, config);
        results.push(result);
    }
    
    results
}

/// 并发归约性能测试
fn benchmark_parallel_reduce(
    data: &[i32],
    thread_count: usize,
    config: &BenchmarkConfig,
) -> BenchmarkResult {
    let mut times = Vec::new();
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        let _ = parallel_reduce(data, thread_count, 0, |acc, x| acc + x);
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        let _ = parallel_reduce(data, thread_count, 0, |acc, x| acc + x);
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "并发归约".to_string(),
        thread_count,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: config.data_size as f64 / avg_time * 1000.0,
        speedup: if thread_count == 1 { 1.0 } else { 
            times[0] / avg_time 
        },
    }
}

/// 并发映射性能测试
fn benchmark_parallel_map(
    data: &[i32],
    thread_count: usize,
    config: &BenchmarkConfig,
) -> BenchmarkResult {
    let mut times = Vec::new();
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        let _ = parallel_map(data, thread_count, |&x| x * 2 + 1);
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        let _ = parallel_map(data, thread_count, |&x| x * 2 + 1);
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "并发映射".to_string(),
        thread_count,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: config.data_size as f64 / avg_time * 1000.0,
        speedup: if thread_count == 1 { 1.0 } else { 
            times[0] / avg_time 
        },
    }
}

/// Rayon并行算法性能测试
fn benchmark_rayon_algorithms(
    data: &[i32],
    thread_count: usize,
    config: &BenchmarkConfig,
) -> BenchmarkResult {
    let mut times = Vec::new();
    
    // 设置Rayon线程池大小
    rayon::ThreadPoolBuilder::new()
        .num_threads(thread_count)
        .build_global()
        .unwrap();
    
    // 预热
    for _ in 0..config.warmup_iterations {
        let start = Instant::now();
        let _: Vec<i32> = data.par_iter().map(|&x| x * 2 + 1).collect();
        let _ = start.elapsed();
    }
    
    // 正式测试
    for _ in 0..config.iterations {
        let start = Instant::now();
        let _: Vec<i32> = data.par_iter().map(|&x| x * 2 + 1).collect();
        times.push(start.elapsed().as_micros() as f64 / 1000.0);
    }
    
    let avg_time = times.iter().sum::<f64>() / times.len() as f64;
    let min_time = times.iter().fold(f64::INFINITY, |a, &b| a.min(b));
    let max_time = times.iter().fold(0.0, |a, &b| a.max(b));
    
    BenchmarkResult {
        name: "Rayon并行算法".to_string(),
        thread_count,
        avg_time_ms: avg_time,
        min_time_ms: min_time,
        max_time_ms: max_time,
        throughput: config.data_size as f64 / avg_time * 1000.0,
        speedup: if thread_count == 1 { 1.0 } else { 
            times[0] / avg_time 
        },
    }
}

// ============================================================================
// 性能报告生成
// ============================================================================

/// 生成性能测试报告
pub fn generate_performance_report(results: &[BenchmarkResult]) -> String {
    let mut report = String::new();
    report.push_str("# 多线程性能测试报告\n\n");
    
    // 按名称分组结果
    let mut grouped_results: std::collections::HashMap<String, Vec<&BenchmarkResult>> = 
        std::collections::HashMap::new();
    
    for result in results {
        grouped_results.entry(result.name.clone()).or_default().push(result);
    }
    
    for (name, group_results) in grouped_results {
        report.push_str(&format!("## {}\n\n", name));
        report.push_str("| 线程数 | 平均时间(ms) | 最小时间(ms) | 最大时间(ms) | 吞吐量 | 加速比 |\n");
        report.push_str("|--------|--------------|--------------|--------------|--------|--------|\n");
        
        for result in group_results {
            report.push_str(&format!(
                "| {} | {:.2} | {:.2} | {:.2} | {:.0} | {:.2} |\n",
                result.thread_count,
                result.avg_time_ms,
                result.min_time_ms,
                result.max_time_ms,
                result.throughput,
                result.speedup,
            ));
        }
        report.push_str("\n");
    }
    
    report
}

// ============================================================================
// 测试模块
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_benchmark_config() {
        let config = BenchmarkConfig::default();
        assert_eq!(config.data_size, 1_000_000);
        assert_eq!(config.thread_counts, vec![1, 2, 4, 8, 16]);
        assert_eq!(config.iterations, 10);
        assert_eq!(config.warmup_iterations, 3);
    }
    
    #[test]
    fn test_benchmark_result() {
        let result = BenchmarkResult {
            name: "测试".to_string(),
            thread_count: 4,
            avg_time_ms: 100.0,
            min_time_ms: 90.0,
            max_time_ms: 110.0,
            throughput: 10000.0,
            speedup: 3.5,
        };
        
        assert_eq!(result.name, "测试");
        assert_eq!(result.thread_count, 4);
        assert_eq!(result.avg_time_ms, 100.0);
        assert_eq!(result.speedup, 3.5);
    }
    
    #[test]
    fn test_generate_performance_report() {
        let results = vec![
            BenchmarkResult {
                name: "测试1".to_string(),
                thread_count: 1,
                avg_time_ms: 100.0,
                min_time_ms: 90.0,
                max_time_ms: 110.0,
                throughput: 10000.0,
                speedup: 1.0,
            },
            BenchmarkResult {
                name: "测试1".to_string(),
                thread_count: 2,
                avg_time_ms: 50.0,
                min_time_ms: 45.0,
                max_time_ms: 55.0,
                throughput: 20000.0,
                speedup: 2.0,
            },
        ];
        
        let report = generate_performance_report(&results);
        assert!(report.contains("多线程性能测试报告"));
        assert!(report.contains("测试1"));
        assert!(report.contains("| 线程数 |"));
    }
}
