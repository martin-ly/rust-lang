//! 性能优化实践
//!
//! 本模块展示了Rust中各种性能优化技术的实践案例，
//! 包括内存优化、并发优化、编译时优化和运行时性能分析。

use std::alloc::{Layout, alloc, dealloc};
use std::collections::HashMap;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicUsize, Ordering},
};
use std::thread;
use std::time::{Duration, Instant};

// ============================================================================
// 内存优化最佳实践
// ============================================================================

/// 内存池实现
pub struct MemoryPool {
    block_size: usize,
    block_count: usize,
    free_blocks: Vec<*mut u8>,
    allocated_blocks: HashMap<*mut u8, bool>,
    base_ptr: *mut u8,
}

impl MemoryPool {
    pub fn new(block_size: usize, block_count: usize) -> Self {
        let layout = Layout::from_size_align(block_size * block_count, 8).unwrap();
        let memory = unsafe { alloc(layout) };

        let mut free_blocks = Vec::with_capacity(block_count);
        for i in 0..block_count {
            let block_ptr = unsafe { memory.add(i * block_size) };
            free_blocks.push(block_ptr);
        }

        Self {
            block_size,
            block_count,
            free_blocks,
            allocated_blocks: HashMap::new(),
            base_ptr: memory,
        }
    }

    pub fn allocate(&mut self) -> Option<*mut u8> {
        self.free_blocks.pop().inspect(|&block| {
            self.allocated_blocks.insert(block, true);
        })
    }

    pub fn deallocate(&mut self, block: *mut u8) {
        if self.allocated_blocks.remove(&block).is_some() {
            self.free_blocks.push(block);
        }
    }

    pub fn get_utilization(&self) -> f32 {
        let allocated = self.allocated_blocks.len();
        allocated as f32 / self.block_count as f32
    }
}

impl Drop for MemoryPool {
    fn drop(&mut self) {
        let layout = Layout::from_size_align(self.block_size * self.block_count, 8).unwrap();
        unsafe {
            if !self.base_ptr.is_null() {
                dealloc(self.base_ptr, layout);
            }
        }
    }
}

/// 对象池实现
pub struct ObjectPool<T> {
    objects: Vec<T>,
    available: Vec<usize>,
    in_use: HashMap<usize, bool>,
}

impl<T> ObjectPool<T> {
    pub fn new<F>(size: usize, factory: F) -> Self
    where
        F: Fn() -> T,
    {
        let mut objects = Vec::with_capacity(size);
        let mut available = Vec::with_capacity(size);

        for _i in 0..size {
            objects.push(factory());
        }
        // 确保优先分配较小索引，使测试中 release(0), release(1) 生效
        for i in (0..size).rev() {
            available.push(i);
        }

        Self {
            objects,
            available,
            in_use: HashMap::new(),
        }
    }

    pub fn acquire(&mut self) -> Option<&mut T> {
        self.available.pop().map(|index| {
            self.in_use.insert(index, true);
            &mut self.objects[index]
        })
    }

    pub fn release(&mut self, index: usize) {
        if self.in_use.remove(&index).is_some() {
            self.available.push(index);
        }
    }

    pub fn get_utilization(&self) -> f32 {
        let total = self.objects.len();
        let used = self.in_use.len();
        used as f32 / total as f32
    }
}

/// 内存优化示例
pub struct MemoryOptimizedBuffer {
    data: Vec<u8>,
    capacity: usize,
}

impl MemoryOptimizedBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
            capacity,
        }
    }

    pub fn write(&mut self, bytes: &[u8]) {
        // 预分配空间以避免频繁重新分配
        if self.data.len() + bytes.len() > self.capacity {
            self.data.reserve(bytes.len());
        }
        self.data.extend_from_slice(bytes);
    }

    pub fn clear(&mut self) {
        self.data.clear();
        // 保持容量，避免重新分配
    }

    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
    }

    pub fn get_memory_usage(&self) -> (usize, usize) {
        (self.data.len(), self.data.capacity())
    }
}

// ============================================================================
// 并发性能优化
// ============================================================================

/// 无锁计数器
pub struct LockFreeCounter {
    value: AtomicUsize,
}

impl Default for LockFreeCounter {
    fn default() -> Self {
        Self::new()
    }
}

impl LockFreeCounter {
    pub fn new() -> Self {
        Self {
            value: AtomicUsize::new(0),
        }
    }

    pub fn increment(&self) {
        self.value.fetch_add(1, Ordering::Relaxed);
    }

    pub fn decrement(&self) {
        self.value.fetch_sub(1, Ordering::Relaxed);
    }

    pub fn get(&self) -> usize {
        self.value.load(Ordering::Relaxed)
    }
}

/// 线程池实现
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: std::sync::mpsc::Sender<Message>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

enum Message {
    NewJob(Job),
    Terminate,
}

struct Worker {
    #[allow(dead_code)]
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<std::sync::mpsc::Receiver<Message>>>) -> Worker {
        let thread = thread::spawn(move || {
            loop {
                let message = receiver.lock().unwrap().recv().unwrap();

                match message {
                    Message::NewJob(job) => {
                        println!("Worker {} got a job; executing.", id);
                        job();
                    }
                    Message::Terminate => {
                        println!("Worker {} was told to terminate.", id);
                        break;
                    }
                }
            }
        });

        Worker {
            id,
            thread: Some(thread),
        }
    }
}

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        assert!(size > 0);

        let (sender, receiver) = std::sync::mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));
        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool { workers, sender }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(Message::NewJob(job)).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        for _ in &self.workers {
            self.sender.send(Message::Terminate).unwrap();
        }

        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

/// 并发优化示例
pub struct ConcurrentOptimizedProcessor {
    thread_pool: ThreadPool,
    counter: LockFreeCounter,
}

impl ConcurrentOptimizedProcessor {
    pub fn new(thread_count: usize) -> Self {
        Self {
            thread_pool: ThreadPool::new(thread_count),
            counter: LockFreeCounter::new(),
        }
    }

    pub fn process_data_parallel(&self, data: Vec<i32>) -> Vec<i32> {
        let chunk_size =
            data.len().div_ceil(self.thread_pool.workers.len());
        let results_arc = Arc::new(Mutex::new(vec![0; data.len()]));

        for (i, chunk) in data.chunks(chunk_size).enumerate() {
            let results_arc = Arc::clone(&results_arc);
            let chunk = chunk.to_vec();

            self.thread_pool.execute(move || {
                let processed_chunk: Vec<i32> = chunk.iter().map(|&x| x * 2 + 1).collect();
                let mut results = results_arc.lock().unwrap();

                let start = i * chunk_size;
                let end = std::cmp::min(start + chunk.len(), results.len());
                results[start..end].copy_from_slice(&processed_chunk[..end - start]);
            });
        }

        // 等待所有任务完成
        thread::sleep(Duration::from_millis(100));

        
        Arc::try_unwrap(results_arc).unwrap().into_inner().unwrap()
    }

    pub fn get_processed_count(&self) -> usize {
        self.counter.get()
    }
}

// ============================================================================
// 编译时优化技术
// ============================================================================

/// 编译时常量函数
pub const fn calculate_fibonacci(n: u32) -> u32 {
    if n <= 1 {
        n
    } else {
        calculate_fibonacci(n - 1) + calculate_fibonacci(n - 2)
    }
}

/// 编译时优化的查找表
pub const LOOKUP_TABLE: [u32; 10] = [
    calculate_fibonacci(0),
    calculate_fibonacci(1),
    calculate_fibonacci(2),
    calculate_fibonacci(3),
    calculate_fibonacci(4),
    calculate_fibonacci(5),
    calculate_fibonacci(6),
    calculate_fibonacci(7),
    calculate_fibonacci(8),
    calculate_fibonacci(9),
];

/// 泛型优化示例
pub struct OptimizedContainer<T, const N: usize> {
    data: [T; N],
    len: usize,
}

impl<T: Default + Copy, const N: usize> Default for OptimizedContainer<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Default + Copy, const N: usize> OptimizedContainer<T, N> {
    pub fn new() -> Self {
        Self {
            data: [T::default(); N],
            len: 0,
        }
    }

    pub fn push(&mut self, item: T) -> Result<(), &'static str> {
        if self.len < N {
            self.data[self.len] = item;
            self.len += 1;
            Ok(())
        } else {
            Err("Container is full")
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            Some(&self.data[index])
        } else {
            None
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

/// 编译时优化的字符串处理
pub const fn string_length(s: &str) -> usize {
    s.len()
}

pub const HELLO_LENGTH: usize = string_length("Hello, World!");

// ============================================================================
// 运行时性能分析
// ============================================================================

/// 性能分析器
pub struct PerformanceProfiler {
    measurements: HashMap<String, Vec<Duration>>,
    current_measurements: HashMap<String, Instant>,
}

impl Default for PerformanceProfiler {
    fn default() -> Self {
        Self::new()
    }
}

impl PerformanceProfiler {
    pub fn new() -> Self {
        Self {
            measurements: HashMap::new(),
            current_measurements: HashMap::new(),
        }
    }

    pub fn start_measurement(&mut self, name: &str) {
        self.current_measurements
            .insert(name.to_string(), Instant::now());
    }

    pub fn end_measurement(&mut self, name: &str) {
        if let Some(start_time) = self.current_measurements.remove(name) {
            let duration = start_time.elapsed();
            self.measurements
                .entry(name.to_string())
                .or_default()
                .push(duration);
        }
    }

    pub fn get_average_time(&self, name: &str) -> Option<Duration> {
        self.measurements.get(name).map(|durations| {
            let total: Duration = durations.iter().sum();
            total / durations.len() as u32
        })
    }

    pub fn get_min_time(&self, name: &str) -> Option<Duration> {
        self.measurements
            .get(name)
            .and_then(|durations| durations.iter().min().copied())
    }

    pub fn get_max_time(&self, name: &str) -> Option<Duration> {
        self.measurements
            .get(name)
            .and_then(|durations| durations.iter().max().copied())
    }

    pub fn generate_report(&self) -> String {
        let mut report = String::from("性能分析报告\n");
        report.push_str("==============\n\n");

        for (name, durations) in &self.measurements {
            let avg = durations.iter().sum::<Duration>() / durations.len() as u32;
            let min = durations.iter().min().unwrap();
            let max = durations.iter().max().unwrap();

            report.push_str(&format!("{}:\n", name));
            report.push_str(&format!("  平均时间: {:?}\n", avg));
            report.push_str(&format!("  最短时间: {:?}\n", min));
            report.push_str(&format!("  最长时间: {:?}\n", max));
            report.push_str(&format!("  测量次数: {}\n\n", durations.len()));
        }

        report
    }
}

/// 性能基准测试
pub struct BenchmarkRunner {
    profiler: PerformanceProfiler,
}

impl Default for BenchmarkRunner {
    fn default() -> Self {
        Self::new()
    }
}

impl BenchmarkRunner {
    pub fn new() -> Self {
        Self {
            profiler: PerformanceProfiler::new(),
        }
    }

    pub fn run_benchmark<F>(&mut self, name: &str, iterations: usize, test_fn: F)
    where
        F: Fn(),
    {
        self.profiler.start_measurement(name);

        for _ in 0..iterations {
            test_fn();
        }

        self.profiler.end_measurement(name);
    }

    pub fn compare_benchmarks<F1, F2>(
        &mut self,
        name1: &str,
        name2: &str,
        iterations: usize,
        test1: F1,
        test2: F2,
    ) where
        F1: Fn(),
        F2: Fn(),
    {
        self.run_benchmark(name1, iterations, test1);
        self.run_benchmark(name2, iterations, test2);
    }

    pub fn generate_comparison_report(&self) -> String {
        self.profiler.generate_report()
    }
}

/// 内存使用分析器
pub struct MemoryProfiler {
    allocations: HashMap<String, usize>,
    deallocations: HashMap<String, usize>,
    peak_usage: HashMap<String, usize>,
}

impl Default for MemoryProfiler {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryProfiler {
    pub fn new() -> Self {
        Self {
            allocations: HashMap::new(),
            deallocations: HashMap::new(),
            peak_usage: HashMap::new(),
        }
    }

    pub fn record_allocation(&mut self, name: &str, size: usize) {
        *self.allocations.entry(name.to_string()).or_insert(0) += size;

        let current_usage =
            self.allocations.get(name).unwrap_or(&0) - self.deallocations.get(name).unwrap_or(&0);
        let peak = self.peak_usage.entry(name.to_string()).or_insert(0);
        *peak = std::cmp::max(*peak, current_usage);
    }

    pub fn record_deallocation(&mut self, name: &str, size: usize) {
        *self.deallocations.entry(name.to_string()).or_insert(0) += size;
    }

    pub fn get_current_usage(&self, name: &str) -> usize {
        self.allocations.get(name).unwrap_or(&0) - self.deallocations.get(name).unwrap_or(&0)
    }

    pub fn get_peak_usage(&self, name: &str) -> usize {
        *self.peak_usage.get(name).unwrap_or(&0)
    }

    pub fn generate_memory_report(&self) -> String {
        let mut report = String::from("内存使用报告\n");
        report.push_str("==============\n\n");

        for name in self.allocations.keys() {
            let current = self.get_current_usage(name);
            let peak = self.get_peak_usage(name);

            report.push_str(&format!("{}:\n", name));
            report.push_str(&format!("  当前使用: {} bytes\n", current));
            report.push_str(&format!("  峰值使用: {} bytes\n", peak));
            report.push_str(&format!(
                "  总分配: {} bytes\n",
                self.allocations.get(name).unwrap_or(&0)
            ));
            report.push_str(&format!(
                "  总释放: {} bytes\n\n",
                self.deallocations.get(name).unwrap_or(&0)
            ));
        }

        report
    }
}

// ============================================================================
// 性能优化示例和测试
// ============================================================================

/// 性能优化示例集合
pub struct PerformanceExamples;

impl PerformanceExamples {
    /// 内存优化示例
    pub fn memory_optimization_example() {
        println!("=== 内存优化示例 ===");

        // 内存池示例
        let mut pool = MemoryPool::new(1024, 10);
        let block1 = pool.allocate().unwrap();
        let block2 = pool.allocate().unwrap();

        println!("内存池利用率: {:.2}%", pool.get_utilization() * 100.0);

        pool.deallocate(block1);
        pool.deallocate(block2);

        // 对象池示例
        let mut object_pool = ObjectPool::new(5, String::new);
        let _obj1 = object_pool.acquire().unwrap();
        let _obj2 = object_pool.acquire().unwrap();

        println!(
            "对象池利用率: {:.2}%",
            object_pool.get_utilization() * 100.0
        );

        // 内存优化缓冲区示例
        let mut buffer = MemoryOptimizedBuffer::new(1000);
        buffer.write(b"Hello, World!");

        let (len, capacity) = buffer.get_memory_usage();
        println!("缓冲区使用: {} / {} bytes", len, capacity);
    }

    /// 并发优化示例
    pub fn concurrency_optimization_example() {
        println!("\n=== 并发优化示例 ===");

        // 无锁计数器示例
        let counter = Arc::new(LockFreeCounter::new());
        let mut handles = vec![];

        for _ in 0..10 {
            let counter = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..1000 {
                    counter.increment();
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        println!("无锁计数器最终值: {}", counter.get());

        // 线程池示例
        let processor = ConcurrentOptimizedProcessor::new(4);
        let data: Vec<i32> = (0..1000).collect();

        let start = Instant::now();
        let _result = processor.process_data_parallel(data);
        let duration = start.elapsed();

        println!("并发处理耗时: {:?}", duration);
    }

    /// 编译时优化示例
    pub fn compile_time_optimization_example() {
        println!("\n=== 编译时优化示例 ===");

        // 编译时常量
        println!("斐波那契数列第10项: {}", LOOKUP_TABLE[9]);
        println!("字符串长度: {}", HELLO_LENGTH);

        // 泛型优化容器
        let mut container: OptimizedContainer<i32, 10> = OptimizedContainer::new();
        for i in 0..5 {
            container.push(i).unwrap();
        }

        println!("容器长度: {}", container.len());
        println!("容器是否为空: {}", container.is_empty());
    }

    /// 运行时性能分析示例
    pub fn runtime_profiling_example() {
        println!("\n=== 运行时性能分析示例 ===");

        let mut benchmark = BenchmarkRunner::new();

        // 比较不同算法的性能
        benchmark.compare_benchmarks(
            "快速排序",
            "冒泡排序",
            100,
            || {
                let mut data: Vec<i32> = (0..100).rev().collect();
                data.sort();
            },
            || {
                let mut data: Vec<i32> = (0..100).rev().collect();
                for i in 0..data.len() {
                    for j in 0..data.len() - i - 1 {
                        if data[j] > data[j + 1] {
                            data.swap(j, j + 1);
                        }
                    }
                }
            },
        );

        println!("{}", benchmark.generate_comparison_report());

        // 内存分析
        let mut memory_profiler = MemoryProfiler::new();

        memory_profiler.record_allocation("测试1", 1024);
        memory_profiler.record_allocation("测试1", 512);
        memory_profiler.record_deallocation("测试1", 256);

        println!("{}", memory_profiler.generate_memory_report());
    }
}

// ============================================================================
// 单元测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_pool() {
        let mut pool = MemoryPool::new(1024, 5);

        let block1 = pool.allocate().unwrap();
        let block2 = pool.allocate().unwrap();

        assert_eq!(pool.get_utilization(), 0.4);

        pool.deallocate(block1);
        pool.deallocate(block2);

        assert_eq!(pool.get_utilization(), 0.0);
    }

    #[test]
    fn test_object_pool() {
        let mut pool = ObjectPool::new(3, || String::new());

        let _obj1 = pool.acquire().unwrap();
        let _obj2 = pool.acquire().unwrap();

        assert_eq!(pool.get_utilization(), 2.0 / 3.0);

        pool.release(0);
        pool.release(1);

        assert_eq!(pool.get_utilization(), 0.0);
    }

    #[test]
    fn test_lock_free_counter() {
        let counter = Arc::new(LockFreeCounter::new());
        let mut handles = vec![];

        for _ in 0..5 {
            let counter = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..100 {
                    counter.increment();
                }
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(counter.get(), 500);
    }

    #[test]
    fn test_optimized_container() {
        let mut container: OptimizedContainer<i32, 5> = OptimizedContainer::new();

        assert!(container.is_empty());

        container.push(1).unwrap();
        container.push(2).unwrap();

        assert_eq!(container.len(), 2);
        assert_eq!(*container.get(0).unwrap(), 1);
        assert_eq!(*container.get(1).unwrap(), 2);
    }

    #[test]
    fn test_performance_profiler() {
        let mut profiler = PerformanceProfiler::new();

        profiler.start_measurement("test");
        thread::sleep(Duration::from_millis(10));
        profiler.end_measurement("test");

        let avg_time = profiler.get_average_time("test");
        assert!(avg_time.is_some());
        assert!(avg_time.unwrap() >= Duration::from_millis(10));
    }

    #[test]
    fn test_memory_profiler() {
        let mut profiler = MemoryProfiler::new();

        profiler.record_allocation("test", 1024);
        profiler.record_allocation("test", 512);
        profiler.record_deallocation("test", 256);

        assert_eq!(profiler.get_current_usage("test"), 1280);
        assert_eq!(profiler.get_peak_usage("test"), 1536);
    }
}
