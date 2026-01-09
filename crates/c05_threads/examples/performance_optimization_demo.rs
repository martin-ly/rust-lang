//! 性能优化示例
//!
//! 本示例展示了各种线程性能优化技术：
//! - 缓存行填充避免伪共享
//! - 内存对齐优化
//! - 无锁数据结构性能对比
//! - 线程池性能调优
//! - NUMA 感知优化
//! - 工作窃取性能分析

use std::sync::{Arc, Mutex, atomic::{AtomicUsize, Ordering}};
use std::thread;
use std::time::{Duration, Instant};
use std::collections::VecDeque;
use rayon::prelude::*;

/// 缓存行填充结构
#[repr(align(64))]
pub struct CacheLinePadded<T> {
    value: T,
    _padding: [u8; 64],
}

impl<T> CacheLinePadded<T> {
    pub fn new(value: T) -> Self {
        Self {
            value,
            _padding: [0; 64],
        }
    }

    pub fn get(&self) -> &T {
        &self.value
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut self.value
    }
}

/// 伪共享测试
pub struct FalseSharingTest {
    counters: Vec<Arc<CacheLinePadded<AtomicUsize>>>,
}

impl FalseSharingTest {
    pub fn new(num_counters: usize) -> Self {
        let counters = (0..num_counters)
            .map(|_| Arc::new(CacheLinePadded::new(AtomicUsize::new(0))))
            .collect();

        Self { counters }
    }

    pub fn run_test(&self, iterations: usize) -> Duration {
        let start = Instant::now();
        let handles: Vec<_> = self.counters.iter().map(|counter| {
            let counter = Arc::clone(counter);
            thread::spawn(move || {
                for _ in 0..iterations {
                    counter.get().fetch_add(1, Ordering::Relaxed);
                }
            })
        }).collect();

        for handle in handles {
            handle.join().unwrap();
        }

        start.elapsed()
    }

    pub fn get_total(&self) -> usize {
        self.counters.iter().map(|c| c.get().load(Ordering::Relaxed)).sum()
    }
}

/// 无锁队列性能测试
pub struct LockFreeQueueBenchmark {
    queue: Arc<crossbeam_queue::SegQueue<usize>>,
}

impl LockFreeQueueBenchmark {
    pub fn new() -> Self {
        Self {
            queue: Arc::new(crossbeam_queue::SegQueue::new()),
        }
    }

    pub fn benchmark_push_pop(&self, num_operations: usize) -> Duration {
        let start = Instant::now();

        // 生产者线程
        let producer = {
            let queue = Arc::clone(&self.queue);
            thread::spawn(move || {
                for i in 0..num_operations {
                    queue.push(i);
                }
            })
        };

        // 消费者线程
        let consumer = {
            let queue = Arc::clone(&self.queue);
            thread::spawn(move || {
                let mut count = 0;
                while count < num_operations {
                    if queue.pop().is_some() {
                        count += 1;
                    }
                }
            })
        };

        producer.join().unwrap();
        consumer.join().unwrap();

        start.elapsed()
    }
}

/// 有锁队列性能测试
pub struct LockedQueueBenchmark {
    queue: Arc<Mutex<VecDeque<usize>>>,
}

impl LockedQueueBenchmark {
    pub fn new() -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    pub fn benchmark_push_pop(&self, num_operations: usize) -> Duration {
        let start = Instant::now();
        let queue = Arc::clone(&self.queue);

        // 生产者线程
        let producer = {
            let queue = Arc::clone(&queue);
            thread::spawn(move || {
                for i in 0..num_operations {
                    queue.lock().unwrap().push_back(i);
                }
            })
        };

        // 消费者线程
        let consumer = {
            let queue = Arc::clone(&queue);
            thread::spawn(move || {
                let mut count = 0;
                while count < num_operations {
                    if queue.lock().unwrap().pop_front().is_some() {
                        count += 1;
                    }
                }
            })
        };

        producer.join().unwrap();
        consumer.join().unwrap();

        start.elapsed()
    }
}

/// 线程池性能测试
pub struct ThreadPoolBenchmark;

impl ThreadPoolBenchmark {
    pub fn benchmark_rayon_pool(num_tasks: usize, num_threads: usize) -> Duration {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap();

        let start = Instant::now();

        pool.install(|| {
            (0..num_tasks).into_par_iter().for_each(|i| {
                // 模拟计算密集型任务
                let mut sum = 0;
                for j in 0..1000 {
                    sum += i * j;
                }
                std::hint::black_box(sum);
            });
        });

        start.elapsed()
    }

    pub fn benchmark_std_threads(num_tasks: usize, num_threads: usize) -> Duration {
        let start = Instant::now();
        let tasks_per_thread = num_tasks / num_threads;
        let mut handles = vec![];

        for thread_id in 0..num_threads {
            let start_task = thread_id * tasks_per_thread;
            let end_task = if thread_id == num_threads - 1 {
                num_tasks
            } else {
                (thread_id + 1) * tasks_per_thread
            };

            let handle = thread::spawn(move || {
                for i in start_task..end_task {
                    // 模拟计算密集型任务
                    let mut sum = 0;
                    for j in 0..1000 {
                        sum += i * j;
                    }
                    std::hint::black_box(sum);
                }
            });

            handles.push(handle);
        }

        for handle in handles {
            handle.join().unwrap();
        }

        start.elapsed()
    }
}

/// NUMA 感知优化测试
pub struct NumaAwareBenchmark;

impl NumaAwareBenchmark {
    pub fn benchmark_memory_access_pattern() -> (Duration, Duration) {
        const SIZE: usize = 1024 * 1024; // 1MB
        let data = vec![0u64; SIZE];

        // 顺序访问
        let start = Instant::now();
        let mut sum = 0u64;
        for &value in &data {
            sum += value;
        }
        let sequential_time = start.elapsed();
        std::hint::black_box(sum);

        // 随机访问
        let start = Instant::now();
        let mut sum = 0u64;
        for i in 0..SIZE {
            let index = (i * 7) % SIZE; // 伪随机访问模式
            sum += data[index];
        }
        let random_time = start.elapsed();
        std::hint::black_box(sum);

        (sequential_time, random_time)
    }

    pub fn benchmark_parallel_memory_access() -> Duration {
        const SIZE: usize = 1024 * 1024;
        let data = Arc::new(vec![0u64; SIZE]);

        let start = Instant::now();

        let handles: Vec<_> = (0..4).map(|thread_id| {
            let data = Arc::clone(&data);
            thread::spawn(move || {
                let mut sum = 0u64;
                let chunk_size = SIZE / 4;
                let start = thread_id * chunk_size;
                let end = if thread_id == 3 { SIZE } else { (thread_id + 1) * chunk_size };

                for i in start..end {
                    sum += data[i];
                }
                sum
            })
        }).collect();

        let total_sum: u64 = handles.into_iter()
            .map(|h| h.join().unwrap())
            .sum();

        std::hint::black_box(total_sum);
        start.elapsed()
    }
}

/// 工作窃取性能分析
pub struct WorkStealingAnalysis;

impl WorkStealingAnalysis {
    pub fn analyze_load_balancing(num_tasks: usize, num_threads: usize) -> Vec<Duration> {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_threads)
            .build()
            .unwrap();

        let task_durations = Arc::new(Mutex::new(Vec::new()));

        pool.install(|| {
            let task_durations = Arc::clone(&task_durations);

            (0..num_tasks).into_par_iter().for_each(|i| {
                let start = Instant::now();

                // 模拟不同计算量的任务
                let workload = 1000 + (i % 100) * 10;
                let mut sum = 0;
                for j in 0..workload {
                    sum += i * j;
                }
                std::hint::black_box(sum);

                let duration = start.elapsed();
                task_durations.lock().unwrap().push(duration);
            });
        });

        task_durations.lock().unwrap().clone()
    }

    pub fn calculate_load_balance_metrics(durations: &[Duration]) -> (Duration, Duration, f64) {
        let total: Duration = durations.iter().sum();
        let avg = total / durations.len() as u32;

        let max = durations.iter().max().unwrap().clone();
        let min = durations.iter().min().unwrap().clone();

        let variance = durations.iter()
            .map(|d| {
                let diff = if *d > avg { *d - avg } else { avg - *d };
                diff.as_nanos() as f64
            })
            .sum::<f64>() / durations.len() as f64;

        (min, max, variance)
    }
}

/// 内存分配性能测试
pub struct MemoryAllocationBenchmark;

impl MemoryAllocationBenchmark {
    pub fn benchmark_vec_growth() -> Duration {
        let start = Instant::now();

        let mut vec = Vec::new();
        for i in 0..100000 {
            vec.push(i);
        }

        start.elapsed()
    }

    pub fn benchmark_vec_with_capacity() -> Duration {
        let start = Instant::now();

        let mut vec = Vec::with_capacity(100000);
        for i in 0..100000 {
            vec.push(i);
        }

        start.elapsed()
    }

    pub fn benchmark_parallel_allocation() -> Duration {
        let start = Instant::now();

        let handles: Vec<_> = (0..4).map(|_| {
            thread::spawn(|| {
                let mut vec = Vec::new();
                for i in 0..25000 {
                    vec.push(i);
                }
                vec
            })
        }).collect();

        for handle in handles {
            handle.join().unwrap();
        }

        start.elapsed()
    }
}

/// 运行性能优化演示
fn main() {
    println!("=== 性能优化示例 ===\n");

    // 1. 伪共享测试
    println!("1. 伪共享测试:");
    let false_sharing_test = FalseSharingTest::new(4);
    let duration = false_sharing_test.run_test(1000000);
    println!("4个计数器各递增100万次，耗时: {:?}", duration);
    println!("总计数: {}", false_sharing_test.get_total());
    println!();

    // 2. 无锁 vs 有锁队列性能对比
    println!("2. 无锁 vs 有锁队列性能对比:");
    let lockfree_queue = LockFreeQueueBenchmark::new();
    let locked_queue = LockedQueueBenchmark::new();

    let num_ops = 100000;
    let lockfree_time = lockfree_queue.benchmark_push_pop(num_ops);
    let locked_time = locked_queue.benchmark_push_pop(num_ops);

    println!("无锁队列 {} 次操作耗时: {:?}", num_ops, lockfree_time);
    println!("有锁队列 {} 次操作耗时: {:?}", num_ops, locked_time);
    println!("性能提升: {:.2}x", locked_time.as_nanos() as f64 / lockfree_time.as_nanos() as f64);
    println!();

    // 3. 线程池性能对比
    println!("3. 线程池性能对比:");
    let num_tasks = 10000;
    let num_threads = 4;

    let rayon_time = ThreadPoolBenchmark::benchmark_rayon_pool(num_tasks, num_threads);
    let std_time = ThreadPoolBenchmark::benchmark_std_threads(num_tasks, num_threads);

    println!("Rayon 线程池 {} 个任务耗时: {:?}", num_tasks, rayon_time);
    println!("标准线程 {} 个任务耗时: {:?}", num_tasks, std_time);
    println!("性能提升: {:.2}x", std_time.as_nanos() as f64 / rayon_time.as_nanos() as f64);
    println!();

    // 4. NUMA 感知优化
    println!("4. NUMA 感知优化:");
    let (sequential_time, random_time) = NumaAwareBenchmark::benchmark_memory_access_pattern();
    let parallel_time = NumaAwareBenchmark::benchmark_parallel_memory_access();

    println!("顺序内存访问耗时: {:?}", sequential_time);
    println!("随机内存访问耗时: {:?}", random_time);
    println!("并行内存访问耗时: {:?}", parallel_time);
    println!("顺序 vs 随机性能比: {:.2}x", random_time.as_nanos() as f64 / sequential_time.as_nanos() as f64);
    println!();

    // 5. 工作窃取负载均衡分析
    println!("5. 工作窃取负载均衡分析:");
    let durations = WorkStealingAnalysis::analyze_load_balancing(1000, 4);
    let (min, max, variance) = WorkStealingAnalysis::calculate_load_balance_metrics(&durations);

    println!("任务执行时间统计:");
    println!("  最短: {:?}", min);
    println!("  最长: {:?}", max);
    println!("  方差: {:.2}", variance);
    println!("  负载均衡度: {:.2}%", (1.0 - variance / max.as_nanos() as f64) * 100.0);
    println!();

    // 6. 内存分配性能测试
    println!("6. 内存分配性能测试:");
    let growth_time = MemoryAllocationBenchmark::benchmark_vec_growth();
    let capacity_time = MemoryAllocationBenchmark::benchmark_vec_with_capacity();
    let parallel_time = MemoryAllocationBenchmark::benchmark_parallel_allocation();

    println!("动态增长 Vec 耗时: {:?}", growth_time);
    println!("预分配容量 Vec 耗时: {:?}", capacity_time);
    println!("并行分配耗时: {:?}", parallel_time);
    println!("预分配性能提升: {:.2}x", growth_time.as_nanos() as f64 / capacity_time.as_nanos() as f64);
    println!();

    println!("=== 性能优化示例完成 ===");
}
