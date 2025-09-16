//! 并发编程模式 - Rust 1.89 特性集成
//!
//! 本模块提供了现代并发编程的核心模式，结合 Rust 1.89 的新特性
//! 包括：生产者-消费者、读者-写者、工作窃取、分治等模式

use std::sync::{
    Arc,
    Mutex,
    //Condvar,
    //Barrier
};

use std::thread;
use std::time::Duration;
// use std::collections::VecDeque;
use crossbeam_channel::{Receiver, Sender, bounded, unbounded};
use parking_lot::{
    //Mutex as ParkingMutex,
    RwLock as ParkingRwLock,
};
use rayon::prelude::*;

/// 生产者-消费者模式实现
///
/// 使用 Rust 1.89 的 scoped threads 和 crossbeam channels
/// 提供高性能的生产者-消费者通信
#[allow(dead_code)]
pub struct ProducerConsumer<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
    buffer_size: usize,
}

impl<T> ProducerConsumer<T> {
    /// 创建新的生产者-消费者实例
    pub fn new(buffer_size: usize) -> Self {
        let (sender, receiver) = bounded(buffer_size);
        Self {
            sender,
            receiver,
            buffer_size,
        }
    }

    /// 创建无界通道的生产者-消费者
    pub fn unbounded() -> Self {
        let (sender, receiver) = unbounded();
        Self {
            sender,
            receiver,
            buffer_size: 0, // 无界
        }
    }

    /// 获取发送端
    pub fn sender(&self) -> Sender<T> {
        self.sender.clone()
    }

    /// 获取接收端
    pub fn receiver(&self) -> Receiver<T> {
        self.receiver.clone()
    }

    /// 运行生产者-消费者示例
    pub fn run_example() {
        let pc = ProducerConsumer::new(10);
        let sender = pc.sender();
        let receiver = pc.receiver();

        // 使用 scoped threads 确保安全借用
        thread::scope(|s| {
            // 生产者线程
            s.spawn(move || {
                for i in 0..100 {
                    sender.send(i).unwrap();
                    if i % 10 == 0 {
                        thread::sleep(Duration::from_millis(1));
                    }
                }
            });

            // 消费者线程
            s.spawn(move || {
                let mut count = 0;
                while let Ok(value) = receiver.recv() {
                    count += 1;
                    if count % 20 == 0 {
                        println!("Consumed: {}", value);
                    }
                }
                println!("Total consumed: {}", count);
            });
        });
    }
}

/// 读者-写者模式实现
///
/// 使用 parking_lot 的高性能读写锁
/// 支持多个读者或单个写者
#[allow(dead_code)]
pub struct ReaderWriterPattern<T> {
    data: Arc<ParkingRwLock<T>>,
    readers_count: Arc<Mutex<usize>>,
    writer_active: Arc<Mutex<bool>>,
}

impl<T> ReaderWriterPattern<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(ParkingRwLock::new(data)),
            readers_count: Arc::new(Mutex::new(0)),
            writer_active: Arc::new(Mutex::new(false)),
        }
    }

    /// 读者操作
    pub fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let guard = self.data.read();
        f(&guard)
    }

    /// 写者操作
    pub fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut guard = self.data.write();
        f(&mut guard)
    }

    /// 运行读者-写者示例
    pub fn run_example() {
        let rw = Arc::new(ReaderWriterPattern::new(vec![1, 2, 3, 4, 5]));

        thread::scope(|s| {
            // 多个读者线程
            for i in 0..5 {
                let rw_clone = rw.clone();
                s.spawn(move || {
                    for _ in 0..10 {
                        let sum: i32 = rw_clone.read(|data| data.iter().sum());
                        println!("Reader {}: sum = {}", i, sum);
                        thread::sleep(Duration::from_millis(10));
                    }
                });
            }

            // 写者线程
            let rw_clone = rw.clone();
            s.spawn(move || {
                for i in 0..3 {
                    rw_clone.write(|data| {
                        data.push(10 + i);
                        println!("Writer: added {}", 10 + i);
                    });
                    thread::sleep(Duration::from_millis(50));
                }
            });
        });
    }
}

/// 分治模式实现
///
/// 使用 rayon 进行并行分治计算
pub struct DivideAndConquer {
    threshold: usize,
}

impl DivideAndConquer {
    pub fn new(threshold: usize) -> Self {
        Self { threshold }
    }

    /// 并行归并排序
    pub fn parallel_merge_sort<T>(&self, mut data: Vec<T>) -> Vec<T>
    where
        T: Send + Sync + Clone + Ord,
    {
        if data.len() <= self.threshold {
            data.sort();
            return data;
        }

        let mid = data.len() / 2;
        let (left, right) = data.split_at(mid);

        let (left_sorted, right_sorted) = rayon::join(
            || self.parallel_merge_sort(left.to_vec()),
            || self.parallel_merge_sort(right.to_vec()),
        );

        self.merge(left_sorted, right_sorted)
    }

    fn merge<T>(&self, mut left: Vec<T>, mut right: Vec<T>) -> Vec<T>
    where
        T: Ord,
    {
        let mut result = Vec::with_capacity(left.len() + right.len());

        while !left.is_empty() && !right.is_empty() {
            if left[0] <= right[0] {
                result.push(left.remove(0));
            } else {
                result.push(right.remove(0));
            }
        }

        result.extend(left);
        result.extend(right);
        result
    }

    /// 并行快速排序
    pub fn parallel_quicksort<T>(&self, mut data: Vec<T>) -> Vec<T>
    where
        T: Send + Sync + Clone + Ord,
    {
        if data.len() <= self.threshold {
            data.sort();
            return data;
        }

        let pivot = data.len() / 2;
        let pivot_val = data[pivot].clone();

        let (left, right): (Vec<T>, Vec<T>) = data.into_iter().partition(|x| *x < pivot_val);

        let (left_sorted, right_sorted) = rayon::join(
            || self.parallel_quicksort(left),
            || self.parallel_quicksort(right),
        );

        let mut result = left_sorted;
        result.push(pivot_val);
        result.extend(right_sorted);
        result
    }

    /// 运行分治示例
    pub fn run_example() {
        let dc = DivideAndConquer::new(1000);

        // 生成测试数据
        let data: Vec<i32> = (0..10000).map(|i| 10000 - i).collect();

        // 并行归并排序
        let start = std::time::Instant::now();
        let sorted_merge = dc.parallel_merge_sort(data.clone());
        let merge_time = start.elapsed();

        // 并行快速排序
        let start = std::time::Instant::now();
        let sorted_quick = dc.parallel_quicksort(data);
        let quick_time = start.elapsed();

        println!("Merge sort time: {:?}", merge_time);
        println!("Quick sort time: {:?}", quick_time);
        println!("Results equal: {}", (sorted_merge == sorted_quick));
    }
}

/// 管道模式实现
///
/// 使用通道连接多个处理阶段
pub struct Pipeline<T> {
    stages: Vec<Box<dyn Fn(T) -> T + Send + Sync>>,
}

impl<T> Pipeline<T> {
    pub fn new() -> Self {
        Self { stages: Vec::new() }
    }

    pub fn add_stage<F>(&mut self, stage: F)
    where
        F: Fn(T) -> T + Send + Sync + 'static,
    {
        self.stages.push(Box::new(stage));
    }

    /// 运行管道处理
    pub fn process(&self, input: T) -> T {
        self.stages.iter().fold(input, |acc, stage| stage(acc))
    }

    /// 并行管道处理
    pub fn process_parallel(&self, inputs: Vec<T>) -> Vec<T>
    where
        T: Send + Sync + Clone,
    {
        inputs
            .par_iter()
            .map(|input| self.process(input.clone()))
            .collect()
    }

    /// 运行管道示例
    pub fn run_example() {
        let mut pipeline = Pipeline::new();

        // 添加处理阶段
        pipeline.add_stage(|x: i32| x * 2);
        pipeline.add_stage(|x: i32| x + 1);
        pipeline.add_stage(|x: i32| x * x);

        // 测试数据
        let inputs: Vec<i32> = (1..=10).collect();

        // 串行处理
        let start = std::time::Instant::now();
        let serial_results: Vec<i32> = inputs.iter().map(|&x| pipeline.process(x)).collect();
        let serial_time = start.elapsed();

        // 并行处理
        let start = std::time::Instant::now();
        let parallel_results = pipeline.process_parallel(inputs);
        let parallel_time = start.elapsed();

        println!("Serial results: {:?}", serial_results);
        println!("Parallel results: {:?}", parallel_results);
        println!("Serial time: {:?}", serial_time);
        println!("Parallel time: {:?}", parallel_time);
    }
}

/// 扇出-扇入模式实现
///
/// 将任务分发到多个工作线程，然后收集结果
pub struct FanOutFanIn<T, R> {
    worker_count: usize,
    worker_fn: Box<dyn Fn(T) -> R + Send + Sync>,
}

impl<T, R> FanOutFanIn<T, R>
where
    T: Send + Sync + Clone,
    R: Send + Sync,
{
    pub fn new<F>(worker_count: usize, worker_fn: F) -> Self
    where
        F: Fn(T) -> R + Send + Sync + 'static,
    {
        Self {
            worker_count,
            worker_fn: Box::new(worker_fn),
        }
    }

    /// 执行扇出-扇入处理
    pub fn process(&self, inputs: Vec<T>) -> Vec<R> {
        let chunk_size = (inputs.len() + self.worker_count - 1) / self.worker_count;

        inputs
            .par_chunks(chunk_size)
            .flat_map(|chunk| {
                chunk
                    .iter()
                    .map(|input| (self.worker_fn)(input.clone()))
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// 运行扇出-扇入示例
    pub fn run_example() {
        let fan_out_fan_in = FanOutFanIn::new(4, |x: i32| {
            // 模拟计算密集型任务
            thread::sleep(Duration::from_millis(10));
            x * x * x
        });

        let inputs: Vec<i32> = (1..=20).collect();

        let start = std::time::Instant::now();
        let results = fan_out_fan_in.process(inputs);
        let elapsed = start.elapsed();

        println!("Fan-out/Fan-in results: {:?}", results);
        println!("Processing time: {:?}", elapsed);
    }
}

/// 并发模式演示
pub fn demonstrate_concurrency_patterns() {
    println!("=== 并发编程模式演示 ===");

    println!("\n1. 生产者-消费者模式:");
    ProducerConsumer::<i32>::run_example();

    println!("\n2. 读者-写者模式:");
    ReaderWriterPattern::<i32>::run_example();

    println!("\n3. 分治模式:");
    DivideAndConquer::run_example();

    println!("\n4. 管道模式:");
    Pipeline::<i32>::run_example();

    println!("\n5. 扇出-扇入模式:");
    FanOutFanIn::<i32, i32>::run_example();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_producer_consumer() {
        let pc = ProducerConsumer::new(5);
        let sender = pc.sender();
        let receiver = pc.receiver();

        thread::scope(|s| {
            s.spawn(move || {
                for i in 0..10 {
                    sender.send(i).unwrap();
                }
            });

            s.spawn(move || {
                let mut count = 0;
                while let Ok(_) = receiver.recv() {
                    count += 1;
                }
                assert_eq!(count, 10);
            });
        });
    }

    #[test]
    fn test_reader_writer() {
        let rw = ReaderWriterPattern::new(vec![1, 2, 3]);

        let sum: i32 = rw.read(|data| data.iter().sum());
        assert_eq!(sum, 6);

        rw.write(|data| data.push(4));
        let sum: i32 = rw.read(|data| data.iter().sum());
        assert_eq!(sum, 10);
    }

    #[test]
    fn test_divide_and_conquer() {
        let dc = DivideAndConquer::new(10);
        let data = vec![5, 2, 8, 1, 9, 3, 7, 4, 6];

        let sorted = dc.parallel_merge_sort(data);
        assert_eq!(sorted, vec![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn test_pipeline() {
        let mut pipeline = Pipeline::new();
        pipeline.add_stage(|x: i32| x * 2);
        pipeline.add_stage(|x: i32| x + 1);

        let result = pipeline.process(5);
        assert_eq!(result, 11); // (5 * 2) + 1 = 11
    }

    #[test]
    fn test_fan_out_fan_in() {
        let fan_out_fan_in = FanOutFanIn::new(2, |x: i32| x * x);
        let inputs = vec![1, 2, 3, 4];
        let results = fan_out_fan_in.process(inputs);
        assert_eq!(results, vec![1, 4, 9, 16]);
    }
}
