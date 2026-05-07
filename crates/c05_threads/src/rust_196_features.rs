//! # Rust 1.96 特性跟踪模块（含历史特性复习与 1.96 前瞻）

use std::ops::RangeInclusive;
use std::sync::Mutex;
use std::thread;

/// `if let` guards (Rust 1.95 稳定，非 1.96 新特性) 在线程同步中的应用
///
/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// 减少嵌套层级，使代码更扁平、更易读。
pub struct ThreadIfLetGuardExamples;

impl ThreadIfLetGuardExamples {
    /// 解析线程优先级
    pub fn parse_thread_priority(input: Option<&str>) -> Result<u8, &'static str> {
        match input {
            Some(s) if let Ok(p) = s.parse::<u8>() => {
                if p <= 100 {
                    Ok(p)
                } else {
                    Err("优先级超出范围")
                }
            }
            Some(_) => Err("无效的优先级格式"),
            None => Err("未指定优先级"),
        }
    }

    /// 检查线程池配置
    pub fn check_pool_config(config: Result<Option<usize>, &'static str>) -> &'static str {
        match config {
            Ok(Some(size)) if size > 0 && size <= 64 => "有效配置",
            Ok(Some(_)) => "配置超出支持范围",
            Ok(None) => "使用默认配置",
            Err(msg) => msg,
        }
    }
}

/// Range 类型应用（标准库基础特性）
pub struct ThreadRangeExamples;

impl ThreadRangeExamples {
    /// 任务分配
    pub fn distribute_tasks(total_tasks: usize, thread_count: usize) -> Vec<RangeInclusive<usize>> {
        if thread_count == 0 || total_tasks == 0 {
            return vec![];
        }

        let base_chunk = total_tasks / thread_count;
        let remainder = total_tasks % thread_count;

        let mut ranges = Vec::with_capacity(thread_count);
        let mut start = 0;

        for i in 0..thread_count {
            let chunk_size = base_chunk + if i < remainder { 1 } else { 0 };
            if chunk_size == 0 {
                continue;
            }
            let end = start + chunk_size - 1;
            ranges.push(start..=end);
            start = end + 1;
        }

        ranges
    }

    /// 线程优先级
    pub fn assign_thread_priority(thread_id: usize) -> u8 {
        match thread_id {
            0..=2 => 10,
            3..=5 => 5,
            _ => 1,
        }
    }

    /// 负载健康检查
    pub fn is_load_healthy(current_load: usize, healthy_range: RangeInclusive<usize>) -> bool {
        healthy_range.contains(&current_load)
    }
}

/// 元组类型应用（泛型编程基础）
pub struct ThreadTupleExamples;

impl ThreadTupleExamples {
    /// 线程执行结果
    pub fn thread_execution_result<T>(
        result: Result<T, String>,
        thread_id: usize,
    ) -> (Result<T, String>, usize, std::time::Duration)
    where
        T: Clone,
    {
        let duration = std::time::Duration::from_millis(100);
        (result, thread_id, duration)
    }

    /// 并发统计
    pub fn concurrent_stats(
        success_count: usize,
        failure_count: usize,
    ) -> (usize, usize, f64, &'static str) {
        let total = success_count + failure_count;
        let success_rate = if total > 0 {
            (success_count as f64 / total as f64) * 100.0
        } else {
            0.0
        };
        let status = if success_rate >= 95.0 {
            "excellent"
        } else if success_rate >= 80.0 {
            "good"
        } else {
            "poor"
        };
        (success_count, failure_count, success_rate, status)
    }

    /// 线程池状态
    pub fn thread_pool_state(
        active: usize,
        idle: usize,
        queue_size: usize,
    ) -> (usize, usize, usize, &'static str) {
        let status = if queue_size > 100 {
            "overloaded"
        } else if active == 0 {
            "idle"
        } else {
            "active"
        };
        (active, idle, queue_size, status)
    }
}

/// 线程安全示例
pub struct ThreadSafetyExamples;

impl ThreadSafetyExamples {
    /// 线程安全处理
    pub fn thread_safe_process<T>(data: T) -> T
    where
        T: Send + Sync + Clone,
    {
        data.clone()
    }

    /// 锁使用
    pub fn safe_lock_usage<T>(mutex: &Mutex<T>) -> Option<T>
    where
        T: Clone,
    {
        match mutex.lock() {
            Ok(guard) => Some(guard.clone()),
            Err(_) => None,
        }
    }

    /// 线程生命周期管理
    pub fn manage_thread_lifecycle<F>(f: F) -> thread::JoinHandle<()>
    where
        F: FnOnce() + Send + 'static,
    {
        thread::spawn(f)
    }
}

/// 线程池范围管理器
pub struct ThreadPoolRangeManager {
    workers: Vec<RangeInclusive<usize>>,
    active_range: RangeInclusive<usize>,
}

impl ThreadPoolRangeManager {
    /// 创建新管理器
    pub fn new(worker_count: usize, total_capacity: usize) -> Self {
        let ranges = ThreadRangeExamples::distribute_tasks(total_capacity, worker_count);
        Self {
            workers: ranges.clone(),
            active_range: 0..=worker_count.saturating_sub(1),
        }
    }

    /// 获取工作线程范围
    pub fn get_worker_range(&self, worker_id: usize) -> Option<&RangeInclusive<usize>> {
        self.workers.get(worker_id)
    }

    /// 检查工作线程是否活跃
    pub fn is_worker_active(&self, worker_id: usize) -> bool {
        self.active_range.contains(&worker_id)
    }

    /// 获取所有范围
    pub fn get_all_ranges(&self) -> &[RangeInclusive<usize>] {
        &self.workers
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.95+ 特性跟踪演示");
    println!("========================================\n");

    let ranges = ThreadRangeExamples::distribute_tasks(100, 4);
    println!("任务分配: {:?}", ranges);

    let priority = ThreadRangeExamples::assign_thread_priority(2);
    println!("线程2优先级: {}", priority);

    let is_healthy = ThreadRangeExamples::is_load_healthy(50, 20..=80);
    println!("负载健康检查: {}", is_healthy);

    let (success, failure, rate, status) = ThreadTupleExamples::concurrent_stats(95, 5);
    println!(
        "并发统计: 成功={}, 失败={}, 率={:.1}%, 状态={}",
        success, failure, rate, status
    );

    let manager = ThreadPoolRangeManager::new(4, 100);
    println!("工作线程范围: {:?}", manager.get_all_ranges());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_thread_info() -> String {
    "Rust 1.95+ 特性跟踪:\n- RangeInclusive for task distribution\n- Tuple coercion for thread \
     results\n- Improved thread pool range management"
        .to_string()
}

// ==================== Rust 1.96 新特性 ====================

/// Rust 1.96 `VecDeque::new` 在 const 上下文中的应用
///
/// `VecDeque::new()` 现在可以在 const 上下文中使用，
/// 允许在编译期初始化环形缓冲区，用于线程间高效通信。
pub struct Rust196ConstRingBuffer<T, const N: usize> {
    buffer: std::collections::VecDeque<T>,
}

impl<T, const N: usize> Rust196ConstRingBuffer<T, N> {
    /// 编译期初始化环形缓冲区
    ///
    /// 利用 `VecDeque::new` 的 const 支持，在编译时创建空队列。
    pub const fn new() -> Self {
        Self {
            buffer: std::collections::VecDeque::new(),
        }
    }
}

impl<T, const N: usize> Default for Rust196ConstRingBuffer<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone, const N: usize> Rust196ConstRingBuffer<T, N> {
    /// 批量填充初始数据（最多 N 个）
    pub fn fill(&mut self, items: &[T]) {
        for item in items.iter().take(N) {
            self.buffer.push_back(item.clone());
        }
    }

    /// 从缓冲区取出所有数据
    pub fn drain(&mut self) -> Vec<T> {
        self.buffer.drain(..).collect()
    }

    /// 当前缓冲区长度
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// 缓冲区是否为空
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }
}

/// Rust 1.96 `core::pin::pin!` 在线程本地数据中的应用
///
/// `pin!` 宏允许在栈上固定数据，适用于需要内存位置稳定的线程本地状态。
pub struct Rust196PinnedThreadLocal;

impl Rust196PinnedThreadLocal {
    /// 固定线程本地字符串并获取其长度
    ///
    /// 无需 `Box::pin` 或 unsafe，直接在栈上固定数据。
    pub fn pin_local_string(data: String) -> usize {
        let pinned = core::pin::pin!(data);
        pinned.len()
    }

    /// 在线程中固定临时数据
    ///
    /// 跨线程传递前在栈上固定数据，确保内存位置稳定。
    pub fn pin_in_thread<F, R>(f: F) -> std::thread::JoinHandle<R>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        std::thread::spawn(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_distribute_tasks() {
        let ranges = ThreadRangeExamples::distribute_tasks(100, 4);
        assert_eq!(ranges.len(), 4);

        let total: usize = ranges.iter().map(|r| r.end() - r.start() + 1).sum();
        assert_eq!(total, 100);
    }

    #[test]
    fn test_assign_thread_priority() {
        assert_eq!(ThreadRangeExamples::assign_thread_priority(0), 10);
        assert_eq!(ThreadRangeExamples::assign_thread_priority(4), 5);
        assert_eq!(ThreadRangeExamples::assign_thread_priority(6), 1);
    }

    #[test]
    fn test_is_load_healthy() {
        assert!(ThreadRangeExamples::is_load_healthy(50, 20..=80));
        assert!(!ThreadRangeExamples::is_load_healthy(100, 20..=80));
    }

    #[test]
    fn test_concurrent_stats() {
        let (success, failure, rate, status) = ThreadTupleExamples::concurrent_stats(95, 5);
        assert_eq!(success, 95);
        assert_eq!(failure, 5);
        assert!((rate - 95.0).abs() < 0.01);
        assert_eq!(status, "excellent");
    }

    #[test]
    fn test_safe_lock_usage() {
        let mutex = Mutex::new(42);
        let result = ThreadSafetyExamples::safe_lock_usage(&mutex);
        assert_eq!(result, Some(42));
    }

    #[test]
    fn test_thread_pool_range_manager() {
        let manager = ThreadPoolRangeManager::new(4, 100);
        assert_eq!(manager.get_all_ranges().len(), 4);
        assert!(manager.is_worker_active(0));
    }

    #[test]
    fn test_parse_thread_priority() {
        assert_eq!(
            ThreadIfLetGuardExamples::parse_thread_priority(Some("50")),
            Ok(50)
        );
        assert_eq!(
            ThreadIfLetGuardExamples::parse_thread_priority(Some("150")),
            Err("优先级超出范围")
        );
        assert_eq!(
            ThreadIfLetGuardExamples::parse_thread_priority(Some("abc")),
            Err("无效的优先级格式")
        );
        assert_eq!(
            ThreadIfLetGuardExamples::parse_thread_priority(None),
            Err("未指定优先级")
        );
    }

    #[test]
    fn test_check_pool_config() {
        assert_eq!(
            ThreadIfLetGuardExamples::check_pool_config(Ok(Some(16))),
            "有效配置"
        );
        assert_eq!(
            ThreadIfLetGuardExamples::check_pool_config(Ok(Some(128))),
            "配置超出支持范围"
        );
        assert_eq!(
            ThreadIfLetGuardExamples::check_pool_config(Ok(None)),
            "使用默认配置"
        );
        assert_eq!(
            ThreadIfLetGuardExamples::check_pool_config(Err("配置解析失败")),
            "配置解析失败"
        );
    }

    #[test]
    fn test_get_rust_196_thread_info() {
        let info = get_rust_196_thread_info();
        assert!(!info.is_empty());
    }

    // ----- Rust 1.96 新特性测试 -----

    #[test]
    fn test_const_ring_buffer() {
        let mut buf = Rust196ConstRingBuffer::<i32, 4>::new();
        assert!(buf.is_empty());
        buf.fill(&[1, 2, 3]);
        assert_eq!(buf.len(), 3);
        assert_eq!(buf.drain(), vec![1, 2, 3]);
    }

    #[test]
    fn test_const_ring_buffer_capacity_limit() {
        let mut buf = Rust196ConstRingBuffer::<i32, 2>::new();
        buf.fill(&[1, 2, 3, 4]);
        assert_eq!(buf.len(), 2);
        assert_eq!(buf.drain(), vec![1, 2]);
    }

    #[test]
    fn test_pin_local_string() {
        assert_eq!(
            Rust196PinnedThreadLocal::pin_local_string("hello".to_string()),
            5
        );
    }

    #[test]
    fn test_pin_in_thread() {
        let handle = Rust196PinnedThreadLocal::pin_in_thread(|| {
            let pinned = core::pin::pin!(42);
            *pinned
        });
        assert_eq!(handle.join().unwrap(), 42);
    }
}

/// 并发 Range 反模式与边界情况专题
pub mod anti_patterns_and_edge_cases {
    use std::ops::RangeInclusive;

    /// 展示并发任务分配中的反模式和边界情况
    pub struct ThreadRangeAntiPatterns;

    impl ThreadRangeAntiPatterns {
        /// ❌ 不推荐：使用半开范围且不做余数处理导致任务遗漏
        pub fn buggy_task_distribution(
            total: usize,
            threads: usize,
        ) -> Vec<std::ops::Range<usize>> {
            // ❌ 反例：简单均分但不处理余数，最后一个 chunk 会遗漏剩余任务
            if threads == 0 || total == 0 {
                return vec![];
            }
            let chunk = total / threads;
            let mut ranges = Vec::new();
            for i in 0..threads {
                let start = i * chunk;
                let end = (i + 1) * chunk; // ❌ 不处理 remainder，最后一个范围可能遗漏
                ranges.push(start..end);
            }
            ranges
        }

        /// ✅ 推荐：正确的包含性范围分配
        pub fn correct_task_distribution(
            total: usize,
            threads: usize,
        ) -> Vec<RangeInclusive<usize>> {
            if threads == 0 || total == 0 {
                return vec![];
            }
            let base = total / threads;
            let rem = total % threads;
            let mut ranges = Vec::new();
            let mut start = 0;
            for i in 0..threads {
                let chunk = base + if i < rem { 1 } else { 0 };
                if chunk == 0 {
                    continue;
                }
                let end = start + chunk - 1;
                ranges.push(start..=end);
                start = end + 1;
            }
            ranges
        }

        /// ⚠️ 边界情况：线程数大于任务数
        pub fn more_threads_than_tasks(tasks: usize, threads: usize) -> Vec<RangeInclusive<usize>> {
            // ⚠️ 边界情况：当 threads > tasks 时，多余的线程应得到空标记范围
            if threads == 0 || tasks == 0 {
                return vec![];
            }
            let actual_threads = threads.min(tasks);
            let mut ranges = Vec::with_capacity(threads);
            let base = tasks / actual_threads;
            let rem = tasks % actual_threads;
            let mut start = 0;
            for i in 0..actual_threads {
                let chunk = base + if i < rem { 1 } else { 0 };
                let end = start + chunk - 1;
                ranges.push(start..=end);
                start = end + 1;
            }
            for _ in actual_threads..threads {
                ranges.push(0..=0); // 空范围标记
            }
            ranges
        }

        /// ⚠️ 边界情况：单线程或零任务的安全处理
        pub fn edge_cases_single_thread(total: usize) -> RangeInclusive<usize> {
            // ⚠️ 边界情况：始终返回安全的包含范围
            if total == 0 { 0..=0 } else { 0..=total - 1 }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_buggy_vs_correct_distribution() {
            // ❌ 反例：半开范围的总长度可能不等于 total
            let buggy = ThreadRangeAntiPatterns::buggy_task_distribution(10, 3);
            let buggy_total: usize = buggy.iter().map(|r| r.end - r.start).sum();
            // 注意：10 / 3 = 3，最后一个 range 是 9..10，总长为 3+3+1=7 < 10！
            assert!(buggy_total < 10);

            // ✅ 正例：包含性范围覆盖全部任务
            let correct = ThreadRangeAntiPatterns::correct_task_distribution(10, 3);
            let correct_total: usize = correct.iter().map(|r| r.end() - r.start() + 1).sum();
            assert_eq!(correct_total, 10);
        }

        #[test]
        fn test_correct_task_distribution() {
            let ranges = ThreadRangeAntiPatterns::correct_task_distribution(10, 3);
            assert_eq!(ranges.len(), 3);
            // 边界：不重叠且连续
            for i in 1..ranges.len() {
                assert_eq!(*ranges[i].start(), ranges[i - 1].end() + 1);
            }
        }

        #[test]
        fn test_more_threads_than_tasks() {
            let ranges = ThreadRangeAntiPatterns::more_threads_than_tasks(3, 5);
            assert_eq!(ranges.len(), 5);
            // 前 3 个范围覆盖任务，后 2 个是空标记
            let valid_total: usize = ranges[..3].iter().map(|r| r.end() - r.start() + 1).sum();
            assert_eq!(valid_total, 3);
        }

        #[test]
        fn test_edge_cases_single_thread() {
            assert_eq!(ThreadRangeAntiPatterns::edge_cases_single_thread(10), 0..=9);
            assert_eq!(ThreadRangeAntiPatterns::edge_cases_single_thread(0), 0..=0);
        }
    }
}
