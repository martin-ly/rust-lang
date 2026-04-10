//! # Rust 1.96.0 线程并发新特性实现模块

use std::ops::RangeInclusive;
use std::sync::Mutex;
use std::thread;

/// RangeInclusive 在并发任务管理中的应用
pub struct ThreadRangeExamples;

impl ThreadRangeExamples {
    /// 任务分配
    pub fn distribute_tasks(
        total_tasks: usize,
        thread_count: usize,
    ) -> Vec<RangeInclusive<usize>> {
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
    pub fn is_load_healthy(
        current_load: usize,
        healthy_range: RangeInclusive<usize>,
    ) -> bool {
        healthy_range.contains(&current_load)
    }
}

/// 元组 coercion 示例
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
    println!("   Rust 1.96.0 线程并发新特性演示");
    println!("========================================\n");

    let ranges = ThreadRangeExamples::distribute_tasks(100, 4);
    println!("任务分配: {:?}", ranges);

    let priority = ThreadRangeExamples::assign_thread_priority(2);
    println!("线程2优先级: {}", priority);

    let is_healthy = ThreadRangeExamples::is_load_healthy(50, 20..=80);
    println!("负载健康检查: {}", is_healthy);

    let (success, failure, rate, status) = ThreadTupleExamples::concurrent_stats(95, 5);
    println!("并发统计: 成功={}, 失败={}, 率={:.1}%, 状态={}", success, failure, rate, status);

    let manager = ThreadPoolRangeManager::new(4, 100);
    println!("工作线程范围: {:?}", manager.get_all_ranges());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_thread_info() -> String {
    "Rust 1.96.0 线程并发新特性:\n\
        - RangeInclusive for task distribution\n\
        - Tuple coercion for thread results\n\
        - Improved thread pool range management"
        .to_string()
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
    fn test_get_rust_196_thread_info() {
        let info = get_rust_196_thread_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}
