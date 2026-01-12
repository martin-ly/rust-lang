//! Rust 1.92.0 进程管理特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在进程管理场景中的应用，包括：
//! - 新的稳定 API（`rotate_right`, `NonZero::div_ceil`）
//! - 性能优化（迭代器方法特化）
//! - 改进的进程队列管理
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::num::NonZeroUsize;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

// ==================== 1. rotate_right 在进程队列管理中的应用 ====================

/// 使用 rotate_right 实现进程优先级队列
///
/// Rust 1.92.0: 新增的 `rotate_right` 方法可以高效实现进程队列的轮转调度
#[derive(Default)]
pub struct ProcessQueue {
    processes: VecDeque<ProcessInfo>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProcessInfo {
    pub pid: u32,
    pub name: String,
    pub priority: u8,
}

impl ProcessQueue {
    pub fn new() -> Self {
        ProcessQueue {
            processes: VecDeque::new(),
        }
    }

    /// 轮转进程队列
    ///
    /// Rust 1.92.0: 使用新的 rotate_right 方法实现高效的队列轮转
    pub fn rotate(&mut self, positions: usize) {
        if self.processes.is_empty() {
            return;
        }

        // 转换为 Vec 以便使用 rotate_right
        let mut vec: Vec<ProcessInfo> = self.processes.drain(..).collect();
        vec.rotate_right(positions);
        self.processes = vec.into_iter().collect();
    }

    pub fn push(&mut self, process: ProcessInfo) {
        self.processes.push_back(process);
    }

    pub fn pop(&mut self) -> Option<ProcessInfo> {
        self.processes.pop_front()
    }

    /// 获取队列中的所有进程（用于演示）
    pub fn iter(&self) -> impl Iterator<Item = &ProcessInfo> {
        self.processes.iter()
    }

    /// 获取队列长度
    pub fn len(&self) -> usize {
        self.processes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.processes.is_empty()
    }
}

/// 使用 rotate_right 实现循环进程调度器
#[allow(dead_code)]
pub struct RoundRobinScheduler {
    queue: Arc<Mutex<ProcessQueue>>,
    quantum: usize,
}

impl RoundRobinScheduler {
    pub fn new(quantum: usize) -> Self {
        RoundRobinScheduler {
            queue: Arc::new(Mutex::new(ProcessQueue::new())),
            quantum,
        }
    }

    /// 执行一轮调度
    pub fn schedule(&self) {
        let mut queue = self.queue.lock().unwrap();

        // Rust 1.92.0: 使用 rotate_right 实现时间片轮转
        if queue.processes.len() > 1 {
            queue.rotate(1);
        }
    }
}

// ==================== 2. NonZero::div_ceil 在进程池大小计算中的应用 ====================

/// 使用 NonZero::div_ceil 计算进程池大小
///
/// Rust 1.92.0: 新增的 `div_ceil` 方法可以安全地计算进程池的容量
pub fn calculate_process_pool_size(
    total_tasks: usize,
    tasks_per_process: NonZeroUsize,
) -> usize {
    if total_tasks == 0 {
        return 0;
    }

    let total = NonZeroUsize::new(total_tasks).unwrap();
    // Rust 1.92.0: 使用 div_ceil 计算需要的进程数
    total.div_ceil(tasks_per_process).get()
}

/// 使用 div_ceil 实现进程资源分配
pub struct ProcessResourceAllocator {
    total_memory: usize,
    memory_per_process: NonZeroUsize,
}

impl ProcessResourceAllocator {
    pub fn new(total_memory: usize, memory_per_process: NonZeroUsize) -> Self {
        ProcessResourceAllocator {
            total_memory,
            memory_per_process,
        }
    }

    /// 计算可以创建的进程数
    pub fn max_processes(&self) -> usize {
        if self.total_memory == 0 {
            return 0;
        }

        let total = NonZeroUsize::new(self.total_memory).unwrap();
        // Rust 1.92.0: 使用 div_ceil 计算最大进程数
        total.div_ceil(self.memory_per_process).get()
    }
}

// ==================== 3. 迭代器方法特化在进程列表比较中的应用 ====================

/// 使用特化的迭代器比较方法比较进程列表
///
/// Rust 1.92.0: Iterator::eq 为 TrustedLen 迭代器特化，性能更好
pub fn compare_process_lists(list1: &[ProcessInfo], list2: &[ProcessInfo]) -> bool {
    // Rust 1.92.0: 特化的迭代器比较方法，性能更好
    list1.iter().eq(list2.iter())
}

/// 使用迭代器特化检查进程状态
pub fn check_process_states(processes: &[ProcessInfo], expected_pids: &[u32]) -> bool {
    let actual_pids: Vec<u32> = processes.iter().map(|p| p.pid).collect();
    // Rust 1.92.0: 特化的迭代器比较
    actual_pids.iter().eq(expected_pids.iter())
}

// ==================== 4. 综合应用示例 ====================

/// 演示 Rust 1.92.0 特性在进程管理中的应用
pub fn demonstrate_rust_192_process_features() {
    println!("\n=== Rust 1.92.0 进程管理特性演示 ===\n");

    // 1. rotate_right 演示
    println!("1. rotate_right 在进程队列中的应用:");
    let mut queue = ProcessQueue::new();
    queue.push(ProcessInfo {
        pid: 1,
        name: "process1".to_string(),
        priority: 10,
    });
    queue.push(ProcessInfo {
        pid: 2,
        name: "process2".to_string(),
        priority: 20,
    });
    queue.push(ProcessInfo {
        pid: 3,
        name: "process3".to_string(),
        priority: 30,
    });

    println!("   原始队列: {:?}",
        queue.processes.iter().map(|p| p.pid).collect::<Vec<_>>());

    queue.rotate(1);
    println!("   轮转后: {:?}",
        queue.processes.iter().map(|p| p.pid).collect::<Vec<_>>());

    // 2. NonZero::div_ceil 演示
    println!("\n2. NonZero::div_ceil 在进程池计算中的应用:");
    let chunk_size = NonZeroUsize::new(5).unwrap();
    let total_tasks = 23;
    let pool_size = calculate_process_pool_size(total_tasks, chunk_size);
    println!("   总任务数: {}", total_tasks);
    println!("   每进程任务数: {}", chunk_size);
    println!("   需要的进程数: {}", pool_size);

    let allocator = ProcessResourceAllocator::new(1024, NonZeroUsize::new(64).unwrap());
    println!("   总内存: 1024 MB");
    println!("   每进程内存: 64 MB");
    println!("   最大进程数: {}", allocator.max_processes());

    // 3. 迭代器特化演示
    println!("\n3. 迭代器方法特化在进程比较中的应用:");
    let list1 = vec![
        ProcessInfo {
            pid: 1,
            name: "p1".to_string(),
            priority: 10,
        },
        ProcessInfo {
            pid: 2,
            name: "p2".to_string(),
            priority: 20,
        },
    ];
    let list2 = vec![
        ProcessInfo {
            pid: 1,
            name: "p1".to_string(),
            priority: 10,
        },
        ProcessInfo {
            pid: 2,
            name: "p2".to_string(),
            priority: 20,
        },
    ];
    println!("   进程列表相等: {}", compare_process_lists(&list1, &list2));

    let expected_pids = vec![1, 2];
    println!("   PID 列表匹配: {}", check_process_states(&list1, &expected_pids));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_queue_rotate() {
        let mut queue = ProcessQueue::new();
        queue.push(ProcessInfo {
            pid: 1,
            name: "p1".to_string(),
            priority: 10,
        });
        queue.push(ProcessInfo {
            pid: 2,
            name: "p2".to_string(),
            priority: 20,
        });

        queue.rotate(1);
        let first = queue.pop().unwrap();
        assert_eq!(first.pid, 2);
    }

    #[test]
    fn test_process_pool_size() {
        let chunk_size = NonZeroUsize::new(5).unwrap();
        assert_eq!(calculate_process_pool_size(23, chunk_size), 5);
        assert_eq!(calculate_process_pool_size(25, chunk_size), 5);
        assert_eq!(calculate_process_pool_size(26, chunk_size), 6);
    }

    #[test]
    fn test_process_resource_allocator() {
        let allocator = ProcessResourceAllocator::new(1024, NonZeroUsize::new(64).unwrap());
        assert_eq!(allocator.max_processes(), 16);
    }

    #[test]
    fn test_compare_process_lists() {
        let list1 = vec![
            ProcessInfo {
                pid: 1,
                name: "p1".to_string(),
                priority: 10,
            },
            ProcessInfo {
                pid: 2,
                name: "p2".to_string(),
                priority: 20,
            },
        ];
        let list2 = list1.clone();
        assert!(compare_process_lists(&list1, &list2));
    }
}
