//! # Rust 1.96.0 进程管理新特性实现模块

use std::ops::RangeInclusive;

/// RangeInclusive 在进程管理中的应用
pub struct ProcessRangeExamples;

impl ProcessRangeExamples {
    /// 进程优先级分配
    pub fn priority_range(nice_level: i8) -> &'static str {
        match nice_level {
            -20..=-10 => "高优先级",
            -9..=0 => "正常优先级",
            1..=10 => "低优先级",
            11..=19 => "最低优先级",
            _ => "无效",
        }
    }

    /// 资源限制检查
    pub fn check_resource_limit(
        current: usize,
        limit: RangeInclusive<usize>,
    ) -> &'static str {
        if current < *limit.start() {
            "正常"
        } else if limit.contains(&current) {
            "警告"
        } else {
            "超限"
        }
    }

    /// 进程分组
    pub fn group_processes(
        processes: &[usize],
        group_size: usize,
    ) -> Vec<RangeInclusive<usize>> {
        if group_size == 0 || processes.is_empty() {
            return vec![];
        }

        let mut groups = Vec::new();
        let mut start = 0;

        while start < processes.len() {
            let end = (start + group_size - 1).min(processes.len() - 1);
            groups.push(start..=end);
            start = end + 1;
        }

        groups
    }
}

/// 元组 coercion 示例
pub struct ProcessTupleExamples;

impl ProcessTupleExamples {
    /// 进程执行结果
    pub fn process_execution_result<T>(
        result: Result<T, String>,
        pid: u32,
    ) -> (Result<T, String>, u32, std::time::Instant)
    where
        T: Clone,
    {
        (result, pid, std::time::Instant::now())
    }

    /// 进程统计
    pub fn process_stats(
        running: usize,
        zombie: usize,
        stopped: usize,
    ) -> (usize, usize, usize, usize, &'static str) {
        let total = running + zombie + stopped;
        let health = if zombie > 10 {
            "critical"
        } else if zombie > 0 {
            "warning"
        } else {
            "healthy"
        };
        (running, zombie, stopped, total, health)
    }

    /// 资源使用
    pub fn resource_usage(
        cpu_percent: f64,
        memory_mb: usize,
    ) -> (f64, usize, &'static str) {
        let status = if cpu_percent > 90.0 {
            "high_cpu"
        } else if memory_mb > 1024 {
            "high_memory"
        } else {
            "normal"
        };
        (cpu_percent, memory_mb, status)
    }
}

/// 进程池管理器
pub struct ProcessPoolManager {
    process_ranges: Vec<RangeInclusive<usize>>,
    active_range: RangeInclusive<usize>,
}

impl ProcessPoolManager {
    /// 创建新管理器
    pub fn new(process_count: usize, batch_size: usize) -> Self {
        let ranges = ProcessRangeExamples::group_processes(
            &(0..process_count).collect::<Vec<_>>(),
            batch_size,
        );
        Self {
            process_ranges: ranges.clone(),
            active_range: 0..=ranges.len().saturating_sub(1),
        }
    }

    /// 获取进程范围
    pub fn get_process_range(&self, group_id: usize) -> Option<&RangeInclusive<usize>> {
        self.process_ranges.get(group_id)
    }

    /// 检查组是否活跃
    pub fn is_group_active(&self, group_id: usize) -> bool {
        self.active_range.contains(&group_id)
    }

    /// 获取所有范围
    pub fn get_all_ranges(&self) -> &[RangeInclusive<usize>] {
        &self.process_ranges
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 进程管理新特性演示");
    println!("========================================\n");

    let priority = ProcessRangeExamples::priority_range(-5);
    println!("优先级(-5): {}", priority);

    let resource_status = ProcessRangeExamples::check_resource_limit(80, 50..=100);
    println!("资源状态(80/50-100): {}", resource_status);

    let groups = ProcessRangeExamples::group_processes(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 3);
    println!("进程分组: {:?}", groups);

    let (running, zombie, stopped, total, health) = ProcessTupleExamples::process_stats(10, 2, 1);
    println!("进程统计: 运行={}, 僵尸={}, 停止={}, 总计={}, 健康={}",
             running, zombie, stopped, total, health);

    let manager = ProcessPoolManager::new(12, 4);
    println!("进程组: {:?}", manager.get_all_ranges());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_process_info() -> String {
    "Rust 1.96.0 进程管理新特性:\n\
        - RangeInclusive for priority and resource management\n\
        - Tuple coercion for process results\n\
        - Better process pool management"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_range() {
        assert_eq!(ProcessRangeExamples::priority_range(-15), "高优先级");
        assert_eq!(ProcessRangeExamples::priority_range(-5), "正常优先级");
        assert_eq!(ProcessRangeExamples::priority_range(5), "低优先级");
    }

    #[test]
    fn test_check_resource_limit() {
        assert_eq!(ProcessRangeExamples::check_resource_limit(30, 50..=100), "正常");
        assert_eq!(ProcessRangeExamples::check_resource_limit(75, 50..=100), "警告");
        assert_eq!(ProcessRangeExamples::check_resource_limit(150, 50..=100), "超限");
    }

    #[test]
    fn test_group_processes() {
        let groups = ProcessRangeExamples::group_processes(&[1, 2, 3, 4, 5], 2);
        assert_eq!(groups.len(), 3);
    }

    #[test]
    fn test_process_stats() {
        let (running, zombie, stopped, total, health) =
            ProcessTupleExamples::process_stats(10, 2, 1);
        assert_eq!(running, 10);
        assert_eq!(zombie, 2);
        assert_eq!(stopped, 1);
        assert_eq!(total, 13);
        assert_eq!(health, "warning");
    }

    #[test]
    fn test_process_pool_manager() {
        let manager = ProcessPoolManager::new(12, 4);
        assert_eq!(manager.get_all_ranges().len(), 3);
        assert!(manager.is_group_active(0));
    }

    #[test]
    fn test_get_rust_196_process_info() {
        let info = get_rust_196_process_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}
