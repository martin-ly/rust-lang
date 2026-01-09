//! Rust 1.92.0 宏系统特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在宏系统场景中的应用，包括：
//! - 新的稳定 API（`rotate_right`, `NonZero::div_ceil`）
//! - 性能优化（迭代器方法特化）
//! - 宏展开性能改进
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::num::NonZeroUsize;
use std::collections::VecDeque;

// ==================== 1. rotate_right 在宏展开队列管理中的应用 ====================

/// 使用 rotate_right 实现宏展开队列
///
/// Rust 1.92.0: 新增的 `rotate_right` 方法可以高效实现宏展开队列的轮转
pub struct MacroExpansionQueue {
    items: VecDeque<MacroExpansionItem>,
}

/// 宏展开项
///
/// 表示一个待展开的宏，包含名称、优先级和深度信息
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroExpansionItem {
    /// 宏名称
    pub name: String,
    /// 展开优先级（数值越大优先级越高）
    pub priority: u8,
    /// 宏展开深度
    pub depth: usize,
}

/// 宏展开队列
#[derive(Default)]
pub struct MacroExpansionQueue {
    items: VecDeque<MacroExpansionItem>,
}

impl MacroExpansionQueue {
    /// 创建一个新的宏展开队列
    pub fn new() -> Self {
        Self::default()
    }

    /// 轮转宏展开队列
    ///
    /// Rust 1.92.0: 使用新的 rotate_right 方法实现高效的队列轮转
    pub fn rotate(&mut self, positions: usize) {
        if self.items.is_empty() {
            return;
        }

        // 转换为 Vec 以便使用 rotate_right
        let mut vec: Vec<MacroExpansionItem> = self.items.drain(..).collect();
        vec.rotate_right(positions);
        self.items = vec.into_iter().collect();
    }

    /// 向队列末尾添加一个宏展开项
    pub fn push(&mut self, item: MacroExpansionItem) {
        self.items.push_back(item);
    }

    /// 从队列头部移除并返回一个宏展开项
    pub fn pop(&mut self) -> Option<MacroExpansionItem> {
        self.items.pop_front()
    }

    /// 获取队列中的所有项（用于演示）
    pub fn iter(&self) -> impl Iterator<Item = &MacroExpansionItem> {
        self.items.iter()
    }

    /// 获取队列长度
    pub fn len(&self) -> usize {
        self.items.len()
    }

    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

// ==================== 2. NonZero::div_ceil 在宏缓存大小计算中的应用 ====================

/// 使用 NonZero::div_ceil 计算宏缓存大小
///
/// Rust 1.92.0: 新增的 `div_ceil` 方法可以安全地计算宏缓存的容量
pub fn calculate_macro_cache_size(
    total_macros: usize,
    macros_per_cache_entry: NonZeroUsize,
) -> usize {
    if total_macros == 0 {
        return 0;
    }

    let total = NonZeroUsize::new(total_macros).unwrap();
    // Rust 1.92.0: 使用 div_ceil 计算需要的缓存条目数
    total.div_ceil(macros_per_cache_entry).get()
}

/// 使用 div_ceil 实现宏展开内存分配
pub struct MacroMemoryAllocator {
    total_memory: usize,
    memory_per_macro: NonZeroUsize,
}

impl MacroMemoryAllocator {
    /// 创建一个新的宏内存分配器
    ///
    /// # 参数
    /// * `total_memory` - 总内存大小（单位：KB）
    /// * `memory_per_macro` - 每个宏所需的内存大小（单位：KB）
    pub fn new(total_memory: usize, memory_per_macro: NonZeroUsize) -> Self {
        MacroMemoryAllocator {
            total_memory,
            memory_per_macro,
        }
    }

    /// 计算可以展开的宏数量
    pub fn max_macros(&self) -> usize {
        if self.total_memory == 0 {
            return 0;
        }

        let total = NonZeroUsize::new(self.total_memory).unwrap();
        // Rust 1.92.0: 使用 div_ceil 计算最大宏数量
        total.div_ceil(self.memory_per_macro).get()
    }
}

// ==================== 3. 迭代器方法特化在宏列表比较中的应用 ====================

/// 使用特化的迭代器比较方法比较宏列表
///
/// Rust 1.92.0: Iterator::eq 为 TrustedLen 迭代器特化，性能更好
pub fn compare_macro_lists(list1: &[MacroExpansionItem], list2: &[MacroExpansionItem]) -> bool {
    // Rust 1.92.0: 特化的迭代器比较方法，性能更好
    list1.iter().eq(list2.iter())
}

/// 使用迭代器特化检查宏展开状态
pub fn check_macro_expansion_states(
    macros: &[MacroExpansionItem],
    expected_names: &[String],
) -> bool {
    let actual_names: Vec<String> = macros.iter().map(|m| m.name.clone()).collect();
    // Rust 1.92.0: 特化的迭代器比较
    actual_names.iter().eq(expected_names.iter())
}

// ==================== 4. 宏展开性能优化 ====================

/// 宏展开性能监控器
///
/// 使用 Rust 1.92.0 的新特性优化宏展开性能
#[derive(Default)]
pub struct MacroExpansionPerformanceMonitor {
    expansion_times: Vec<u64>,
    cache_hits: usize,
    cache_misses: usize,
}

impl MacroExpansionPerformanceMonitor {
    /// 创建一个新的宏展开性能监控器
    pub fn new() -> Self {
        Self::default()
    }

    /// 记录一次宏展开及其耗时
    ///
    /// # 参数
    /// * `time_ns` - 展开耗时（纳秒）
    pub fn record_expansion(&mut self, time_ns: u64) {
        self.expansion_times.push(time_ns);
    }

    /// 记录一次缓存命中
    pub fn record_cache_hit(&mut self) {
        self.cache_hits += 1;
    }

    /// 记录一次缓存未命中
    pub fn record_cache_miss(&mut self) {
        self.cache_misses += 1;
    }

    /// 计算平均展开时间
    pub fn average_expansion_time(&self) -> Option<f64> {
        if self.expansion_times.is_empty() {
            return None;
        }

        let sum: u64 = self.expansion_times.iter().sum();
        Some(sum as f64 / self.expansion_times.len() as f64)
    }

    /// 计算缓存命中率
    pub fn cache_hit_rate(&self) -> f64 {
        let total = self.cache_hits + self.cache_misses;
        if total == 0 {
            return 0.0;
        }
        self.cache_hits as f64 / total as f64
    }

    /// 获取总展开次数
    pub fn expansion_count(&self) -> usize {
        self.expansion_times.len()
    }

    /// 获取缓存命中次数
    pub fn cache_hits(&self) -> usize {
        self.cache_hits
    }

    /// 获取缓存未命中次数
    pub fn cache_misses(&self) -> usize {
        self.cache_misses
    }
}

// ==================== 5. 综合应用示例 ====================

/// 演示 Rust 1.92.0 特性在宏系统中的应用
pub fn demonstrate_rust_192_macro_features() {
    println!("\n=== Rust 1.92.0 宏系统特性演示 ===\n");

    // 1. rotate_right 演示
    println!("1. rotate_right 在宏展开队列中的应用:");
    let mut queue = MacroExpansionQueue::new();
    queue.push(MacroExpansionItem {
        name: "macro1".to_string(),
        priority: 10,
        depth: 1,
    });
    queue.push(MacroExpansionItem {
        name: "macro2".to_string(),
        priority: 20,
        depth: 2,
    });
    queue.push(MacroExpansionItem {
        name: "macro3".to_string(),
        priority: 30,
        depth: 3,
    });

    println!("   原始队列: {:?}",
        queue.items.iter().map(|m| &m.name).collect::<Vec<_>>());

    queue.rotate(1);
    println!("   轮转后: {:?}",
        queue.items.iter().map(|m| &m.name).collect::<Vec<_>>());

    // 2. NonZero::div_ceil 演示
    println!("\n2. NonZero::div_ceil 在宏缓存计算中的应用:");
    let macros_per_entry = NonZeroUsize::new(10).unwrap();
    let total_macros = 47;
    let cache_size = calculate_macro_cache_size(total_macros, macros_per_entry);
    println!("   总宏数: {}", total_macros);
    println!("   每缓存条目宏数: {}", macros_per_entry);
    println!("   需要的缓存条目数: {}", cache_size);

    let allocator = MacroMemoryAllocator::new(1024, NonZeroUsize::new(32).unwrap());
    println!("   总内存: 1024 KB");
    println!("   每宏内存: 32 KB");
    println!("   最大宏数: {}", allocator.max_macros());

    // 3. 迭代器特化演示
    println!("\n3. 迭代器方法特化在宏比较中的应用:");
    let list1 = vec![
        MacroExpansionItem {
            name: "m1".to_string(),
            priority: 10,
            depth: 1,
        },
        MacroExpansionItem {
            name: "m2".to_string(),
            priority: 20,
            depth: 2,
        },
    ];
    let list2 = list1.clone();
    println!("   宏列表相等: {}", compare_macro_lists(&list1, &list2));

    let expected_names = vec!["m1".to_string(), "m2".to_string()];
    println!("   宏名称列表匹配: {}",
        check_macro_expansion_states(&list1, &expected_names));

    // 4. 性能监控演示
    println!("\n4. 宏展开性能监控:");
    let mut monitor = MacroExpansionPerformanceMonitor::new();
    monitor.record_expansion(100);
    monitor.record_expansion(150);
    monitor.record_expansion(120);
    monitor.record_cache_hit();
    monitor.record_cache_hit();
    monitor.record_cache_miss();

    if let Some(avg) = monitor.average_expansion_time() {
        println!("   平均展开时间: {:.2} ns", avg);
    }
    println!("   缓存命中率: {:.2}%", monitor.cache_hit_rate() * 100.0);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_queue_rotate() {
        let mut queue = MacroExpansionQueue::new();
        queue.push(MacroExpansionItem {
            name: "m1".to_string(),
            priority: 10,
            depth: 1,
        });
        queue.push(MacroExpansionItem {
            name: "m2".to_string(),
            priority: 20,
            depth: 2,
        });

        queue.rotate(1);
        let first = queue.pop().unwrap();
        assert_eq!(first.name, "m2");
    }

    #[test]
    fn test_macro_cache_size() {
        let macros_per_entry = NonZeroUsize::new(10).unwrap();
        assert_eq!(calculate_macro_cache_size(47, macros_per_entry), 5);
        assert_eq!(calculate_macro_cache_size(50, macros_per_entry), 5);
        assert_eq!(calculate_macro_cache_size(51, macros_per_entry), 6);
    }

    #[test]
    fn test_macro_memory_allocator() {
        let allocator = MacroMemoryAllocator::new(1024, NonZeroUsize::new(32).unwrap());
        assert_eq!(allocator.max_macros(), 32);
    }

    #[test]
    fn test_compare_macro_lists() {
        let list1 = vec![
            MacroExpansionItem {
                name: "m1".to_string(),
                priority: 10,
                depth: 1,
            },
            MacroExpansionItem {
                name: "m2".to_string(),
                priority: 20,
                depth: 2,
            },
        ];
        let list2 = list1.clone();
        assert!(compare_macro_lists(&list1, &list2));
    }

    #[test]
    fn test_performance_monitor() {
        let mut monitor = MacroExpansionPerformanceMonitor::new();
        monitor.record_expansion(100);
        monitor.record_expansion(200);
        monitor.record_cache_hit();
        monitor.record_cache_miss();

        assert_eq!(monitor.average_expansion_time(), Some(150.0));
        assert_eq!(monitor.cache_hit_rate(), 0.5);
    }
}
