//! # Rust 1.96.0 设计模式新特性实现模块

use std::ops::RangeInclusive;

/// RangeInclusive 在设计模式中的应用
pub struct PatternRangeExamples;

impl PatternRangeExamples {
    /// 对象池大小控制
    pub fn object_pool_size_range(
        current: usize,
        min: usize,
        max: usize,
    ) -> RangeInclusive<usize> {
        let target = if current < min {
            min
        } else if current > max {
            max
        } else {
            current
        };
        min..=target.max(min)
    }

    /// 装饰器链深度控制
    pub fn decorator_depth_category(depth: usize) -> &'static str {
        match depth {
            0..=2 => "简单",
            3..=5 => "中等",
            6..=10 => "复杂",
            _ => "过度装饰",
        }
    }

    /// 工厂模式批次生产
    pub fn factory_batch_ranges(
        total_items: usize,
        batch_size: usize,
    ) -> Vec<RangeInclusive<usize>> {
        if batch_size == 0 || total_items == 0 {
            return vec![];
        }

        let mut ranges = Vec::new();
        let mut start = 0;

        while start < total_items {
            let end = (start + batch_size - 1).min(total_items - 1);
            ranges.push(start..=end);
            start = end + 1;
        }

        ranges
    }

    /// 访问控制
    pub fn access_level_permission(
        user_level: u8,
        required_range: RangeInclusive<u8>,
    ) -> bool {
        required_range.contains(&user_level)
    }
}

/// 元组 coercion 示例
pub struct PatternTupleExamples;

impl PatternTupleExamples {
    /// 构建器结果
    pub fn builder_result<T>(
        result: Result<T, String>,
        steps: usize,
    ) -> (Result<T, String>, usize, &'static str)
    where
        T: Clone,
    {
        let status = if result.is_ok() { "built" } else { "failed" };
        (result, steps, status)
    }

    /// 代理调用结果
    pub fn proxy_call_result<T>(
        result: Result<T, String>,
        cached: bool,
        latency_ms: u64,
    ) -> (Result<T, String>, bool, u64, &'static str)
    where
        T: Clone,
    {
        let source = if cached { "cache" } else { "origin" };
        (result, cached, latency_ms, source)
    }

    /// 适配器转换
    pub fn adapter_conversion<T, U>(
        from: T,
        to: U,
        adapter_type: &'static str,
    ) -> (T, U, &'static str, bool)
    where
        T: Clone,
        U: Clone,
    {
        (from, to, adapter_type, true)
    }
}

/// 实际应用
pub struct PracticalPatternExamples;

impl PracticalPatternExamples {
    /// 连接池配置
    pub fn connection_pool_config(
        current: usize,
        demand: usize,
    ) -> (RangeInclusive<usize>, &'static str) {
        let target = current.max(demand);
        let min = 5;
        let max = 100;

        let range = min..=target.clamp(min, max);
        let action = if target > current {
            "expand"
        } else if target < current {
            "shrink"
        } else {
            "maintain"
        };

        (range, action)
    }

    /// 缓存大小分级
    pub fn cache_tier(size_mb: usize) -> &'static str {
        match size_mb {
            0..=16 => "L1",
            17..=64 => "L2",
            65..=256 => "L3",
            _ => "disk",
        }
    }
}

/// 设计模式组合器
pub struct PatternComposer {
    pattern_ranges: Vec<RangeInclusive<usize>>,
    active_range: RangeInclusive<usize>,
}

impl PatternComposer {
    /// 创建新模式组合器
    pub fn new(pattern_count: usize, group_size: usize) -> Self {
        let ranges = PatternRangeExamples::factory_batch_ranges(pattern_count, group_size);
        Self {
            pattern_ranges: ranges.clone(),
            active_range: 0..=ranges.len().saturating_sub(1),
        }
    }

    /// 获取模式范围
    pub fn get_pattern_range(&self, group_id: usize) -> Option<&RangeInclusive<usize>> {
        self.pattern_ranges.get(group_id)
    }

    /// 检查组是否活跃
    pub fn is_group_active(&self, group_id: usize) -> bool {
        self.active_range.contains(&group_id)
    }

    /// 获取所有范围
    pub fn get_all_ranges(&self) -> &[RangeInclusive<usize>] {
        &self.pattern_ranges
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 设计模式新特性演示");
    println!("========================================\n");

    let pool_range = PatternRangeExamples::object_pool_size_range(5, 10, 50);
    println!("对象池大小范围: {:?}", pool_range);

    let category = PatternRangeExamples::decorator_depth_category(4);
    println!("装饰器深度4类别: {}", category);

    let batches = PatternRangeExamples::factory_batch_ranges(100, 20);
    println!("工厂批次: {:?}", batches);

    let allowed = PatternRangeExamples::access_level_permission(5, 1..=10);
    println!("访问级别5在[1..=10]内: {}", allowed);

    let (range, action) = PracticalPatternExamples::connection_pool_config(10, 20);
    println!("连接池: 范围={:?}, 动作={}", range, action);

    let composer = PatternComposer::new(30, 6);
    println!("模式范围: {:?}", composer.get_all_ranges());

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取特性信息
pub fn get_rust_196_pattern_info() -> String {
    "Rust 1.96.0 设计模式新特性:\n\
        - RangeInclusive for pool and cache management\n\
        - Tuple coercion for builder and factory results\n\
        - Improved decorator depth control"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_object_pool_size_range() {
        let range = PatternRangeExamples::object_pool_size_range(5, 10, 50);
        assert_eq!(*range.start(), 10);
    }

    #[test]
    fn test_decorator_depth_category() {
        assert_eq!(PatternRangeExamples::decorator_depth_category(1), "简单");
        assert_eq!(PatternRangeExamples::decorator_depth_category(4), "中等");
        assert_eq!(PatternRangeExamples::decorator_depth_category(15), "过度装饰");
    }

    #[test]
    fn test_factory_batch_ranges() {
        let batches = PatternRangeExamples::factory_batch_ranges(100, 20);
        assert_eq!(batches.len(), 5);
    }

    #[test]
    fn test_access_level_permission() {
        assert!(PatternRangeExamples::access_level_permission(5, 1..=10));
        assert!(!PatternRangeExamples::access_level_permission(15, 1..=10));
    }

    #[test]
    fn test_connection_pool_config() {
        let (range, action) = PracticalPatternExamples::connection_pool_config(10, 20);
        assert_eq!(*range.start(), 5);
        assert_eq!(action, "expand");
    }

    #[test]
    fn test_cache_tier() {
        assert_eq!(PracticalPatternExamples::cache_tier(10), "L1");
        assert_eq!(PracticalPatternExamples::cache_tier(32), "L2");
        assert_eq!(PracticalPatternExamples::cache_tier(500), "disk");
    }

    #[test]
    fn test_pattern_composer() {
        let composer = PatternComposer::new(30, 6);
        assert_eq!(composer.get_all_ranges().len(), 5);
        assert!(composer.is_group_active(0));
    }

    #[test]
    fn test_get_rust_196_pattern_info() {
        let info = get_rust_196_pattern_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}
