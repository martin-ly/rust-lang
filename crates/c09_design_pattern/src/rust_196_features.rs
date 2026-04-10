//! # Rust 1.96.0 设计模式新特性实现模块
//!
//! 本模块展示了 Rust 1.96.0 中设计模式相关的关键改进。

use std::ops::RangeInclusive;

/// if let guards 在设计模式中的应用
pub struct PatternGuardExamples;

impl PatternGuardExamples {
    /// 使用 if let guards 实现策略模式选择
    pub fn select_strategy<T>(
        strategies: &[Box<dyn Fn(T) -> T>],
        selector: Option<usize>,
        input: T,
    ) -> Result<T, String>
    where
        T: Clone,
    {
        match selector {
            Some(idx) if let Some(strategy) = strategies.get(idx) => Ok(strategy(input)),
            Some(idx) => Err(format!("策略索引 {} 越界", idx)),
            None => Err("未选择策略".to_string()),
        }
    }

    /// 使用 if let guards 处理观察者通知
    pub fn notify_observers<T>(
        observers: &[Box<dyn Fn(&T)>],
        event: Option<T>,
    ) -> usize
    where
        T: Clone,
    {
        match event {
            Some(e) if let true = !observers.is_empty() => {
                for observer in observers {
                    observer(&e);
                }
                observers.len()
            }
            _ => 0,
        }
    }

    /// 使用 if let guards 实现状态机转换
    pub fn state_transition(
        current: &'static str,
        event: Option<&'static str>,
    ) -> &'static str {
        match (current, event) {
            ("idle", Some("start")) => "running",
            ("running", Some("pause")) => "paused",
            ("running", Some("stop")) => "completed",
            ("running", Some("complete")) => "completed",
            ("paused", Some("resume")) => "running",
            ("paused", Some("stop")) => "completed",
            (state, _) => state,
        }
    }
}

/// RangeInclusive 在设计模式中的应用
pub struct PatternRangeExamples;

impl PatternRangeExamples {
    /// 使用 RangeInclusive 实现对象池大小控制
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

    /// 使用 RangeInclusive 进行装饰器链深度控制
    pub fn decorator_depth_category(depth: usize) -> &'static str {
        match depth {
            0..=2 => "简单",
            3..=5 => "中等",
            6..=10 => "复杂",
            _ => "过度装饰",
        }
    }

    /// 使用 RangeInclusive 实现工厂模式批次生产
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

    /// 使用 RangeInclusive 进行访问控制
    pub fn access_level_permission(
        user_level: u8,
        required_range: RangeInclusive<u8>,
    ) -> bool {
        required_range.contains(&user_level)
    }
}

/// 元组 coercion 在设计模式中的应用
pub struct PatternTupleExamples;

impl PatternTupleExamples {
    /// 使用元组 coercion 返回构建器结果
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

    /// 使用元组 coercion 返回工厂产品信息
    pub fn factory_product_info<T>(
        product: T,
        factory_id: usize,
    ) -> (T, usize, std::time::Instant, &'static str)
    where
        T: Clone,
    {
        (product, factory_id, std::time::Instant::now(), "produced")
    }

    /// 使用元组 coercion 返回代理调用结果
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

    /// 使用元组 coercion 返回适配器转换信息
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

/// 实际设计模式应用示例
pub struct PracticalPatternExamples;

impl PracticalPatternExamples {
    /// 使用 if let guards 实现责任链处理
    pub fn chain_of_responsibility<T>(
        handlers: &[Box<dyn Fn(&T) -> Option<String>>],
        request: T,
    ) -> Option<String>
    where
        T: Clone,
    {
        for handler in handlers {
            match handler(&request) {
                Some(result) if let true = !result.is_empty() => return Some(result),
                _ => continue,
            }
        }
        None
    }

    /// 使用 RangeInclusive 进行连接池管理
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

    /// 使用元组 coercion 返回命令模式执行结果
    pub fn command_execution<T>(
        result: Result<T, String>,
        command_id: usize,
        undoable: bool,
    ) -> (Result<T, String>, usize, bool, &'static str)
    where
        T: Clone,
    {
        let status = if result.is_ok() { "executed" } else { "failed" };
        (result, command_id, undoable, status)
    }

    /// 使用 RangeInclusive 进行缓存大小分级
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
    /// 创建新的模式组合器
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

    /// 获取所有模式范围
    pub fn get_all_ranges(&self) -> &[RangeInclusive<usize>] {
        &self.pattern_ranges
    }
}

/// 演示函数
pub fn demonstrate_rust_196_features() {
    println!("\n========================================");
    println!("   Rust 1.96.0 设计模式新特性演示");
    println!("========================================\n");

    // if let guards 演示
    println!("=== if let guards 演示 ===");
    let state = PatternGuardExamples::state_transition("idle", Some("start"));
    println!("状态转换(idle->start): {}", state);

    let state = PatternGuardExamples::state_transition("running", Some("stop"));
    println!("状态转换(running->stop): {}", state);

    // Range 类型演示
    println!("\n=== Range 类型演示 ===");
    let pool_range = PatternRangeExamples::object_pool_size_range(5, 10, 50);
    println!("对象池大小范围: {:?}", pool_range);

    let category = PatternRangeExamples::decorator_depth_category(4);
    println!("装饰器深度4类别: {}", category);

    let batches = PatternRangeExamples::factory_batch_ranges(100, 20);
    println!("工厂批次: {:?}", batches);

    let allowed = PatternRangeExamples::access_level_permission(5, 1..=10);
    println!("访问级别5在[1..=10]内: {}", allowed);

    // 元组 coercion 演示
    println!("\n=== 元组 coercion 演示 ===");
    let (result, steps, status) = PatternTupleExamples::builder_result(Ok("product"), 5);
    println!("构建器: result={:?}, steps={}, status={}", result, steps, status);

    let (result, cached, latency, source) =
        PatternTupleExamples::proxy_call_result(Ok("data"), true, 10);
    println!("代理调用: cached={}, latency={}ms, source={}", cached, latency, source);

    // 模式组合器演示
    println!("\n=== 模式组合器演示 ===");
    let composer = PatternComposer::new(30, 6);
    println!("模式范围: {:?}", composer.get_all_ranges());
    println!("组0是否活跃: {}", composer.is_group_active(0));

    println!("\n========================================");
    println!("   演示完成");
    println!("========================================\n");
}

/// 获取 Rust 1.96.0 设计模式特性信息
pub fn get_rust_196_pattern_info() -> String {
    "Rust 1.96.0 设计模式新特性:\n\
        - if let guards in pattern selection\n\
        - RangeInclusive for pool and cache management\n\
        - Tuple coercion for builder and factory results\n\
        - Better chain of responsibility handling\n\
        - Improved decorator depth control"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_state_transition() {
        assert_eq!(
            PatternGuardExamples::state_transition("idle", Some("start")),
            "running"
        );
        assert_eq!(
            PatternGuardExamples::state_transition("running", Some("pause")),
            "paused"
        );
        assert_eq!(
            PatternGuardExamples::state_transition("running", Some("stop")),
            "completed"
        );
        assert_eq!(
            PatternGuardExamples::state_transition("paused", Some("stop")),
            "completed"
        );
        assert_eq!(
            PatternGuardExamples::state_transition("running", None),
            "running"
        );
    }

    #[test]
    fn test_object_pool_size_range() {
        let range = PatternRangeExamples::object_pool_size_range(5, 10, 50);
        assert_eq!(*range.start(), 10);
        assert_eq!(*range.end(), 10);

        let range = PatternRangeExamples::object_pool_size_range(60, 10, 50);
        assert_eq!(*range.end(), 50);
    }

    #[test]
    fn test_decorator_depth_category() {
        assert_eq!(PatternRangeExamples::decorator_depth_category(1), "简单");
        assert_eq!(PatternRangeExamples::decorator_depth_category(4), "中等");
        assert_eq!(PatternRangeExamples::decorator_depth_category(8), "复杂");
        assert_eq!(PatternRangeExamples::decorator_depth_category(15), "过度装饰");
    }

    #[test]
    fn test_factory_batch_ranges() {
        let batches = PatternRangeExamples::factory_batch_ranges(100, 20);
        assert_eq!(batches.len(), 5);
        
        let total: usize = batches.iter().map(|r| r.end() - r.start() + 1).sum();
        assert_eq!(total, 100);
    }

    #[test]
    fn test_access_level_permission() {
        assert!(PatternRangeExamples::access_level_permission(5, 1..=10));
        assert!(!PatternRangeExamples::access_level_permission(15, 1..=10));
    }

    #[test]
    fn test_builder_result() {
        let (result, steps, status) = PatternTupleExamples::builder_result(Ok("product"), 5);
        assert!(result.is_ok());
        assert_eq!(steps, 5);
        assert_eq!(status, "built");
    }

    #[test]
    fn test_proxy_call_result() {
        let (result, cached, latency, source) =
            PatternTupleExamples::proxy_call_result(Ok("data"), true, 10);
        assert!(result.is_ok());
        assert!(cached);
        assert_eq!(latency, 10);
        assert_eq!(source, "cache");
    }

    #[test]
    fn test_adapter_conversion() {
        let (from, to, adapter_type, success) =
            PatternTupleExamples::adapter_conversion("input", "output", "json");
        assert_eq!(from, "input");
        assert_eq!(to, "output");
        assert_eq!(adapter_type, "json");
        assert!(success);
    }

    #[test]
    fn test_connection_pool_config() {
        let (range, action) = PracticalPatternExamples::connection_pool_config(10, 20);
        assert_eq!(*range.start(), 5);
        assert_eq!(action, "expand");

        let (range, action) = PracticalPatternExamples::connection_pool_config(30, 15);
        assert_eq!(action, "maintain");
    }

    #[test]
    fn test_cache_tier() {
        assert_eq!(PracticalPatternExamples::cache_tier(10), "L1");
        assert_eq!(PracticalPatternExamples::cache_tier(32), "L2");
        assert_eq!(PracticalPatternExamples::cache_tier(100), "L3");
        assert_eq!(PracticalPatternExamples::cache_tier(500), "disk");
    }

    #[test]
    fn test_pattern_composer() {
        let composer = PatternComposer::new(30, 6);
        assert_eq!(composer.get_all_ranges().len(), 5);
        assert!(composer.is_group_active(0));
        assert!(composer.get_pattern_range(0).is_some());
    }

    #[test]
    fn test_get_rust_196_pattern_info() {
        let info = get_rust_196_pattern_info();
        assert!(info.contains("Rust 1.96.0"));
    }
}
