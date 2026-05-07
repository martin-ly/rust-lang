//! # Rust 1.96 特性跟踪模块（含历史特性复习与 1.96 前瞻）

use std::ops::RangeInclusive;

/// if let guards (Rust 1.95 稳定，非 1.96 新特性) 在设计模式中的应用
///
/// `if let` guards 允许在 match arm 上直接进行模式匹配和条件判断，
/// 减少嵌套层级，使代码更扁平、更易读。
pub struct PatternIfLetGuardExamples;

impl PatternIfLetGuardExamples {
    /// 解析策略配置
    pub fn parse_strategy_config(input: Option<&str>) -> Result<String, &'static str> {
        match input {
            Some(s) if let Ok(size) = s.parse::<usize>() => Ok(format!("固定大小策略: {}", size)),
            Some("dynamic") => Ok("动态策略".to_string()),
            Some(_) => Err("未知的策略配置"),
            None => Ok("默认策略".to_string()),
        }
    }

    /// 解析观察者阈值配置
    pub fn parse_observer_threshold(input: Option<&str>) -> Result<u8, &'static str> {
        match input {
            Some(s) if let Ok(t) = s.parse::<u8>() => Ok(t),
            Some(_) => Err("无效的阈值"),
            None => Ok(50), // 默认阈值 50%
        }
    }
}

/// RangeInclusive 在设计模式中的应用
pub struct PatternRangeExamples;

impl PatternRangeExamples {
    /// 对象池大小控制
    pub fn object_pool_size_range(current: usize, min: usize, max: usize) -> RangeInclusive<usize> {
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
    pub fn access_level_permission(user_level: u8, required_range: RangeInclusive<u8>) -> bool {
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
    println!("   Rust 设计模式特性演示");
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
    "Rust 设计模式特性:\n- RangeInclusive for pool and cache management\n- Tuple coercion for \
     builder and factory results\n- Improved decorator depth control"
        .to_string()
}

// ============================================================================
// Rust 1.96 稳定新特性
// ============================================================================

use std::marker::PhantomPinned;
use std::path::{Path, PathBuf};

/// `core::pin::pin!` 宏在构建者模式中的应用
///
/// Rust 1.96 稳定了 `core::pin::pin!` 宏，允许在栈上固定值，
/// 无需 `Box::pin` 的堆分配。这在构建自引用结构时非常有用。
pub struct PinnedConfig {
    name: String,
    _pin: PhantomPinned,
}

impl PinnedConfig {
    /// 创建新的配置（未固定）
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            _pin: PhantomPinned,
        }
    }

    /// 使用 `pin!` 在栈上固定配置并返回名称长度
    ///
    /// `pin!` 宏避免了将数据移动到堆上的开销，适合短期存在的固定对象。
    pub fn name_len_pinned(self) -> usize {
        let pinned = std::pin::pin!(self);
        pinned.name.len()
    }
}

/// `core::pin::pin!` 宏在观察者模式中的应用
///
/// 观察者模式中的事件通知可以使用 `pin!` 固定临时状态，
/// 避免为短期观察任务分配堆内存。
pub struct PinnedNotification {
    message: String,
    _pin: PhantomPinned,
}

impl PinnedNotification {
    /// 创建新通知
    pub fn new(message: &str) -> Self {
        Self {
            message: message.to_string(),
            _pin: PhantomPinned,
        }
    }

    /// 在栈上固定通知并获取消息内容
    pub fn message_pinned(self) -> String {
        let pinned = std::pin::pin!(self);
        pinned.message.clone()
    }
}

/// `impl DerefMut for PathBuf` 在代理模式中的应用
///
/// Rust 1.96 为 `PathBuf` 实现了 `DerefMut<Target = Path>`，
/// 使得代理模式中可以更方便地获取内部路径的可变引用。
pub struct ConfigPathProxy {
    inner: PathBuf,
}

impl ConfigPathProxy {
    /// 创建新的路径代理
    pub fn new<P: AsRef<Path>>(path: P) -> Self {
        Self {
            inner: path.as_ref().to_path_buf(),
        }
    }

    /// 获取内部路径的可变引用（利用 PathBuf 的 DerefMut）
    pub fn path_mut(&mut self) -> &mut Path {
        &mut self.inner
    }

    /// 获取内部路径的不可变引用
    pub fn path(&self) -> &Path {
        &self.inner
    }

    /// 替换内部路径
    pub fn set_path<P: AsRef<Path>>(&mut self, path: P) {
        self.inner = path.as_ref().to_path_buf();
    }
}

/// 演示 Rust 1.96 新特性
pub fn demonstrate_rust_196_new_features() {
    println!("\n=== Rust 1.96 新特性演示 ===");

    // pin! 在构建者模式中的应用
    let config = PinnedConfig::new("database_pool");
    println!("固定配置名称长度: {}", config.name_len_pinned());

    // pin! 在观察者模式中的应用
    let notification = PinnedNotification::new("observer_update");
    println!("固定通知消息: {}", notification.message_pinned());

    // DerefMut for PathBuf 在代理模式中的应用
    let mut proxy = ConfigPathProxy::new("/etc/app");
    println!("代理路径: {:?}", proxy.path());
    proxy.set_path("/var/lib/app");
    println!("更新后路径: {:?}", proxy.path());
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
        assert_eq!(
            PatternRangeExamples::decorator_depth_category(15),
            "过度装饰"
        );
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
    fn test_parse_strategy_config() {
        assert_eq!(
            PatternIfLetGuardExamples::parse_strategy_config(Some("16")),
            Ok("固定大小策略: 16".to_string())
        );
        assert_eq!(
            PatternIfLetGuardExamples::parse_strategy_config(Some("dynamic")),
            Ok("动态策略".to_string())
        );
        assert_eq!(
            PatternIfLetGuardExamples::parse_strategy_config(Some("unknown")),
            Err("未知的策略配置")
        );
        assert_eq!(
            PatternIfLetGuardExamples::parse_strategy_config(None),
            Ok("默认策略".to_string())
        );
    }

    #[test]
    fn test_parse_observer_threshold() {
        assert_eq!(
            PatternIfLetGuardExamples::parse_observer_threshold(Some("75")),
            Ok(75)
        );
        assert_eq!(
            PatternIfLetGuardExamples::parse_observer_threshold(Some("abc")),
            Err("无效的阈值")
        );
        assert_eq!(
            PatternIfLetGuardExamples::parse_observer_threshold(None),
            Ok(50)
        );
    }

    #[test]
    fn test_get_rust_196_pattern_info() {
        let info = get_rust_196_pattern_info();
        assert!(info.contains("Rust 设计模式特性"));
    }

    // Rust 1.96 新特性测试
    #[test]
    fn test_pinned_config() {
        let config = PinnedConfig::new("test_config");
        assert_eq!(config.name_len_pinned(), 11);
    }

    #[test]
    fn test_pinned_notification() {
        let notification = PinnedNotification::new("hello_observer");
        assert_eq!(notification.message_pinned(), "hello_observer");
    }

    #[test]
    fn test_config_path_proxy() {
        let mut proxy = ConfigPathProxy::new("/etc/app");
        assert_eq!(proxy.path(), Path::new("/etc/app"));
        proxy.set_path("/var/lib/app");
        assert_eq!(proxy.path(), Path::new("/var/lib/app"));
    }

    #[test]
    fn test_path_buf_deref_mut() {
        let mut pb = PathBuf::from("/tmp/test");
        let path_mut: &mut Path = &mut pb;
        // DerefMut 允许从 &mut PathBuf 获取 &mut Path，这是 1.96 新增的实现
        assert_eq!(path_mut, Path::new("/tmp/test"));
    }
}
