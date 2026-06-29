// [来源: Rust Standard Library / CLRS]

pub mod arc_cache;
pub mod clock_cache;
pub mod dsu;
pub mod fenwick;
pub mod hazard_pointer;
pub mod lfu_cache;
pub mod lock_free_queue;
pub mod lock_free_stack;
pub mod lru_cache;
pub mod persistent_segment_tree;
pub mod priority_queue;
pub mod red_black_tree;
pub mod segtree;
pub mod skip_list;
pub mod sparse_table;
pub mod stack;
pub mod treap;
pub mod treiber_stack;
pub mod w_tinylfu_cache;

pub use arc_cache::ArcCache;
pub use clock_cache::ClockCache;
pub use lfu_cache::LfuCache;
pub use lru_cache::LruCache;
pub use persistent_segment_tree::PersistentSegmentTree;
pub use red_black_tree::RedBlackTree;
pub use skip_list::SkipList;
pub use treap::Treap;
pub use treiber_stack::TreiberStack;
pub use w_tinylfu_cache::WTinyLfuCache;

/// 统一缓存淘汰策略接口。
///
/// 该 trait 用于在示例与基准测试中对 `LruCache`、`LfuCache`、`ArcCache`、
/// `ClockCache`、`WTinyLfuCache` 等策略进行静态分发（static dispatch）。
pub trait CachePolicy<K, V> {
    /// 创建指定容量的缓存。
    fn new(capacity: usize) -> Self;

    /// 读取键对应的值；命中时策略内部应更新访问统计/顺序。
    fn get(&mut self, key: &K) -> Option<&V>;

    /// 写入键值对；容量满时按策略淘汰旧条目。
    fn put(&mut self, key: K, value: V);

    /// 当前缓存条目数。
    fn len(&self) -> usize;

    /// 缓存是否为空。
    fn is_empty(&self) -> bool;
}

#[cfg(test)]
mod tests {
    use super::*;

    /// 使用统一接口验证任意缓存策略的基本语义。
    fn smoke_test<C: CachePolicy<i32, &'static str>>(cap: usize) {
        let mut cache = C::new(cap);
        cache.put(1, "a");
        cache.put(2, "b");
        assert_eq!(cache.get(&1), Some(&"a"));
        assert_eq!(cache.len(), 2);
        cache.put(3, "c");
        assert!(cache.len() <= cap);
    }

    #[test]
    fn cache_policy_smoke_lru() {
        smoke_test::<lru_cache::LruCache<i32, &'static str>>(2);
    }

    #[test]
    fn cache_policy_smoke_lfu() {
        smoke_test::<lfu_cache::LfuCache<i32, &'static str>>(2);
    }

    #[test]
    fn cache_policy_smoke_arc() {
        smoke_test::<arc_cache::ArcCache<i32, &'static str>>(2);
    }

    #[test]
    fn cache_policy_smoke_clock() {
        smoke_test::<clock_cache::ClockCache<i32, &'static str>>(2);
    }

    #[test]
    fn cache_policy_smoke_w_tinylfu() {
        smoke_test::<w_tinylfu_cache::WTinyLfuCache<i32, &'static str>>(2);
    }
}
