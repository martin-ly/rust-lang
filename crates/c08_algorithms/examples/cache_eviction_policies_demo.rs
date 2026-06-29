//! 缓存淘汰策略对比示例。
//!
//! 对 LRU、LFU、ARC、CLOCK、W-TinyLFU 五种策略运行若干典型负载，
//! 统计命中率，帮助理解不同策略的适用场景与边界行为。

use c08_algorithms::data_structure::CachePolicy;
use c08_algorithms::data_structure::arc_cache::ArcCache;
use c08_algorithms::data_structure::clock_cache::ClockCache;
use c08_algorithms::data_structure::lfu_cache::LfuCache;
use c08_algorithms::data_structure::lru_cache::LruCache;
use c08_algorithms::data_structure::w_tinylfu_cache::WTinyLfuCache;

/// 在指定策略上回放工作负载，返回（命中次数，未命中次数）。
fn simulate<C: CachePolicy<i32, &'static str>>(
    capacity: usize,
    workload: &[i32],
) -> (usize, usize) {
    let mut cache = C::new(capacity);
    let mut hits = 0usize;
    let mut misses = 0usize;

    for &key in workload {
        if cache.get(&key).is_some() {
            hits += 1;
        } else {
            misses += 1;
            cache.put(key, "v");
        }
    }

    (hits, misses)
}

fn format_result(name: &str, hits: usize, misses: usize) {
    let total = hits + misses;
    let rate = if total == 0 {
        0.0
    } else {
        (hits as f64 / total as f64) * 100.0
    };
    println!(
        "{:<12} 命中 {:>3} / 未命中 {:>3} / 总计 {:>3} -> {:.1}%",
        name, hits, misses, total, rate
    );
}

fn run_workload(name: &str, capacity: usize, workload: &[i32]) {
    println!("\n▶ 负载: {} (容量={})", name, capacity);
    let (h, m) = simulate::<LruCache<i32, &'static str>>(capacity, workload);
    format_result("LRU", h, m);
    let (h, m) = simulate::<LfuCache<i32, &'static str>>(capacity, workload);
    format_result("LFU", h, m);
    let (h, m) = simulate::<ArcCache<i32, &'static str>>(capacity, workload);
    format_result("ARC", h, m);
    let (h, m) = simulate::<ClockCache<i32, &'static str>>(capacity, workload);
    format_result("CLOCK", h, m);
    let (h, m) = simulate::<WTinyLfuCache<i32, &'static str>>(capacity, workload);
    format_result("W-TinyLFU", h, m);
}

fn main() {
    println!("=== 缓存淘汰策略命中率对比 ===");

    // 1. 局部性良好的循环访问（LRU 友好）
    let localized: Vec<i32> = vec![1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 3];
    run_workload("局部性循环", 3, &localized);

    // 2. 扫描型负载：一次性顺序访问大量键（LRU 不利）
    let scan: Vec<i32> = (1..=10).chain(1..=10).collect();
    run_workload("扫描型负载", 4, &scan);

    // 3. 混合负载：少数高频键 + 大量低频键
    let mixed: Vec<i32> = vec![
        1, 2, 1, 3, 1, 4, 1, 5, 1, 6, 1, 7, 1, 8, 1, 9, 1, 10, 1, 2, 1, 3, 1, 4, 1, 5, 1, 6, 1, 7,
        1, 8, 1, 9, 1, 10,
    ];
    run_workload("混合高频", 4, &mixed);

    // 4. 突发新键：新键短暂出现后不再访问（LFU 可能保留噪声）
    let bursts: Vec<i32> = vec![
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10, // 突发
        1, 2, 3, 1, 2, 3, 1, 2, 3, // 稳定热点
    ];
    run_workload("突发新键", 4, &bursts);
}
