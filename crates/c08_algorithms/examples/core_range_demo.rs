//! Rust 1.95.0 `core::range` 模块专题示例
//!
//! 本示例展示 Rust 1.95.0 中 `core::range` 模块的新 API，
//! 包括 `RangeInclusive`、`RangeInclusiveIter` 以及它们在算法中的应用。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! cargo run --example core_range_demo -p c08_algorithms
//! ```

use std::ops::RangeInclusive;

// ==================== 示例 1: RangeInclusive 基础 ====================

/// 使用 core::range::RangeInclusive 创建包含性范围
fn demonstrate_range_inclusive() {
    println!("--- core::range::RangeInclusive 基础 ---");

    // 创建 RangeInclusive
    let range: RangeInclusive<i32> = 1..=5;
    println!("  RangeInclusive::new(1, 5): {:?}", range);
    println!("  start: {}, end: {}", range.start(), range.end());

    // 迭代
    print!("  迭代: ");
    for i in range {
        print!("{} ", i);
    }
    println!();

    // 包含性检查（使用新的 range 避免与上面迭代的 range 冲突）
    let range2: RangeInclusive<i32> = 10..=20;
    println!("  10 在 [10, 20] 中? {}", range2.contains(&10));
    println!("  20 在 [10, 20] 中? {}", range2.contains(&20));
    println!("  15 在 [10, 20] 中? {}", range2.contains(&15));
    println!("  9  在 [10, 20] 中? {}", range2.contains(&9));
}

// ==================== 示例 2: RangeInclusiveIter 迭代器 ====================

/// 展示 RangeInclusiveIter 的使用
fn demonstrate_range_inclusive_iter() {
    println!("\n--- RangeInclusiveIter 迭代器 ---");

    let range: RangeInclusive<i32> = 1..=10;
    let iter = range.into_iter();

    println!("  手动迭代:");
    for n in iter {
        print!("{} ", n);
    }
    println!();

    // 使用迭代器遍历字符范围
    let char_range: RangeInclusive<char> = 'a'..='e';
    print!("  char 迭代: ");
    for c in char_range {
        print!("{} ", c);
    }
    println!();
}

// ==================== 示例 3: 与 std::ops::RangeInclusive 的对比 ====================

/// 对比 core::range::RangeInclusive 和 std::ops::RangeInclusive
fn compare_range_inclusive_types() {
    println!("\n--- core::range vs std::ops RangeInclusive ---");

    // std::ops::RangeInclusive（旧类型，仍然可用）
    let std_range: std::ops::RangeInclusive<i32> = 1..=5;

    // core::range::RangeInclusive（1.95.0+，等价但位于 core::range）
    let core_range: RangeInclusive<i32> = 1..=5;

    println!("  std::ops::RangeInclusive: {:?}", std_range);
    println!("  core::range::RangeInclusive: {:?}", core_range);

    // 两者可以比较
    assert_eq!(std_range.start(), core_range.start());
    assert_eq!(std_range.end(), core_range.end());

    println!("  ✅ 两者语义等价，core::range 版本更利于 no_std 场景");
}

// ==================== 示例 4: 算法应用 — 闭区间二分查找 ====================

/// 使用 RangeInclusive 实现包含边界的二分查找
fn inclusive_binary_search(
    arr: &[i32],
    target: i32,
    range: &RangeInclusive<usize>,
) -> Option<usize> {
    let mut left = *range.start();
    let mut right = *range.end();

    // 包含 right 边界，所以条件是 <= 而非 <
    while left <= right {
        let mid = left + (right - left) / 2;

        match arr.get(mid) {
            Some(&val) if val == target => return Some(mid),
            Some(&val) if val < target => left = mid + 1,
            _ => {
                if mid == 0 {
                    break;
                }
                right = mid - 1;
            }
        }
    }

    None
}

fn demonstrate_inclusive_binary_search() {
    println!("\n--- 算法: 闭区间二分查找 ---");

    let arr = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
    let range = 0..=(arr.len() - 1);

    println!("  数组: {:?}", arr);
    println!("  搜索范围: [{}, {}]", range.start(), range.end());

    for target in [1, 7, 19, 20] {
        match inclusive_binary_search(&arr, target, &range) {
            Some(idx) => println!("  查找 {} -> 索引 {}", target, idx),
            None => println!("  查找 {} -> 未找到", target),
        }
    }
}

// ==================== 示例 5: 算法应用 — 区间调度 ====================

#[derive(Debug, Clone, PartialEq)]
struct TimeRange {
    name: &'static str,
    range: RangeInclusive<u8>,
}

/// 找出重叠的区间
fn find_overlapping_intervals(intervals: &[TimeRange]) -> Vec<(&'static str, &'static str)> {
    let mut overlaps = Vec::new();

    for i in 0..intervals.len() {
        for j in (i + 1)..intervals.len() {
            let a = &intervals[i].range;
            let b = &intervals[j].range;

            // 两个闭区间重叠的条件
            if a.start() <= b.end() && b.start() <= a.end() {
                overlaps.push((intervals[i].name, intervals[j].name));
            }
        }
    }

    overlaps
}

fn demonstrate_interval_scheduling() {
    println!("\n--- 算法: 区间重叠检测 ---");

    let intervals = vec![
        TimeRange {
            name: "Meeting A",
            range: 9..=11,
        },
        TimeRange {
            name: "Meeting B",
            range: 10..=12,
        },
        TimeRange {
            name: "Meeting C",
            range: 14..=16,
        },
        TimeRange {
            name: "Meeting D",
            range: 11..=13,
        },
    ];

    println!("  区间列表:");
    for interval in &intervals {
        println!(
            "    {}: [{}, {}]",
            interval.name,
            interval.range.start(),
            interval.range.end()
        );
    }

    let overlaps = find_overlapping_intervals(&intervals);
    println!("  重叠区间对:");
    for (a, b) in overlaps {
        println!("    {} <-> {}", a, b);
    }
}

// ==================== 示例 6: 算法应用 — 分页范围计算 ====================

/// 计算分页的 item 索引范围
fn page_range(
    total_items: usize,
    page_size: usize,
    page_number: usize,
) -> Option<RangeInclusive<usize>> {
    if page_size == 0 || page_number == 0 {
        return None;
    }

    let start = (page_number - 1) * page_size;
    if start >= total_items {
        return None;
    }

    let end = (start + page_size - 1).min(total_items - 1);
    Some(start..=end)
}

fn demonstrate_pagination() {
    println!("\n--- 应用: 分页范围计算 ---");

    let total_items = 25;
    let page_size = 10;

    println!("  总项目: {}, 每页: {}", total_items, page_size);

    for page in 1..=3 {
        match page_range(total_items, page_size, page) {
            Some(range) => {
                let start = *range.start();
                let end = *range.end();
                let items: Vec<_> = range.clone().map(|i| format!("item_{}", i)).collect();
                println!("  第 {} 页: 索引 [{}, {}] -> {:?}", page, start, end, items);
            }
            None => println!("  第 {} 页: 无数据", page),
        }
    }
}

// ==================== 示例 7: no_std 友好性 ====================

/// core::range 模块完全在 core 中定义，无需 std
fn demonstrate_no_std_friendly() {
    println!("\n--- no_std 友好性 ---");
    println!("  core::range::RangeInclusive 完全定义在 core 中");
    println!("  这意味着在 #![no_std] 环境中可直接使用");
    println!("  无需 alloc，仅需 core");
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `core::range` 模块专题演示\n");

    demonstrate_range_inclusive();
    demonstrate_range_inclusive_iter();
    compare_range_inclusive_types();
    demonstrate_inclusive_binary_search();
    demonstrate_interval_scheduling();
    demonstrate_pagination();
    demonstrate_no_std_friendly();

    println!("\n✅ `core::range` 演示完成！");
    println!("   关键要点:");
    println!("   - core::range::RangeInclusive 是 std::ops::RangeInclusive 的 core 层等价物");
    println!("   - 语义完全一致，但更适合 no_std 和嵌入式场景");
    println!("   - RangeInclusiveIter 是配套的迭代器类型");
}
