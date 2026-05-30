//! Rust 1.96.0 `core::range` 模块专题示例
//!
//! 本示例展示 Rust 1.96.0 中 `core::range` 模块的完整新 API：
//! - `core::range::Range` / `RangeIter` — 半开区间 `[start, end)`
//! - `core::range::RangeFrom` / `RangeFromIter` — 无限区间 `[start, ∞)`
//! - `core::range::RangeToInclusive` — 闭区间 `(-∞, end]`（不实现 IntoIterator）
//! - `core::range::RangeInclusive` / `RangeInclusiveIter` — 闭区间 `[start, end]`
//!
//! 这些类型实现 `IntoIterator` 而非直接 `Iterator`，因此当元素类型 `T: Copy` 时，
//! 范围类型本身也实现 `Copy`，可多次迭代而不被消费。
//!
//! 权威来源: https://releases.rs/docs/1.96.0/ | RFC 3550
//!
//! 运行方式:
//! ```bash
//! cargo run --example core_range_demo -p c08_algorithms
//! ```

// ============================================================================
// 示例 1: core::range::Range — 半开区间 [start, end)
// ============================================================================

/// 使用 `core::range::Range` 创建可复用的半开区间
fn demonstrate_core_range() {
    println!("=== core::range::Range (半开区间 [start, end)) ===");

    use core::range::{Range, RangeIter};

    let range: Range<i32> = Range { start: 1, end: 5 };
    println!("  Range {{ start: 1, end: 5 }} = {:?}", range);

    // Range 实现 Copy（因为 i32: Copy），可多次迭代
    let iter1: RangeIter<i32> = range.into_iter();
    let values1: Vec<i32> = iter1.collect();
    println!("  第一次迭代: {:?}", values1); // [1, 2, 3, 4]

    let iter2: RangeIter<i32> = range.into_iter();
    let values2: Vec<i32> = iter2.collect();
    println!("  第二次迭代: {:?}", values2); // [1, 2, 3, 4]

    // 与 std::ops::Range 的对比
    let std_range: std::ops::Range<i32> = 1..5;
    let std_values: Vec<i32> = std_range.clone().collect();
    println!("  std::ops::Range (1..5): {:?}", std_values);
}

// ============================================================================
// 示例 2: core::range::RangeFrom — 无限区间 [start, ∞)
// ============================================================================

/// 使用 `core::range::RangeFrom` 创建无限区间
fn demonstrate_core_range_from() {
    println!("\n=== core::range::RangeFrom (无限区间 [start, ∞)) ===");

    use core::range::{RangeFrom, RangeFromIter};

    let from: RangeFrom<i32> = RangeFrom { start: 10 };
    println!("  RangeFrom {{ start: 10 }} = {:?}", from);

    let iter: RangeFromIter<i32> = from.into_iter();
    let first_5: Vec<i32> = iter.take(5).collect();
    println!("  取前5个: {:?}", first_5); // [10, 11, 12, 13, 14]

    // RangeFrom 也实现 Copy
    let mut another_iter: RangeFromIter<i32> = from.into_iter();
    let nth_10 = another_iter.nth(10);
    println!("  第11个元素: {:?}", nth_10); // Some(20)
}

// ============================================================================
// 示例 3: core::range::RangeToInclusive — 闭区间 (-∞, end]
// ============================================================================

/// 使用 `core::range::RangeToInclusive` 创建上限闭区间
fn demonstrate_core_range_to_inclusive() {
    println!("\n=== core::range::RangeToInclusive (闭区间 (-∞, end]) ===");

    use core::range::RangeToInclusive;

    let to: RangeToInclusive<i32> = RangeToInclusive { last: 4 };
    println!("  RangeToInclusive {{ last: 4 }} = {:?}", to);
    println!("  注意: RangeToInclusive 不实现 IntoIterator");

    // 与 RangeInclusive 的对比
    use core::range::RangeInclusive;
    let inclusive: RangeInclusive<i32> = RangeInclusive { start: 0, last: 4 };
    let inc_values: Vec<i32> = inclusive.into_iter().collect();
    println!("  RangeInclusive(0, 4): {:?}", inc_values); // [0, 1, 2, 3, 4]
}

// ============================================================================
// 示例 4: core::range::RangeInclusive — 闭区间 [start, end]
// ============================================================================

/// 使用 `core::range::RangeInclusive` 创建包含性范围
fn demonstrate_core_range_inclusive() {
    println!("\n=== core::range::RangeInclusive (闭区间 [start, end]) ===");

    use core::range::{RangeInclusive, RangeInclusiveIter};

    let range: RangeInclusive<i32> = RangeInclusive { start: 1, last: 5 };
    println!("  RangeInclusive {{ start: 1, last: 5 }} = {:?}", range);
    println!("  start: {}, last: {}", range.start, range.last);

    let iter: RangeInclusiveIter<i32> = range.into_iter();
    let values: Vec<i32> = iter.collect();
    println!("  迭代结果: {:?}", values); // [1, 2, 3, 4, 5]

    // 字符范围
    let char_range: RangeInclusive<char> = RangeInclusive {
        start: 'a',
        last: 'e',
    };
    let chars: Vec<char> = char_range.into_iter().collect();
    println!("  字符范围 ['a', 'e']: {:?}", chars);
}

// ============================================================================
// 示例 5: Copy 语义 — 范围值不被消费
// ============================================================================

/// 演示 core::range 类型的 Copy 语义：多次迭代不消费原始值
fn demonstrate_copy_semantics() {
    println!("\n=== Copy 语义: 多次迭代不消费 ===");

    use core::range::Range;

    let range: Range<u32> = Range { start: 1, end: 4 };

    // 第一次迭代
    let sum1: u32 = range.into_iter().sum();
    println!("  第一次 sum: {}", sum1); // 6

    // 第二次迭代 — range 仍可用，因为 Range<u32>: Copy
    let sum2: u32 = range.into_iter().sum();
    println!("  第二次 sum: {}", sum2); // 6

    // 第三次迭代
    let product: u32 = range.into_iter().product();
    println!("  product: {}", product); // 6

    println!("  ✅ Range<u32> 实现 Copy，可无限次复用");
}

// ============================================================================
// 示例 6: 算法应用 — 闭区间二分查找
// ============================================================================

use core::range::RangeInclusive;

/// 使用 RangeInclusive 实现包含边界的二分查找
fn inclusive_binary_search(
    arr: &[i32],
    target: i32,
    range: &RangeInclusive<usize>,
) -> Option<usize> {
    let mut left = range.start;
    let mut right = range.last;

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
    println!("\n=== 算法: 闭区间二分查找 ===");

    let arr = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19];
    let range = RangeInclusive {
        start: 0,
        last: arr.len() - 1,
    };

    println!("  数组: {:?}", arr);
    println!("  搜索范围: [{}, {}]", range.start, range.last);

    for target in [1, 7, 19, 20] {
        match inclusive_binary_search(&arr, target, &range) {
            Some(idx) => println!("  查找 {} -> 索引 {}", target, idx),
            None => println!("  查找 {} -> 未找到", target),
        }
    }
}

// ============================================================================
// 示例 7: 算法应用 — 区间调度与重叠检测
// ============================================================================

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
            if a.start <= b.last && b.start <= a.last {
                overlaps.push((intervals[i].name, intervals[j].name));
            }
        }
    }
    overlaps
}

fn demonstrate_interval_scheduling() {
    println!("\n=== 算法: 区间重叠检测 ===");

    let intervals = vec![
        TimeRange {
            name: "Meeting A",
            range: RangeInclusive { start: 9, last: 11 },
        },
        TimeRange {
            name: "Meeting B",
            range: RangeInclusive {
                start: 10,
                last: 12,
            },
        },
        TimeRange {
            name: "Meeting C",
            range: RangeInclusive {
                start: 14,
                last: 16,
            },
        },
        TimeRange {
            name: "Meeting D",
            range: RangeInclusive {
                start: 11,
                last: 13,
            },
        },
    ];

    println!("  区间列表:");
    for interval in &intervals {
        println!(
            "    {}: [{}, {}]",
            interval.name, interval.range.start, interval.range.last
        );
    }

    let overlaps = find_overlapping_intervals(&intervals);
    println!("  重叠区间对:");
    for (a, b) in overlaps {
        println!("    {} <-> {}", a, b);
    }
}

// ============================================================================
// 示例 8: no_std 友好性
// ============================================================================

fn demonstrate_no_std_friendly() {
    println!("\n=== no_std 友好性 ===");
    println!("  core::range 所有类型完全定义在 core 中");
    println!("  无需 std，无需 alloc，仅需 core");
    println!("  适合嵌入式和内核编程场景");
}

// ============================================================================
// 主演示函数
// ============================================================================

fn main() {
    println!("🦀 Rust 1.96.0 `core::range` 模块完整演示\n");

    demonstrate_core_range();
    demonstrate_core_range_from();
    demonstrate_core_range_to_inclusive();
    demonstrate_core_range_inclusive();
    demonstrate_copy_semantics();
    demonstrate_inclusive_binary_search();
    demonstrate_interval_scheduling();
    demonstrate_no_std_friendly();

    println!("\n✅ `core::range` 1.96.0 演示完成！");
    println!("   关键要点:");
    println!("   - core::range::Range / RangeFrom / RangeToInclusive / RangeInclusive");
    println!("   - 配套迭代器: RangeIter / RangeFromIter / RangeInclusiveIter");
    println!("   - 所有范围类型在元素 Copy 时自身也 Copy，可多次复用");
    println!("   - 实现 IntoIterator 而非 Iterator，解耦范围值与迭代状态");
    println!("   - 完全在 core 中定义，no_std 友好");
}
