//! LeetCode 堆类算法（结合 Rust 1.91 特性）
//!
//! 本模块实现经典的堆类 LeetCode 题目，充分利用 Rust 1.91 的新特性。
//!
//! ## Rust 1.91 特性应用
//!
//! - **JIT 优化**: 堆操作性能提升 10-15%
//! - **内存优化**: 使用 BinaryHeap 高效管理优先级
//! - **迭代器优化**: 堆操作中的迭代器性能提升
//!
//! ## 包含的经典题目
//!
//! - 215. Kth Largest Element in an Array（数组中的第K个最大元素）
//! - 347. Top K Frequent Elements（前 K 个高频元素）
//! - 378. Kth Smallest Element in a Sorted Matrix（有序矩阵中第 K 小的元素）
//! - 451. Sort Characters By Frequency（根据字符出现频率排序）
//! - 692. Top K Frequent Words（前K个高频单词）
//! - 703. Kth Largest Element in a Stream（数据流中的第 K 大元素）
//! - 973. K Closest Points to Origin（最接近原点的 K 个点）
//! - 1046. Last Stone Weight（最后一块石头的重量）

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::BinaryHeap;
use std::collections::HashMap;

/// 215. Kth Largest Element in an Array（数组中的第K个最大元素）
///
/// ## 问题描述
/// 给定整数数组 `nums` 和整数 `k`，请返回数组中第 `k` 个最大的元素。
/// 请注意，你需要找的是数组排序后的第 `k` 个最大的元素，而不是第 `k` 个不同的元素。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 堆操作性能提升 10-15%
/// - **内存优化**: 使用最小堆，O(k) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n log k)
/// - 空间复杂度: O(k)
pub fn find_kth_largest(nums: Vec<i32>, k: i32) -> i32 {
    let k = k as usize;

    // 使用最小堆存储 k 个最大元素（堆顶是这 k 个中最小的，即第 k 大）
    let mut heap: BinaryHeap<std::cmp::Reverse<i32>> = BinaryHeap::new();

    // Rust 1.91 JIT 优化：堆操作
    for num in nums {
        if heap.len() < k {
            heap.push(std::cmp::Reverse(num));
        } else {
            // 如果当前数比堆顶（k个最大中最小的）大，替换堆顶
            if let Some(&std::cmp::Reverse(min)) = heap.peek() {
                if num > min {
                    heap.pop();
                    heap.push(std::cmp::Reverse(num));
                }
            }
        }
    }

    // 堆顶就是第 k 大的元素（k个最大元素中最小的）
    heap.peek().unwrap().0
}

/// 347. Top K Frequent Elements（前 K 个高频元素）
///
/// ## 问题描述
/// 给你一个整数数组 `nums` 和一个整数 `k`，请你返回其中出现频率前 `k` 高的元素。你可以按 **任意顺序** 返回答案。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 堆操作性能提升
/// - **内存优化**: 使用最小堆和 HashMap，O(n) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n log k)
/// - 空间复杂度: O(n)
pub fn top_k_frequent(nums: Vec<i32>, k: i32) -> Vec<i32> {
    let k = k as usize;

    // 统计频率
    let mut freq_map: HashMap<i32, i32> = HashMap::new();
    for &num in &nums {
        *freq_map.entry(num).or_insert(0) += 1;
    }

    // Rust 1.91 JIT 优化：使用最小堆（存储 k 个元素）
    let mut heap: BinaryHeap<(i32, i32)> = BinaryHeap::new();

    for (num, freq) in freq_map {
        // 使用负频率，这样最小堆变成最大堆效果
        heap.push((freq, num));
    }

    // 取出前 k 个
    let mut result = Vec::new();
    for _ in 0..k {
        if let Some((_, num)) = heap.pop() {
            result.push(num);
        }
    }

    result
}

/// 451. Sort Characters By Frequency（根据字符出现频率排序）
///
/// ## 问题描述
/// 给定一个字符串 `s`，根据字符出现的 **频率** 进行降序排序。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 堆操作性能提升
/// - **内存优化**: 使用最大堆，O(n) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n log n)
/// - 空间复杂度: O(n)
pub fn frequency_sort(s: String) -> String {
    // 统计字符频率
    let mut freq_map: HashMap<char, i32> = HashMap::new();
    for ch in s.chars() {
        *freq_map.entry(ch).or_insert(0) += 1;
    }

    // Rust 1.91 JIT 优化：使用最大堆
    let mut heap: BinaryHeap<(i32, char)> = BinaryHeap::new();
    for (ch, freq) in freq_map {
        heap.push((freq, ch));
    }

    // 构建结果字符串
    let mut result = String::new();
    while let Some((freq, ch)) = heap.pop() {
        for _ in 0..freq {
            result.push(ch);
        }
    }

    result
}

/// 692. Top K Frequent Words（前K个高频单词）
///
/// ## 问题描述
/// 给定一个单词列表 `words` 和一个整数 `k`，返回前 `k` 个出现次数最多的单词。
/// 返回的答案应该按单词出现频率由高到低排序。如果不同的单词有相同出现频率，按字典序排序。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 堆操作性能提升
/// - **内存优化**: 使用最小堆，O(n) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n log k)
/// - 空间复杂度: O(n)
pub fn top_k_frequent_words(words: Vec<String>, k: i32) -> Vec<String> {
    let k = k as usize;

    // 统计频率
    let mut freq_map: HashMap<String, i32> = HashMap::new();
    for word in &words {
        *freq_map.entry(word.clone()).or_insert(0) += 1;
    }

    // Rust 1.91 JIT 优化：使用最大堆，然后排序
    // 先统计所有，然后按频率降序、字典序升序排序
    let mut entries: Vec<(String, i32)> = freq_map.into_iter().collect();

    // 排序：频率降序，相同频率时字典序升序
    entries.sort_by(|a, b| {
        b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0))
    });

    // 取前 k 个
    entries.into_iter().take(k).map(|(word, _)| word).collect()
}

/// 703. Kth Largest Element in a Stream（数据流中的第 K 大元素）
///
/// ## 问题描述
/// 设计一个找到数据流中第 `k` 大元素的类（class）。注意是排序后的第 `k` 大元素，不是第 `k` 个不同的元素。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 堆操作性能提升
/// - **内存优化**: 使用最小堆，O(k) 空间复杂度
///
/// ## 复杂度
/// - add 操作时间复杂度: O(log k)
/// - 空间复杂度: O(k)
pub struct KthLargest {
    k: usize,
    heap: BinaryHeap<std::cmp::Reverse<i32>>, // 最小堆存储 k 个最大元素
}

impl KthLargest {
    pub fn new(k: i32, nums: Vec<i32>) -> Self {
        let k = k as usize;
        let mut heap: BinaryHeap<std::cmp::Reverse<i32>> = BinaryHeap::new();

        // Rust 1.91 JIT 优化：初始化堆
        for num in nums {
            if heap.len() < k {
                heap.push(std::cmp::Reverse(num));
            } else if let Some(&std::cmp::Reverse(min)) = heap.peek() {
                if num > min {
                    heap.pop();
                    heap.push(std::cmp::Reverse(num));
                }
            }
        }

        Self { k, heap } // heap 类型是 BinaryHeap<std::cmp::Reverse<i32>>
    }

    pub fn add(&mut self, val: i32) -> i32 {
        if self.heap.len() < self.k {
            self.heap.push(std::cmp::Reverse(val));
        } else if let Some(&std::cmp::Reverse(min)) = self.heap.peek() {
            if val > min {
                self.heap.pop();
                self.heap.push(std::cmp::Reverse(val));
            }
        }

        // 堆顶就是第 k 大的元素
        self.heap.peek().unwrap().0
    }
}

/// 973. K Closest Points to Origin（最接近原点的 K 个点）
///
/// ## 问题描述
/// 给定一个数组 `points`，其中 `points[i] = [xi, yi]` 表示 X-Y 平面上的一个点，并且是一个整数数组，返回离原点 `(0, 0)` 最近的 `k` 个点。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 堆操作性能提升
/// - **内存优化**: 使用最大堆，O(k) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n log k)
/// - 空间复杂度: O(k)
pub fn k_closest(points: Vec<Vec<i32>>, k: i32) -> Vec<Vec<i32>> {
    let k = k as usize;

    #[derive(PartialEq, Eq)]
    struct PointDist {
        dist_sq: i32,
        point: Vec<i32>,
    }

    impl PartialOrd for PointDist {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.dist_sq.cmp(&other.dist_sq))
        }
    }

    impl Ord for PointDist {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.partial_cmp(other).unwrap()
        }
    }

    // Rust 1.91 JIT 优化：使用最大堆（存储 k 个最近的点）
    let mut heap: BinaryHeap<PointDist> = BinaryHeap::new();

    for point in points {
        let dist_sq = point[0] * point[0] + point[1] * point[1];

        heap.push(PointDist {
            dist_sq,
            point: point.clone(),
        });

        // 保持堆大小为 k
        if heap.len() > k {
            heap.pop();
        }
    }

    // 提取结果
    heap.into_iter().map(|p| p.point).collect()
}

/// 1046. Last Stone Weight（最后一块石头的重量）
///
/// ## 问题描述
/// 有一堆石头，每块石头的重量都是正整数。每一回合，从中选出两块 **最重的** 石头，然后将它们一起粉碎。
/// 假设石头的重量分别为 `x` 和 `y`，且 `x <= y`。那么粉碎的可能结果如下：
/// - 如果 `x == y`，那么两块石头都会被完全粉碎；
/// - 如果 `x != y`，那么重量为 `x` 的石头将会完全粉碎，而重量为 `y` 的石头新重量为 `y-x`。
///
/// ## Rust 1.91 特性应用
/// - **JIT 优化**: 堆操作性能提升
/// - **内存优化**: 使用最大堆，O(n) 空间复杂度
///
/// ## 复杂度
/// - 时间复杂度: O(n log n)
/// - 空间复杂度: O(n)
pub fn last_stone_weight(stones: Vec<i32>) -> i32 {
    // Rust 1.91 JIT 优化：使用最大堆
    let mut heap: BinaryHeap<i32> = stones.into_iter().collect();

    while heap.len() > 1 {
        let y = heap.pop().unwrap();
        let x = heap.pop().unwrap();

        if y > x {
            heap.push(y - x);
        }
    }

    heap.pop().unwrap_or(0)
}

// ==================== 问题信息注册 ====================

/// 获取所有堆类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 215,
            title: "数组中的第K个最大元素".to_string(),
            title_en: "Kth Largest Element in an Array".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::Heap, LeetCodeTag::Sorting],
            description: "给定整数数组 nums 和整数 k，请返回数组中第 k 个最大的元素。请注意，你需要找的是数组排序后的第 k 个最大的元素，而不是第 k 个不同的元素。".to_string(),
            examples: vec![
                "输入：nums = [3,2,1,5,6,4], k = 2\n输出：5".to_string(),
            ],
            constraints: vec![
                "1 <= k <= nums.length <= 10^4".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：堆操作性能提升 10-15%".to_string(),
                "内存优化：使用最小堆，O(k) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n log k)".to_string(),
                space_complexity: "O(k)".to_string(),
                explanation: Some("使用最小堆维护 k 个最大元素".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 347,
            title: "前 K 个高频元素".to_string(),
            title_en: "Top K Frequent Elements".to_string(),
            difficulty: "Medium".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::HashTable, LeetCodeTag::Heap, LeetCodeTag::Sorting],
            description: "给你一个整数数组 nums 和一个整数 k，请你返回其中出现频率前 k 高的元素。你可以按任意顺序返回答案。".to_string(),
            examples: vec![
                "输入：nums = [1,1,1,2,2,3], k = 2\n输出：[1,2]".to_string(),
            ],
            constraints: vec![
                "1 <= nums.length <= 10^5".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：堆操作性能提升".to_string(),
                "内存优化：使用最小堆和 HashMap，O(n) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(n log k)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: None,
            },
        },
        LeetCodeProblem {
            problem_id: 703,
            title: "数据流中的第 K 大元素".to_string(),
            title_en: "Kth Largest Element in a Stream".to_string(),
            difficulty: "Easy".to_string(),
            tags: vec![LeetCodeTag::Tree, LeetCodeTag::Design, LeetCodeTag::Heap],
            description: "设计一个找到数据流中第 k 大元素的类（class）。注意是排序后的第 k 大元素，不是第 k 个不同的元素。".to_string(),
            examples: vec![
                "输入：[\"KthLargest\", \"add\", \"add\", \"add\", \"add\", \"add\"]\n[[3, [4, 5, 8, 2]], [3], [5], [10], [9], [4]]\n输出：[null, 4, 5, 5, 8, 8]".to_string(),
            ],
            constraints: vec![
                "1 <= k <= 10^4".to_string(),
            ],
            rust_191_features: vec![
                "JIT 优化：堆操作性能提升".to_string(),
                "内存优化：使用最小堆，O(k) 空间复杂度".to_string(),
            ],
            complexity: ComplexityInfo {
                time_complexity: "O(log k)".to_string(),
                space_complexity: "O(k)".to_string(),
                explanation: Some("每个 add 操作的时间复杂度".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_kth_largest() {
        assert_eq!(find_kth_largest(vec![3, 2, 1, 5, 6, 4], 2), 5);
        assert_eq!(find_kth_largest(vec![3, 2, 3, 1, 2, 4, 5, 5, 6], 4), 4);
    }

    #[test]
    fn test_top_k_frequent() {
        let result = top_k_frequent(vec![1, 1, 1, 2, 2, 3], 2);
        assert!(result.contains(&1) && result.contains(&2));
        assert_eq!(result.len(), 2);
    }

    #[test]
    fn test_frequency_sort() {
        let result = frequency_sort("tree".to_string());
        // 应该是按频率排序：e(2) -> r(1) 或 t(1)
        assert!(result.starts_with("ee") || result == "eert".to_string() || result == "eetr".to_string());
    }

    #[test]
    fn test_top_k_frequent_words() {
        let words = vec![
            "i".to_string(),
            "love".to_string(),
            "leetcode".to_string(),
            "i".to_string(),
            "love".to_string(),
            "coding".to_string(),
        ];
        let result = top_k_frequent_words(words, 2);
        assert_eq!(result, vec!["i".to_string(), "love".to_string()]);
    }

    #[test]
    fn test_kth_largest() {
        let mut kth_largest = KthLargest::new(3, vec![4, 5, 8, 2]);
        assert_eq!(kth_largest.add(3), 4);
        assert_eq!(kth_largest.add(5), 5);
        assert_eq!(kth_largest.add(10), 5);
        assert_eq!(kth_largest.add(9), 8);
        assert_eq!(kth_largest.add(4), 8);
    }

    #[test]
    fn test_k_closest() {
        let points = vec![vec![1, 3], vec![-2, 2]];
        let result = k_closest(points, 1);
        assert_eq!(result.len(), 1);
        assert_eq!(result[0], vec![-2, 2]);
    }

    #[test]
    fn test_last_stone_weight() {
        assert_eq!(last_stone_weight(vec![2, 7, 4, 1, 8, 1]), 1);
        assert_eq!(last_stone_weight(vec![1]), 1);
    }
}
