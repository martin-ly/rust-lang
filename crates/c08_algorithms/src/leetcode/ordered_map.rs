//! LeetCode 有序映射类算法（结合 Rust 1.92 特性）
//!
//! 本模块实现经典的有序映射类 LeetCode 题目，充分利用 Rust 1.92 的新特性。
//!
//! ## Rust 1.92 特性应用
//!
//! 1. **性能优化**: 使用 BTreeMap 等有序映射数据结构
//! 2. **内存优化**: 高效的有序映射实现

use crate::leetcode::{ComplexityInfo, LeetCodeProblem, LeetCodeTag};
use std::collections::BTreeMap;

// ==================== 数据结构定义 ====================

/// 352. Data Stream as Disjoint Intervals（将数据流变为多个不相交区间）
pub struct SummaryRanges {
    intervals: BTreeMap<i32, i32>, // start -> end
}

impl SummaryRanges {
    pub fn new() -> Self {
        SummaryRanges {
            intervals: BTreeMap::new(),
        }
    }

    pub fn add_num(&mut self, val: i32) {
        let mut start = val;
        let mut end = val;
        
        // 查找可能合并的区间
        if let Some((&s, &e)) = self.intervals.range(..=val).next_back() {
            if e >= val {
                return; // 已经在某个区间内
            }
            if e == val - 1 {
                start = s;
                self.intervals.remove(&s);
            }
        }
        
        if let Some((&s, &e)) = self.intervals.range(val + 1..).next() {
            if s == val + 1 {
                end = e;
                self.intervals.remove(&s);
            }
        }
        
        self.intervals.insert(start, end);
    }

    pub fn get_intervals(&self) -> Vec<Vec<i32>> {
        self.intervals
            .iter()
            .map(|(&s, &e)| vec![s, e])
            .collect()
    }
}

impl Default for SummaryRanges {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 经典题目实现 ====================

/// 220. Contains Duplicate III（存在重复元素 III）
pub fn contains_nearby_almost_duplicate(nums: Vec<i32>, k: i32, t: i32) -> bool {
    use std::collections::BTreeSet;
    
    let k = k as usize;
    let t = t as i64;
    let mut set = BTreeSet::new();
    
    for i in 0..nums.len() {
        if i > k {
            set.remove(&(nums[i - k - 1] as i64));
        }
        
        let num = nums[i] as i64;
        if let Some(&lower) = set.range(..=num).next_back() {
            if num - lower <= t {
                return true;
            }
        }
        if let Some(&upper) = set.range(num..).next() {
            if upper - num <= t {
                return true;
            }
        }
        
        set.insert(num);
    }
    
    false
}

/// 699. Falling Squares（掉落的方块）- 有序映射版本
pub fn falling_squares_ordered_map(positions: Vec<Vec<i32>>) -> Vec<i32> {
    let mut heights = BTreeMap::new();
    let mut result = Vec::new();
    let mut max_height = 0;
    
    for pos in positions {
        let left = pos[0];
        let side = pos[1];
        let right = left + side;
        
        let mut max_h = 0;
        for (_, &height) in heights.range(left..right) {
            max_h = max_h.max(height);
        }
        
        let new_height = max_h + side;
        heights.insert(left, new_height);
        heights.insert(right, max_h);
        
        // 移除中间的点
        let keys_to_remove: Vec<i32> = heights
            .range((left + 1)..right)
            .map(|(&k, _)| k)
            .collect();
        for key in keys_to_remove {
            heights.remove(&key);
        }
        
        max_height = max_height.max(new_height);
        result.push(max_height);
    }
    
    result
}

// ==================== 问题信息注册 ====================

/// 获取所有有序映射类问题
pub fn get_all_problems() -> Vec<LeetCodeProblem> {
    vec![
        LeetCodeProblem {
            problem_id: 220,
            title: "存在重复元素 III".to_string(),
            title_en: "Contains Duplicate III".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::SlidingWindow, LeetCodeTag::OrderedMap],
            description: "给你一个整数数组 nums 和两个整数 k 和 t 。请你判断是否存在 两个不同下标 i 和 j，使得 abs(nums[i] - nums[j]) <= t ，同时又满足 abs(i - j) <= k 。如果存在则返回 true，不存在返回 false。".to_string(),
            examples: vec!["输入：nums = [1,2,3,1], k = 3, t = 0\n输出：true".to_string()],
            constraints: vec!["0 <= nums.length <= 2 * 10^4".to_string()],
            rust_191_features: vec!["使用有序映射，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(k)".to_string(),
                explanation: Some("使用 BTreeMap 维护滑动窗口".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 352,
            title: "将数据流变为多个不相交区间".to_string(),
            title_en: "Data Stream as Disjoint Intervals".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::BinarySearch, LeetCodeTag::Design, LeetCodeTag::OrderedMap],
            description: "给你一个由非负整数 a1, a2, ..., an 组成的数据流输入，请你将到目前为止看到的数字总结为不相交的区间列表。实现 SummaryRanges 类：SummaryRanges() 使用一个空数据流初始化对象。void addNum(int val) 向数据流中加入整数 val 。int[][] getIntervals() 以不相交区间 [starti, endi] 的列表形式返回对数据流中整数的总结。".to_string(),
            examples: vec!["输入：[\"SummaryRanges\", \"addNum\", \"getIntervals\", \"addNum\", \"getIntervals\", \"addNum\", \"getIntervals\", \"addNum\", \"getIntervals\", \"addNum\", \"getIntervals\"]\n[[], [1], [], [3], [], [7], [], [2], [], [6], []]\n输出：[null, null, [[1, 1]], null, [[1, 1], [3, 3]], null, [[1, 1], [3, 3], [7, 7]], null, [[1, 3], [7, 7]], null, [[1, 3], [6, 7]]]".to_string()],
            constraints: vec!["0 <= val <= 10^4".to_string()],
            rust_191_features: vec!["使用有序映射维护区间，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("n 是添加的数字数量".to_string()),
            },
        },
        LeetCodeProblem {
            problem_id: 699,
            title: "掉落的方块".to_string(),
            title_en: "Falling Squares".to_string(),
            difficulty: "Hard".to_string(),
            tags: vec![LeetCodeTag::Array, LeetCodeTag::SegmentTree, LeetCodeTag::OrderedMap],
            description: "在二维平面上的 x 轴上，放置着一些方块。给你一个二维整数数组 positions ，其中 positions[i] = [lefti, sideLengthi] 表示：第 i 个方块边长为 sideLengthi ，其左侧边与 x 轴上坐标点 lefti 对齐。每个方块都从一个比目前所有的落地方块更高的高度掉落而下。方块沿 y 轴负方向下落，直到着陆到 另一个方块的顶面 或者是 x 轴上 。一个方块「擦过」另一个方块的左侧边或右侧边不算着陆。一旦着陆，它就会固定在原地，无法移动。在每个方块掉落后，你必须记录目前所有已经落稳的 方块堆叠的最高高度 。返回一个整数数组 ans ，其中 ans[i] 表示在第 i 块方块掉落后堆叠的最高高度。".to_string(),
            examples: vec!["输入：positions = [[1,2],[2,3],[6,1]]\n输出：[2,5,5]".to_string()],
            constraints: vec!["1 <= positions.length <= 1000".to_string()],
            rust_191_features: vec!["使用有序映射或线段树，Rust 1.92 性能优化".to_string()],
            complexity: ComplexityInfo {
                time_complexity: "O(n log n)".to_string(),
                space_complexity: "O(n)".to_string(),
                explanation: Some("n 是方块数量".to_string()),
            },
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_summary_ranges() {
        let mut sr = SummaryRanges::new();
        sr.add_num(1);
        sr.add_num(3);
        sr.add_num(7);
        sr.add_num(2);
        sr.add_num(6);
        let intervals = sr.get_intervals();
        assert_eq!(intervals, vec![vec![1, 3], vec![6, 7]]);
    }

    #[test]
    fn test_contains_nearby_almost_duplicate() {
        assert!(contains_nearby_almost_duplicate(vec![1, 2, 3, 1], 3, 0));
    }
}
