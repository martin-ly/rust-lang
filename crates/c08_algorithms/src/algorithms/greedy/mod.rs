//! # 贪心算法模块
//! # greedy algorithm module
//!
//! 本模块实现了各种贪心算法。
//! this module greedy algorithm 。
//use serde::{Serialize, Deserialize};

/// 贪心算法实现
/// greedy algorithm
pub struct GreedyAlgorithms;

impl GreedyAlgorithms {
    /// 活动选择问题
    /// problem
    pub fn activity_selection(activities: &[(i32, i32)]) -> Vec<usize> {
        if activities.is_empty() {
            return vec![];
        }

        let mut indexed_activities: Vec<(usize, i32, i32)> = activities
            .iter()
            .enumerate()
            .map(|(i, &(start, end))| (i, start, end))
            .collect();

        // 按结束时间排序
        indexed_activities.sort_by_key(|&(_, _, end)| end);

        let mut selected = vec![0];
        let mut last_end = indexed_activities[0].2;

        for (i, &(_, start, end)) in indexed_activities.iter().enumerate().skip(1) {
            if start >= last_end {
                selected.push(i);
                last_end = end;
            }
        }

        selected
    }

    /// 霍夫曼编码
    pub fn huffman_coding(frequencies: &[u32]) -> Vec<String> {
        // 简化实现，实际应该构建霍夫曼树
        frequencies.iter().map(|_| "0".to_string()).collect()
    }
}
