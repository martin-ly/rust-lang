//! # 搜索算法模块
//!
//! 本模块实现了各种搜索算法。

use serde::{Serialize, Deserialize};

/// 搜索算法类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SearchingAlgorithm {
    LinearSearch,
    BinarySearch,
    InterpolationSearch,
    HashSearch,
}

/// 搜索结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub found: bool,
    pub index: Option<usize>,
    pub comparisons: usize,
    pub execution_time: std::time::Duration,
}

/// 搜索算法实现
pub struct SearchingAlgorithms;

impl SearchingAlgorithms {
    /// 线性搜索
    pub fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> SearchResult {
        let start = std::time::Instant::now();
        let mut comparisons = 0;

        for (i, item) in arr.iter().enumerate() {
            comparisons += 1;
            if item == target {
                return SearchResult {
                    found: true,
                    index: Some(i),
                    comparisons,
                    execution_time: start.elapsed(),
                };
            }
        }

        SearchResult {
            found: false,
            index: None,
            comparisons,
            execution_time: start.elapsed(),
        }
    }

    /// 二分搜索
    pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> SearchResult {
        let start = std::time::Instant::now();
        let mut comparisons = 0;
        let mut left = 0;
        let mut right = arr.len();

        while left < right {
            let mid = left + (right - left) / 2;
            comparisons += 1;

            match arr[mid].cmp(target) {
                std::cmp::Ordering::Equal => {
                    return SearchResult {
                        found: true,
                        index: Some(mid),
                        comparisons,
                        execution_time: start.elapsed(),
                    };
                }
                std::cmp::Ordering::Less => left = mid + 1,
                std::cmp::Ordering::Greater => right = mid,
            }
        }

        SearchResult {
            found: false,
            index: None,
            comparisons,
            execution_time: start.elapsed(),
        }
    }
}
