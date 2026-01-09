//! # 算法正确性验证模块
//!
//! 本模块提供算法正确性验证的工具和方法。

use serde::{Serialize, Deserialize};

/// 正确性验证结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorrectnessVerificationResult {
    pub algorithm_name: String,
    pub verification_passed: bool,
    pub test_cases: Vec<TestCase>,
    pub invariants_verified: Vec<String>,
    pub edge_cases_handled: bool,
    pub verification_time: std::time::Duration,
}

/// 测试用例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestCase {
    pub name: String,
    pub input: serde_json::Value,
    pub expected_output: serde_json::Value,
    pub actual_output: Option<serde_json::Value>,
    pub status: TestStatus,
    pub execution_time: std::time::Duration,
}

/// 测试状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TestStatus {
    Passed,
    Failed,
    Skipped,
    Error,
}

/// 正确性验证器
pub struct CorrectnessVerifier;

impl CorrectnessVerifier {
    /// 验证排序算法的正确性
    pub fn verify_sorting_correctness<T: Clone + Ord>(
        sort_fn: impl Fn(&mut [T]),
        test_cases: &[Vec<T>],
    ) -> bool {
        for test_case in test_cases {
            let mut data = test_case.clone();
            sort_fn(&mut data);

            // 检查是否已排序
            if !Self::is_sorted(&data) {
                return false;
            }

            // 检查元素是否保持不变
            if !Self::has_same_elements(test_case, &data) {
                return false;
            }
        }
        true
    }

    /// 验证搜索算法的正确性
    pub fn verify_search_correctness<T: Clone + Ord>(
        search_fn: impl Fn(&[T], &T) -> Option<usize>,
        test_cases: &[(Vec<T>, T, Option<usize>)],
    ) -> bool {
        for (arr, target, expected) in test_cases {
            let result = search_fn(arr, target);
            if result != *expected {
                return false;
            }
        }
        true
    }

    /// 检查数组是否已排序
    fn is_sorted<T: Ord>(arr: &[T]) -> bool {
        arr.windows(2).all(|w| w[0] <= w[1])
    }

    /// 检查两个数组是否包含相同的元素
    fn has_same_elements<T: Clone + Ord>(arr1: &[T], arr2: &[T]) -> bool {
        if arr1.len() != arr2.len() {
            return false;
        }

        let mut sorted1 = arr1.to_vec();
        let mut sorted2 = arr2.to_vec();
        sorted1.sort();
        sorted2.sort();

        sorted1 == sorted2
    }
}
