//! # 复杂度分析模块
//! 
//! 本模块提供算法复杂度分析的工具和方法。

use serde::{Serialize, Deserialize};

/// 复杂度分析结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityAnalysisResult {
    pub algorithm_name: String,
    pub time_complexity: ComplexityBounds,
    pub space_complexity: ComplexityBounds,
    pub best_case: String,
    pub average_case: String,
    pub worst_case: String,
    pub amortized_analysis: Option<String>,
    pub practical_performance: String,
}

/// 复杂度边界
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComplexityBounds {
    pub lower_bound: String,
    pub upper_bound: String,
    pub tight_bound: Option<String>,
    pub proof: Option<String>,
}

/// 复杂度分析器
pub struct ComplexityAnalyzer;

impl ComplexityAnalyzer {
    /// 分析排序算法复杂度
    pub fn analyze_sorting_complexity(algorithm_name: &str) -> ComplexityAnalysisResult {
        match algorithm_name {
            "QuickSort" => ComplexityAnalysisResult {
                algorithm_name: algorithm_name.to_string(),
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(n log n)".to_string(),
                    upper_bound: "O(n²)".to_string(),
                    tight_bound: Some("Θ(n log n) 平均情况".to_string()),
                    proof: Some("分治分析".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(log n)".to_string(),
                    upper_bound: "O(log n)".to_string(),
                    tight_bound: Some("Θ(log n)".to_string()),
                    proof: Some("递归深度分析".to_string()),
                },
                best_case: "O(n log n)".to_string(),
                average_case: "O(n log n)".to_string(),
                worst_case: "O(n²)".to_string(),
                amortized_analysis: Some("平均情况下 O(n log n)".to_string()),
                practical_performance: "实际应用中表现优异，常数因子小".to_string(),
            },
            "MergeSort" => ComplexityAnalysisResult {
                algorithm_name: algorithm_name.to_string(),
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(n log n)".to_string(),
                    upper_bound: "O(n log n)".to_string(),
                    tight_bound: Some("Θ(n log n)".to_string()),
                    proof: Some("分治分析".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(n)".to_string(),
                    upper_bound: "O(n)".to_string(),
                    tight_bound: Some("Θ(n)".to_string()),
                    proof: Some("合并操作需要额外空间".to_string()),
                },
                best_case: "O(n log n)".to_string(),
                average_case: "O(n log n)".to_string(),
                worst_case: "O(n log n)".to_string(),
                amortized_analysis: None,
                practical_performance: "性能稳定，但空间开销较大".to_string(),
            },
            _ => ComplexityAnalysisResult {
                algorithm_name: algorithm_name.to_string(),
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(n)".to_string(),
                    upper_bound: "O(n²)".to_string(),
                    tight_bound: None,
                    proof: None,
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(1)".to_string(),
                    upper_bound: "O(n)".to_string(),
                    tight_bound: None,
                    proof: None,
                },
                best_case: "O(n)".to_string(),
                average_case: "O(n²)".to_string(),
                worst_case: "O(n²)".to_string(),
                amortized_analysis: None,
                practical_performance: "需要具体分析".to_string(),
            },
        }
    }

    /// 分析搜索算法复杂度
    pub fn analyze_search_complexity(algorithm_name: &str) -> ComplexityAnalysisResult {
        match algorithm_name {
            "BinarySearch" => ComplexityAnalysisResult {
                algorithm_name: algorithm_name.to_string(),
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(log n)".to_string(),
                    upper_bound: "O(log n)".to_string(),
                    tight_bound: Some("Θ(log n)".to_string()),
                    proof: Some("搜索空间每次减半".to_string()),
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(1)".to_string(),
                    upper_bound: "O(1)".to_string(),
                    tight_bound: Some("Θ(1)".to_string()),
                    proof: Some("只使用常数空间".to_string()),
                },
                best_case: "O(1) - 目标在中间".to_string(),
                average_case: "O(log n)".to_string(),
                worst_case: "O(log n)".to_string(),
                amortized_analysis: None,
                practical_performance: "非常高效，常数因子小".to_string(),
            },
            _ => ComplexityAnalysisResult {
                algorithm_name: algorithm_name.to_string(),
                time_complexity: ComplexityBounds {
                    lower_bound: "Ω(1)".to_string(),
                    upper_bound: "O(n)".to_string(),
                    tight_bound: None,
                    proof: None,
                },
                space_complexity: ComplexityBounds {
                    lower_bound: "Ω(1)".to_string(),
                    upper_bound: "O(n)".to_string(),
                    tight_bound: None,
                    proof: None,
                },
                best_case: "O(1)".to_string(),
                average_case: "O(n)".to_string(),
                worst_case: "O(n)".to_string(),
                amortized_analysis: None,
                practical_performance: "需要具体分析".to_string(),
            },
        }
    }
}
