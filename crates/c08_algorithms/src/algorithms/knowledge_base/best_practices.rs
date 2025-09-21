//! # 算法最佳实践模块
//! 
//! 本模块提供算法实现和使用的最佳实践。

use serde::{Serialize, Deserialize};

/// 最佳实践
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BestPractices {
    pub algorithm_name: String,
    pub implementation_tips: Vec<String>,
    pub performance_optimizations: Vec<String>,
    pub common_pitfalls: Vec<String>,
    pub testing_strategies: Vec<String>,
    pub usage_guidelines: Vec<String>,
}

/// 最佳实践分析器
pub struct BestPracticesAnalyzer;

impl BestPracticesAnalyzer {
    /// 分析排序算法的最佳实践
    pub fn analyze_sorting_best_practices(algorithm_name: &str) -> BestPractices {
        match algorithm_name {
            "QuickSort" => BestPractices {
                algorithm_name: algorithm_name.to_string(),
                implementation_tips: vec![
                    "使用三数取中法选择基准".to_string(),
                    "小数组使用插入排序".to_string(),
                    "避免重复元素的最坏情况".to_string(),
                ],
                performance_optimizations: vec![
                    "尾递归优化".to_string(),
                    "三路快排处理重复元素".to_string(),
                    "缓存友好的内存访问模式".to_string(),
                ],
                common_pitfalls: vec![
                    "基准选择不当导致最坏情况".to_string(),
                    "递归深度过深导致栈溢出".to_string(),
                    "分区操作实现错误".to_string(),
                ],
                testing_strategies: vec![
                    "随机数据测试".to_string(),
                    "已排序数据测试".to_string(),
                    "逆序数据测试".to_string(),
                    "重复元素测试".to_string(),
                ],
                usage_guidelines: vec![
                    "适合通用排序场景".to_string(),
                    "不适合稳定性要求高的场景".to_string(),
                    "注意最坏情况的时间复杂度".to_string(),
                ],
            },
            "MergeSort" => BestPractices {
                algorithm_name: algorithm_name.to_string(),
                implementation_tips: vec![
                    "原地合并优化".to_string(),
                    "小数组使用插入排序".to_string(),
                    "避免重复分配内存".to_string(),
                ],
                performance_optimizations: vec![
                    "内存池管理".to_string(),
                    "缓存友好的合并操作".to_string(),
                ],
                common_pitfalls: vec![
                    "合并操作实现错误".to_string(),
                    "内存使用过多".to_string(),
                ],
                testing_strategies: vec![
                    "稳定性测试".to_string(),
                    "边界情况测试".to_string(),
                ],
                usage_guidelines: vec![
                    "适合稳定排序需求".to_string(),
                    "适合外部排序".to_string(),
                    "注意空间复杂度".to_string(),
                ],
            },
            _ => BestPractices {
                algorithm_name: algorithm_name.to_string(),
                implementation_tips: vec![],
                performance_optimizations: vec![],
                common_pitfalls: vec![],
                testing_strategies: vec![],
                usage_guidelines: vec![],
            },
        }
    }
}
