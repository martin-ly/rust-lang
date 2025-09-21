//! # 算法应用模块
//! 
//! 本模块提供算法的应用场景和实际案例。

use serde::{Serialize, Deserialize};

/// 应用知识
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ApplicationKnowledge {
    pub domain: String,
    pub description: String,
    pub algorithms_used: Vec<String>,
    pub performance_requirements: Vec<String>,
    pub implementation_considerations: Vec<String>,
    pub real_world_examples: Vec<String>,
}

/// 应用分析器
pub struct ApplicationAnalyzer;

impl ApplicationAnalyzer {
    /// 分析排序算法的应用场景
    pub fn analyze_sorting_applications(algorithm_name: &str) -> Vec<ApplicationKnowledge> {
        match algorithm_name {
            "QuickSort" => vec![
                ApplicationKnowledge {
                    domain: "数据库系统".to_string(),
                    description: "数据库查询优化中的排序操作".to_string(),
                    algorithms_used: vec!["快速排序".to_string()],
                    performance_requirements: vec!["高吞吐量".to_string(), "低延迟".to_string()],
                    implementation_considerations: vec!["内存管理".to_string(), "并发控制".to_string()],
                    real_world_examples: vec!["MySQL".to_string(), "PostgreSQL".to_string()],
                },
                ApplicationKnowledge {
                    domain: "操作系统".to_string(),
                    description: "操作系统调度算法中的排序".to_string(),
                    algorithms_used: vec!["快速排序".to_string()],
                    performance_requirements: vec!["实时性".to_string(), "公平性".to_string()],
                    implementation_considerations: vec!["中断处理".to_string(), "上下文切换".to_string()],
                    real_world_examples: vec!["Linux内核".to_string(), "Windows内核".to_string()],
                },
            ],
            "MergeSort" => vec![
                ApplicationKnowledge {
                    domain: "外部排序".to_string(),
                    description: "处理超出内存限制的大文件排序".to_string(),
                    algorithms_used: vec!["归并排序".to_string()],
                    performance_requirements: vec!["内存效率".to_string(), "I/O优化".to_string()],
                    implementation_considerations: vec!["磁盘I/O".to_string(), "内存管理".to_string()],
                    real_world_examples: vec!["大数据处理".to_string(), "日志分析".to_string()],
                },
            ],
            _ => vec![],
        }
    }
}
