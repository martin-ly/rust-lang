//! # 工作流工具模块 / Workflow Tools Module
//!
//! 本模块提供了工作流系统的各种工具函数和实用程序。
//! This module provides various utility functions and tools for the workflow system.

use crate::error::*;
use crate::types::*;
use std::collections::HashMap;
use std::time::Duration;

/// 工作流验证工具 / Workflow Validation Tools
pub struct WorkflowValidator;

impl WorkflowValidator {
    /// 验证工作流定义 / Validate workflow definition
    pub fn validate_workflow(definition: &WorkflowDefinition) -> Result<(), WorkflowError> {
        // 基本验证逻辑
        if definition.states.is_empty() {
            return Err(WorkflowError::ValidationError(
                "工作流必须包含至少一个状态".to_string(),
            ));
        }

        if definition.initial_state.is_empty() {
            return Err(WorkflowError::ValidationError(
                "工作流必须指定初始状态".to_string(),
            ));
        }

        // 验证初始状态存在
        if !definition.states.contains(&definition.initial_state) {
            return Err(WorkflowError::ValidationError("初始状态不存在".to_string()));
        }

        Ok(())
    }
}

/// 工作流分析工具 / Workflow Analysis Tools
pub struct WorkflowAnalyzer;

impl WorkflowAnalyzer {
    /// 分析工作流复杂度 / Analyze workflow complexity
    pub fn analyze_complexity(definition: &WorkflowDefinition) -> WorkflowComplexity {
        let state_count = definition.states.len();
        let transition_count = definition.transitions.len();

        let complexity = match (state_count, transition_count) {
            (s, t) if s <= 5 && t <= 10 => ComplexityLevel::Low,
            (s, t) if s <= 15 && t <= 30 => ComplexityLevel::Medium,
            (s, t) if s <= 30 && t <= 60 => ComplexityLevel::High,
            _ => ComplexityLevel::VeryHigh,
        };

        WorkflowComplexity {
            state_count,
            transition_count,
            complexity_level: complexity,
        }
    }
}

/// 工作流复杂度级别 / Workflow Complexity Level
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComplexityLevel {
    Low,
    Medium,
    High,
    VeryHigh,
}

/// 工作流复杂度分析结果 / Workflow Complexity Analysis Result
#[derive(Debug, Clone)]
pub struct WorkflowComplexity {
    pub state_count: usize,
    pub transition_count: usize,
    pub complexity_level: ComplexityLevel,
}

/// 工作流性能分析工具 / Workflow Performance Analysis Tools
pub struct PerformanceAnalyzer;

impl PerformanceAnalyzer {
    /// 分析工作流性能瓶颈 / Analyze workflow performance bottlenecks
    pub fn analyze_bottlenecks(instances: &[WorkflowInstance]) -> Vec<PerformanceBottleneck> {
        let mut bottlenecks = Vec::new();

        // 分析状态停留时间
        let mut state_durations: HashMap<String, Vec<Duration>> = HashMap::new();

        for instance in instances {
            for (i, record) in instance.history.iter().enumerate() {
                if i > 0 {
                    // 计算与前一个记录的时间差作为停留时间
                    let prev_record = &instance.history[i - 1];
                    let duration = record.timestamp.duration_since(prev_record.timestamp);
                    state_durations
                        .entry(prev_record.from_state.clone())
                        .or_insert_with(Vec::new)
                        .push(duration);
                }
            }
        }

        // 识别瓶颈状态
        for (state_name, durations) in state_durations {
            if !durations.is_empty() {
                let total_duration = durations.iter().sum::<Duration>();
                let avg_duration = total_duration / durations.len() as u32;
                let max_duration = durations.iter().max().unwrap_or(&Duration::ZERO);

                if avg_duration > Duration::from_secs(60) {
                    bottlenecks.push(PerformanceBottleneck {
                        state_name,
                        avg_duration,
                        max_duration: *max_duration,
                        occurrence_count: durations.len(),
                    });
                }
            }
        }

        bottlenecks.sort_by(|a, b| b.avg_duration.cmp(&a.avg_duration));
        bottlenecks
    }
}

/// 性能瓶颈信息 / Performance Bottleneck Information
#[derive(Debug, Clone)]
pub struct PerformanceBottleneck {
    pub state_name: String,
    pub avg_duration: Duration,
    pub max_duration: Duration,
    pub occurrence_count: usize,
}

/// 工作流优化建议工具 / Workflow Optimization Suggestion Tools
pub struct OptimizationAdvisor;

impl OptimizationAdvisor {
    /// 生成优化建议 / Generate optimization suggestions
    pub fn generate_suggestions(
        definition: &WorkflowDefinition,
        bottlenecks: &[PerformanceBottleneck],
    ) -> Vec<OptimizationSuggestion> {
        let mut suggestions = Vec::new();

        // 基于瓶颈生成建议
        for bottleneck in bottlenecks {
            suggestions.push(OptimizationSuggestion {
                target: bottleneck.state_name.clone(),
                suggestion_type: OptimizationType::ReduceProcessingTime,
                description: format!(
                    "状态 '{}' 平均处理时间为 {:?}，建议优化处理逻辑",
                    bottleneck.state_name, bottleneck.avg_duration
                ),
                priority: SuggestionPriority::High,
            });
        }

        // 基于工作流结构生成建议
        if definition.states.len() > 20 {
            suggestions.push(OptimizationSuggestion {
                target: "workflow_structure".to_string(),
                suggestion_type: OptimizationType::SimplifyStructure,
                description: "工作流状态过多，建议拆分为多个子工作流".to_string(),
                priority: SuggestionPriority::Medium,
            });
        }

        suggestions
    }
}

/// 优化建议类型 / Optimization Suggestion Type
#[derive(Debug, Clone)]
pub enum OptimizationType {
    ReduceProcessingTime,
    SimplifyStructure,
    AddParallelization,
    ImproveErrorHandling,
    OptimizeDataFlow,
}

/// 建议优先级 / Suggestion Priority
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum SuggestionPriority {
    Low,
    Medium,
    High,
    Critical,
}

/// 优化建议 / Optimization Suggestion
#[derive(Debug, Clone)]
pub struct OptimizationSuggestion {
    pub target: String,
    pub suggestion_type: OptimizationType,
    pub description: String,
    pub priority: SuggestionPriority,
}
