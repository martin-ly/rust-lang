//! # 执行流感知系统（Execution Flow Awareness）
//!
//! 提供调用链追踪、执行图分析、依赖检测和性能瓶颈识别功能。
//!
//! ## 核心功能
//!
//! - **调用链追踪**：记录完整的方法调用链
//! - **执行图分析**：构建和分析执行依赖图
//! - **依赖检测**：识别服务间依赖关系
//! - **性能瓶颈识别**：自动发现慢查询和热点
//! - **异常传播追踪**：跟踪错误传播路径
//!
//! ## 架构设计
//!
//! ```text
//!                 ┌───────────────────┐
//!                 │  Execution Flow   │
//!                 │    Tracker        │
//!                 └─────────┬─────────┘
//!                           │
//!       ┌───────────────────┼───────────────────┐
//!       │                   │                   │
//!  ┌────▼────┐        ┌────▼────┐        ┌────▼────┐
//!  │  Call   │        │Execution│        │Dependency│
//!  │  Chain  │        │  Graph  │        │ Detector │
//!  └────┬────┘        └────┬────┘        └────┬────┘
//!       │                  │                   │
//!       └──────────────────┼───────────────────┘
//!                          │
//!                  ┌───────▼────────┐
//!                  │  Performance   │
//!                  │   Analyzer     │
//!                  └────────────────┘
//! ```

pub mod call_chain;
pub mod execution_graph;
pub mod dependency_detector;
pub mod performance_analyzer;
pub mod bottleneck_identifier;

// Re-export commonly used types
pub use call_chain::{
    CallChainTracker, CallEntry, CallChain, CallChainStats,
};

pub use execution_graph::{
    ExecutionGraph, ExecutionNode, ExecutionEdge, GraphAnalyzer,
};

pub use dependency_detector::{
    DependencyDetector, ServiceDependency, DependencyGraph, DependencyType,
};

pub use performance_analyzer::{
    PerformanceAnalyzer, PerformanceMetrics, PerformanceReport,
};

pub use bottleneck_identifier::{
    BottleneckIdentifier, Bottleneck, BottleneckType, BottleneckSeverity,
};

/// 执行流配置
#[derive(Debug, Clone)]
pub struct ExecutionFlowConfig {
    /// 是否启用调用链追踪
    pub enable_call_chain: bool,
    /// 是否启用执行图分析
    pub enable_execution_graph: bool,
    /// 是否启用依赖检测
    pub enable_dependency_detection: bool,
    /// 是否启用性能分析
    pub enable_performance_analysis: bool,
    /// 采样率（0.0-1.0）
    pub sampling_rate: f64,
    /// 最大调用链深度
    pub max_call_depth: usize,
}

impl Default for ExecutionFlowConfig {
    fn default() -> Self {
        Self {
            enable_call_chain: true,
            enable_execution_graph: true,
            enable_dependency_detection: true,
            enable_performance_analysis: true,
            sampling_rate: 1.0,
            max_call_depth: 100,
        }
    }
}

/// 执行流追踪器
#[allow(dead_code)]
pub struct ExecutionFlowTracker {
    config: ExecutionFlowConfig,
    call_chain_tracker: CallChainTracker,
    execution_graph: ExecutionGraph,
    dependency_detector: DependencyDetector,
    performance_analyzer: PerformanceAnalyzer,
    bottleneck_identifier: BottleneckIdentifier,
}

impl ExecutionFlowTracker {
    /// 创建新的执行流追踪器
    pub fn new(config: ExecutionFlowConfig) -> Self {
        Self {
            config: config.clone(),
            call_chain_tracker: CallChainTracker::new(),
            execution_graph: ExecutionGraph::new(),
            dependency_detector: DependencyDetector::new(),
            performance_analyzer: PerformanceAnalyzer::new(),
            bottleneck_identifier: BottleneckIdentifier::new(),
        }
    }
    
    /// 开始追踪执行
    pub fn start_tracking(&self, operation: &str) -> TrackingContext {
        TrackingContext {
            operation: operation.to_string(),
            start_time: std::time::Instant::now(),
        }
    }
    
    /// 结束追踪
    pub fn end_tracking(&self, _context: TrackingContext) {
        // 实际实现会记录执行信息
    }
    
    /// 获取调用链追踪器
    pub fn call_chain_tracker(&self) -> &CallChainTracker {
        &self.call_chain_tracker
    }
    
    /// 获取执行图
    pub fn execution_graph(&self) -> &ExecutionGraph {
        &self.execution_graph
    }
    
    /// 获取依赖检测器
    pub fn dependency_detector(&self) -> &DependencyDetector {
        &self.dependency_detector
    }
    
    /// 获取性能分析器
    pub fn performance_analyzer(&self) -> &PerformanceAnalyzer {
        &self.performance_analyzer
    }
    
    /// 获取瓶颈识别器
    pub fn bottleneck_identifier(&self) -> &BottleneckIdentifier {
        &self.bottleneck_identifier
    }
}

/// 追踪上下文
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct TrackingContext {
    pub operation: String,
    pub start_time: std::time::Instant,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_execution_flow_tracker() {
        let tracker = ExecutionFlowTracker::new(ExecutionFlowConfig::default());
        let ctx = tracker.start_tracking("test_operation");
        tracker.end_tracking(ctx);
    }
}

