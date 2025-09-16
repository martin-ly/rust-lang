//! # 工作流设计模式模块 / Workflow Design Patterns Module
//!
//! 本模块实现了二十多个工作流设计模式，为工作流系统提供丰富的设计模式支持。
//! This module implements over twenty workflow design patterns, providing rich design pattern support for workflow systems.

pub mod behavioral;
pub mod concurrent;
pub mod creational;
pub mod structural;

// 重新导出主要模式 / Re-export main patterns
pub use behavioral::*;
pub use concurrent::*;
pub use creational::*;
pub use structural::*;

/// 工作流设计模式版本 / Workflow Design Patterns Version
pub const PATTERNS_VERSION: &str = "1.0.0";

/// 初始化工作流设计模式 / Initialize workflow design patterns
pub fn init_workflow_patterns() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("初始化工作流设计模式 / Initializing workflow design patterns");

    // 初始化创建型模式 / Initialize creational patterns
    init_creational_patterns()?;

    // 初始化结构型模式 / Initialize structural patterns
    init_structural_patterns()?;

    // 初始化行为型模式 / Initialize behavioral patterns
    init_behavioral_patterns()?;

    // 初始化并发模式 / Initialize concurrent patterns
    init_concurrent_patterns()?;

    tracing::info!("工作流设计模式初始化完成 / Workflow design patterns initialized");
    Ok(())
}

/// 工作流模式注册表 / Workflow Pattern Registry
///
/// 用于注册和管理各种工作流设计模式。
/// Used for registering and managing various workflow design patterns.
pub struct WorkflowPatternRegistry {
    creational_patterns: std::collections::HashMap<String, Box<dyn WorkflowPattern>>,
    structural_patterns: std::collections::HashMap<String, Box<dyn WorkflowPattern>>,
    behavioral_patterns: std::collections::HashMap<String, Box<dyn WorkflowPattern>>,
    concurrent_patterns: std::collections::HashMap<String, Box<dyn WorkflowPattern>>,
}

/// 工作流模式特征 / Workflow Pattern Trait
pub trait WorkflowPattern: Send + Sync {
    /// 模式名称 / Pattern name
    fn name(&self) -> &str;

    /// 模式描述 / Pattern description
    fn description(&self) -> &str;

    /// 模式类别 / Pattern category
    fn category(&self) -> PatternCategory;

    /// 应用模式 / Apply pattern
    fn apply(&self, context: &WorkflowContext) -> Result<WorkflowResult, String>;

    /// 验证模式 / Validate pattern
    fn validate(&self, context: &WorkflowContext) -> Result<(), String>;
}

/// 模式类别 / Pattern Category
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PatternCategory {
    Creational,
    Structural,
    Behavioral,
    Concurrent,
}

/// 工作流上下文 / Workflow Context
#[derive(Debug, Clone)]
pub struct WorkflowContext {
    pub workflow_id: String,
    pub data: serde_json::Value,
    pub metadata: std::collections::HashMap<String, String>,
}

/// 工作流结果 / Workflow Result
#[derive(Debug, Clone)]
pub struct WorkflowResult {
    pub success: bool,
    pub data: serde_json::Value,
    pub message: String,
}

impl WorkflowPatternRegistry {
    /// 创建工作流模式注册表 / Create workflow pattern registry
    pub fn new() -> Self {
        Self {
            creational_patterns: std::collections::HashMap::new(),
            structural_patterns: std::collections::HashMap::new(),
            behavioral_patterns: std::collections::HashMap::new(),
            concurrent_patterns: std::collections::HashMap::new(),
        }
    }

    /// 注册模式 / Register pattern
    pub fn register_pattern(&mut self, pattern: Box<dyn WorkflowPattern>) {
        let name = pattern.name().to_string();
        let category = pattern.category();

        match category {
            PatternCategory::Creational => {
                self.creational_patterns.insert(name, pattern);
            }
            PatternCategory::Structural => {
                self.structural_patterns.insert(name, pattern);
            }
            PatternCategory::Behavioral => {
                self.behavioral_patterns.insert(name, pattern);
            }
            PatternCategory::Concurrent => {
                self.concurrent_patterns.insert(name, pattern);
            }
        }
    }

    /// 获取模式 / Get pattern
    pub fn get_pattern(
        &self,
        name: &str,
        category: PatternCategory,
    ) -> Option<&dyn WorkflowPattern> {
        match category {
            PatternCategory::Creational => self.creational_patterns.get(name).map(|p| p.as_ref()),
            PatternCategory::Structural => self.structural_patterns.get(name).map(|p| p.as_ref()),
            PatternCategory::Behavioral => self.behavioral_patterns.get(name).map(|p| p.as_ref()),
            PatternCategory::Concurrent => self.concurrent_patterns.get(name).map(|p| p.as_ref()),
        }
    }

    /// 列出所有模式 / List all patterns
    pub fn list_patterns(&self) -> Vec<PatternInfo> {
        let mut patterns = Vec::new();

        for (name, pattern) in &self.creational_patterns {
            patterns.push(PatternInfo {
                name: name.clone(),
                description: pattern.description().to_string(),
                category: PatternCategory::Creational,
            });
        }

        for (name, pattern) in &self.structural_patterns {
            patterns.push(PatternInfo {
                name: name.clone(),
                description: pattern.description().to_string(),
                category: PatternCategory::Structural,
            });
        }

        for (name, pattern) in &self.behavioral_patterns {
            patterns.push(PatternInfo {
                name: name.clone(),
                description: pattern.description().to_string(),
                category: PatternCategory::Behavioral,
            });
        }

        for (name, pattern) in &self.concurrent_patterns {
            patterns.push(PatternInfo {
                name: name.clone(),
                description: pattern.description().to_string(),
                category: PatternCategory::Concurrent,
            });
        }

        patterns
    }
}

/// 模式信息 / Pattern Info
#[derive(Debug, Clone)]
pub struct PatternInfo {
    pub name: String,
    pub description: String,
    pub category: PatternCategory,
}

/// 工作流模式工厂 / Workflow Pattern Factory
///
/// 用于创建和管理工作流模式实例。
/// Used for creating and managing workflow pattern instances.
pub struct WorkflowPatternFactory {
    registry: WorkflowPatternRegistry,
}

impl WorkflowPatternFactory {
    /// 创建工作流模式工厂 / Create workflow pattern factory
    pub fn new() -> Self {
        let mut registry = WorkflowPatternRegistry::new();

        // 注册所有模式 / Register all patterns
        Self::register_all_patterns(&mut registry);

        Self { registry }
    }

    /// 注册所有模式 / Register all patterns
    fn register_all_patterns(registry: &mut WorkflowPatternRegistry) {
        // 注册创建型模式 / Register creational patterns
        registry.register_pattern(Box::new(creational::WorkflowBuilder::new()));
        registry.register_pattern(Box::new(creational::WorkflowFactory::new()));
        registry.register_pattern(Box::new(creational::WorkflowPrototype::new()));
        registry.register_pattern(Box::new(creational::WorkflowSingleton::new()));

        // 注册结构型模式 / Register structural patterns
        registry.register_pattern(Box::new(structural::WorkflowAdapter::new()));
        registry.register_pattern(Box::new(structural::WorkflowBridge::new()));
        registry.register_pattern(Box::new(structural::WorkflowComposite::new()));
        registry.register_pattern(Box::new(structural::WorkflowDecorator::new()));
        registry.register_pattern(Box::new(structural::WorkflowFacade::new()));
        registry.register_pattern(Box::new(structural::WorkflowFlyweight::new()));
        registry.register_pattern(Box::new(structural::WorkflowProxy::new()));

        // 注册行为型模式 / Register behavioral patterns
        registry.register_pattern(Box::new(behavioral::WorkflowChainOfResponsibility::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowCommand::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowInterpreter::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowIterator::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowMediator::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowMemento::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowObserver::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowState::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowStrategy::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowTemplateMethod::new()));
        registry.register_pattern(Box::new(behavioral::WorkflowVisitor::new()));

        // 注册并发模式 / Register concurrent patterns
        registry.register_pattern(Box::new(concurrent::WorkflowActor::new()));
        registry.register_pattern(Box::new(concurrent::WorkflowProducerConsumer::new()));
        registry.register_pattern(Box::new(concurrent::WorkflowPipeline::new()));
        registry.register_pattern(Box::new(concurrent::WorkflowReactor::new()));
        registry.register_pattern(Box::new(concurrent::WorkflowThreadPool::new()));
    }

    /// 创建模式实例 / Create pattern instance
    pub fn create_pattern(
        &self,
        name: &str,
        category: PatternCategory,
    ) -> Option<&dyn WorkflowPattern> {
        self.registry.get_pattern(name, category)
    }

    /// 获取所有模式信息 / Get all pattern information
    pub fn get_all_patterns(&self) -> Vec<PatternInfo> {
        self.registry.list_patterns()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_workflow_pattern_registry() {
        let mut registry = WorkflowPatternRegistry::new();

        // 测试模式注册 / Test pattern registration
        let pattern = Box::new(creational::WorkflowBuilder::new());
        registry.register_pattern(pattern);

        // 测试模式获取 / Test pattern retrieval
        let retrieved = registry.get_pattern("WorkflowBuilder", PatternCategory::Creational);
        assert!(retrieved.is_some());

        // 测试模式列表 / Test pattern listing
        let patterns = registry.list_patterns();
        assert_eq!(patterns.len(), 1);
        assert_eq!(patterns[0].name, "WorkflowBuilder");
    }

    #[test]
    fn test_workflow_pattern_factory() {
        let factory = WorkflowPatternFactory::new();

        // 测试工厂创建 / Test factory creation
        let patterns = factory.get_all_patterns();
        assert!(!patterns.is_empty());

        // 测试模式创建 / Test pattern creation
        let pattern = factory.create_pattern("WorkflowBuilder", PatternCategory::Creational);
        assert!(pattern.is_some());
    }
}
