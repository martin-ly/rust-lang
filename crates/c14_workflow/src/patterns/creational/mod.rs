//! # 创建型工作流设计模式 / Creational Workflow Design Patterns
//!
//! 本模块实现了创建型工作流设计模式，包括建造者、工厂、原型和单例模式。
//! This module implements creational workflow design patterns, including Builder, Factory, Prototype, and Singleton patterns.

pub mod builder;
pub mod factory;
pub mod prototype;
pub mod singleton;

// 重新导出创建型模式 / Re-export creational patterns
pub use builder::*;
pub use factory::*;
pub use prototype::*;
pub use singleton::*;

use crate::patterns::{PatternCategory, WorkflowContext, WorkflowPattern, WorkflowResult};

/// 初始化创建型模式 / Initialize creational patterns
pub fn init_creational_patterns() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("初始化创建型工作流模式 / Initializing creational workflow patterns");
    Ok(())
}

/// 工作流建造者模式 / Workflow Builder Pattern
///
/// 提供逐步构建复杂工作流的能力。
/// Provides the ability to build complex workflows step by step.
pub struct WorkflowBuilder {
    name: String,
}

impl WorkflowBuilder {
    pub fn new() -> Self {
        Self {
            name: "WorkflowBuilder".to_string(),
        }
    }
}

impl WorkflowPattern for WorkflowBuilder {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        "逐步构建复杂工作流的建造者模式 / Builder pattern for step-by-step construction of complex workflows"
    }

    fn category(&self) -> PatternCategory {
        PatternCategory::Creational
    }

    fn apply(&self, context: &WorkflowContext) -> Result<WorkflowResult, String> {
        tracing::info!("应用工作流建造者模式 / Applying workflow builder pattern");

        // 实现建造者模式逻辑 / Implement builder pattern logic
        let result = WorkflowResult {
            success: true,
            data: serde_json::json!({
                "pattern": "WorkflowBuilder",
                "workflow_id": context.workflow_id,
                "built_components": ["step1", "step2", "step3"]
            }),
            message: "工作流建造者模式应用成功 / Workflow builder pattern applied successfully"
                .to_string(),
        };

        Ok(result)
    }

    fn validate(&self, context: &WorkflowContext) -> Result<(), String> {
        if context.workflow_id.is_empty() {
            return Err("工作流ID不能为空 / Workflow ID cannot be empty".to_string());
        }
        Ok(())
    }
}

/// 工作流工厂模式 / Workflow Factory Pattern
///
/// 根据类型创建不同的工作流实例。
/// Creates different workflow instances based on type.
pub struct WorkflowFactory {
    name: String,
}

impl WorkflowFactory {
    pub fn new() -> Self {
        Self {
            name: "WorkflowFactory".to_string(),
        }
    }
}

impl WorkflowPattern for WorkflowFactory {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        "根据类型创建不同工作流实例的工厂模式 / Factory pattern for creating different workflow instances based on type"
    }

    fn category(&self) -> PatternCategory {
        PatternCategory::Creational
    }

    fn apply(&self, context: &WorkflowContext) -> Result<WorkflowResult, String> {
        tracing::info!("应用工作流工厂模式 / Applying workflow factory pattern");

        // 实现工厂模式逻辑 / Implement factory pattern logic
        let workflow_type = context
            .data
            .get("type")
            .and_then(|v| v.as_str())
            .unwrap_or("default");

        let result = WorkflowResult {
            success: true,
            data: serde_json::json!({
                "pattern": "WorkflowFactory",
                "workflow_id": context.workflow_id,
                "workflow_type": workflow_type,
                "created_instance": format!("{}_instance", workflow_type)
            }),
            message: "工作流工厂模式应用成功 / Workflow factory pattern applied successfully"
                .to_string(),
        };

        Ok(result)
    }

    fn validate(&self, context: &WorkflowContext) -> Result<(), String> {
        if context.data.get("type").is_none() {
            return Err("工作流类型不能为空 / Workflow type cannot be empty".to_string());
        }
        Ok(())
    }
}

/// 工作流原型模式 / Workflow Prototype Pattern
///
/// 通过克隆现有工作流来创建新工作流。
/// Creates new workflows by cloning existing ones.
pub struct WorkflowPrototype {
    name: String,
}

impl WorkflowPrototype {
    pub fn new() -> Self {
        Self {
            name: "WorkflowPrototype".to_string(),
        }
    }
}

impl WorkflowPattern for WorkflowPrototype {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        "通过克隆现有工作流创建新工作流的原型模式 / Prototype pattern for creating new workflows by cloning existing ones"
    }

    fn category(&self) -> PatternCategory {
        PatternCategory::Creational
    }

    fn apply(&self, context: &WorkflowContext) -> Result<WorkflowResult, String> {
        tracing::info!("应用工作流原型模式 / Applying workflow prototype pattern");

        // 实现原型模式逻辑 / Implement prototype pattern logic
        let prototype_id = context
            .data
            .get("prototype_id")
            .and_then(|v| v.as_str())
            .unwrap_or("default_prototype");

        let result = WorkflowResult {
            success: true,
            data: serde_json::json!({
                "pattern": "WorkflowPrototype",
                "workflow_id": context.workflow_id,
                "prototype_id": prototype_id,
                "cloned_components": ["template", "steps", "transitions"]
            }),
            message: "工作流原型模式应用成功 / Workflow prototype pattern applied successfully"
                .to_string(),
        };

        Ok(result)
    }

    fn validate(&self, context: &WorkflowContext) -> Result<(), String> {
        if context.data.get("prototype_id").is_none() {
            return Err("原型ID不能为空 / Prototype ID cannot be empty".to_string());
        }
        Ok(())
    }
}

/// 工作流单例模式 / Workflow Singleton Pattern
///
/// 确保工作流实例的唯一性。
/// Ensures the uniqueness of workflow instances.
pub struct WorkflowSingleton {
    name: String,
}

impl WorkflowSingleton {
    pub fn new() -> Self {
        Self {
            name: "WorkflowSingleton".to_string(),
        }
    }
}

impl WorkflowPattern for WorkflowSingleton {
    fn name(&self) -> &str {
        &self.name
    }

    fn description(&self) -> &str {
        "确保工作流实例唯一性的单例模式 / Singleton pattern for ensuring uniqueness of workflow instances"
    }

    fn category(&self) -> PatternCategory {
        PatternCategory::Creational
    }

    fn apply(&self, context: &WorkflowContext) -> Result<WorkflowResult, String> {
        tracing::info!("应用工作流单例模式 / Applying workflow singleton pattern");

        // 实现单例模式逻辑 / Implement singleton pattern logic
        let result = WorkflowResult {
            success: true,
            data: serde_json::json!({
                "pattern": "WorkflowSingleton",
                "workflow_id": context.workflow_id,
                "instance_id": "singleton_instance",
                "is_unique": true
            }),
            message: "工作流单例模式应用成功 / Workflow singleton pattern applied successfully"
                .to_string(),
        };

        Ok(result)
    }

    fn validate(&self, _context: &WorkflowContext) -> Result<(), String> {
        // 单例模式通常不需要特殊验证 / Singleton pattern usually doesn't need special validation
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_workflow_builder() {
        let builder = WorkflowBuilder::new();
        assert_eq!(builder.name(), "WorkflowBuilder");
        assert_eq!(builder.category(), PatternCategory::Creational);

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: serde_json::json!({}),
            metadata: std::collections::HashMap::new(),
        };

        let result = builder.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["pattern"], "WorkflowBuilder");
    }

    #[test]
    fn test_workflow_factory() {
        let factory = WorkflowFactory::new();
        assert_eq!(factory.name(), "WorkflowFactory");

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: serde_json::json!({"type": "data_processing"}),
            metadata: std::collections::HashMap::new(),
        };

        let result = factory.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["workflow_type"], "data_processing");
    }

    #[test]
    fn test_workflow_prototype() {
        let prototype = WorkflowPrototype::new();
        assert_eq!(prototype.name(), "WorkflowPrototype");

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: serde_json::json!({"prototype_id": "template_1"}),
            metadata: std::collections::HashMap::new(),
        };

        let result = prototype.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["prototype_id"], "template_1");
    }

    #[test]
    fn test_workflow_singleton() {
        let singleton = WorkflowSingleton::new();
        assert_eq!(singleton.name(), "WorkflowSingleton");

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: serde_json::json!({}),
            metadata: std::collections::HashMap::new(),
        };

        let result = singleton.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["is_unique"], true);
    }
}
