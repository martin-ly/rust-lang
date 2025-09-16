//! # 工作流原型模式 / Workflow Prototype Pattern
//!
//! 本模块实现了工作流原型模式，通过克隆现有工作流来创建新工作流。
//! This module implements the workflow prototype pattern, creating new workflows by cloning existing ones.

use crate::patterns::{PatternCategory, WorkflowContext, WorkflowPattern, WorkflowResult};
use crate::types::{StateTransition, WorkflowDefinition};
use serde_json::json;
use std::collections::HashMap;

/// 工作流原型注册表 / Workflow Prototype Registry
pub struct WorkflowPrototypeRegistry {
    prototypes: HashMap<String, WorkflowDefinition>,
}

impl WorkflowPrototypeRegistry {
    /// 创建新的原型注册表 / Create new prototype registry
    pub fn new() -> Self {
        Self {
            prototypes: HashMap::new(),
        }
    }

    /// 注册原型 / Register prototype
    pub fn register_prototype(&mut self, name: String, prototype: WorkflowDefinition) {
        self.prototypes.insert(name, prototype);
    }

    /// 克隆原型 / Clone prototype
    pub fn clone_prototype(
        &self,
        name: &str,
        new_name: Option<String>,
    ) -> Result<WorkflowDefinition, String> {
        let prototype = self
            .prototypes
            .get(name)
            .ok_or_else(|| format!("原型不存在 / Prototype not found: {}", name))?;

        let mut cloned = prototype.clone();

        if let Some(name) = new_name {
            cloned.name = name;
        } else {
            cloned.name = format!(
                "{}_clone_{}",
                prototype.name,
                uuid::Uuid::new_v4().to_string()[..8].to_string()
            );
        }

        // 更新元数据以标识这是克隆的 / Update metadata to identify this as a clone
        cloned.metadata.insert("is_clone".to_string(), json!(true));
        cloned
            .metadata
            .insert("original_prototype".to_string(), json!(name));
        cloned.metadata.insert(
            "cloned_at".to_string(),
            json!(chrono::Utc::now().to_rfc3339()),
        );

        Ok(cloned)
    }

    /// 获取所有原型名称 / Get all prototype names
    pub fn get_prototype_names(&self) -> Vec<String> {
        self.prototypes.keys().cloned().collect()
    }

    /// 检查原型是否存在 / Check if prototype exists
    pub fn has_prototype(&self, name: &str) -> bool {
        self.prototypes.contains_key(name)
    }
}

/// 工作流原型模式实现 / Workflow Prototype Pattern Implementation
pub struct WorkflowPrototypePattern {
    name: String,
    registry: WorkflowPrototypeRegistry,
}

impl WorkflowPrototypePattern {
    pub fn new() -> Self {
        let mut registry = WorkflowPrototypeRegistry::new();

        // 注册默认原型 / Register default prototypes
        Self::register_default_prototypes(&mut registry);

        Self {
            name: "WorkflowPrototype".to_string(),
            registry,
        }
    }

    /// 注册默认原型 / Register default prototypes
    fn register_default_prototypes(registry: &mut WorkflowPrototypeRegistry) {
        // 简单工作流原型 / Simple workflow prototype
        let simple_prototype = WorkflowDefinition {
            name: "simple_workflow_prototype".to_string(),
            description: Some("简单工作流原型 / Simple workflow prototype".to_string()),
            version: "1.0.0".to_string(),
            states: vec!["start".to_string(), "end".to_string()],
            transitions: vec![StateTransition {
                from_state: "start".to_string(),
                to_state: "end".to_string(),
                condition: Some("complete".to_string()),
                actions: vec!["finish".to_string()],
                timeout: None,
            }],
            initial_state: "start".to_string(),
            final_states: vec!["end".to_string()],
            metadata: {
                let mut meta = std::collections::HashMap::new();
                meta.insert("category".to_string(), json!("simple"));
                meta.insert("complexity".to_string(), json!("low"));
                meta
            },
        };

        registry.register_prototype("simple".to_string(), simple_prototype);

        // 复杂工作流原型 / Complex workflow prototype
        let complex_prototype = WorkflowDefinition {
            name: "complex_workflow_prototype".to_string(),
            description: Some("复杂工作流原型 / Complex workflow prototype".to_string()),
            version: "1.0.0".to_string(),
            states: vec![
                "init".to_string(),
                "validate".to_string(),
                "process".to_string(),
                "verify".to_string(),
                "complete".to_string(),
                "error".to_string(),
            ],
            transitions: vec![
                StateTransition {
                    from_state: "init".to_string(),
                    to_state: "validate".to_string(),
                    condition: Some("initialized".to_string()),
                    actions: vec!["start_validation".to_string()],
                    timeout: None,
                },
                StateTransition {
                    from_state: "validate".to_string(),
                    to_state: "process".to_string(),
                    condition: Some("validation_success".to_string()),
                    actions: vec!["start_processing".to_string()],
                    timeout: None,
                },
                StateTransition {
                    from_state: "validate".to_string(),
                    to_state: "error".to_string(),
                    condition: Some("validation_failed".to_string()),
                    actions: vec!["handle_error".to_string()],
                    timeout: None,
                },
                StateTransition {
                    from_state: "process".to_string(),
                    to_state: "verify".to_string(),
                    condition: Some("processing_complete".to_string()),
                    actions: vec!["start_verification".to_string()],
                    timeout: None,
                },
                StateTransition {
                    from_state: "verify".to_string(),
                    to_state: "complete".to_string(),
                    condition: Some("verification_success".to_string()),
                    actions: vec!["complete_workflow".to_string()],
                    timeout: None,
                },
                StateTransition {
                    from_state: "verify".to_string(),
                    to_state: "error".to_string(),
                    condition: Some("verification_failed".to_string()),
                    actions: vec!["handle_error".to_string()],
                    timeout: None,
                },
            ],
            initial_state: "init".to_string(),
            final_states: vec!["complete".to_string(), "error".to_string()],
            metadata: {
                let mut meta = std::collections::HashMap::new();
                meta.insert("category".to_string(), json!("complex"));
                meta.insert("complexity".to_string(), json!("high"));
                meta.insert("error_handling".to_string(), json!(true));
                meta
            },
        };

        registry.register_prototype("complex".to_string(), complex_prototype);
    }
}

impl WorkflowPattern for WorkflowPrototypePattern {
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

        // 从上下文数据中提取原型参数 / Extract prototype parameters from context data
        let prototype_name = context
            .data
            .get("prototype_name")
            .and_then(|v| v.as_str())
            .unwrap_or("simple");

        let new_name = context
            .data
            .get("new_name")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());

        // 使用原型模式克隆工作流 / Use prototype pattern to clone workflow
        let cloned_workflow = self.registry.clone_prototype(prototype_name, new_name)?;

        let result = WorkflowResult {
            success: true,
            data: json!({
                "pattern": "WorkflowPrototype",
                "workflow_id": context.workflow_id,
                "prototype_name": prototype_name,
                "cloned_workflow": cloned_workflow,
                "cloning_method": "clone_prototype"
            }),
            message: "工作流原型模式应用成功 / Workflow prototype pattern applied successfully"
                .to_string(),
        };

        Ok(result)
    }

    fn validate(&self, context: &WorkflowContext) -> Result<(), String> {
        if context.data.get("prototype_name").is_none() {
            return Err("原型名称不能为空 / Prototype name cannot be empty".to_string());
        }

        let prototype_name = context
            .data
            .get("prototype_name")
            .and_then(|v| v.as_str())
            .unwrap_or("");

        if !self.registry.has_prototype(prototype_name) {
            return Err(format!(
                "原型不存在 / Prototype not found: {}",
                prototype_name
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_workflow_prototype_registry() {
        let mut registry = WorkflowPrototypeRegistry::new();

        // 注册原型 / Register prototype
        let prototype = WorkflowDefinition {
            name: "test_prototype".to_string(),
            description: Some("测试原型 / Test prototype".to_string()),
            version: "1.0.0".to_string(),
            states: vec!["start".to_string(), "end".to_string()],
            transitions: vec![],
            initial_state: "start".to_string(),
            final_states: vec!["end".to_string()],
            metadata: std::collections::HashMap::new(),
        };

        registry.register_prototype("test".to_string(), prototype);

        // 测试克隆 / Test cloning
        let cloned = registry.clone_prototype("test", Some("cloned_test".to_string()));
        assert!(cloned.is_ok());
        let cloned_def = cloned.unwrap();
        assert_eq!(cloned_def.name, "cloned_test");
        assert!(cloned_def.metadata["is_clone"].as_bool().unwrap());

        // 测试不存在的原型 / Test non-existent prototype
        let result = registry.clone_prototype("nonexistent", None);
        assert!(result.is_err());
    }

    #[test]
    fn test_workflow_prototype_pattern() {
        let pattern = WorkflowPrototypePattern::new();
        assert_eq!(pattern.name(), "WorkflowPrototype");
        assert_eq!(pattern.category(), PatternCategory::Creational);

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({
                "prototype_name": "simple",
                "new_name": "my_simple_workflow"
            }),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["prototype_name"], "simple");
    }

    #[test]
    fn test_workflow_prototype_validation() {
        let pattern = WorkflowPrototypePattern::new();

        // 测试缺少原型名称 / Test missing prototype name
        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({}),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.validate(&context);
        assert!(result.is_err());

        // 测试不存在的原型 / Test non-existent prototype
        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({"prototype_name": "nonexistent"}),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.validate(&context);
        assert!(result.is_err());
    }
}
