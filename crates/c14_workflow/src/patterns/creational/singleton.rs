//! # 工作流单例模式 / Workflow Singleton Pattern
//!
//! 本模块实现了工作流单例模式，确保工作流实例的唯一性。
//! This module implements the workflow singleton pattern, ensuring the uniqueness of workflow instances.

use crate::patterns::{PatternCategory, WorkflowContext, WorkflowPattern, WorkflowResult};
use crate::types::{StateTransition, WorkflowDefinition};
use once_cell::sync::OnceCell;
use serde_json::json;
use std::sync::{Arc, Mutex};

/// 工作流单例管理器 / Workflow Singleton Manager
pub struct WorkflowSingletonManager {
    instances: Arc<Mutex<std::collections::HashMap<String, WorkflowDefinition>>>,
}

impl WorkflowSingletonManager {
    /// 获取单例实例 / Get singleton instance
    pub fn get_instance() -> &'static WorkflowSingletonManager {
        static SINGLETON: OnceCell<WorkflowSingletonManager> = OnceCell::new();

        SINGLETON.get_or_init(|| WorkflowSingletonManager {
            instances: Arc::new(Mutex::new(std::collections::HashMap::new())),
        })
    }

    /// 获取或创建工作流实例 / Get or create workflow instance
    pub fn get_or_create_workflow(
        &self,
        name: String,
        factory: impl FnOnce() -> WorkflowDefinition,
    ) -> Result<WorkflowDefinition, String> {
        let mut instances = self
            .instances
            .lock()
            .map_err(|_| "锁获取失败 / Lock acquisition failed".to_string())?;

        if let Some(instance) = instances.get(&name) {
            tracing::info!(
                "返回现有工作流实例 / Returning existing workflow instance: {}",
                name
            );
            Ok(instance.clone())
        } else {
            tracing::info!(
                "创建新的工作流实例 / Creating new workflow instance: {}",
                name
            );
            let new_instance = factory();
            instances.insert(name.clone(), new_instance.clone());
            Ok(new_instance)
        }
    }

    /// 检查工作流实例是否存在 / Check if workflow instance exists
    pub fn has_workflow(&self, name: &str) -> bool {
        if let Ok(instances) = self.instances.lock() {
            instances.contains_key(name)
        } else {
            false
        }
    }

    /// 获取所有工作流实例名称 / Get all workflow instance names
    pub fn get_workflow_names(&self) -> Vec<String> {
        if let Ok(instances) = self.instances.lock() {
            instances.keys().cloned().collect()
        } else {
            Vec::new()
        }
    }

    /// 移除工作流实例 / Remove workflow instance
    pub fn remove_workflow(&self, name: &str) -> Result<Option<WorkflowDefinition>, String> {
        let mut instances = self
            .instances
            .lock()
            .map_err(|_| "锁获取失败 / Lock acquisition failed".to_string())?;
        Ok(instances.remove(name))
    }
}

/// 工作流单例模式实现 / Workflow Singleton Pattern Implementation
pub struct WorkflowSingletonPattern {
    name: String,
}

impl WorkflowSingletonPattern {
    pub fn new() -> Self {
        Self {
            name: "WorkflowSingleton".to_string(),
        }
    }
}

impl WorkflowPattern for WorkflowSingletonPattern {
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

        // 从上下文数据中提取单例参数 / Extract singleton parameters from context data
        let workflow_name = context
            .data
            .get("workflow_name")
            .and_then(|v| v.as_str())
            .unwrap_or("default_singleton_workflow");

        let workflow_type = context
            .data
            .get("workflow_type")
            .and_then(|v| v.as_str())
            .unwrap_or("simple");

        // 使用单例模式获取或创建工作流实例 / Use singleton pattern to get or create workflow instance
        let singleton_manager = WorkflowSingletonManager::get_instance();

        let workflow_def =
            singleton_manager.get_or_create_workflow(workflow_name.to_string(), || {
                // 根据类型创建工作流定义 / Create workflow definition based on type
                match workflow_type {
                    "simple" => WorkflowDefinition {
                        name: workflow_name.to_string(),
                        description: Some("简单单例工作流 / Simple singleton workflow".to_string()),
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
                            meta.insert("pattern".to_string(), json!("singleton"));
                            meta.insert("type".to_string(), json!("simple"));
                            meta.insert(
                                "created_at".to_string(),
                                json!(chrono::Utc::now().to_rfc3339()),
                            );
                            meta
                        },
                    },
                    "complex" => WorkflowDefinition {
                        name: workflow_name.to_string(),
                        description: Some(
                            "复杂单例工作流 / Complex singleton workflow".to_string(),
                        ),
                        version: "1.0.0".to_string(),
                        states: vec![
                            "init".to_string(),
                            "process".to_string(),
                            "validate".to_string(),
                            "complete".to_string(),
                        ],
                        transitions: vec![
                            StateTransition {
                                from_state: "init".to_string(),
                                to_state: "process".to_string(),
                                condition: Some("initialized".to_string()),
                                actions: vec!["start_processing".to_string()],
                                timeout: None,
                            },
                            StateTransition {
                                from_state: "process".to_string(),
                                to_state: "validate".to_string(),
                                condition: Some("processing_complete".to_string()),
                                actions: vec!["start_validation".to_string()],
                                timeout: None,
                            },
                            StateTransition {
                                from_state: "validate".to_string(),
                                to_state: "complete".to_string(),
                                condition: Some("validation_success".to_string()),
                                actions: vec!["complete_workflow".to_string()],
                                timeout: None,
                            },
                        ],
                        initial_state: "init".to_string(),
                        final_states: vec!["complete".to_string()],
                        metadata: {
                            let mut meta = std::collections::HashMap::new();
                            meta.insert("pattern".to_string(), json!("singleton"));
                            meta.insert("type".to_string(), json!("complex"));
                            meta.insert(
                                "created_at".to_string(),
                                json!(chrono::Utc::now().to_rfc3339()),
                            );
                            meta
                        },
                    },
                    _ => WorkflowDefinition {
                        name: workflow_name.to_string(),
                        description: Some(
                            "默认单例工作流 / Default singleton workflow".to_string(),
                        ),
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
                            meta.insert("pattern".to_string(), json!("singleton"));
                            meta.insert("type".to_string(), json!("default"));
                            meta.insert(
                                "created_at".to_string(),
                                json!(chrono::Utc::now().to_rfc3339()),
                            );
                            meta
                        },
                    },
                }
            })?;

        let result = WorkflowResult {
            success: true,
            data: json!({
                "pattern": "WorkflowSingleton",
                "workflow_id": context.workflow_id,
                "workflow_name": workflow_name,
                "workflow_type": workflow_type,
                "singleton_instance": workflow_def,
                "is_unique": true,
                "singleton_method": "get_or_create_workflow"
            }),
            message: "工作流单例模式应用成功 / Workflow singleton pattern applied successfully"
                .to_string(),
        };

        Ok(result)
    }

    fn validate(&self, context: &WorkflowContext) -> Result<(), String> {
        // 单例模式通常不需要特殊验证 / Singleton pattern usually doesn't need special validation
        // 但可以检查工作流名称 / But can check workflow name
        if let Some(workflow_name) = context.data.get("workflow_name").and_then(|v| v.as_str()) {
            if workflow_name.is_empty() {
                return Err("工作流名称不能为空 / Workflow name cannot be empty".to_string());
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_workflow_singleton_manager() {
        let manager = WorkflowSingletonManager::get_instance();

        // 测试获取或创建工作流 / Test get or create workflow
        let workflow_def = WorkflowDefinition {
            name: "test_workflow".to_string(),
            description: Some("测试工作流 / Test workflow".to_string()),
            version: "1.0.0".to_string(),
            states: vec!["start".to_string(), "end".to_string()],
            transitions: vec![],
            initial_state: "start".to_string(),
            final_states: vec!["end".to_string()],
            metadata: std::collections::HashMap::new(),
        };

        let result =
            manager.get_or_create_workflow("test_workflow".to_string(), || workflow_def.clone());
        assert!(result.is_ok());

        // 测试再次获取相同工作流 / Test getting the same workflow again
        let result2 = manager.get_or_create_workflow("test_workflow".to_string(), || {
            panic!("不应该创建新实例 / Should not create new instance");
        });
        assert!(result2.is_ok());

        // 测试检查工作流是否存在 / Test checking if workflow exists
        assert!(manager.has_workflow("test_workflow"));
        assert!(!manager.has_workflow("nonexistent_workflow"));

        // 测试获取工作流名称列表 / Test getting workflow names
        let names = manager.get_workflow_names();
        assert!(names.contains(&"test_workflow".to_string()));
    }

    #[test]
    fn test_workflow_singleton_pattern() {
        let pattern = WorkflowSingletonPattern::new();
        assert_eq!(pattern.name(), "WorkflowSingleton");
        assert_eq!(pattern.category(), PatternCategory::Creational);

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({
                "workflow_name": "my_singleton_workflow",
                "workflow_type": "simple"
            }),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["workflow_name"], "my_singleton_workflow");
        assert_eq!(result.data["is_unique"], true);
    }

    #[test]
    fn test_workflow_singleton_validation() {
        let pattern = WorkflowSingletonPattern::new();

        // 测试空工作流名称 / Test empty workflow name
        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({
                "workflow_name": "",
                "workflow_type": "simple"
            }),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.validate(&context);
        assert!(result.is_err());

        // 测试正常情况 / Test normal case
        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({
                "workflow_name": "valid_workflow",
                "workflow_type": "complex"
            }),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.validate(&context);
        assert!(result.is_ok());
    }
}
