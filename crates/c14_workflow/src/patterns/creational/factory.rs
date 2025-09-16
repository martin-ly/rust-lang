//! # 工作流工厂模式 / Workflow Factory Pattern
//!
//! 本模块实现了工作流工厂模式，根据类型创建不同的工作流实例。
//! This module implements the workflow factory pattern, creating different workflow instances based on type.

use crate::patterns::{PatternCategory, WorkflowContext, WorkflowPattern, WorkflowResult};
use crate::types::{StateTransition, WorkflowDefinition};
use serde_json::json;
use std::collections::HashMap;

/// 工作流类型 / Workflow Type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum WorkflowType {
    DataProcessing,
    ApiIntegration,
    FileOperation,
    DatabaseOperation,
    Custom(String),
}

/// 工作流工厂 / Workflow Factory
pub struct WorkflowFactory {
    workflow_templates: std::collections::HashMap<WorkflowType, WorkflowDefinition>,
}

impl WorkflowFactory {
    /// 创建新的工作流工厂 / Create new workflow factory
    pub fn new() -> Self {
        let mut factory = Self {
            workflow_templates: std::collections::HashMap::new(),
        };

        // 注册默认工作流模板 / Register default workflow templates
        factory.register_default_templates();
        factory
    }

    /// 注册默认工作流模板 / Register default workflow templates
    fn register_default_templates(&mut self) {
        // 数据处理工作流 / Data processing workflow
        self.workflow_templates.insert(
            WorkflowType::DataProcessing,
            WorkflowDefinition {
                name: "data_processing_workflow".to_string(),
                description: Some("数据处理工作流 / Data processing workflow".to_string()),
                version: "1.0.0".to_string(),
                states: vec![
                    "input".to_string(),
                    "transform".to_string(),
                    "validate".to_string(),
                    "output".to_string(),
                ],
                transitions: vec![
                    StateTransition {
                        from_state: "input".to_string(),
                        to_state: "transform".to_string(),
                        condition: Some("data_received".to_string()),
                        actions: vec!["transform_data".to_string()],
                        timeout: None,
                    },
                    StateTransition {
                        from_state: "transform".to_string(),
                        to_state: "validate".to_string(),
                        condition: Some("transformation_complete".to_string()),
                        actions: vec!["validate_data".to_string()],
                        timeout: None,
                    },
                    StateTransition {
                        from_state: "validate".to_string(),
                        to_state: "output".to_string(),
                        condition: Some("validation_success".to_string()),
                        actions: vec!["output_data".to_string()],
                        timeout: None,
                    },
                ],
                initial_state: "input".to_string(),
                final_states: vec!["output".to_string()],
                metadata: {
                    let mut meta = HashMap::new();
                    meta.insert("category".to_string(), json!("data_processing"));
                    meta.insert("complexity".to_string(), json!("medium"));
                    meta
                },
            },
        );

        // API 集成工作流 / API integration workflow
        self.workflow_templates.insert(
            WorkflowType::ApiIntegration,
            WorkflowDefinition {
                name: "api_integration_workflow".to_string(),
                description: Some("API 集成工作流 / API integration workflow".to_string()),
                version: "1.0.0".to_string(),
                states: vec![
                    "prepare".to_string(),
                    "authenticate".to_string(),
                    "request".to_string(),
                    "response".to_string(),
                    "complete".to_string(),
                ],
                transitions: vec![
                    StateTransition {
                        from_state: "prepare".to_string(),
                        to_state: "authenticate".to_string(),
                        condition: Some("preparation_complete".to_string()),
                        actions: vec!["authenticate".to_string()],
                        timeout: None,
                    },
                    StateTransition {
                        from_state: "authenticate".to_string(),
                        to_state: "request".to_string(),
                        condition: Some("authentication_success".to_string()),
                        actions: vec!["send_request".to_string()],
                        timeout: None,
                    },
                    StateTransition {
                        from_state: "request".to_string(),
                        to_state: "response".to_string(),
                        condition: Some("response_received".to_string()),
                        actions: vec!["process_response".to_string()],
                        timeout: None,
                    },
                    StateTransition {
                        from_state: "response".to_string(),
                        to_state: "complete".to_string(),
                        condition: Some("response_processed".to_string()),
                        actions: vec!["complete_integration".to_string()],
                        timeout: None,
                    },
                ],
                initial_state: "prepare".to_string(),
                final_states: vec!["complete".to_string()],
                metadata: {
                    let mut meta = std::collections::HashMap::new();
                    meta.insert("category".to_string(), json!("api_integration"));
                    meta.insert("complexity".to_string(), json!("high"));
                    meta
                },
            },
        );

        // 文件操作工作流 / File operation workflow
        self.workflow_templates.insert(
            WorkflowType::FileOperation,
            WorkflowDefinition {
                name: "file_operation_workflow".to_string(),
                description: Some("文件操作工作流 / File operation workflow".to_string()),
                version: "1.0.0".to_string(),
                states: vec![
                    "check_file".to_string(),
                    "process_file".to_string(),
                    "save_result".to_string(),
                ],
                transitions: vec![
                    StateTransition {
                        from_state: "check_file".to_string(),
                        to_state: "process_file".to_string(),
                        condition: Some("file_exists".to_string()),
                        actions: vec!["process_file".to_string()],
                        timeout: None,
                    },
                    StateTransition {
                        from_state: "process_file".to_string(),
                        to_state: "save_result".to_string(),
                        condition: Some("processing_complete".to_string()),
                        actions: vec!["save_result".to_string()],
                        timeout: None,
                    },
                ],
                initial_state: "check_file".to_string(),
                final_states: vec!["save_result".to_string()],
                metadata: {
                    let mut meta = std::collections::HashMap::new();
                    meta.insert("category".to_string(), json!("file_operation"));
                    meta.insert("complexity".to_string(), json!("low"));
                    meta
                },
            },
        );
    }

    /// 创建工作流实例 / Create workflow instance
    pub fn create_workflow(
        &self,
        workflow_type: &WorkflowType,
        custom_name: Option<String>,
    ) -> Result<WorkflowDefinition, String> {
        let template = self.workflow_templates.get(workflow_type).ok_or_else(|| {
            format!(
                "不支持的工作流类型 / Unsupported workflow type: {:?}",
                workflow_type
            )
        })?;

        let mut workflow = template.clone();

        if let Some(name) = custom_name {
            workflow.name = name;
        } else {
            workflow.name = format!(
                "{}_{}",
                workflow.name,
                uuid::Uuid::new_v4().to_string()[..8].to_string()
            );
        }

        Ok(workflow)
    }

    /// 注册自定义工作流模板 / Register custom workflow template
    pub fn register_template(&mut self, workflow_type: WorkflowType, template: WorkflowDefinition) {
        self.workflow_templates.insert(workflow_type, template);
    }

    /// 获取支持的工作流类型 / Get supported workflow types
    pub fn get_supported_types(&self) -> Vec<WorkflowType> {
        self.workflow_templates.keys().cloned().collect()
    }
}

/// 工作流工厂模式实现 / Workflow Factory Pattern Implementation
pub struct WorkflowFactoryPattern {
    name: String,
    factory: WorkflowFactory,
}

impl WorkflowFactoryPattern {
    pub fn new() -> Self {
        Self {
            name: "WorkflowFactory".to_string(),
            factory: WorkflowFactory::new(),
        }
    }
}

impl WorkflowPattern for WorkflowFactoryPattern {
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

        // 从上下文数据中提取工厂参数 / Extract factory parameters from context data
        let workflow_type_str = context
            .data
            .get("type")
            .and_then(|v| v.as_str())
            .unwrap_or("data_processing");

        let workflow_type = match workflow_type_str {
            "data_processing" => WorkflowType::DataProcessing,
            "api_integration" => WorkflowType::ApiIntegration,
            "file_operation" => WorkflowType::FileOperation,
            "database_operation" => WorkflowType::DatabaseOperation,
            custom => WorkflowType::Custom(custom.to_string()),
        };

        let custom_name = context
            .data
            .get("custom_name")
            .and_then(|v| v.as_str())
            .map(|s| s.to_string());

        // 使用工厂模式创建工作流 / Use factory pattern to create workflow
        let workflow_def = self.factory.create_workflow(&workflow_type, custom_name)?;

        let result = WorkflowResult {
            success: true,
            data: json!({
                "pattern": "WorkflowFactory",
                "workflow_id": context.workflow_id,
                "workflow_type": workflow_type_str,
                "created_workflow": workflow_def,
                "factory_method": "create_workflow"
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

        let workflow_type_str = context
            .data
            .get("type")
            .and_then(|v| v.as_str())
            .unwrap_or("");

        // 检查是否支持该工作流类型 / Check if workflow type is supported
        let workflow_type = match workflow_type_str {
            "data_processing" => WorkflowType::DataProcessing,
            "api_integration" => WorkflowType::ApiIntegration,
            "file_operation" => WorkflowType::FileOperation,
            "database_operation" => WorkflowType::DatabaseOperation,
            _ => WorkflowType::Custom(workflow_type_str.to_string()),
        };

        if !self.factory.workflow_templates.contains_key(&workflow_type) {
            return Err(format!(
                "不支持的工作流类型 / Unsupported workflow type: {}",
                workflow_type_str
            ));
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_workflow_factory() {
        let factory = WorkflowFactory::new();

        // 测试创建数据处理工作流 / Test creating data processing workflow
        let workflow = factory.create_workflow(&WorkflowType::DataProcessing, None);
        assert!(workflow.is_ok());
        let def = workflow.unwrap();
        assert!(def.name.contains("data_processing_workflow"));
        assert_eq!(def.states.len(), 4);

        // 测试创建 API 集成工作流 / Test creating API integration workflow
        let workflow = factory.create_workflow(
            &WorkflowType::ApiIntegration,
            Some("custom_api".to_string()),
        );
        assert!(workflow.is_ok());
        let def = workflow.unwrap();
        assert_eq!(def.name, "custom_api");

        // 测试不支持的类型 / Test unsupported type
        let workflow = factory.create_workflow(&WorkflowType::DatabaseOperation, None);
        assert!(workflow.is_err());
    }

    #[test]
    fn test_workflow_factory_pattern() {
        let pattern = WorkflowFactoryPattern::new();
        assert_eq!(pattern.name(), "WorkflowFactory");
        assert_eq!(pattern.category(), PatternCategory::Creational);

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({
                "type": "data_processing",
                "custom_name": "test_data_processing"
            }),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["workflow_type"], "data_processing");
    }

    #[test]
    fn test_workflow_factory_validation() {
        let pattern = WorkflowFactoryPattern::new();

        // 测试缺少类型 / Test missing type
        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({}),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.validate(&context);
        assert!(result.is_err());

        // 测试不支持的类型 / Test unsupported type
        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({"type": "unsupported_type"}),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.validate(&context);
        assert!(result.is_err());
    }
}
