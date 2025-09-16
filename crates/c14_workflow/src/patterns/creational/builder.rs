//! # 工作流建造者模式 / Workflow Builder Pattern
//!
//! 本模块实现了工作流建造者模式，提供逐步构建复杂工作流的能力。
//! This module implements the workflow builder pattern, providing the ability to build complex workflows step by step.

use crate::patterns::{PatternCategory, WorkflowContext, WorkflowPattern, WorkflowResult};
use crate::types::{StateTransition, WorkflowDefinition};
use serde_json::json;

/// 工作流建造者 / Workflow Builder
pub struct WorkflowBuilder {
    name: String,
    description: Option<String>,
    version: String,
    states: Vec<String>,
    transitions: Vec<StateTransition>,
    initial_state: Option<String>,
    final_states: Vec<String>,
    metadata: std::collections::HashMap<String, serde_json::Value>,
}

impl WorkflowBuilder {
    /// 创建新的工作流建造者 / Create new workflow builder
    pub fn new(name: String) -> Self {
        Self {
            name,
            description: None,
            version: "1.0.0".to_string(),
            states: Vec::new(),
            transitions: Vec::new(),
            initial_state: None,
            final_states: Vec::new(),
            metadata: std::collections::HashMap::new(),
        }
    }

    /// 设置描述 / Set description
    pub fn description(mut self, description: String) -> Self {
        self.description = Some(description);
        self
    }

    /// 设置版本 / Set version
    pub fn version(mut self, version: String) -> Self {
        self.version = version;
        self
    }

    /// 添加状态 / Add state
    pub fn add_state(mut self, state: String) -> Self {
        self.states.push(state);
        self
    }

    /// 添加多个状态 / Add multiple states
    pub fn add_states(mut self, states: Vec<String>) -> Self {
        self.states.extend(states);
        self
    }

    /// 添加转换 / Add transition
    pub fn add_transition(mut self, transition: StateTransition) -> Self {
        self.transitions.push(transition);
        self
    }

    /// 设置初始状态 / Set initial state
    pub fn initial_state(mut self, state: String) -> Self {
        self.initial_state = Some(state);
        self
    }

    /// 添加最终状态 / Add final state
    pub fn add_final_state(mut self, state: String) -> Self {
        self.final_states.push(state);
        self
    }

    /// 设置元数据 / Set metadata
    pub fn metadata(
        mut self,
        metadata: std::collections::HashMap<String, serde_json::Value>,
    ) -> Self {
        self.metadata = metadata;
        self
    }

    /// 构建工作流定义 / Build workflow definition
    pub fn build(self) -> Result<WorkflowDefinition, String> {
        if self.states.is_empty() {
            return Err(
                "工作流必须至少有一个状态 / Workflow must have at least one state".to_string(),
            );
        }

        let initial_state = self
            .initial_state
            .ok_or("必须设置初始状态 / Initial state must be set")?;

        if !self.states.contains(&initial_state) {
            return Err(
                "初始状态必须在状态列表中 / Initial state must be in states list".to_string(),
            );
        }

        for final_state in &self.final_states {
            if !self.states.contains(final_state) {
                return Err(format!(
                    "最终状态 {} 必须在状态列表中 / Final state {} must be in states list",
                    final_state, final_state
                ));
            }
        }

        Ok(WorkflowDefinition {
            name: self.name,
            description: self.description,
            version: self.version,
            states: self.states,
            transitions: self.transitions,
            initial_state,
            final_states: self.final_states,
            metadata: self.metadata,
        })
    }
}

/// 工作流建造者模式实现 / Workflow Builder Pattern Implementation
pub struct WorkflowBuilderPattern {
    name: String,
}

impl WorkflowBuilderPattern {
    pub fn new() -> Self {
        Self {
            name: "WorkflowBuilder".to_string(),
        }
    }
}

impl WorkflowPattern for WorkflowBuilderPattern {
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

        // 从上下文数据中提取建造者参数 / Extract builder parameters from context data
        let builder_name = context
            .data
            .get("builder_name")
            .and_then(|v| v.as_str())
            .unwrap_or("default_workflow");

        let states = context
            .data
            .get("states")
            .and_then(|v| v.as_array())
            .map(|arr| {
                arr.iter()
                    .filter_map(|v| v.as_str().map(|s| s.to_string()))
                    .collect()
            })
            .unwrap_or_else(|| vec!["start".to_string(), "end".to_string()]);

        // 使用建造者模式构建工作流 / Use builder pattern to build workflow
        let workflow_def = WorkflowBuilder::new(builder_name.to_string())
            .description(
                "使用建造者模式构建的工作流 / Workflow built using builder pattern".to_string(),
            )
            .add_states(states)
            .initial_state("start".to_string())
            .add_final_state("end".to_string())
            .metadata({
                let mut meta = std::collections::HashMap::new();
                meta.insert("built_with".to_string(), json!("WorkflowBuilder"));
                meta.insert("pattern".to_string(), json!("Builder"));
                meta
            })
            .build()?;

        let result = WorkflowResult {
            success: true,
            data: json!({
                "pattern": "WorkflowBuilder",
                "workflow_id": context.workflow_id,
                "built_workflow": workflow_def,
                "components_built": ["states", "transitions", "metadata"]
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

        if context.data.get("builder_name").is_none() {
            return Err("建造者名称不能为空 / Builder name cannot be empty".to_string());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_workflow_builder() {
        let workflow_def = WorkflowBuilder::new("test_workflow".to_string())
            .description("测试工作流 / Test workflow".to_string())
            .version("1.0.0".to_string())
            .add_state("start".to_string())
            .add_state("processing".to_string())
            .add_state("end".to_string())
            .initial_state("start".to_string())
            .add_final_state("end".to_string())
            .metadata({
                let mut meta = std::collections::HashMap::new();
                meta.insert("test".to_string(), json!(true));
                meta
            })
            .build();

        assert!(workflow_def.is_ok());
        let def = workflow_def.unwrap();
        assert_eq!(def.name, "test_workflow");
        assert_eq!(def.states.len(), 3);
        assert_eq!(def.initial_state, "start");
        assert_eq!(def.final_states.len(), 1);
    }

    #[test]
    fn test_workflow_builder_validation() {
        // 测试缺少初始状态 / Test missing initial state
        let result = WorkflowBuilder::new("test".to_string())
            .add_state("start".to_string())
            .build();

        assert!(result.is_err());
        assert!(result.unwrap_err().contains("初始状态"));
    }

    #[test]
    fn test_workflow_builder_pattern() {
        let pattern = WorkflowBuilderPattern::new();
        assert_eq!(pattern.name(), "WorkflowBuilder");
        assert_eq!(pattern.category(), PatternCategory::Creational);

        let context = WorkflowContext {
            workflow_id: "test_workflow".to_string(),
            data: json!({
                "builder_name": "test_builder",
                "states": ["start", "end"]
            }),
            metadata: std::collections::HashMap::new(),
        };

        let result = pattern.apply(&context).unwrap();
        assert!(result.success);
        assert_eq!(result.data["pattern"], "WorkflowBuilder");
    }
}
