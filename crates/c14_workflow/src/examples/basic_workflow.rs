//! # 基础工作流示例 / Basic Workflow Examples
//!
//! 本模块提供了基础工作流系统的使用示例。
//! This module provides usage examples for basic workflow systems.

// use crate::examples::{ExampleConfig, ExampleResult};
use crate::engine::*;
use crate::types::*;
use serde_json::json;
use std::time::Duration;

/// 运行基础工作流示例 / Run basic workflow examples
pub async fn run_basic_workflow_examples() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("开始运行基础工作流示例 / Starting basic workflow examples");

    // 示例1：简单工作流创建和执行 / Example 1: Simple workflow creation and execution
    simple_workflow_example().await?;

    // 示例2：工作流状态管理 / Example 2: Workflow state management
    workflow_state_management_example().await?;

    // 示例3：工作流错误处理 / Example 3: Workflow error handling
    workflow_error_handling_example().await?;

    // 示例4：工作流数据传递 / Example 4: Workflow data passing
    workflow_data_passing_example().await?;

    tracing::info!("基础工作流示例运行完成 / Basic workflow examples completed");
    Ok(())
}

/// 简单工作流示例 / Simple workflow example
async fn simple_workflow_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行简单工作流示例 / Running simple workflow example");

    // 创建工作流定义 / Create workflow definition
    let workflow_def = WorkflowDefinition {
        name: "simple_workflow".to_string(),
        description: Some("简单工作流示例 / Simple workflow example".to_string()),
        version: "1.0.0".to_string(),
        states: vec![
            "start".to_string(),
            "processing".to_string(),
            "completed".to_string(),
        ],
        transitions: vec![
            StateTransition {
                from_state: "start".to_string(),
                to_state: "processing".to_string(),
                condition: Some("data_ready".to_string()),
                actions: vec!["start_processing".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "processing".to_string(),
                to_state: "completed".to_string(),
                condition: Some("processing_done".to_string()),
                actions: vec!["complete_processing".to_string()],
                timeout: None,
            },
        ],
        initial_state: "start".to_string(),
        final_states: vec!["completed".to_string()],
        metadata: {
            let mut meta = std::collections::HashMap::new();
            meta.insert("author".to_string(), json!("Rust Workflow Team"));
            meta.insert("created_at".to_string(), json!("2025-01-01"));
            meta
        },
    };

    // 创建工作流引擎 / Create workflow engine
    let engine = WorkflowEngine::new();

    // 注册工作流 / Register workflow
    engine
        .register_workflow("simple_workflow".to_string(), workflow_def)
        .await?;

    // 创建初始数据 / Create initial data
    let initial_data = WorkflowData {
        content: json!({
            "id": "workflow_data_1",
            "input": "Hello, Workflow!",
            "processed": false
        }),
        version: "1.0".to_string(),
        metadata: {
            let mut meta = std::collections::HashMap::new();
            meta.insert("source".to_string(), json!("example"));
            meta.insert("priority".to_string(), json!("normal"));
            meta
        },
        created_at: std::time::Instant::now(),
        updated_at: std::time::Instant::now(),
    };

    // 启动工作流实例 / Start workflow instance
    let instance_id = engine
        .start_workflow("simple_workflow", initial_data)
        .await?;
    tracing::info!(
        "工作流实例已启动 / Workflow instance started: {}",
        instance_id
    );

    // 模拟工作流执行 / Simulate workflow execution
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 获取工作流状态 / Get workflow state
    let state = engine.get_workflow_state(&instance_id).await?;
    tracing::info!("工作流状态 / Workflow state: {:?}", state);

    Ok(())
}

/// 工作流状态管理示例 / Workflow state management example
async fn workflow_state_management_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行工作流状态管理示例 / Running workflow state management example");

    // 创建状态管理工作流 / Create state management workflow
    let workflow_def = WorkflowDefinition {
        name: "state_management_workflow".to_string(),
        description: Some("状态管理工作流示例 / State management workflow example".to_string()),
        version: "1.0.0".to_string(),
        states: vec![
            "initial".to_string(),
            "validating".to_string(),
            "processing".to_string(),
            "validating_result".to_string(),
            "completed".to_string(),
            "failed".to_string(),
        ],
        transitions: vec![
            StateTransition {
                from_state: "initial".to_string(),
                to_state: "validating".to_string(),
                condition: Some("start_validation".to_string()),
                actions: vec!["validate_input".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "validating".to_string(),
                to_state: "processing".to_string(),
                condition: Some("validation_success".to_string()),
                actions: vec!["start_processing".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "validating".to_string(),
                to_state: "failed".to_string(),
                condition: Some("validation_failed".to_string()),
                actions: vec!["handle_validation_error".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "processing".to_string(),
                to_state: "validating_result".to_string(),
                condition: Some("processing_complete".to_string()),
                actions: vec!["validate_result".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "validating_result".to_string(),
                to_state: "completed".to_string(),
                condition: Some("result_valid".to_string()),
                actions: vec!["complete_workflow".to_string()],
                timeout: None,
            },
        ],
        initial_state: "initial".to_string(),
        final_states: vec!["completed".to_string(), "failed".to_string()],
        metadata: {
            let mut meta = std::collections::HashMap::new();
            meta.insert("complexity".to_string(), json!("medium"));
            meta.insert("requires_validation".to_string(), json!(true));
            meta
        },
    };

    let engine = WorkflowEngine::new();
    engine
        .register_workflow("state_management_workflow".to_string(), workflow_def)
        .await?;

    // 创建测试数据 / Create test data
    let test_data = WorkflowData {
        content: json!({
            "id": "state_test_data",
            "input_value": 42,
            "validation_rules": ["positive", "integer"],
            "processing_type": "calculation"
        }),
        version: "1.0".to_string(),
        metadata: {
            let mut meta = std::collections::HashMap::new();
            meta.insert("test_case".to_string(), json!("state_management"));
            meta.insert("expected_result".to_string(), json!("success"));
            meta
        },
        created_at: std::time::Instant::now(),
        updated_at: std::time::Instant::now(),
    };

    // 启动工作流 / Start workflow
    let instance_id = engine
        .start_workflow("state_management_workflow", test_data)
        .await?;

    // 模拟状态转换 / Simulate state transitions
    let states = vec![
        "initial",
        "validating",
        "processing",
        "validating_result",
        "completed",
    ];
    for _state in states {
        tokio::time::sleep(Duration::from_millis(50)).await;
        let current_state = engine.get_workflow_state(&instance_id).await?;
        tracing::info!("当前状态 / Current state: {}", current_state);
    }

    Ok(())
}

/// 工作流错误处理示例 / Workflow error handling example
async fn workflow_error_handling_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行工作流错误处理示例 / Running workflow error handling example");

    // 创建错误处理工作流 / Create error handling workflow
    let workflow_def = WorkflowDefinition {
        name: "error_handling_workflow".to_string(),
        description: Some("错误处理工作流示例 / Error handling workflow example".to_string()),
        version: "1.0.0".to_string(),
        states: vec![
            "start".to_string(),
            "processing".to_string(),
            "error_handling".to_string(),
            "retry".to_string(),
            "completed".to_string(),
            "failed".to_string(),
        ],
        transitions: vec![
            StateTransition {
                from_state: "start".to_string(),
                to_state: "processing".to_string(),
                condition: Some("start_processing".to_string()),
                actions: vec!["begin_processing".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "processing".to_string(),
                to_state: "error_handling".to_string(),
                condition: Some("error_occurred".to_string()),
                actions: vec!["handle_error".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "error_handling".to_string(),
                to_state: "retry".to_string(),
                condition: Some("retry_possible".to_string()),
                actions: vec!["retry_processing".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "error_handling".to_string(),
                to_state: "failed".to_string(),
                condition: Some("retry_exhausted".to_string()),
                actions: vec!["fail_workflow".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "retry".to_string(),
                to_state: "processing".to_string(),
                condition: Some("retry_ready".to_string()),
                actions: vec!["resume_processing".to_string()],
                timeout: None,
            },
            StateTransition {
                from_state: "processing".to_string(),
                to_state: "completed".to_string(),
                condition: Some("processing_success".to_string()),
                actions: vec!["complete_workflow".to_string()],
                timeout: None,
            },
        ],
        initial_state: "start".to_string(),
        final_states: vec!["completed".to_string(), "failed".to_string()],
        metadata: {
            let mut meta = std::collections::HashMap::new();
            meta.insert("error_handling".to_string(), json!("comprehensive"));
            meta.insert("retry_count".to_string(), json!(3));
            meta
        },
    };

    let engine = WorkflowEngine::new();
    engine
        .register_workflow("error_handling_workflow".to_string(), workflow_def)
        .await?;

    // 创建会触发错误的数据 / Create data that will trigger errors
    let error_data = WorkflowData {
        content: json!({
            "id": "error_test_data",
            "operation": "risky_operation",
            "retry_count": 0,
            "max_retries": 3,
            "error_probability": 0.7
        }),
        version: "1.0".to_string(),
        metadata: {
            let mut meta = std::collections::HashMap::new();
            meta.insert("test_type".to_string(), json!("error_handling"));
            meta.insert("expected_behavior".to_string(), json!("retry_and_recover"));
            meta
        },
        created_at: std::time::Instant::now(),
        updated_at: std::time::Instant::now(),
    };

    // 启动工作流 / Start workflow
    let instance_id = engine
        .start_workflow("error_handling_workflow", error_data)
        .await?;

    // 模拟错误处理流程 / Simulate error handling flow
    let error_states = vec![
        "start",
        "processing",
        "error_handling",
        "retry",
        "processing",
        "completed",
    ];
    for _state in error_states {
        tokio::time::sleep(Duration::from_millis(100)).await;
        let current_state = engine.get_workflow_state(&instance_id).await?;
        tracing::info!("错误处理状态 / Error handling state: {}", current_state);
    }

    Ok(())
}

/// 工作流数据传递示例 / Workflow data passing example
async fn workflow_data_passing_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行工作流数据传递示例 / Running workflow data passing example");

    // 创建数据传递工作流 / Create data passing workflow
    let workflow_def = WorkflowDefinition {
        name: "data_passing_workflow".to_string(),
        description: Some("数据传递工作流示例 / Data passing workflow example".to_string()),
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
            let mut meta = std::collections::HashMap::new();
            meta.insert("data_flow".to_string(), json!("linear"));
            meta.insert("transformation_steps".to_string(), json!(2));
            meta
        },
    };

    let engine = WorkflowEngine::new();
    engine
        .register_workflow("data_passing_workflow".to_string(), workflow_def)
        .await?;

    // 创建复杂数据 / Create complex data
    let complex_data = WorkflowData {
        content: json!({
            "id": "data_passing_test",
            "raw_data": [1, 2, 3, 4, 5],
            "transformation_rules": {
                "multiply_by": 2,
                "add_offset": 10
            },
            "validation_rules": {
                "min_value": 10,
                "max_value": 30
            },
            "output_format": "json"
        }),
        version: "1.0".to_string(),
        metadata: {
            let mut meta = std::collections::HashMap::new();
            meta.insert("data_type".to_string(), json!("numeric_array"));
            meta.insert("processing_mode".to_string(), json!("batch"));
            meta
        },
        created_at: std::time::Instant::now(),
        updated_at: std::time::Instant::now(),
    };

    // 启动工作流 / Start workflow
    let instance_id = engine
        .start_workflow("data_passing_workflow", complex_data)
        .await?;

    // 模拟数据传递流程 / Simulate data passing flow
    let data_states = vec!["input", "transform", "validate", "output"];
    for state in data_states {
        tokio::time::sleep(Duration::from_millis(75)).await;
        let current_state = engine.get_workflow_state(&instance_id).await?;
        tracing::info!("数据传递状态 / Data passing state: {}", current_state);

        // 模拟数据转换 / Simulate data transformation
        if state == "transform" {
            tracing::info!("执行数据转换 / Executing data transformation");
        } else if state == "validate" {
            tracing::info!("执行数据验证 / Executing data validation");
        } else if state == "output" {
            tracing::info!("输出最终数据 / Outputting final data");
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_simple_workflow_example() {
        let result = simple_workflow_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_workflow_state_management_example() {
        let result = workflow_state_management_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_workflow_error_handling_example() {
        let result = workflow_error_handling_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_workflow_data_passing_example() {
        let result = workflow_data_passing_example().await;
        assert!(result.is_ok());
    }
}
