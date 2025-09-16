//! # 工作流设计模式示例 / Workflow Design Pattern Examples
//!
//! 本模块展示了如何使用各种工作流设计模式来构建复杂的工作流系统。
//! This module demonstrates how to use various workflow design patterns to build complex workflow systems.

// use crate::examples::{ExampleConfig, ExampleResult};
use crate::patterns::*;
use serde_json::json;
use std::collections::HashMap;

/// 运行设计模式示例 / Run design pattern examples
pub async fn run_pattern_examples() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("开始运行设计模式示例 / Starting design pattern examples");

    // 示例1：创建型模式 / Example 1: Creational patterns
    creational_patterns_example().await?;

    // 示例2：结构型模式 / Example 2: Structural patterns
    structural_patterns_example().await?;

    // 示例3：行为型模式 / Example 3: Behavioral patterns
    behavioral_patterns_example().await?;

    // 示例4：并发模式 / Example 4: Concurrent patterns
    concurrent_patterns_example().await?;

    // 示例5：模式组合使用 / Example 5: Pattern combination usage
    pattern_combination_example().await?;

    tracing::info!("设计模式示例运行完成 / Design pattern examples completed");
    Ok(())
}

/// 创建型模式示例 / Creational patterns example
async fn creational_patterns_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行创建型模式示例 / Running creational patterns example");

    // 创建模式工厂 / Create pattern factory
    let factory = WorkflowPatternFactory::new();

    // 获取所有创建型模式 / Get all creational patterns
    let patterns = factory.get_all_patterns();
    let creational_patterns: Vec<_> = patterns
        .iter()
        .filter(|p| p.category == PatternCategory::Creational)
        .collect();

    tracing::info!(
        "找到 {} 个创建型模式 / Found {} creational patterns",
        creational_patterns.len(),
        creational_patterns.len()
    );

    // 测试建造者模式 / Test builder pattern
    let builder_pattern = factory.create_pattern("WorkflowBuilder", PatternCategory::Creational);
    if let Some(pattern) = builder_pattern {
        let context = WorkflowContext {
            workflow_id: "builder_test".to_string(),
            data: json!({
                "builder_name": "test_builder",
                "states": ["start", "process", "end"]
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "建造者模式应用结果 / Builder pattern application result: {:?}",
            result
        );
    }

    // 测试工厂模式 / Test factory pattern
    let factory_pattern = factory.create_pattern("WorkflowFactory", PatternCategory::Creational);
    if let Some(pattern) = factory_pattern {
        let context = WorkflowContext {
            workflow_id: "factory_test".to_string(),
            data: json!({
                "type": "data_processing",
                "custom_name": "my_data_processor"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "工厂模式应用结果 / Factory pattern application result: {:?}",
            result
        );
    }

    // 测试原型模式 / Test prototype pattern
    let prototype_pattern =
        factory.create_pattern("WorkflowPrototype", PatternCategory::Creational);
    if let Some(pattern) = prototype_pattern {
        let context = WorkflowContext {
            workflow_id: "prototype_test".to_string(),
            data: json!({
                "prototype_name": "simple",
                "new_name": "my_simple_workflow"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "原型模式应用结果 / Prototype pattern application result: {:?}",
            result
        );
    }

    // 测试单例模式 / Test singleton pattern
    let singleton_pattern =
        factory.create_pattern("WorkflowSingleton", PatternCategory::Creational);
    if let Some(pattern) = singleton_pattern {
        let context = WorkflowContext {
            workflow_id: "singleton_test".to_string(),
            data: json!({
                "workflow_name": "my_singleton_workflow",
                "workflow_type": "simple"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "单例模式应用结果 / Singleton pattern application result: {:?}",
            result
        );
    }

    Ok(())
}

/// 结构型模式示例 / Structural patterns example
async fn structural_patterns_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行结构型模式示例 / Running structural patterns example");

    // 创建模式工厂 / Create pattern factory
    let factory = WorkflowPatternFactory::new();

    // 获取所有结构型模式 / Get all structural patterns
    let patterns = factory.get_all_patterns();
    let structural_patterns: Vec<_> = patterns
        .iter()
        .filter(|p| p.category == PatternCategory::Structural)
        .collect();

    tracing::info!(
        "找到 {} 个结构型模式 / Found {} structural patterns",
        structural_patterns.len(),
        structural_patterns.len()
    );

    // 测试适配器模式 / Test adapter pattern
    let adapter_pattern = factory.create_pattern("WorkflowAdapter", PatternCategory::Structural);
    if let Some(pattern) = adapter_pattern {
        let context = WorkflowContext {
            workflow_id: "adapter_test".to_string(),
            data: json!({
                "legacy_interface": "old_workflow_api",
                "modern_interface": "new_workflow_api"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "适配器模式应用结果 / Adapter pattern application result: {:?}",
            result
        );
    }

    // 测试桥接模式 / Test bridge pattern
    let bridge_pattern = factory.create_pattern("WorkflowBridge", PatternCategory::Structural);
    if let Some(pattern) = bridge_pattern {
        let context = WorkflowContext {
            workflow_id: "bridge_test".to_string(),
            data: json!({
                "abstraction": "workflow_interface",
                "implementation": "workflow_engine"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "桥接模式应用结果 / Bridge pattern application result: {:?}",
            result
        );
    }

    // 测试组合模式 / Test composite pattern
    let composite_pattern =
        factory.create_pattern("WorkflowComposite", PatternCategory::Structural);
    if let Some(pattern) = composite_pattern {
        let context = WorkflowContext {
            workflow_id: "composite_test".to_string(),
            data: json!({
                "components": ["workflow1", "workflow2", "workflow3"],
                "composition_type": "hierarchical"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "组合模式应用结果 / Composite pattern application result: {:?}",
            result
        );
    }

    // 测试装饰器模式 / Test decorator pattern
    let decorator_pattern =
        factory.create_pattern("WorkflowDecorator", PatternCategory::Structural);
    if let Some(pattern) = decorator_pattern {
        let context = WorkflowContext {
            workflow_id: "decorator_test".to_string(),
            data: json!({
                "base_workflow": "simple_workflow",
                "decorations": ["logging", "monitoring", "caching"]
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "装饰器模式应用结果 / Decorator pattern application result: {:?}",
            result
        );
    }

    Ok(())
}

/// 行为型模式示例 / Behavioral patterns example
async fn behavioral_patterns_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行行为型模式示例 / Running behavioral patterns example");

    // 创建模式工厂 / Create pattern factory
    let factory = WorkflowPatternFactory::new();

    // 获取所有行为型模式 / Get all behavioral patterns
    let patterns = factory.get_all_patterns();
    let behavioral_patterns: Vec<_> = patterns
        .iter()
        .filter(|p| p.category == PatternCategory::Behavioral)
        .collect();

    tracing::info!(
        "找到 {} 个行为型模式 / Found {} behavioral patterns",
        behavioral_patterns.len(),
        behavioral_patterns.len()
    );

    // 测试责任链模式 / Test chain of responsibility pattern
    let chain_pattern =
        factory.create_pattern("WorkflowChainOfResponsibility", PatternCategory::Behavioral);
    if let Some(pattern) = chain_pattern {
        let context = WorkflowContext {
            workflow_id: "chain_test".to_string(),
            data: json!({
                "handlers": ["handler1", "handler2", "handler3"],
                "request_type": "workflow_request"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "责任链模式应用结果 / Chain of responsibility pattern application result: {:?}",
            result
        );
    }

    // 测试命令模式 / Test command pattern
    let command_pattern = factory.create_pattern("WorkflowCommand", PatternCategory::Behavioral);
    if let Some(pattern) = command_pattern {
        let context = WorkflowContext {
            workflow_id: "command_test".to_string(),
            data: json!({
                "command_type": "execute_workflow",
                "parameters": {"workflow_id": "test_workflow"},
                "undoable": true
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "命令模式应用结果 / Command pattern application result: {:?}",
            result
        );
    }

    // 测试观察者模式 / Test observer pattern
    let observer_pattern = factory.create_pattern("WorkflowObserver", PatternCategory::Behavioral);
    if let Some(pattern) = observer_pattern {
        let context = WorkflowContext {
            workflow_id: "observer_test".to_string(),
            data: json!({
                "observers": ["observer1", "observer2", "observer3"],
                "event_type": "workflow_state_change"
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "观察者模式应用结果 / Observer pattern application result: {:?}",
            result
        );
    }

    // 测试状态模式 / Test state pattern
    let state_pattern = factory.create_pattern("WorkflowState", PatternCategory::Behavioral);
    if let Some(pattern) = state_pattern {
        let context = WorkflowContext {
            workflow_id: "state_test".to_string(),
            data: json!({
                "current_state": "processing",
                "available_transitions": ["pending", "processing", "completed"]
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "状态模式应用结果 / State pattern application result: {:?}",
            result
        );
    }

    // 测试策略模式 / Test strategy pattern
    let strategy_pattern = factory.create_pattern("WorkflowStrategy", PatternCategory::Behavioral);
    if let Some(pattern) = strategy_pattern {
        let context = WorkflowContext {
            workflow_id: "strategy_test".to_string(),
            data: json!({
                "strategy_type": "optimized_processing",
                "available_strategies": ["fast", "optimized", "thorough"]
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "策略模式应用结果 / Strategy pattern application result: {:?}",
            result
        );
    }

    Ok(())
}

/// 并发模式示例 / Concurrent patterns example
async fn concurrent_patterns_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行并发模式示例 / Running concurrent patterns example");

    // 创建模式工厂 / Create pattern factory
    let factory = WorkflowPatternFactory::new();

    // 获取所有并发模式 / Get all concurrent patterns
    let patterns = factory.get_all_patterns();
    let concurrent_patterns: Vec<_> = patterns
        .iter()
        .filter(|p| p.category == PatternCategory::Concurrent)
        .collect();

    tracing::info!(
        "找到 {} 个并发模式 / Found {} concurrent patterns",
        concurrent_patterns.len(),
        concurrent_patterns.len()
    );

    // 测试 Actor 模式 / Test actor pattern
    let actor_pattern = factory.create_pattern("WorkflowActor", PatternCategory::Concurrent);
    if let Some(pattern) = actor_pattern {
        let context = WorkflowContext {
            workflow_id: "actor_test".to_string(),
            data: json!({
                "actor_id": "workflow_actor_1",
                "message_queue_size": 100,
                "concurrent_processing": true
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "Actor 模式应用结果 / Actor pattern application result: {:?}",
            result
        );
    }

    // 测试生产者-消费者模式 / Test producer-consumer pattern
    let producer_consumer_pattern =
        factory.create_pattern("WorkflowProducerConsumer", PatternCategory::Concurrent);
    if let Some(pattern) = producer_consumer_pattern {
        let context = WorkflowContext {
            workflow_id: "producer_consumer_test".to_string(),
            data: json!({
                "producer_count": 2,
                "consumer_count": 3,
                "buffer_size": 1000
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "生产者-消费者模式应用结果 / Producer-consumer pattern application result: {:?}",
            result
        );
    }

    // 测试管道模式 / Test pipeline pattern
    let pipeline_pattern = factory.create_pattern("WorkflowPipeline", PatternCategory::Concurrent);
    if let Some(pattern) = pipeline_pattern {
        let context = WorkflowContext {
            workflow_id: "pipeline_test".to_string(),
            data: json!({
                "pipeline_stages": ["input", "process", "validate", "output"],
                "stage_parallelism": 2
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "管道模式应用结果 / Pipeline pattern application result: {:?}",
            result
        );
    }

    // 测试反应器模式 / Test reactor pattern
    let reactor_pattern = factory.create_pattern("WorkflowReactor", PatternCategory::Concurrent);
    if let Some(pattern) = reactor_pattern {
        let context = WorkflowContext {
            workflow_id: "reactor_test".to_string(),
            data: json!({
                "event_handlers": ["handler1", "handler2", "handler3"],
                "event_queue_size": 500
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "反应器模式应用结果 / Reactor pattern application result: {:?}",
            result
        );
    }

    // 测试线程池模式 / Test thread pool pattern
    let thread_pool_pattern =
        factory.create_pattern("WorkflowThreadPool", PatternCategory::Concurrent);
    if let Some(pattern) = thread_pool_pattern {
        let context = WorkflowContext {
            workflow_id: "thread_pool_test".to_string(),
            data: json!({
                "pool_size": 10,
                "active_threads": 7,
                "queued_tasks": 15
            }),
            metadata: HashMap::new(),
        };

        let result = pattern.apply(&context)?;
        tracing::info!(
            "线程池模式应用结果 / Thread pool pattern application result: {:?}",
            result
        );
    }

    Ok(())
}

/// 模式组合使用示例 / Pattern combination usage example
async fn pattern_combination_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行模式组合使用示例 / Running pattern combination usage example");

    // 创建模式工厂 / Create pattern factory
    let factory = WorkflowPatternFactory::new();

    // 组合使用多个模式 / Combine multiple patterns
    let context = WorkflowContext {
        workflow_id: "combination_test".to_string(),
        data: json!({
            "builder_name": "complex_workflow_builder",
            "type": "data_processing",
            "prototype_name": "complex",
            "workflow_name": "my_complex_workflow",
            "strategy_type": "optimized_processing",
            "actor_id": "workflow_actor_1"
        }),
        metadata: HashMap::new(),
    };

    // 按顺序应用多个模式 / Apply multiple patterns in sequence
    let patterns_to_apply = vec![
        ("WorkflowBuilder", PatternCategory::Creational),
        ("WorkflowFactory", PatternCategory::Creational),
        ("WorkflowPrototype", PatternCategory::Creational),
        ("WorkflowSingleton", PatternCategory::Creational),
        ("WorkflowStrategy", PatternCategory::Behavioral),
        ("WorkflowActor", PatternCategory::Concurrent),
    ];

    for (pattern_name, category) in patterns_to_apply {
        if let Some(pattern) = factory.create_pattern(pattern_name, category) {
            let result = pattern.apply(&context)?;
            tracing::info!(
                "模式 {} 应用成功 / Pattern {} applied successfully: {:?}",
                pattern_name,
                pattern_name,
                result
            );
        }
    }

    // 测试模式验证 / Test pattern validation
    let builder_pattern = factory.create_pattern("WorkflowBuilder", PatternCategory::Creational);
    if let Some(pattern) = builder_pattern {
        let validation_result = pattern.validate(&context);
        match validation_result {
            Ok(_) => {
                tracing::info!("模式验证成功 / Pattern validation successful");
            }
            Err(error) => {
                tracing::error!("模式验证失败 / Pattern validation failed: {}", error);
            }
        }
    }

    // 获取所有模式信息 / Get all pattern information
    let all_patterns = factory.get_all_patterns();
    tracing::info!(
        "总共有 {} 个可用模式 / Total of {} available patterns",
        all_patterns.len(),
        all_patterns.len()
    );

    // 按类别统计模式 / Count patterns by category
    let mut category_counts = HashMap::new();
    for pattern in &all_patterns {
        let count = category_counts.entry(pattern.category).or_insert(0);
        *count += 1;
    }

    for (category, count) in category_counts {
        tracing::info!(
            "类别 {:?} 有 {} 个模式 / Category {:?} has {} patterns",
            category,
            count,
            category,
            count
        );
    }

    Ok(())
}

/// 工作流模式性能测试 / Workflow Pattern Performance Test
pub async fn run_pattern_performance_test() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行工作流模式性能测试 / Running workflow pattern performance test");

    let factory = WorkflowPatternFactory::new();
    let patterns = factory.get_all_patterns();

    // 测试每个模式的性能 / Test performance of each pattern
    for pattern_info in &patterns {
        let start_time = std::time::Instant::now();

        if let Some(pattern) = factory.create_pattern(&pattern_info.name, pattern_info.category) {
            let context = WorkflowContext {
                workflow_id: format!("perf_test_{}", pattern_info.name),
                data: json!({"test": "performance"}),
                metadata: HashMap::new(),
            };

            let result = pattern.apply(&context);
            let duration = start_time.elapsed();

            match result {
                Ok(_) => {
                    tracing::info!(
                        "模式 {} 性能测试完成，耗时: {}ms / Pattern {} performance test completed, duration: {}ms",
                        pattern_info.name,
                        duration.as_millis(),
                        pattern_info.name,
                        duration.as_millis()
                    );
                }
                Err(error) => {
                    tracing::error!(
                        "模式 {} 性能测试失败: {} / Pattern {} performance test failed: {}",
                        pattern_info.name,
                        error,
                        pattern_info.name,
                        error
                    );
                }
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_creational_patterns_example() {
        let result = creational_patterns_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_structural_patterns_example() {
        let result = structural_patterns_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_behavioral_patterns_example() {
        let result = behavioral_patterns_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_concurrent_patterns_example() {
        let result = concurrent_patterns_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_pattern_combination_example() {
        let result = pattern_combination_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_pattern_performance_test() {
        let result = run_pattern_performance_test().await;
        assert!(result.is_ok());
    }
}
