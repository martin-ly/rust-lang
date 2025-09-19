//! 异步生态系统全面测试套件
//! 
//! 本测试套件涵盖了所有异步运行时的功能测试，
//! 包括std、tokio、async-std、smol等库的测试

use std::sync::Arc;
use std::time::Duration;
use anyhow::Result;
use tokio::time::sleep;
use tokio::sync::{Mutex, Semaphore};
use c06_async::async_ecosystem_comprehensive::*;
use c06_async::async_integration_framework::*;
use c06_async::async_runtime_integration_framework_simple::{
    AsyncTask, ExampleTask, TaskPriority, RuntimeConfig, 
    SimpleAsyncRuntimeFramework, AsyncSyncConversionService, 
    AggregationCompositionService, DataProcessingComponent as SimpleDataProcessingComponent,
    AsyncRuntimeType, RuntimeMetrics, demonstrate_simple_async_runtime_framework
};

/// 测试异步运行时分析器
#[tokio::test]
async fn test_async_runtime_analyzer() {
    let analyzer = AsyncRuntimeAnalyzer::new();
    
    // 测试获取运行时分析
    assert!(analyzer.get_runtime_analysis("tokio").is_some());
    assert!(analyzer.get_runtime_analysis("async-std").is_some());
    assert!(analyzer.get_runtime_analysis("smol").is_some());
    assert!(analyzer.get_runtime_analysis("std").is_some());
    
    // 测试运行时比较
    let comparison = analyzer.compare_runtimes("tokio", "async-std");
    assert!(comparison.is_some());
    
    let comparison = comparison.unwrap();
    assert_eq!(comparison.runtime1.runtime_name, "tokio");
    assert_eq!(comparison.runtime2.runtime_name, "async-std");
}

/// 测试异步集成模式
#[tokio::test]
async fn test_async_integration_patterns() {
    let patterns = AsyncIntegrationPatterns::new(3);
    
    // 测试运行时适配器模式
    assert!(patterns.runtime_adapter_pattern().await.is_ok());
    
    // 测试任务组合模式
    assert!(patterns.task_composition_pattern().await.is_ok());
    
    // 测试运行时抽象模式
    assert!(patterns.runtime_abstraction_pattern().await.is_ok());
    
    // 测试异步同步转换模式
    assert!(patterns.async_sync_conversion_pattern().await.is_ok());
    
    // 测试聚合组合模式
    assert!(patterns.aggregation_composition_pattern().await.is_ok());
}

/// 测试异步运行时共性分析器
#[tokio::test]
async fn test_async_commonality_analyzer() {
    let analyzer = AsyncCommonalityAnalyzer::new();
    
    // 测试获取运行时共性
    assert!(analyzer.get_runtime_commonality("tokio").is_some());
    assert!(analyzer.get_runtime_commonality("async-std").is_some());
    assert!(analyzer.get_runtime_commonality("smol").is_some());
    assert!(analyzer.get_runtime_commonality("std").is_some());
    
    // 测试分析共同特性
    let common_features = analyzer.analyze_common_features();
    assert!(!common_features.is_empty());
    
    // 测试分析共同模式
    let common_patterns = analyzer.analyze_common_patterns();
    assert!(!common_patterns.is_empty());
}

/// 测试异步同步转换框架
#[tokio::test]
async fn test_async_sync_conversion_framework() {
    let framework = AsyncSyncConversionFramework::new(4);
    
    // 测试混合转换
    assert!(framework.hybrid_conversion().await.is_ok());
    
    // 测试转换缓存
    let cached_result = framework.conversion_with_caching("test_key", || {
        Ok("cached_operation_result".to_string())
    }).await;
    assert!(cached_result.is_ok());
    assert_eq!(cached_result.unwrap(), "cached_operation_result");
}

/// 测试聚合组合设计模式框架
#[tokio::test]
async fn test_aggregation_composition_framework() {
    let framework = AggregationCompositionFramework::new();
    
    // 注册组件
    let component1 = Box::new(DataProcessingComponent::new("processor1", 10));
    let component2 = Box::new(DataProcessingComponent::new("processor2", 15));
    
    assert!(framework.register_component(component1).await.is_ok());
    assert!(framework.register_component(component2).await.is_ok());
    
    // 测试顺序聚合
    let sequential_results = framework.sequential_aggregation(
        vec!["processor1".to_string(), "processor2".to_string()],
        "input_data"
    ).await;
    assert!(sequential_results.is_ok());
    
    // 测试并行聚合
    let parallel_results = framework.parallel_aggregation(
        vec!["processor1".to_string(), "processor2".to_string()],
        "input_data"
    ).await;
    assert!(parallel_results.is_ok());
    
    // 测试管道聚合
    let pipeline_results = framework.pipeline_aggregation(
        vec![
            vec!["processor1".to_string()],
            vec!["processor2".to_string()],
        ],
        "pipeline_input"
    ).await;
    assert!(pipeline_results.is_ok());
    
    // 测试扇出聚合
    let fan_out_results = framework.fan_out_aggregation(
        "processor1",
        vec!["input1".to_string(), "input2".to_string()]
    ).await;
    assert!(fan_out_results.is_ok());
    
    // 测试扇入聚合
    let fan_in_result = framework.fan_in_aggregation(
        vec!["processor1".to_string(), "processor2".to_string()],
        "fan_in_input"
    ).await;
    assert!(fan_in_result.is_ok());
}

/// 测试简化的异步运行时框架
#[tokio::test]
async fn test_simple_async_runtime_framework() {
    let config = RuntimeConfig::default();
    let framework = SimpleAsyncRuntimeFramework::new(config);
    
    // 测试执行单个任务
    let task = Box::new(ExampleTask::new("test_task", TaskPriority::Normal, 10));
    let result = framework.execute_task(task).await;
    assert!(result.is_ok());
    assert!(result.unwrap().contains("test_task_completed"));
    
    // 测试执行批量任务
    let batch_tasks: Vec<Box<dyn AsyncTask>> = vec![
        Box::new(ExampleTask::new("batch_task_1", TaskPriority::Normal, 5)),
        Box::new(ExampleTask::new("batch_task_2", TaskPriority::High, 5)),
    ];
    
    let batch_results = framework.execute_batch(batch_tasks).await;
    assert!(batch_results.is_ok());
    assert_eq!(batch_results.unwrap().len(), 2);
    
    // 测试获取性能指标
    let metrics = framework.get_metrics().await;
    assert!(metrics.task_count > 0);
    
    // 测试健康检查
    let health_status = framework.health_check().await;
    assert!(health_status.is_ok());
    assert!(health_status.unwrap());
}

/// 测试异步同步转换服务
#[tokio::test]
async fn test_async_sync_conversion_service() {
    let service = AsyncSyncConversionService::new(2);
    
    // 测试混合转换
    let (async_result, sync_result) = service.hybrid_conversion().await.unwrap();
    assert_eq!(async_result, "async_result");
    assert_eq!(sync_result, "sync_result");
    
    // 测试异步到同步转换
    let async_to_sync_result = service.async_to_sync(async {
        sleep(Duration::from_millis(5)).await;
        Ok("async_to_sync_result".to_string())
    }).await;
    assert!(async_to_sync_result.is_ok());
    assert_eq!(async_to_sync_result.unwrap(), "async_to_sync_result");
    
    // 测试同步到异步转换
    let sync_to_async_result = service.sync_to_async(|| {
        std::thread::sleep(Duration::from_millis(5));
        Ok("sync_to_async_result".to_string())
    }).await;
    assert!(sync_to_async_result.is_ok());
    assert_eq!(sync_to_async_result.unwrap(), "sync_to_async_result");
}

/// 测试聚合组合服务
#[tokio::test]
async fn test_aggregation_composition_service() {
    let service = AggregationCompositionService::new();
    
    // 注册组件
    let component1 = Box::new(SimpleDataProcessingComponent::new("processor1", 5));
    let component2 = Box::new(SimpleDataProcessingComponent::new("processor2", 5));
    
    assert!(service.register_component(component1).await.is_ok());
    assert!(service.register_component(component2).await.is_ok());
    
    // 测试顺序聚合
    let sequential_results = service.sequential_aggregation(
        vec!["processor1".to_string(), "processor2".to_string()],
        "input_data"
    ).await;
    assert!(sequential_results.is_ok());
    let results = sequential_results.unwrap();
    assert_eq!(results.len(), 2);
    assert!(results[0].contains("processor1_processed_input_data"));
    assert!(results[1].contains("processor2_processed_"));
    
    // 测试并行聚合
    let parallel_results = service.parallel_aggregation(
        vec!["processor1".to_string(), "processor2".to_string()],
        "input_data"
    ).await;
    assert!(parallel_results.is_ok());
    let results = parallel_results.unwrap();
    assert_eq!(results.len(), 2);
}

/// 测试数据源
#[tokio::test]
async fn test_data_source() {
    let data_source = DataSource::new("test_source", vec![1, 2, 3, 4, 5]);
    
    let data = data_source.get_data().await.unwrap();
    assert_eq!(data, vec![1, 2, 3, 4, 5]);
}

/// 测试抽象异步操作
#[tokio::test]
async fn test_abstract_async_operation() {
    let operation = AbstractAsyncOperation::new("test_operation", Duration::from_millis(10));
    
    let result = operation.execute().await;
    assert_eq!(result, "test_operation_completed");
}

/// 测试任务优先级
#[tokio::test]
async fn test_task_priority() {
    assert!(TaskPriority::Critical > TaskPriority::High);
    assert!(TaskPriority::High > TaskPriority::Normal);
    assert!(TaskPriority::Normal > TaskPriority::Low);
}

/// 测试运行时类型
#[tokio::test]
async fn test_runtime_type() {
    let runtime_types = vec![
        AsyncRuntimeType::Std,
        AsyncRuntimeType::Tokio,
        AsyncRuntimeType::AsyncStd,
        AsyncRuntimeType::Smol,
    ];
    
    for runtime_type in runtime_types {
        match runtime_type {
            AsyncRuntimeType::Std => assert_eq!(runtime_type, AsyncRuntimeType::Std),
            AsyncRuntimeType::Tokio => assert_eq!(runtime_type, AsyncRuntimeType::Tokio),
            AsyncRuntimeType::AsyncStd => assert_eq!(runtime_type, AsyncRuntimeType::AsyncStd),
            AsyncRuntimeType::Smol => assert_eq!(runtime_type, AsyncRuntimeType::Smol),
        }
    }
}

/// 测试性能指标
#[tokio::test]
async fn test_runtime_metrics() {
    let mut metrics = RuntimeMetrics::default();
    
    metrics.task_count = 10;
    metrics.success_count = 8;
    metrics.failure_count = 2;
    metrics.average_execution_time = Duration::from_millis(50);
    
    assert_eq!(metrics.task_count, 10);
    assert_eq!(metrics.success_count, 8);
    assert_eq!(metrics.failure_count, 2);
    assert_eq!(metrics.average_execution_time, Duration::from_millis(50));
}

/// 测试运行时配置
#[tokio::test]
async fn test_runtime_config() {
    let config = RuntimeConfig {
        runtime_type: AsyncRuntimeType::Tokio,
        max_concurrent_tasks: 50,
        timeout_duration: Duration::from_secs(60),
        enable_monitoring: true,
    };
    
    assert_eq!(config.runtime_type, AsyncRuntimeType::Tokio);
    assert_eq!(config.max_concurrent_tasks, 50);
    assert_eq!(config.timeout_duration, Duration::from_secs(60));
    assert!(config.enable_monitoring);
}

/// 测试并发安全性
#[tokio::test]
async fn test_concurrency_safety() {
    let semaphore = Arc::new(Semaphore::new(3));
    let counter = Arc::new(Mutex::new(0));
    
    let mut handles = Vec::new();
    
    for i in 0..10 {
        let semaphore = Arc::clone(&semaphore);
        let counter = Arc::clone(&counter);
        
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            sleep(Duration::from_millis(10)).await;
            
            let mut count = counter.lock().await;
            *count += 1;
            
            println!("任务 {} 完成，当前计数: {}", i, *count);
        });
        
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        handle.await.unwrap();
    }
    
    let final_count = *counter.lock().await;
    assert_eq!(final_count, 10);
}

/// 测试错误处理
#[tokio::test]
async fn test_error_handling() {
    let framework = SimpleAsyncRuntimeFramework::new(RuntimeConfig::default());
    
    // 创建一个会失败的任务
    let failing_task = Box::new(FailingTask::new("failing_task", TaskPriority::Normal, 10));
    
    let result = framework.execute_task(failing_task).await;
    assert!(result.is_err());
    
    // 验证指标更新
    let metrics = framework.get_metrics().await;
    assert!(metrics.failure_count > 0);
}

/// 失败任务实现
struct FailingTask {
    name: String,
    priority: TaskPriority,
    execution_delay: Duration,
}

impl FailingTask {
    fn new(name: &str, priority: TaskPriority, delay_ms: u64) -> Self {
        Self {
            name: name.to_string(),
            priority,
            execution_delay: Duration::from_millis(delay_ms),
        }
    }
}

#[async_trait::async_trait]
impl AsyncTask for FailingTask {
    async fn execute(&self) -> Result<String> {
        sleep(self.execution_delay).await;
        Err(anyhow::anyhow!("任务执行失败: {}", self.name))
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
    
    fn get_priority(&self) -> TaskPriority {
        self.priority
    }
    
    fn get_timeout(&self) -> Duration {
        Duration::from_secs(30)
    }
}

/// 集成测试：完整的异步生态系统演示
#[tokio::test]
async fn test_complete_async_ecosystem_demo() {
    // 测试异步生态系统全面演示
    let result = demonstrate_async_ecosystem_comprehensive().await;
    assert!(result.is_ok());
    
    // 测试异步集成框架演示
    let result = demonstrate_async_integration_framework().await;
    assert!(result.is_ok());
    
    // 测试简化异步运行时框架演示
    let result = demonstrate_simple_async_runtime_framework().await;
    assert!(result.is_ok());
}

/// 压力测试：大量并发任务
#[tokio::test]
async fn test_high_concurrency() {
    let framework = SimpleAsyncRuntimeFramework::new(RuntimeConfig {
        max_concurrent_tasks: 100,
        ..Default::default()
    });
    
    let mut tasks: Vec<Box<dyn AsyncTask>> = Vec::new();
    
    // 创建100个并发任务
    for i in 0..100 {
        let task: Box<dyn AsyncTask> = Box::new(ExampleTask::new(
            &format!("concurrent_task_{}", i),
            TaskPriority::Normal,
            5
        ));
        tasks.push(task);
    }
    
    let start = std::time::Instant::now();
    let results = framework.execute_batch(tasks).await;
    let elapsed = start.elapsed();
    
    assert!(results.is_ok());
    assert_eq!(results.unwrap().len(), 100);
    
    // 验证性能：100个任务应该在合理时间内完成
    assert!(elapsed < Duration::from_secs(10));
    
    println!("100个并发任务完成时间: {:?}", elapsed);
}

/// 内存泄漏测试
#[tokio::test]
async fn test_memory_leak_prevention() {
    let framework = SimpleAsyncRuntimeFramework::new(RuntimeConfig::default());
    
    // 执行大量任务，检查内存使用
    for _ in 0..1000 {
        let task = Box::new(ExampleTask::new("memory_test_task", TaskPriority::Low, 1));
        let _ = framework.execute_task(task).await;
    }
    
    // 获取最终指标
    let metrics = framework.get_metrics().await;
    assert_eq!(metrics.task_count, 1000);
    assert_eq!(metrics.success_count, 1000);
    assert_eq!(metrics.failure_count, 0);
    
    println!("内存泄漏测试完成，处理了 {} 个任务", metrics.task_count);
}
