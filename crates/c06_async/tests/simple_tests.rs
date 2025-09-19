//! 简化的测试套件
//! 
//! 专注于核心功能的测试，避免复杂的依赖问题

use std::time::Duration;
use anyhow::Result;
use tokio::time::sleep;
use c06_async::async_runtime_integration_framework_simple::*;

/// 测试简化的异步运行时框架
#[tokio::test]
async fn test_simple_framework() {
    let config = RuntimeConfig::default();
    let framework = SimpleAsyncRuntimeFramework::new(config);
    
    let task: Box<dyn AsyncTask> = Box::new(ExampleTask::new("test_task", TaskPriority::Normal, 10));
    let result = framework.execute_task(task).await.unwrap();
    assert!(result.contains("test_task_completed"));
}

/// 测试异步同步转换服务
#[tokio::test]
async fn test_async_sync_conversion() {
    let service = AsyncSyncConversionService::new(2);
    let (async_result, sync_result) = service.hybrid_conversion().await.unwrap();
    assert_eq!(async_result, "async_result");
    assert_eq!(sync_result, "sync_result");
}

/// 测试聚合组合服务
#[tokio::test]
async fn test_aggregation_composition() {
    let service = AggregationCompositionService::new();
    let component = Box::new(DataProcessingComponent::new("test", 1));
    service.register_component(component).await.unwrap();
    
    let results = service.parallel_aggregation(
        vec!["test".to_string()],
        "input"
    ).await.unwrap();
    
    assert_eq!(results.len(), 1);
    assert!(results[0].contains("test_processed_input"));
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

/// 测试健康检查
#[tokio::test]
async fn test_health_check() {
    let config = RuntimeConfig::default();
    let framework = SimpleAsyncRuntimeFramework::new(config);
    
    let is_healthy = framework.health_check().await.unwrap();
    assert!(is_healthy);
}

/// 测试批量任务执行
#[tokio::test]
async fn test_batch_execution() {
    let config = RuntimeConfig::default();
    let framework = SimpleAsyncRuntimeFramework::new(config);
    
    let batch_tasks: Vec<Box<dyn AsyncTask>> = vec![
        Box::new(ExampleTask::new("task1", TaskPriority::Normal, 5)),
        Box::new(ExampleTask::new("task2", TaskPriority::High, 5)),
        Box::new(ExampleTask::new("task3", TaskPriority::Low, 5)),
    ];
    
    let results = framework.execute_batch(batch_tasks).await.unwrap();
    assert_eq!(results.len(), 3);
    
    for result in results {
        assert!(result.contains("completed"));
    }
}

/// 测试性能监控
#[tokio::test]
async fn test_performance_monitoring() {
    let config = RuntimeConfig::default();
    let framework = SimpleAsyncRuntimeFramework::new(config);
    
    // 执行一些任务
    for i in 0..5 {
        let task: Box<dyn AsyncTask> = Box::new(ExampleTask::new(
            &format!("monitor_task_{}", i),
            TaskPriority::Normal,
            1
        ));
        let _ = framework.execute_task(task).await;
    }
    
    let metrics = framework.get_metrics().await;
    assert_eq!(metrics.task_count, 5);
    assert_eq!(metrics.success_count, 5);
    assert_eq!(metrics.failure_count, 0);
}

/// 测试错误处理
#[tokio::test]
async fn test_error_handling() {
    let config = RuntimeConfig::default();
    let framework = SimpleAsyncRuntimeFramework::new(config);
    
    // 创建一个会失败的任务
    let failing_task: Box<dyn AsyncTask> = Box::new(FailingTask::new("failing_task", TaskPriority::Normal, 10));
    
    let result = framework.execute_task(failing_task).await;
    // 验证任务执行失败
    assert!(result.is_err());
    
    // 验证错误信息包含预期内容
    let error_msg = result.unwrap_err().to_string();
    assert!(error_msg.contains("任务执行失败"));
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
