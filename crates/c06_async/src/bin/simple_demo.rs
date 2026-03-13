//! 简单的异步生态系统演示程序
use c06_async::async_runtime_integration_framework_simple::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Rust 异步生态系统演示");
    println!("================================");
    
    // 创建异步运行时框架
    let config = RuntimeConfig::default();
    let framework = SimpleAsyncRuntimeFramework::new(config);
    
    // 执行单个任务
    println!("\n📋 执行单个任务:");
    let task: Box<dyn AsyncTask> = Box::new(ExampleTask::new("demo_task", TaskPriority::High, 100));
    let result = framework.execute_task(task).await?;
    println!("✅ 任务执行结果: {}", result);
    
    // 执行批量任务
    println!("\n📋 执行批量任务:");
    let batch_tasks: Vec<Box<dyn AsyncTask>> = vec![
        Box::new(ExampleTask::new("batch_task_1", TaskPriority::Normal, 50)),
        Box::new(ExampleTask::new("batch_task_2", TaskPriority::High, 30)),
        Box::new(ExampleTask::new("batch_task_3", TaskPriority::Low, 70)),
    ];
    
    let batch_results = framework.execute_batch(batch_tasks).await?;
    for (i, result) in batch_results.iter().enumerate() {
        println!("✅ 批量任务 {} 结果: {}", i + 1, result);
    }
    
    // 性能监控
    println!("\n📊 性能指标:");
    let metrics = framework.get_metrics().await;
    println!("  总任务数: {}", metrics.task_count);
    println!("  成功数: {}", metrics.success_count);
    println!("  失败数: {}", metrics.failure_count);
    println!("  平均执行时间: {:?}", metrics.average_execution_time);
    
    // 健康检查
    println!("\n🏥 健康检查:");
    let is_healthy = framework.health_check().await?;
    println!("  系统状态: {}", if is_healthy { "健康" } else { "异常" });
    
    // 异步同步转换服务
    println!("\n🔄 异步同步转换:");
    let conversion_service = AsyncSyncConversionService::new(5);
    let (async_result, sync_result) = conversion_service.hybrid_conversion().await?;
    println!("  异步结果: {}", async_result);
    println!("  同步结果: {}", sync_result);
    
    // 聚合组合服务
    println!("\n📦 聚合组合服务:");
    let composition_service = AggregationCompositionService::new();
    
    // 注册组件
    let component1 = Box::new(DataProcessingComponent::new("processor1", 20));
    let component2 = Box::new(DataProcessingComponent::new("processor2", 30));
    let component3 = Box::new(DataProcessingComponent::new("processor3", 25));
    
    composition_service.register_component(component1).await?;
    composition_service.register_component(component2).await?;
    composition_service.register_component(component3).await?;
    
    // 顺序聚合
    let sequential_results = composition_service.sequential_aggregation(
        vec!["processor1".to_string(), "processor2".to_string()],
        "input_data"
    ).await?;
    println!("  顺序聚合结果: {:?}", sequential_results);
    
    // 并行聚合
    let parallel_results = composition_service.parallel_aggregation(
        vec!["processor1".to_string(), "processor2".to_string(), "processor3".to_string()],
        "input_data"
    ).await?;
    println!("  并行聚合结果: {:?}", parallel_results);
    
    println!("\n✅ 演示完成!");
    
    Ok(())
}
