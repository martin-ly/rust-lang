//! 性能测试套件
//! 
//! 测试各种性能指标和基准

use anyhow::Result;
use c19_ai::*;
use std::time::{Duration, Instant};
use tokio::time::timeout;

/// 测试引擎初始化性能
#[tokio::test]
async fn test_engine_initialization_performance() -> Result<()> {
    let start = Instant::now();
    let engine = AIEngine::new();
    let duration = start.elapsed();
    
    // 初始化应该在100ms内完成
    assert!(duration < Duration::from_millis(100));
    
    Ok(())
}

/// 测试模块注册性能
#[tokio::test]
async fn test_module_registration_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    // 测试单个模块注册性能
    let start = Instant::now();
    let module = AIModule::new("test_module".to_string(), "1.0.0".to_string());
    engine.register_module(module);
    let duration = start.elapsed();
    
    // 单个模块注册应该在1ms内完成
    assert!(duration < Duration::from_millis(1));
    
    Ok(())
}

/// 测试批量模块注册性能
#[tokio::test]
async fn test_batch_module_registration_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    let start = Instant::now();
    
    // 注册1000个模块
    for i in 0..1000 {
        let module = AIModule::new(format!("module_{}", i), "1.0.0".to_string());
        engine.register_module(module);
    }
    
    let duration = start.elapsed();
    
    // 1000个模块注册应该在1秒内完成
    assert!(duration < Duration::from_secs(1));
    
    // 验证所有模块都已注册
    assert_eq!(engine.list_modules().len(), 1000);
    
    Ok(())
}

/// 测试配置设置性能
#[tokio::test]
async fn test_config_setting_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    let start = Instant::now();
    
    // 设置1000个配置
    for i in 0..1000 {
        let config = ModelConfig {
            name: format!("config_{}", i),
            model_type: ModelType::MachineLearning,
            version: "1.0.0".to_string(),
            path: None,
            parameters: std::collections::HashMap::new(),
            framework: Some("candle".to_string()),
            device: None,
            precision: None,
        };
        engine.set_config(&format!("config_{}", i), config)?;
    }
    
    let duration = start.elapsed();
    
    // 1000个配置设置应该在500ms内完成
    assert!(duration < Duration::from_millis(500));
    
    Ok(())
}

/// 测试配置获取性能
#[tokio::test]
async fn test_config_retrieval_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    // 预先设置配置
    for i in 0..1000 {
        let config = ModelConfig {
            name: format!("config_{}", i),
            version: "1.0.0".to_string(),
            model_type: "test".to_string(),
            framework: "candle".to_string(),
            parameters: std::collections::HashMap::new(),
        };
        engine.set_config(&format!("config_{}", i), config)?;
    }
    
    let start = Instant::now();
    
    // 获取1000个配置
    for i in 0..1000 {
        let config = engine.get_config(&format!("config_{}", i));
        assert!(config.is_some());
    }
    
    let duration = start.elapsed();
    
    // 1000个配置获取应该在100ms内完成
    assert!(duration < Duration::from_millis(100));
    
    Ok(())
}

/// 测试并发性能
#[tokio::test]
async fn test_concurrent_performance() -> Result<()> {
    let engine = std::sync::Arc::new(AIEngine::new()?);
    let mut handles = Vec::new();
    
    let start = Instant::now();
    
    // 创建100个并发任务
    for i in 0..100 {
        let engine_clone = engine.clone();
        let handle = tokio::spawn(async move {
            let mut engine_guard = engine_clone.lock().await;
            let module = AIModule::new(&format!("concurrent_module_{}", i), "1.0.0");
            engine_guard.register_module(module)
        });
        handles.push(handle);
    }
    
    // 等待所有任务完成
    for handle in handles {
        let result = timeout(Duration::from_secs(5), handle).await?;
        assert!(result.is_ok());
    }
    
    let duration = start.elapsed();
    
    // 100个并发任务应该在2秒内完成
    assert!(duration < Duration::from_secs(2));
    
    Ok(())
}

/// 测试内存使用性能
#[tokio::test]
async fn test_memory_usage_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    // 测试大量数据的内存使用
    let start = Instant::now();
    
    for i in 0..10000 {
        let config = ModelConfig {
            name: format!("memory_test_{}", i),
            version: "1.0.0".to_string(),
            model_type: "test".to_string(),
            framework: "candle".to_string(),
            parameters: std::collections::HashMap::new(),
        };
        engine.set_config(&format!("memory_test_{}", i), config)?;
    }
    
    let duration = start.elapsed();
    
    // 10000个配置应该在5秒内完成
    assert!(duration < Duration::from_secs(5));
    
    // 清理内存
    engine.cleanup()?;
    
    Ok(())
}

/// 测试指标记录性能
#[tokio::test]
async fn test_metrics_recording_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    let start = Instant::now();
    
    // 记录10000个指标
    for i in 0..10000 {
        engine.record_metric(&format!("metric_{}", i), i as f64)?;
    }
    
    let duration = start.elapsed();
    
    // 10000个指标记录应该在1秒内完成
    assert!(duration < Duration::from_secs(1));
    
    // 验证指标数量
    let metrics = engine.get_metrics();
    assert_eq!(metrics.len(), 10000);
    
    Ok(())
}

/// 测试状态管理性能
#[tokio::test]
async fn test_state_management_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    let start = Instant::now();
    
    // 设置10000个状态
    for i in 0..10000 {
        engine.set_state(&format!("state_{}", i), &format!("value_{}", i))?;
    }
    
    let duration = start.elapsed();
    
    // 10000个状态设置应该在500ms内完成
    assert!(duration < Duration::from_millis(500));
    
    // 获取所有状态
    let start = Instant::now();
    for i in 0..10000 {
        let value = engine.get_state(&format!("state_{}", i));
        assert_eq!(value, Some(format!("value_{}", i)));
    }
    let duration = start.elapsed();
    
    // 10000个状态获取应该在200ms内完成
    assert!(duration < Duration::from_millis(200));
    
    Ok(())
}

/// 测试事件系统性能
#[tokio::test]
async fn test_event_system_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    // 注册事件监听器
    let mut event_count = 0;
    engine.on_event("test_event", Box::new(move |_event| {
        event_count += 1;
    }))?;
    
    let start = Instant::now();
    
    // 触发10000个事件
    for i in 0..10000 {
        engine.emit_event("test_event", &format!("event_{}", i))?;
    }
    
    let duration = start.elapsed();
    
    // 10000个事件触发应该在1秒内完成
    assert!(duration < Duration::from_secs(1));
    
    // 验证事件计数
    assert_eq!(event_count, 10000);
    
    Ok(())
}

/// 测试资源清理性能
#[tokio::test]
async fn test_cleanup_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    // 预先创建大量资源
    for i in 0..10000 {
        let module = AIModule::new(&format!("cleanup_module_{}", i), "1.0.0");
        engine.register_module(module);
        
        let config = ModelConfig {
            name: format!("cleanup_config_{}", i),
            version: "1.0.0".to_string(),
            model_type: "test".to_string(),
            framework: "candle".to_string(),
            parameters: std::collections::HashMap::new(),
        };
        engine.set_config(&format!("cleanup_config_{}", i), config)?;
    }
    
    let start = Instant::now();
    
    // 清理所有资源
    engine.cleanup()?;
    
    let duration = start.elapsed();
    
    // 清理应该在1秒内完成
    assert!(duration < Duration::from_secs(1));
    
    // 验证资源已被清理
    assert_eq!(engine.list_modules().len(), 0);
    
    Ok(())
}

/// 测试错误处理性能
#[tokio::test]
async fn test_error_handling_performance() -> Result<()> {
    let engine = AIEngine::new();
    
    let start = Instant::now();
    
    // 尝试获取10000个不存在的模块
    for i in 0..10000 {
        let module = engine.get_module(&format!("nonexistent_module_{}", i));
        assert!(module.is_none());
    }
    
    let duration = start.elapsed();
    
    // 10000个错误处理应该在100ms内完成
    assert!(duration < Duration::from_millis(100));
    
    Ok(())
}

/// 测试超时处理性能
#[tokio::test]
async fn test_timeout_handling_performance() -> Result<()> {
    let start = Instant::now();
    
    // 测试超时处理
    let result = timeout(Duration::from_millis(10), async {
        tokio::time::sleep(Duration::from_millis(100)).await;
        Ok::<(), anyhow::Error>(())
    }).await;
    
    let duration = start.elapsed();
    
    // 超时处理应该在20ms内完成
    assert!(duration < Duration::from_millis(20));
    assert!(result.is_err());
    
    Ok(())
}

/// 测试资源限制性能
#[tokio::test]
async fn test_resource_limits_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    let start = Instant::now();
    
    // 设置资源限制
    engine.set_resource_limit("max_modules", 1000)?;
    
    // 注册模块直到达到限制
    for i in 0..1000 {
        let module = AIModule::new(&format!("limit_module_{}", i), "1.0.0");
        engine.register_module(module);
    }
    
    let duration = start.elapsed();
    
    // 1000个模块注册应该在500ms内完成
    assert!(duration < Duration::from_millis(500));
    
    // 验证限制
    assert_eq!(engine.list_modules().len(), 1000);
    
    Ok(())
}

/// 测试数据持久化性能
#[tokio::test]
async fn test_data_persistence_performance() -> Result<()> {
    let mut engine = AIEngine::new();
    
    let start = Instant::now();
    
    // 保存大量数据
    for i in 0..1000 {
        let config = ModelConfig {
            name: format!("persistent_config_{}", i),
            version: "1.0.0".to_string(),
            model_type: "test".to_string(),
            framework: "candle".to_string(),
            parameters: std::collections::HashMap::new(),
        };
        engine.set_config(&format!("persistent_config_{}", i), config)?;
    }
    
    let duration = start.elapsed();
    
    // 1000个配置保存应该在1秒内完成
    assert!(duration < Duration::from_secs(1));
    
    Ok(())
}
