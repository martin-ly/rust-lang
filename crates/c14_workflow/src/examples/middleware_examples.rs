//! # 工作流中间件示例 / Workflow Middleware Examples
//!
//! 本模块展示了如何使用各种工作流中间件来构建可扩展的工作流系统。
//! This module demonstrates how to use various workflow middleware to build extensible workflow systems.

// use crate::examples::{ExampleConfig, ExampleResult};
use crate::middleware::*;
use serde_json::json;
use std::collections::HashMap;

/// 运行中间件示例 / Run middleware examples
pub async fn run_middleware_examples() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("开始运行中间件示例 / Starting middleware examples");

    // 示例1：核心中间件 / Example 1: Core middleware
    core_middleware_example().await?;

    // 示例2：扩展中间件 / Example 2: Extension middleware
    extension_middleware_example().await?;

    // 示例3：插件中间件 / Example 3: Plugin middleware
    plugin_middleware_example().await?;

    // 示例4：中间件链 / Example 4: Middleware chain
    middleware_chain_example().await?;

    // 示例5：中间件管理器 / Example 5: Middleware manager
    middleware_manager_example().await?;

    tracing::info!("中间件示例运行完成 / Middleware examples completed");
    Ok(())
}

/// 核心中间件示例 / Core middleware example
async fn core_middleware_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行核心中间件示例 / Running core middleware example");

    // 创建中间件管理器 / Create middleware manager
    let manager = WorkflowMiddlewareManager::new();

    // 注册核心中间件 / Register core middleware
    manager
        .register_middleware(Box::new(core::AuthenticationMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(core::AuthorizationMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(core::LoggingMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(core::MonitoringMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(core::RateLimitingMiddleware::new()))
        .await?;

    // 获取所有中间件信息 / Get all middleware information
    let middlewares = manager.list_middlewares().await;
    tracing::info!(
        "注册了 {} 个核心中间件 / Registered {} core middlewares",
        middlewares.len(),
        middlewares.len()
    );

    for middleware in &middlewares {
        tracing::info!(
            "中间件: {} v{} - {} / Middleware: {} v{} - {}",
            middleware.name,
            middleware.version,
            middleware.description,
            middleware.name,
            middleware.version,
            middleware.description
        );
    }

    // 创建中间件上下文 / Create middleware context
    let context = MiddlewareContext::new(
        "req_1".to_string(),
        "workflow_1".to_string(),
        json!({"test": "data"}),
    );

    // 创建中间件链 / Create middleware chain
    let mut chain = manager.create_chain(context).await?;

    // 执行中间件链 / Execute middleware chain
    let result = chain.execute().await?;
    tracing::info!(
        "中间件链执行结果 / Middleware chain execution result: {:?}",
        result
    );

    Ok(())
}

/// 扩展中间件示例 / Extension middleware example
async fn extension_middleware_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行扩展中间件示例 / Running extension middleware example");

    // 创建中间件管理器 / Create middleware manager
    let manager = WorkflowMiddlewareManager::new();

    // 注册扩展中间件 / Register extension middleware
    manager
        .register_middleware(Box::new(extensions::CachingMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(extensions::CompressionMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(extensions::EncryptionMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(extensions::RetryMiddleware::new()))
        .await?;

    manager
        .register_middleware(Box::new(extensions::TimeoutMiddleware::new()))
        .await?;

    // 获取所有中间件信息 / Get all middleware information
    let middlewares = manager.list_middlewares().await;
    tracing::info!(
        "注册了 {} 个扩展中间件 / Registered {} extension middlewares",
        middlewares.len(),
        middlewares.len()
    );

    for middleware in &middlewares {
        tracing::info!(
            "扩展中间件: {} v{} - {} / Extension middleware: {} v{} - {}",
            middleware.name,
            middleware.version,
            middleware.description,
            middleware.name,
            middleware.version,
            middleware.description
        );
    }

    // 创建中间件上下文 / Create middleware context
    let context = MiddlewareContext::new(
        "req_2".to_string(),
        "workflow_2".to_string(),
        json!({
            "data": "test_data",
            "compression": "gzip",
            "encryption": "aes256"
        }),
    );

    // 创建中间件链 / Create middleware chain
    let mut chain = manager.create_chain(context).await?;

    // 执行中间件链 / Execute middleware chain
    let result = chain.execute().await?;
    tracing::info!(
        "扩展中间件链执行结果 / Extension middleware chain execution result: {:?}",
        result
    );

    Ok(())
}

/// 插件中间件示例 / Plugin middleware example
async fn plugin_middleware_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行插件中间件示例 / Running plugin middleware example");

    // 创建插件加载器 / Create plugin loader
    let mut loader = plugins::PluginLoader::new();

    // 从配置加载插件 / Load plugin from configuration
    let config = plugins::PluginConfig {
        id: "custom_plugin".to_string(),
        name: "Custom Plugin".to_string(),
        version: "1.0.0".to_string(),
        description: "自定义插件 / Custom plugin".to_string(),
        author: "Plugin Author".to_string(),
        dependencies: vec![],
        metadata: HashMap::new(),
    };

    loader.load_plugin_from_config(config).await?;

    // 从文件加载插件 / Load plugin from file
    loader.load_plugin_from_file("custom_plugin.so").await?;

    // 获取插件管理器 / Get plugin manager
    let plugin_manager = loader.get_plugin_manager_mut();

    // 激活插件 / Activate plugin
    plugin_manager.activate_plugin("custom_plugin")?;

    // 获取插件信息 / Get plugin information
    let plugin_info = plugin_manager.get_plugin_info("custom_plugin");
    if let Some(info) = plugin_info {
        tracing::info!(
            "插件信息 / Plugin info: {} v{} - {} / {} v{} - {}",
            info.name,
            info.version,
            info.description,
            info.name,
            info.version,
            info.description
        );
    }

    // 获取活跃插件列表 / Get active plugins list
    let active_plugins = plugin_manager.get_active_plugins();
    tracing::info!(
        "活跃插件: {:?} / Active plugins: {:?}",
        active_plugins,
        active_plugins
    );

    // 测试插件中间件包装器 / Test plugin middleware wrapper
    // 注意：这里我们直接创建一个新的中间件实例，因为 get_plugin 返回的是引用
    let custom_middleware = core::LoggingMiddleware::new();
    let wrapper = plugins::PluginMiddlewareWrapper::new(
        "custom_plugin".to_string(),
        Box::new(custom_middleware),
    );

    let context = MiddlewareContext::new(
        "req_3".to_string(),
        "workflow_3".to_string(),
        json!({"plugin": "test"}),
    );

    let result = wrapper.before_request(&mut context.clone()).await;
    match result {
        Ok(_) => {
            tracing::info!("插件中间件执行成功 / Plugin middleware execution successful");
        }
        Err(error) => {
            tracing::error!(
                "插件中间件执行失败: {} / Plugin middleware execution failed: {}",
                error,
                error
            );
        }
    }

    Ok(())
}

/// 中间件链示例 / Middleware chain example
async fn middleware_chain_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行中间件链示例 / Running middleware chain example");

    // 创建中间件链 / Create middleware chain
    let context = MiddlewareContext::new(
        "req_4".to_string(),
        "workflow_4".to_string(),
        json!({
            "chain_test": true,
            "data": "chain_data"
        }),
    );

    let mut chain = WorkflowMiddlewareChain::new(context);

    // 添加中间件到链中 / Add middlewares to chain
    chain.add_middleware(Box::new(core::AuthenticationMiddleware::new()));
    chain.add_middleware(Box::new(core::AuthorizationMiddleware::new()));
    chain.add_middleware(Box::new(core::LoggingMiddleware::new()));
    chain.add_middleware(Box::new(extensions::CachingMiddleware::new()));
    chain.add_middleware(Box::new(extensions::CompressionMiddleware::new()));

    // 执行中间件链 / Execute middleware chain
    let result = chain.execute().await?;
    tracing::info!(
        "中间件链执行结果 / Middleware chain execution result: {:?}",
        result
    );

    // 测试错误处理 / Test error handling
    let error_context = MiddlewareContext::new(
        "req_5".to_string(),
        "workflow_5".to_string(),
        json!({"error_test": true}),
    );

    let mut error_chain = WorkflowMiddlewareChain::new(error_context);
    error_chain.add_middleware(Box::new(core::AuthenticationMiddleware::new()));

    // 模拟错误处理 / Simulate error handling
    let error_result = error_chain.handle_error("模拟错误 / Simulated error").await;
    match error_result {
        Ok(_) => {
            tracing::info!("错误处理成功 / Error handling successful");
        }
        Err(error) => {
            tracing::error!("错误处理失败: {} / Error handling failed: {}", error, error);
        }
    }

    Ok(())
}

/// 中间件管理器示例 / Middleware manager example
async fn middleware_manager_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行中间件管理器示例 / Running middleware manager example");

    // 创建中间件管理器 / Create middleware manager
    let manager = WorkflowMiddlewareManager::new();

    // 注册各种中间件 / Register various middlewares
    manager
        .register_middleware(Box::new(core::AuthenticationMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(core::AuthorizationMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(core::LoggingMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(core::MonitoringMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(core::RateLimitingMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(extensions::CachingMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(extensions::CompressionMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(extensions::EncryptionMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(extensions::RetryMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(extensions::TimeoutMiddleware::new()))
        .await?;

    // 获取所有中间件信息 / Get all middleware information
    let middlewares = manager.list_middlewares().await;
    tracing::info!(
        "总共注册了 {} 个中间件 / Total of {} middlewares registered",
        middlewares.len(),
        middlewares.len()
    );

    // 按优先级分组中间件 / Group middlewares by priority
    let mut priority_groups: HashMap<MiddlewarePriority, Vec<&MiddlewareInfo>> = HashMap::new();
    for middleware in &middlewares {
        priority_groups
            .entry(middleware.priority)
            .or_default()
            .push(middleware);
    }

    for (priority, middlewares) in priority_groups {
        tracing::info!(
            "优先级 {:?} 有 {} 个中间件 / Priority {:?} has {} middlewares",
            priority,
            middlewares.len(),
            priority,
            middlewares.len()
        );
        for middleware in middlewares {
            tracing::info!(
                "  - {} v{} / - {} v{}",
                middleware.name,
                middleware.version,
                middleware.name,
                middleware.version
            );
        }
    }

    // 创建中间件事件处理器 / Create middleware event handler
    let event_handler = WorkflowMiddlewareEventHandler::new();

    // 发送中间件事件 / Send middleware events
    event_handler
        .send_event(MiddlewareEvent::MiddlewareRegistered {
            name: "test_middleware".to_string(),
            version: "1.0.0".to_string(),
        })
        .await?;

    event_handler
        .send_event(MiddlewareEvent::MiddlewareExecutionStarted {
            name: "test_middleware".to_string(),
            request_id: "req_6".to_string(),
        })
        .await?;

    event_handler
        .send_event(MiddlewareEvent::MiddlewareExecutionCompleted {
            name: "test_middleware".to_string(),
            request_id: "req_6".to_string(),
            duration: 100,
        })
        .await?;

    tracing::info!("中间件事件发送成功 / Middleware events sent successfully");

    Ok(())
}

/// 中间件性能测试 / Middleware Performance Test
pub async fn run_middleware_performance_test() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行中间件性能测试 / Running middleware performance test");

    // 创建中间件管理器 / Create middleware manager
    let manager = WorkflowMiddlewareManager::new();

    // 注册中间件 / Register middlewares
    manager
        .register_middleware(Box::new(core::AuthenticationMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(core::LoggingMiddleware::new()))
        .await?;
    manager
        .register_middleware(Box::new(extensions::CachingMiddleware::new()))
        .await?;

    // 创建测试上下文 / Create test context
    let context = MiddlewareContext::new(
        "perf_test".to_string(),
        "workflow_perf".to_string(),
        json!({"performance": "test"}),
    );

    // 创建中间件链 / Create middleware chain
    let _chain = manager.create_chain(context).await?;

    // 性能测试 / Performance test
    let iterations = 1000;
    let start_time = std::time::Instant::now();

    for i in 0..iterations {
        let test_context = MiddlewareContext::new(
            format!("req_{}", i),
            format!("workflow_{}", i),
            json!({"iteration": i}),
        );

        let mut test_chain = manager.create_chain(test_context).await?;
        let _result = test_chain.execute().await?;
    }

    let duration = start_time.elapsed();
    let avg_duration = duration / iterations;

    tracing::info!("中间件性能测试完成 / Middleware performance test completed");
    tracing::info!(
        "总迭代次数: {} / Total iterations: {}",
        iterations,
        iterations
    );
    tracing::info!(
        "总耗时: {}ms / Total duration: {}ms",
        duration.as_millis(),
        duration.as_millis()
    );
    tracing::info!(
        "平均耗时: {}μs / Average duration: {}μs",
        avg_duration.as_micros(),
        avg_duration.as_micros()
    );

    Ok(())
}

/// 中间件配置示例 / Middleware Configuration Example
pub async fn run_middleware_configuration_example() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("运行中间件配置示例 / Running middleware configuration example");

    // 创建中间件管理器 / Create middleware manager
    let manager = WorkflowMiddlewareManager::new();

    // 配置认证中间件 / Configure authentication middleware
    let auth_middleware = core::AuthenticationMiddleware::new();
    manager
        .register_middleware(Box::new(auth_middleware))
        .await?;

    // 配置日志中间件 / Configure logging middleware
    let logging_middleware = core::LoggingMiddleware::new();
    manager
        .register_middleware(Box::new(logging_middleware))
        .await?;

    // 配置缓存中间件 / Configure caching middleware
    let caching_middleware = extensions::CachingMiddleware::new();
    manager
        .register_middleware(Box::new(caching_middleware))
        .await?;

    // 配置重试中间件 / Configure retry middleware
    let retry_middleware = extensions::RetryMiddleware::new()
        .with_max_retries(5)
        .with_retry_delay(std::time::Duration::from_secs(2));
    manager
        .register_middleware(Box::new(retry_middleware))
        .await?;

    // 配置超时中间件 / Configure timeout middleware
    let timeout_middleware =
        extensions::TimeoutMiddleware::new().with_timeout(std::time::Duration::from_secs(30));
    manager
        .register_middleware(Box::new(timeout_middleware))
        .await?;

    // 获取配置后的中间件信息 / Get configured middleware information
    let middlewares = manager.list_middlewares().await;
    tracing::info!(
        "配置了 {} 个中间件 / Configured {} middlewares",
        middlewares.len(),
        middlewares.len()
    );

    for middleware in &middlewares {
        tracing::info!(
            "配置的中间件: {} v{} - {} / Configured middleware: {} v{} - {}",
            middleware.name,
            middleware.version,
            middleware.description,
            middleware.name,
            middleware.version,
            middleware.description
        );
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_core_middleware_example() {
        let result = core_middleware_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_extension_middleware_example() {
        let result = extension_middleware_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_plugin_middleware_example() {
        let result = plugin_middleware_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_middleware_chain_example() {
        let result = middleware_chain_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_middleware_manager_example() {
        let result = middleware_manager_example().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_middleware_performance_test() {
        let result = run_middleware_performance_test().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_middleware_configuration_example() {
        let result = run_middleware_configuration_example().await;
        assert!(result.is_ok());
    }
}
