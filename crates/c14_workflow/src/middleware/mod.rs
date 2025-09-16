//! # 工作流中间件系统 / Workflow Middleware System
//!
//! 本模块提供了完整的工作流中间件系统，支持插件化架构和扩展性。
//! This module provides a complete workflow middleware system with plugin architecture and extensibility.

pub mod core;
pub mod extensions;
pub mod plugins;

// 重新导出中间件组件 / Re-export middleware components
pub use core::*;
pub use extensions::*;
pub use plugins::*;

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::{RwLock, mpsc};

/// 工作流中间件系统版本 / Workflow Middleware System Version
pub const MIDDLEWARE_VERSION: &str = "1.0.0";

/// 初始化工作流中间件系统 / Initialize workflow middleware system
pub fn init_workflow_middleware() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("初始化工作流中间件系统 / Initializing workflow middleware system");

    // 初始化核心中间件 / Initialize core middleware
    init_core_middleware()?;

    // 初始化扩展中间件 / Initialize extension middleware
    init_extension_middleware()?;

    // 初始化插件中间件 / Initialize plugin middleware
    init_plugin_middleware()?;

    tracing::info!("工作流中间件系统初始化完成 / Workflow middleware system initialized");
    Ok(())
}

/// 工作流中间件特征 / Workflow Middleware Trait
#[async_trait]
pub trait WorkflowMiddleware: Send + Sync {
    /// 中间件名称 / Middleware name
    fn name(&self) -> &str;

    /// 中间件版本 / Middleware version
    fn version(&self) -> &str;

    /// 中间件描述 / Middleware description
    fn description(&self) -> &str;

    /// 中间件优先级 / Middleware priority
    fn priority(&self) -> MiddlewarePriority;

    /// 处理请求前 / Before request processing
    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String>;

    /// 处理请求后 / After request processing
    async fn after_request(&self, context: &mut MiddlewareContext) -> Result<(), String>;

    /// 处理错误 / Handle error
    async fn handle_error(
        &self,
        context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String>;
}

/// 中间件优先级 / Middleware Priority
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MiddlewarePriority {
    Critical = 1,
    High = 2,
    Normal = 3,
    Low = 4,
}

/// 中间件上下文 / Middleware Context
#[derive(Debug, Clone)]
pub struct MiddlewareContext {
    pub request_id: String,
    pub workflow_id: String,
    pub data: serde_json::Value,
    pub metadata: HashMap<String, String>,
    pub headers: HashMap<String, String>,
    pub start_time: std::time::Instant,
    pub end_time: Option<std::time::Instant>,
}

impl MiddlewareContext {
    /// 创建中间件上下文 / Create middleware context
    pub fn new(request_id: String, workflow_id: String, data: serde_json::Value) -> Self {
        Self {
            request_id,
            workflow_id,
            data,
            metadata: HashMap::new(),
            headers: HashMap::new(),
            start_time: std::time::Instant::now(),
            end_time: None,
        }
    }

    /// 设置元数据 / Set metadata
    pub fn set_metadata(&mut self, key: String, value: String) {
        self.metadata.insert(key, value);
    }

    /// 获取元数据 / Get metadata
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }

    /// 设置头部 / Set header
    pub fn set_header(&mut self, key: String, value: String) {
        self.headers.insert(key, value);
    }

    /// 获取头部 / Get header
    pub fn get_header(&self, key: &str) -> Option<&String> {
        self.headers.get(key)
    }

    /// 完成请求 / Complete request
    pub fn complete(&mut self) {
        self.end_time = Some(std::time::Instant::now());
    }

    /// 获取执行时间 / Get execution time
    pub fn execution_time(&self) -> Option<std::time::Duration> {
        self.end_time.map(|end| end.duration_since(self.start_time))
    }
}

/// 工作流中间件链 / Workflow Middleware Chain
pub struct WorkflowMiddlewareChain {
    middlewares: Vec<Box<dyn WorkflowMiddleware>>,
    context: MiddlewareContext,
}

impl WorkflowMiddlewareChain {
    /// 创建中间件链 / Create middleware chain
    pub fn new(context: MiddlewareContext) -> Self {
        Self {
            middlewares: Vec::new(),
            context,
        }
    }

    /// 添加中间件 / Add middleware
    pub fn add_middleware(&mut self, middleware: Box<dyn WorkflowMiddleware>) {
        self.middlewares.push(middleware);
        // 按优先级排序 / Sort by priority
        self.middlewares.sort_by_key(|a| a.priority());
    }

    /// 执行中间件链 / Execute middleware chain
    pub async fn execute(&mut self) -> Result<MiddlewareContext, String> {
        // 执行请求前中间件 / Execute before request middlewares
        for middleware in &self.middlewares {
            middleware
                .before_request(&mut self.context)
                .await
                .map_err(|e| {
                    format!(
                        "Middleware {} before_request failed: {}",
                        middleware.name(),
                        e
                    )
                })?;
        }

        // 执行请求后中间件 / Execute after request middlewares
        for middleware in &self.middlewares {
            middleware
                .after_request(&mut self.context)
                .await
                .map_err(|e| {
                    format!(
                        "Middleware {} after_request failed: {}",
                        middleware.name(),
                        e
                    )
                })?;
        }

        self.context.complete();
        Ok(self.context.clone())
    }

    /// 处理错误 / Handle error
    pub async fn handle_error(&mut self, error: &str) -> Result<(), String> {
        for middleware in &self.middlewares {
            middleware
                .handle_error(&mut self.context, error)
                .await
                .map_err(|e| {
                    format!(
                        "Middleware {} handle_error failed: {}",
                        middleware.name(),
                        e
                    )
                })?;
        }
        Ok(())
    }
}

/// 工作流中间件管理器 / Workflow Middleware Manager
pub struct WorkflowMiddlewareManager {
    middlewares: RwLock<HashMap<String, Box<dyn WorkflowMiddleware>>>,
    middleware_chain: RwLock<Vec<String>>,
}

impl Default for WorkflowMiddlewareManager {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkflowMiddlewareManager {
    /// 创建中间件管理器 / Create middleware manager
    pub fn new() -> Self {
        Self {
            middlewares: RwLock::new(HashMap::new()),
            middleware_chain: RwLock::new(Vec::new()),
        }
    }

    /// 注册中间件 / Register middleware
    pub async fn register_middleware(
        &self,
        middleware: Box<dyn WorkflowMiddleware>,
    ) -> Result<(), String> {
        let name = middleware.name().to_string();
        let mut middlewares = self.middlewares.write().await;

        if middlewares.contains_key(&name) {
            return Err(format!(
                "中间件 {} 已存在 / Middleware {} already exists",
                name, name
            ));
        }

        middlewares.insert(name.clone(), middleware);

        // 添加到中间件链 / Add to middleware chain
        let mut chain = self.middleware_chain.write().await;
        chain.push(name);

        Ok(())
    }

    /// 获取中间件 / Get middleware
    pub async fn get_middleware(&self, name: &str) -> Option<Box<dyn WorkflowMiddleware>> {
        let middlewares = self.middlewares.read().await;
        middlewares.get(name).map(|_m| {
            // 这里需要实现克隆逻辑，实际应用中可能需要使用 Arc 或其他方式
            // Here we need to implement cloning logic, in actual applications we might need to use Arc or other methods
            todo!("Implement middleware cloning")
        })
    }

    /// 创建中间件链 / Create middleware chain
    pub async fn create_chain(
        &self,
        context: MiddlewareContext,
    ) -> Result<WorkflowMiddlewareChain, String> {
        let chain = WorkflowMiddlewareChain::new(context);
        let middlewares = self.middlewares.read().await;
        let chain_order = self.middleware_chain.read().await;

        for name in chain_order.iter() {
            if let Some(_middleware) = middlewares.get(name) {
                // 这里需要实现克隆逻辑
                // Here we need to implement cloning logic
                todo!("Implement middleware cloning for chain creation")
            }
        }

        Ok(chain)
    }

    /// 列出所有中间件 / List all middlewares
    pub async fn list_middlewares(&self) -> Vec<MiddlewareInfo> {
        let middlewares = self.middlewares.read().await;
        middlewares
            .values()
            .map(|m| MiddlewareInfo {
                name: m.name().to_string(),
                version: m.version().to_string(),
                description: m.description().to_string(),
                priority: m.priority(),
            })
            .collect()
    }
}

/// 中间件信息 / Middleware Info
#[derive(Debug, Clone)]
pub struct MiddlewareInfo {
    pub name: String,
    pub version: String,
    pub description: String,
    pub priority: MiddlewarePriority,
}

/// 工作流中间件事件 / Workflow Middleware Event
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MiddlewareEvent {
    /// 中间件注册 / Middleware registered
    MiddlewareRegistered { name: String, version: String },
    /// 中间件执行开始 / Middleware execution started
    MiddlewareExecutionStarted { name: String, request_id: String },
    /// 中间件执行完成 / Middleware execution completed
    MiddlewareExecutionCompleted {
        name: String,
        request_id: String,
        duration: u64,
    },
    /// 中间件执行错误 / Middleware execution error
    MiddlewareExecutionError {
        name: String,
        request_id: String,
        error: String,
    },
}

/// 工作流中间件事件处理器 / Workflow Middleware Event Handler
pub struct WorkflowMiddlewareEventHandler {
    event_sender: mpsc::Sender<MiddlewareEvent>,
    event_receiver: mpsc::Receiver<MiddlewareEvent>,
}

impl Default for WorkflowMiddlewareEventHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl WorkflowMiddlewareEventHandler {
    /// 创建事件处理器 / Create event handler
    pub fn new() -> Self {
        let (event_sender, event_receiver) = mpsc::channel(1000);
        Self {
            event_sender,
            event_receiver,
        }
    }

    /// 发送事件 / Send event
    pub async fn send_event(&self, event: MiddlewareEvent) -> Result<(), String> {
        self.event_sender
            .send(event)
            .await
            .map_err(|_| "事件发送失败 / Event send failed".to_string())
    }

    /// 处理事件 / Handle events
    pub async fn handle_events(&mut self) -> Result<(), String> {
        while let Some(event) = self.event_receiver.recv().await {
            match event {
                MiddlewareEvent::MiddlewareRegistered { name, version } => {
                    tracing::info!(
                        "中间件已注册 / Middleware registered: {} v{}",
                        name,
                        version
                    );
                }
                MiddlewareEvent::MiddlewareExecutionStarted { name, request_id } => {
                    tracing::debug!(
                        "中间件执行开始 / Middleware execution started: {} for request {}",
                        name,
                        request_id
                    );
                }
                MiddlewareEvent::MiddlewareExecutionCompleted {
                    name,
                    request_id,
                    duration,
                } => {
                    tracing::debug!(
                        "中间件执行完成 / Middleware execution completed: {} for request {} in {}ms",
                        name,
                        request_id,
                        duration
                    );
                }
                MiddlewareEvent::MiddlewareExecutionError {
                    name,
                    request_id,
                    error,
                } => {
                    tracing::error!(
                        "中间件执行错误 / Middleware execution error: {} for request {}: {}",
                        name,
                        request_id,
                        error
                    );
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_middleware_context() {
        let mut context = MiddlewareContext::new(
            "req_1".to_string(),
            "workflow_1".to_string(),
            serde_json::json!({"test": "data"}),
        );

        context.set_metadata("key1".to_string(), "value1".to_string());
        assert_eq!(context.get_metadata("key1"), Some(&"value1".to_string()));

        context.set_header("Content-Type".to_string(), "application/json".to_string());
        assert_eq!(
            context.get_header("Content-Type"),
            Some(&"application/json".to_string())
        );

        context.complete();
        assert!(context.execution_time().is_some());
    }

    #[tokio::test]
    async fn test_middleware_manager() {
        let manager = WorkflowMiddlewareManager::new();

        // 测试中间件列表 / Test middleware listing
        let middlewares = manager.list_middlewares().await;
        assert_eq!(middlewares.len(), 0);
    }

    #[tokio::test]
    async fn test_middleware_event_handler() {
        let handler = WorkflowMiddlewareEventHandler::new();

        let event = MiddlewareEvent::MiddlewareRegistered {
            name: "test_middleware".to_string(),
            version: "1.0.0".to_string(),
        };

        let result = handler.send_event(event).await;
        assert!(result.is_ok());
    }
}
