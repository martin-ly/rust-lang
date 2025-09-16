//! # 工作流插件中间件 / Workflow Plugin Middleware
//!
//! 本模块实现了工作流系统的插件中间件，支持动态加载和插件生命周期管理。
//! This module implements plugin middleware for workflow systems, supporting dynamic loading and plugin lifecycle management.

use crate::middleware::{MiddlewareContext, MiddlewarePriority, WorkflowMiddleware};
use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 初始化插件中间件 / Initialize plugin middleware
pub fn init_plugin_middleware() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("初始化插件中间件 / Initializing plugin middleware");
    Ok(())
}

/// 插件生命周期状态 / Plugin Lifecycle State
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PluginState {
    Unloaded,
    Loading,
    Loaded,
    Active,
    Inactive,
    Unloading,
    Error,
}

/// 插件信息 / Plugin Info
#[derive(Debug, Clone)]
pub struct PluginInfo {
    pub id: String,
    pub name: String,
    pub version: String,
    pub description: String,
    pub author: String,
    pub dependencies: Vec<String>,
    pub state: PluginState,
    pub load_time: Option<std::time::Instant>,
    pub metadata: HashMap<String, String>,
}

/// 插件管理器 / Plugin Manager
pub struct PluginManager {
    plugins: HashMap<String, Box<dyn WorkflowMiddleware>>,
    plugin_info: HashMap<String, PluginInfo>,
    plugin_states: HashMap<String, PluginState>,
}

impl Default for PluginManager {
    fn default() -> Self {
        Self::new()
    }
}

impl PluginManager {
    /// 创建插件管理器 / Create plugin manager
    pub fn new() -> Self {
        Self {
            plugins: HashMap::new(),
            plugin_info: HashMap::new(),
            plugin_states: HashMap::new(),
        }
    }

    /// 注册插件 / Register plugin
    pub fn register_plugin(
        &mut self,
        plugin: Box<dyn WorkflowMiddleware>,
        info: PluginInfo,
    ) -> Result<(), String> {
        let plugin_id = info.id.clone();

        if self.plugins.contains_key(&plugin_id) {
            return Err(format!(
                "插件 {} 已存在 / Plugin {} already exists",
                plugin_id, plugin_id
            ));
        }

        self.plugins.insert(plugin_id.clone(), plugin);
        self.plugin_info.insert(plugin_id.clone(), info.clone());
        self.plugin_states.insert(plugin_id, PluginState::Loaded);

        tracing::info!(
            "插件已注册 / Plugin registered: {} v{}",
            info.name,
            info.version
        );
        Ok(())
    }

    /// 获取插件 / Get plugin
    pub fn get_plugin(&self, plugin_id: &str) -> Option<&dyn WorkflowMiddleware> {
        self.plugins.get(plugin_id).map(|p| p.as_ref())
    }

    /// 获取插件信息 / Get plugin info
    pub fn get_plugin_info(&self, plugin_id: &str) -> Option<&PluginInfo> {
        self.plugin_info.get(plugin_id)
    }

    /// 获取所有插件信息 / Get all plugin info
    pub fn get_all_plugin_info(&self) -> Vec<&PluginInfo> {
        self.plugin_info.values().collect()
    }

    /// 激活插件 / Activate plugin
    pub fn activate_plugin(&mut self, plugin_id: &str) -> Result<(), String> {
        if let Some(state) = self.plugin_states.get_mut(plugin_id) {
            match *state {
                PluginState::Loaded | PluginState::Inactive => {
                    *state = PluginState::Active;
                    tracing::info!("插件已激活 / Plugin activated: {}", plugin_id);
                    Ok(())
                }
                PluginState::Active => {
                    tracing::warn!("插件已处于激活状态 / Plugin already active: {}", plugin_id);
                    Ok(())
                }
                _ => Err(format!(
                    "插件 {} 无法激活，当前状态: {:?} / Plugin {} cannot be activated, current state: {:?}",
                    plugin_id, state, plugin_id, state
                )),
            }
        } else {
            Err(format!(
                "插件 {} 不存在 / Plugin {} does not exist",
                plugin_id, plugin_id
            ))
        }
    }

    /// 停用插件 / Deactivate plugin
    pub fn deactivate_plugin(&mut self, plugin_id: &str) -> Result<(), String> {
        if let Some(state) = self.plugin_states.get_mut(plugin_id) {
            match *state {
                PluginState::Active => {
                    *state = PluginState::Inactive;
                    tracing::info!("插件已停用 / Plugin deactivated: {}", plugin_id);
                    Ok(())
                }
                PluginState::Inactive => {
                    tracing::warn!(
                        "插件已处于停用状态 / Plugin already inactive: {}",
                        plugin_id
                    );
                    Ok(())
                }
                _ => Err(format!(
                    "插件 {} 无法停用，当前状态: {:?} / Plugin {} cannot be deactivated, current state: {:?}",
                    plugin_id, state, plugin_id, state
                )),
            }
        } else {
            Err(format!(
                "插件 {} 不存在 / Plugin {} does not exist",
                plugin_id, plugin_id
            ))
        }
    }

    /// 卸载插件 / Unload plugin
    pub fn unload_plugin(&mut self, plugin_id: &str) -> Result<(), String> {
        if let Some(state) = self.plugin_states.get_mut(plugin_id) {
            match *state {
                PluginState::Loaded | PluginState::Inactive => {
                    *state = PluginState::Unloading;
                    self.plugins.remove(plugin_id);
                    self.plugin_info.remove(plugin_id);
                    self.plugin_states.remove(plugin_id);
                    tracing::info!("插件已卸载 / Plugin unloaded: {}", plugin_id);
                    Ok(())
                }
                PluginState::Active => Err(format!(
                    "插件 {} 正在使用中，无法卸载 / Plugin {} is in use, cannot unload",
                    plugin_id, plugin_id
                )),
                _ => Err(format!(
                    "插件 {} 无法卸载，当前状态: {:?} / Plugin {} cannot be unloaded, current state: {:?}",
                    plugin_id, state, plugin_id, state
                )),
            }
        } else {
            Err(format!(
                "插件 {} 不存在 / Plugin {} does not exist",
                plugin_id, plugin_id
            ))
        }
    }

    /// 获取插件状态 / Get plugin state
    pub fn get_plugin_state(&self, plugin_id: &str) -> Option<PluginState> {
        self.plugin_states.get(plugin_id).cloned()
    }

    /// 获取活跃插件列表 / Get active plugins list
    pub fn get_active_plugins(&self) -> Vec<String> {
        self.plugin_states
            .iter()
            .filter(|(_, state)| **state == PluginState::Active)
            .map(|(id, _)| id.clone())
            .collect()
    }
}

/// 插件中间件包装器 / Plugin Middleware Wrapper
pub struct PluginMiddlewareWrapper {
    plugin_id: String,
    plugin: Box<dyn WorkflowMiddleware>,
    state: PluginState,
}

impl PluginMiddlewareWrapper {
    /// 创建插件中间件包装器 / Create plugin middleware wrapper
    pub fn new(plugin_id: String, plugin: Box<dyn WorkflowMiddleware>) -> Self {
        Self {
            plugin_id,
            plugin,
            state: PluginState::Active,
        }
    }

    /// 检查插件是否可用 / Check if plugin is available
    fn is_available(&self) -> bool {
        self.state == PluginState::Active
    }
}

#[async_trait]
impl WorkflowMiddleware for PluginMiddlewareWrapper {
    fn name(&self) -> &str {
        self.plugin.name()
    }

    fn version(&self) -> &str {
        self.plugin.version()
    }

    fn description(&self) -> &str {
        self.plugin.description()
    }

    fn priority(&self) -> MiddlewarePriority {
        self.plugin.priority()
    }

    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        if !self.is_available() {
            return Err(format!(
                "插件 {} 不可用 / Plugin {} is not available",
                self.plugin_id, self.plugin_id
            ));
        }

        tracing::debug!(
            "执行插件中间件 / Executing plugin middleware: {}",
            self.plugin_id
        );
        self.plugin.before_request(context).await
    }

    async fn after_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        if !self.is_available() {
            return Err(format!(
                "插件 {} 不可用 / Plugin {} is not available",
                self.plugin_id, self.plugin_id
            ));
        }

        self.plugin.after_request(context).await
    }

    async fn handle_error(
        &self,
        context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String> {
        if !self.is_available() {
            return Err(format!(
                "插件 {} 不可用 / Plugin {} is not available",
                self.plugin_id, self.plugin_id
            ));
        }

        self.plugin.handle_error(context, error).await
    }
}

/// 插件加载器 / Plugin Loader
pub struct PluginLoader {
    plugin_manager: PluginManager,
    load_paths: Vec<String>,
}

impl Default for PluginLoader {
    fn default() -> Self {
        Self::new()
    }
}

impl PluginLoader {
    /// 创建插件加载器 / Create plugin loader
    pub fn new() -> Self {
        Self {
            plugin_manager: PluginManager::new(),
            load_paths: vec!["./plugins".to_string()],
        }
    }

    /// 添加加载路径 / Add load path
    pub fn add_load_path(&mut self, path: String) {
        self.load_paths.push(path);
    }

    /// 从文件加载插件 / Load plugin from file
    pub async fn load_plugin_from_file(&mut self, file_path: &str) -> Result<(), String> {
        tracing::info!("从文件加载插件 / Loading plugin from file: {}", file_path);

        // 在实际实现中，这里会动态加载插件文件
        // In actual implementation, this would dynamically load plugin files
        // 这里只是模拟加载过程 / This is just simulating the loading process

        let plugin_info = PluginInfo {
            id: "file_plugin".to_string(),
            name: "File Plugin".to_string(),
            version: "1.0.0".to_string(),
            description: "从文件加载的插件 / Plugin loaded from file".to_string(),
            author: "Plugin Author".to_string(),
            dependencies: vec![],
            state: PluginState::Unloaded,
            load_time: Some(std::time::Instant::now()),
            metadata: HashMap::new(),
        };

        // 创建模拟插件 / Create mock plugin
        let plugin = Box::new(MockPlugin::new("file_plugin".to_string()));

        self.plugin_manager.register_plugin(plugin, plugin_info)?;
        Ok(())
    }

    /// 从配置加载插件 / Load plugin from configuration
    pub async fn load_plugin_from_config(&mut self, config: PluginConfig) -> Result<(), String> {
        tracing::info!(
            "从配置加载插件 / Loading plugin from configuration: {}",
            config.name
        );

        let plugin_info = PluginInfo {
            id: config.id.clone(),
            name: config.name.clone(),
            version: config.version.clone(),
            description: config.description.clone(),
            author: config.author.clone(),
            dependencies: config.dependencies.clone(),
            state: PluginState::Unloaded,
            load_time: Some(std::time::Instant::now()),
            metadata: config.metadata.clone(),
        };

        // 创建模拟插件 / Create mock plugin
        let plugin = Box::new(MockPlugin::new(config.id.clone()));

        self.plugin_manager.register_plugin(plugin, plugin_info)?;
        Ok(())
    }

    /// 获取插件管理器 / Get plugin manager
    pub fn get_plugin_manager(&self) -> &PluginManager {
        &self.plugin_manager
    }

    /// 获取可变插件管理器 / Get mutable plugin manager
    pub fn get_plugin_manager_mut(&mut self) -> &mut PluginManager {
        &mut self.plugin_manager
    }
}

/// 插件配置 / Plugin Configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PluginConfig {
    pub id: String,
    pub name: String,
    pub version: String,
    pub description: String,
    pub author: String,
    pub dependencies: Vec<String>,
    pub metadata: HashMap<String, String>,
}

/// 模拟插件 / Mock Plugin
struct MockPlugin {
    id: String,
}

impl MockPlugin {
    fn new(id: String) -> Self {
        Self { id }
    }
}

#[async_trait]
impl WorkflowMiddleware for MockPlugin {
    fn name(&self) -> &str {
        "MockPlugin"
    }

    fn version(&self) -> &str {
        "1.0.0"
    }

    fn description(&self) -> &str {
        "模拟插件 / Mock plugin"
    }

    fn priority(&self) -> MiddlewarePriority {
        MiddlewarePriority::Normal
    }

    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("模拟插件执行 / Mock plugin executing: {}", self.id);
        context.set_metadata("mock_plugin_executed".to_string(), "true".to_string());
        Ok(())
    }

    async fn after_request(&self, _context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!(
            "模拟插件请求后处理 / Mock plugin after request processing: {}",
            self.id
        );
        Ok(())
    }

    async fn handle_error(
        &self,
        _context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String> {
        tracing::error!(
            "模拟插件错误处理 / Mock plugin error handling: {} - {}",
            self.id,
            error
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_plugin_manager() {
        let mut manager = PluginManager::new();

        // 创建模拟插件 / Create mock plugin
        let plugin = Box::new(MockPlugin::new("test_plugin".to_string()));
        let plugin_info = PluginInfo {
            id: "test_plugin".to_string(),
            name: "Test Plugin".to_string(),
            version: "1.0.0".to_string(),
            description: "测试插件 / Test plugin".to_string(),
            author: "Test Author".to_string(),
            dependencies: vec![],
            state: PluginState::Unloaded,
            load_time: Some(std::time::Instant::now()),
            metadata: HashMap::new(),
        };

        // 测试注册插件 / Test registering plugin
        let result = manager.register_plugin(plugin, plugin_info);
        assert!(result.is_ok());

        // 测试获取插件 / Test getting plugin
        let plugin = manager.get_plugin("test_plugin");
        assert!(plugin.is_some());

        // 测试激活插件 / Test activating plugin
        let result = manager.activate_plugin("test_plugin");
        assert!(result.is_ok());

        // 测试获取插件状态 / Test getting plugin state
        let state = manager.get_plugin_state("test_plugin");
        assert_eq!(state, Some(PluginState::Active));

        // 测试获取活跃插件列表 / Test getting active plugins list
        let active_plugins = manager.get_active_plugins();
        assert!(active_plugins.contains(&"test_plugin".to_string()));
    }

    #[test]
    fn test_plugin_middleware_wrapper() {
        let plugin = Box::new(MockPlugin::new("test_plugin".to_string()));
        let wrapper = PluginMiddlewareWrapper::new("test_plugin".to_string(), plugin);

        assert_eq!(wrapper.name(), "MockPlugin");
        assert_eq!(wrapper.version(), "1.0.0");
        assert!(wrapper.is_available());
    }

    #[tokio::test]
    async fn test_plugin_loader() {
        let mut loader = PluginLoader::new();

        // 测试从配置加载插件 / Test loading plugin from configuration
        let config = PluginConfig {
            id: "config_plugin".to_string(),
            name: "Config Plugin".to_string(),
            version: "1.0.0".to_string(),
            description: "配置插件 / Config plugin".to_string(),
            author: "Config Author".to_string(),
            dependencies: vec![],
            metadata: HashMap::new(),
        };

        let result = loader.load_plugin_from_config(config).await;
        assert!(result.is_ok());

        // 测试获取插件管理器 / Test getting plugin manager
        let manager = loader.get_plugin_manager();
        let plugin_info = manager.get_plugin_info("config_plugin");
        assert!(plugin_info.is_some());
        assert_eq!(plugin_info.unwrap().name, "Config Plugin");
    }
}
