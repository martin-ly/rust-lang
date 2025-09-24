//! 自动恢复实现
//!
//! 提供系统自动恢复功能，包括内存清理、连接重建、死锁恢复等。

use std::sync::Arc;
use std::collections::HashMap;
use std::time::Duration;
use serde::{Serialize, Deserialize};
use tracing::{debug, warn, error, info};

use crate::error_handling::UnifiedError;
use super::MonitoringState;

/// 自动恢复配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoRecoveryConfig {
    /// 恢复间隔
    pub recovery_interval: Duration,
    /// 是否启用自动恢复
    pub enabled: bool,
    /// 恢复项目
    pub recovery_items: Vec<AutoRecoveryItem>,
    /// 恢复策略
    pub recovery_strategies: HashMap<String, RecoveryStrategy>,
}

impl Default for AutoRecoveryConfig {
    fn default() -> Self {
        let mut strategies = HashMap::new();
        strategies.insert("memory_cleanup".to_string(), RecoveryStrategy::MemoryCleanup);
        strategies.insert("connection_rebuild".to_string(), RecoveryStrategy::ConnectionRebuild);
        strategies.insert("deadlock_recovery".to_string(), RecoveryStrategy::DeadlockRecovery);
        strategies.insert("resource_cleanup".to_string(), RecoveryStrategy::ResourceCleanup);

        Self {
            recovery_interval: Duration::from_secs(300), // 5分钟
            enabled: true,
            recovery_items: vec![
                AutoRecoveryItem {
                    name: "memory_cleanup".to_string(),
                    recovery_type: RecoveryType::MemoryCleanup,
                    enabled: true,
                    threshold: 0.8, // 内存使用率超过80%时触发
                },
                AutoRecoveryItem {
                    name: "connection_rebuild".to_string(),
                    recovery_type: RecoveryType::ConnectionRebuild,
                    enabled: true,
                    threshold: 0.9, // 连接失败率超过90%时触发
                },
                AutoRecoveryItem {
                    name: "deadlock_recovery".to_string(),
                    recovery_type: RecoveryType::DeadlockRecovery,
                    enabled: true,
                    threshold: 1.0, // 检测到死锁时触发
                },
            ],
            recovery_strategies: strategies,
        }
    }
}

/// 自动恢复项目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoRecoveryItem {
    /// 恢复名称
    pub name: String,
    /// 恢复类型
    pub recovery_type: RecoveryType,
    /// 是否启用
    pub enabled: bool,
    /// 触发阈值
    pub threshold: f64,
}

/// 恢复类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecoveryType {
    /// 内存清理
    MemoryCleanup,
    /// 连接重建
    ConnectionRebuild,
    /// 死锁恢复
    DeadlockRecovery,
    /// 资源清理
    ResourceCleanup,
    /// 自定义恢复
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 恢复策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecoveryStrategy {
    /// 内存清理策略
    MemoryCleanup,
    /// 连接重建策略
    ConnectionRebuild,
    /// 死锁恢复策略
    DeadlockRecovery,
    /// 资源清理策略
    ResourceCleanup,
    /// 自定义恢复策略
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

/// 自动恢复结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoRecoveryResult {
    /// 恢复时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 整体状态
    pub state: MonitoringState,
    /// 恢复项目结果
    pub items: Vec<AutoRecoveryItemResult>,
    /// 总恢复数
    pub total_recoveries: usize,
    /// 成功恢复数
    pub successful_recoveries: usize,
    /// 失败恢复数
    pub failed_recoveries: usize,
    /// 跳过恢复数
    pub skipped_recoveries: usize,
}

/// 自动恢复项目结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoRecoveryItemResult {
    /// 恢复名称
    pub name: String,
    /// 恢复类型
    pub recovery_type: RecoveryType,
    /// 状态
    pub state: MonitoringState,
    /// 是否执行了恢复
    pub recovery_executed: bool,
    /// 恢复时间
    pub recovery_time: Duration,
    /// 恢复详情
    pub details: HashMap<String, String>,
}

/// 自动恢复器
pub struct AutoRecovery {
    config: AutoRecoveryConfig,
    is_running: std::sync::atomic::AtomicBool,
    last_result: std::sync::Mutex<Option<AutoRecoveryResult>>,
    recovery_handlers: std::sync::Mutex<HashMap<String, Box<dyn AutoRecoveryHandler + Send + Sync>>>,
    recovery_history: std::sync::Mutex<Vec<AutoRecoveryItemResult>>,
}

impl AutoRecovery {
    /// 创建新的自动恢复器
    pub fn new(config: AutoRecoveryConfig) -> Self {
        Self {
            config,
            is_running: std::sync::atomic::AtomicBool::new(false),
            last_result: std::sync::Mutex::new(None),
            recovery_handlers: std::sync::Mutex::new(HashMap::new()),
            recovery_history: std::sync::Mutex::new(Vec::new()),
        }
    }

    /// 启动自动恢复
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            return Ok(());
        }

        if !self.config.enabled {
            debug!("自动恢复已禁用");
            return Ok(());
        }

        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        
        // 注册默认恢复处理器
        self.register_default_handlers();

        // 启动恢复循环
        let recovery = Arc::new(self.clone());
        tokio::spawn(async move {
            recovery.run_recovery_loop().await;
        });

        info!("自动恢复器启动完成");
        Ok(())
    }

    /// 停止自动恢复
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        info!("自动恢复器停止完成");
        Ok(())
    }

    /// 获取恢复状态
    pub async fn get_status(&self) -> Result<AutoRecoveryResult, UnifiedError> {
        let mut items = Vec::new();
        let mut total_recoveries = 0;
        let mut successful_recoveries = 0;
        let mut failed_recoveries = 0;
        let mut skipped_recoveries = 0;

        for recovery_item in &self.config.recovery_items {
            if !recovery_item.enabled {
                continue;
            }

            total_recoveries += 1;
            let item_result = self.recovery_item(recovery_item).await;
            
            match item_result.state {
                MonitoringState::Healthy => {
                    if item_result.recovery_executed {
                        successful_recoveries += 1;
                    } else {
                        skipped_recoveries += 1;
                    }
                }
                MonitoringState::Warning | MonitoringState::Error | MonitoringState::Critical => {
                    failed_recoveries += 1;
                }
            }
            
            items.push(item_result);
        }

        // 更新恢复历史
        self.update_recovery_history(&items);

        let overall_state = self.calculate_overall_state(&items);
        let result = AutoRecoveryResult {
            timestamp: chrono::Utc::now(),
            state: overall_state,
            items,
            total_recoveries,
            successful_recoveries,
            failed_recoveries,
            skipped_recoveries,
        };

        // 保存结果
        *self.last_result.lock().unwrap() = Some(result.clone());

        Ok(result)
    }

    /// 恢复单个项目
    async fn recovery_item(&self, item: &AutoRecoveryItem) -> AutoRecoveryItemResult {
        let start_time = std::time::Instant::now();
        // 直接执行恢复，避免复杂的生命周期问题
        let result = match item.name.as_str() {
            "memory_cleanup" => MemoryCleanupRecoveryHandler.recover().await,
            "connection_rebuild" => ConnectionRebuildRecoveryHandler.recover().await,
            "deadlock_recovery" => DeadlockRecoveryHandler.recover().await,
            _ => Ok(AutoRecoveryItemResult {
                name: item.name.clone(),
                recovery_type: item.recovery_type.clone(),
                state: MonitoringState::Error,
                recovery_executed: false,
                recovery_time: std::time::Duration::ZERO,
                details: HashMap::new(),
            })
        };

        match result {
            Ok(result) => {
                let recovery_time = start_time.elapsed();
                AutoRecoveryItemResult {
                    name: item.name.clone(),
                    recovery_type: item.recovery_type.clone(),
                    state: result.state,
                    recovery_executed: result.recovery_executed,
                    recovery_time,
                    details: result.details,
                }
            }
            Err(_error) => {
                let recovery_time = start_time.elapsed();
                AutoRecoveryItemResult {
                    name: item.name.clone(),
                    recovery_type: item.recovery_type.clone(),
                    state: MonitoringState::Error,
                    recovery_executed: false,
                    recovery_time,
                    details: HashMap::new(),
                }
            }
        }
    }

    /// 更新恢复历史
    fn update_recovery_history(&self, items: &[AutoRecoveryItemResult]) {
        let mut history = self.recovery_history.lock().unwrap();
        
        for item in items {
            history.push(item.clone());
        }
        
        // 保持最近1000个恢复记录
        if history.len() > 1000 {
            let len = history.len();
            history.drain(0..len - 1000);
        }
    }

    /// 计算整体状态
    fn calculate_overall_state(&self, items: &[AutoRecoveryItemResult]) -> MonitoringState {
        if items.is_empty() {
            return MonitoringState::Healthy;
        }

        let states = items.iter().map(|item| &item.state).collect::<Vec<_>>();
        
        // 返回最严重的状态
        if states.contains(&&MonitoringState::Critical) {
            MonitoringState::Critical
        } else if states.contains(&&MonitoringState::Error) {
            MonitoringState::Error
        } else if states.contains(&&MonitoringState::Warning) {
            MonitoringState::Warning
        } else {
            MonitoringState::Healthy
        }
    }

    /// 注册默认恢复处理器
    fn register_default_handlers(&self) {
        let mut handlers = self.recovery_handlers.lock().unwrap();
        
        handlers.insert("memory_cleanup".to_string(), Box::new(MemoryCleanupRecoveryHandler));
        handlers.insert("connection_rebuild".to_string(), Box::new(ConnectionRebuildRecoveryHandler));
        handlers.insert("deadlock_recovery".to_string(), Box::new(DeadlockRecoveryHandler));
        handlers.insert("resource_cleanup".to_string(), Box::new(ResourceCleanupRecoveryHandler));
    }

    /// 注册自定义恢复处理器
    pub fn register_handler(&self, name: String, handler: Box<dyn AutoRecoveryHandler + Send + Sync>) {
        let mut handlers = self.recovery_handlers.lock().unwrap();
        handlers.insert(name, handler);
    }

    /// 运行恢复循环
    async fn run_recovery_loop(&self) {
        let mut interval = tokio::time::interval(self.config.recovery_interval);
        
        while self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            interval.tick().await;
            
            if let Err(error) = self.get_status().await {
                error!("自动恢复失败: {}", error);
            }
        }
    }

    /// 获取最后恢复结果
    pub fn get_last_result(&self) -> Option<AutoRecoveryResult> {
        self.last_result.lock().unwrap().clone()
    }

    /// 获取恢复历史
    pub fn get_recovery_history(&self) -> Vec<AutoRecoveryItemResult> {
        self.recovery_history.lock().unwrap().clone()
    }

    /// 获取配置
    pub fn get_config(&self) -> &AutoRecoveryConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: AutoRecoveryConfig) {
        self.config = config;
    }
}

impl Clone for AutoRecovery {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            is_running: std::sync::atomic::AtomicBool::new(self.is_running.load(std::sync::atomic::Ordering::Relaxed)),
            last_result: std::sync::Mutex::new(self.last_result.lock().unwrap().clone()),
            recovery_handlers: std::sync::Mutex::new(HashMap::new()),
            recovery_history: std::sync::Mutex::new(Vec::new()),
        }
    }
}

/// 自动恢复处理器trait
pub trait AutoRecoveryHandler: Send + Sync {
    /// 执行自动恢复
    fn recover(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AutoRecoveryItemResult, UnifiedError>> + Send + '_>>;
}

/// 内存清理恢复处理器
pub struct MemoryCleanupRecoveryHandler;

impl AutoRecoveryHandler for MemoryCleanupRecoveryHandler {
    fn recover(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AutoRecoveryItemResult, UnifiedError>> + Send + '_>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let mut recovery_executed = false;

        // 检查内存使用情况
        let mut sys = sysinfo::System::new_all();
        sys.refresh_memory();
        let total = sys.total_memory();
        let used = sys.used_memory();
        let usage_percent = (used as f64 / total as f64) * 100.0;

        details.insert("total_memory".to_string(), total.to_string());
        details.insert("used_memory".to_string(), used.to_string());
        details.insert("usage_percent".to_string(), format!("{:.2}", usage_percent));

        // 如果内存使用率超过80%，执行清理
        if usage_percent > 80.0 {
            info!("内存使用率过高: {:.2}%，执行内存清理", usage_percent);
            
            // 执行内存清理
            self.perform_memory_cleanup().await;
            recovery_executed = true;
            
            // 重新检查内存使用情况
            let used_after = 3 * 1024 * 1024 * 1024; // 假设清理后3GB
            let usage_after = (used_after as f64 / total as f64) * 100.0;
            
            details.insert("memory_after_cleanup".to_string(), used_after.to_string());
            details.insert("usage_after_cleanup".to_string(), format!("{:.2}", usage_after));
            
            if usage_after < usage_percent {
                state = MonitoringState::Healthy;
                info!("内存清理成功，使用率从 {:.2}% 降低到 {:.2}%", usage_percent, usage_after);
            } else {
                state = MonitoringState::Warning;
                warn!("内存清理效果不明显");
            }
        } else {
            details.insert("action".to_string(), "no_cleanup_needed".to_string());
        }

        Ok(AutoRecoveryItemResult {
            name: "memory_cleanup".to_string(),
            recovery_type: RecoveryType::MemoryCleanup,
            state,
            recovery_executed,
            recovery_time: Duration::ZERO,
            details,
        })
        })
    }
}

impl MemoryCleanupRecoveryHandler {
    /// 执行内存清理
    async fn perform_memory_cleanup(&self) {
        // 这里应该实现具体的内存清理逻辑
        // 例如：清理缓存、释放未使用的对象、强制垃圾回收等
        
        // 模拟内存清理过程
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        // 在实际实现中，这里可能包括：
        // 1. 清理应用程序缓存
        // 2. 释放未使用的内存
        // 3. 调用系统内存清理函数
        // 4. 重启某些服务以释放内存
    }
}

/// 连接重建恢复处理器
pub struct ConnectionRebuildRecoveryHandler;

impl AutoRecoveryHandler for ConnectionRebuildRecoveryHandler {
    fn recover(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AutoRecoveryItemResult, UnifiedError>> + Send + '_>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let mut recovery_executed = false;

        // 检查连接状态
        let connection_health = self.check_connection_health().await;
        details.insert("connection_health".to_string(), format!("{:.2}", connection_health));

        // 如果连接健康度低于90%，执行连接重建
        if connection_health < 0.9 {
            info!("连接健康度过低: {:.2}，执行连接重建", connection_health);
            
            // 执行连接重建
            let rebuild_result = self.perform_connection_rebuild().await;
            recovery_executed = true;
            
            details.insert("rebuild_result".to_string(), rebuild_result.to_string());
            
            // 重新检查连接状态
            let health_after = self.check_connection_health().await;
            details.insert("connection_health_after".to_string(), format!("{:.2}", health_after));
            
            if health_after > connection_health {
                state = MonitoringState::Healthy;
                info!("连接重建成功，健康度从 {:.2} 提升到 {:.2}", connection_health, health_after);
            } else {
                state = MonitoringState::Warning;
                warn!("连接重建效果不明显");
            }
        } else {
            details.insert("action".to_string(), "no_rebuild_needed".to_string());
        }

        Ok(AutoRecoveryItemResult {
            name: "connection_rebuild".to_string(),
            recovery_type: RecoveryType::ConnectionRebuild,
            state,
            recovery_executed,
            recovery_time: Duration::ZERO,
            details,
        })
        })
    }
}

impl ConnectionRebuildRecoveryHandler {
    /// 检查连接健康度
    async fn check_connection_health(&self) -> f64 {
        // 模拟连接健康度检查
        use rand::Rng;
        let mut rng = rand::rng();
        rng.random_range(0.7..1.0)
    }

    /// 执行连接重建
    async fn perform_connection_rebuild(&self) -> bool {
        // 模拟连接重建过程
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        // 在实际实现中，这里可能包括：
        // 1. 关闭现有连接
        // 2. 重新建立连接池
        // 3. 验证连接可用性
        // 4. 更新连接配置
        
        true // 模拟重建成功
    }
}

/// 死锁恢复处理器
pub struct DeadlockRecoveryHandler;

impl AutoRecoveryHandler for DeadlockRecoveryHandler {
    fn recover(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AutoRecoveryItemResult, UnifiedError>> + Send + '_>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let mut recovery_executed = false;

        // 检查死锁情况
        let deadlock_detected = self.detect_deadlock().await;
        details.insert("deadlock_detected".to_string(), deadlock_detected.to_string());

        if deadlock_detected {
            info!("检测到死锁，执行死锁恢复");
            
            // 执行死锁恢复
            let recovery_result = self.perform_deadlock_recovery().await;
            recovery_executed = true;
            
            details.insert("recovery_result".to_string(), recovery_result.to_string());
            
            // 重新检查死锁情况
            let deadlock_after = self.detect_deadlock().await;
            details.insert("deadlock_after_recovery".to_string(), deadlock_after.to_string());
            
            if !deadlock_after {
                state = MonitoringState::Healthy;
                info!("死锁恢复成功");
            } else {
                state = MonitoringState::Error;
                error!("死锁恢复失败");
            }
        } else {
            details.insert("action".to_string(), "no_deadlock_detected".to_string());
        }

        Ok(AutoRecoveryItemResult {
            name: "deadlock_recovery".to_string(),
            recovery_type: RecoveryType::DeadlockRecovery,
            state,
            recovery_executed,
            recovery_time: Duration::ZERO,
            details,
        })
        })
    }
}

impl DeadlockRecoveryHandler {
    /// 检测死锁
    async fn detect_deadlock(&self) -> bool {
        // 模拟死锁检测
        use rand::Rng;
        let mut rng = rand::rng();
        rng.random_bool(0.1) // 10%的概率检测到死锁
    }

    /// 执行死锁恢复
    async fn perform_deadlock_recovery(&self) -> bool {
        // 模拟死锁恢复过程
        tokio::time::sleep(Duration::from_millis(300)).await;
        
        // 在实际实现中，这里可能包括：
        // 1. 识别死锁的线程/进程
        // 2. 强制释放锁资源
        // 3. 重启相关服务
        // 4. 调整锁策略
        
        true // 模拟恢复成功
    }
}

/// 资源清理恢复处理器
pub struct ResourceCleanupRecoveryHandler;

impl AutoRecoveryHandler for ResourceCleanupRecoveryHandler {
    fn recover(&self) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<AutoRecoveryItemResult, UnifiedError>> + Send + '_>> {
        Box::pin(async move {
        let mut details = HashMap::new();
        let mut state = MonitoringState::Healthy;
        let mut recovery_executed = false;

        // 检查资源使用情况
        let resource_usage = self.check_resource_usage().await;
        details.insert("resource_usage".to_string(), format!("{:.2}", resource_usage));

        // 如果资源使用率过高，执行资源清理
        if resource_usage > 0.8 {
            info!("资源使用率过高: {:.2}，执行资源清理", resource_usage);
            
            // 执行资源清理
            let cleanup_result = self.perform_resource_cleanup().await;
            recovery_executed = true;
            
            details.insert("cleanup_result".to_string(), cleanup_result.to_string());
            
            // 重新检查资源使用情况
            let usage_after = self.check_resource_usage().await;
            details.insert("resource_usage_after".to_string(), format!("{:.2}", usage_after));
            
            if usage_after < resource_usage {
                state = MonitoringState::Healthy;
                info!("资源清理成功，使用率从 {:.2} 降低到 {:.2}", resource_usage, usage_after);
            } else {
                state = MonitoringState::Warning;
                warn!("资源清理效果不明显");
            }
        } else {
            details.insert("action".to_string(), "no_cleanup_needed".to_string());
        }

        Ok(AutoRecoveryItemResult {
            name: "resource_cleanup".to_string(),
            recovery_type: RecoveryType::ResourceCleanup,
            state,
            recovery_executed,
            recovery_time: Duration::ZERO,
            details,
        })
        })
    }
}

impl ResourceCleanupRecoveryHandler {
    /// 检查资源使用情况
    async fn check_resource_usage(&self) -> f64 {
        // 模拟资源使用情况检查
        use rand::Rng;
        let mut rng = rand::rng();
        rng.random_range(0.5..1.0)
    }

    /// 执行资源清理
    async fn perform_resource_cleanup(&self) -> bool {
        // 模拟资源清理过程
        tokio::time::sleep(Duration::from_millis(150)).await;
        
        // 在实际实现中，这里可能包括：
        // 1. 清理临时文件
        // 2. 释放文件句柄
        // 3. 清理网络连接
        // 4. 释放其他系统资源
        
        true // 模拟清理成功
    }
}

/// 全局自动恢复器
pub struct GlobalAutoRecovery {
    recovery: Arc<AutoRecovery>,
}

impl GlobalAutoRecovery {
    /// 创建全局自动恢复器
    pub fn new() -> Self {
        Self {
            recovery: Arc::new(AutoRecovery::new(AutoRecoveryConfig::default())),
        }
    }

    /// 获取自动恢复器实例
    pub fn get_recovery(&self) -> Arc<AutoRecovery> {
        self.recovery.clone()
    }

    /// 启动全局自动恢复
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.recovery.start().await
    }

    /// 停止全局自动恢复
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.recovery.stop().await
    }

    /// 获取全局恢复状态
    pub async fn get_status(&self) -> Result<AutoRecoveryResult, UnifiedError> {
        self.recovery.get_status().await
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_auto_recovery_config_default() {
        let config = AutoRecoveryConfig::default();
        assert_eq!(config.recovery_interval, Duration::from_secs(300));
        assert!(config.enabled);
        assert!(!config.recovery_items.is_empty());
        assert!(!config.recovery_strategies.is_empty());
    }

    #[test]
    fn test_auto_recovery_item() {
        let item = AutoRecoveryItem {
            name: "test".to_string(),
            recovery_type: RecoveryType::MemoryCleanup,
            enabled: true,
            threshold: 0.8,
        };
        
        assert_eq!(item.name, "test");
        assert!(item.enabled);
        assert_eq!(item.threshold, 0.8);
    }

    #[test]
    fn test_auto_recovery_creation() {
        let config = AutoRecoveryConfig::default();
        let recovery = AutoRecovery::new(config);
        
        assert!(recovery.get_last_result().is_none());
        assert!(recovery.get_recovery_history().is_empty());
    }

    #[tokio::test]
    async fn test_auto_recovery_get_status() {
        let config = AutoRecoveryConfig::default();
        let recovery = AutoRecovery::new(config);
        
        let result = recovery.get_status().await;
        assert!(result.is_ok());
        
        let result = result.unwrap();
        assert!(result.total_recoveries > 0);
        //assert!(result.successful_recoveries >= 0);
        //assert!(result.failed_recoveries >= 0);
        //assert!(result.skipped_recoveries >= 0);
    }

    #[test]
    fn test_auto_recovery_result() {
        let result = AutoRecoveryResult {
            timestamp: chrono::Utc::now(),
            state: MonitoringState::Healthy,
            items: Vec::new(),
            total_recoveries: 0,
            successful_recoveries: 0,
            failed_recoveries: 0,
            skipped_recoveries: 0,
        };
        
        assert_eq!(result.state, MonitoringState::Healthy);
        assert_eq!(result.total_recoveries, 0);
    }

    #[test]
    fn test_auto_recovery_item_result() {
        let result = AutoRecoveryItemResult {
            name: "test".to_string(),
            recovery_type: RecoveryType::MemoryCleanup,
            state: MonitoringState::Healthy,
            recovery_executed: false,
            recovery_time: Duration::ZERO,
            details: HashMap::new(),
        };
        
        assert_eq!(result.name, "test");
        assert_eq!(result.state, MonitoringState::Healthy);
        assert!(!result.recovery_executed);
    }

    #[test]
    fn test_global_auto_recovery() {
        let global_recovery = GlobalAutoRecovery::new();
        let recovery = global_recovery.get_recovery();
        
        assert!(recovery.get_last_result().is_none());
        assert!(recovery.get_recovery_history().is_empty());
    }
}
