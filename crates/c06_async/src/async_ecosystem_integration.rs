//! 异步生态系统集成模块
//! 
//! 本模块展示了如何集成和组合使用不同的异步运行时和设计模式：
//! 1. 多运行时集成策略
//! 2. 聚合组合设计模式
//! 3. 异步同步转换最佳实践
//! 4. 跨运行时任务调度
//! 5. 统一异步接口设计

use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::HashMap;
use anyhow::Result;
use tokio::sync::{Mutex, RwLock, mpsc, oneshot};
use tokio::time::{sleep, timeout};
use serde::{Deserialize, Serialize};
use tracing::{info, warn, error, debug, info_span, Level};
use uuid::Uuid;

/// 异步运行时抽象接口
#[async_trait::async_trait]
pub trait AsyncRuntime: Send + Sync {
    /// 运行时名称
    fn name(&self) -> &str;
    
    /// 启动运行时
    async fn start(&self) -> Result<()>;
    
    /// 停止运行时
    async fn stop(&self) -> Result<()>;
    
    /// 执行异步任务
    async fn spawn<F, T>(&self, future: F) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static;
    
    /// 阻塞等待任务完成
    async fn block_on<F, T>(&self, future: F) -> Result<T>
    where
        F: std::future::Future<Output = T>;
    
    /// 获取运行时状态
    async fn get_status(&self) -> RuntimeStatus;
}

/// 运行时状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeStatus {
    pub name: String,
    pub is_running: bool,
    pub active_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub memory_usage: u64,
    pub cpu_usage: f64,
}

/// Tokio运行时实现
pub struct TokioRuntime {
    runtime: Arc<tokio::runtime::Runtime>,
    status: Arc<Mutex<RuntimeStatus>>,
}

impl TokioRuntime {
    pub fn new() -> Self {
        let runtime = Arc::new(
            tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime")
        );
        
        let status = Arc::new(Mutex::new(RuntimeStatus {
            name: "Tokio".to_string(),
            is_running: false,
            active_tasks: 0,
            completed_tasks: 0,
            failed_tasks: 0,
            memory_usage: 0,
            cpu_usage: 0.0,
        }));
        
        Self { runtime, status }
    }
}

#[async_trait::async_trait]
impl AsyncRuntime for TokioRuntime {
    fn name(&self) -> &str {
        "Tokio"
    }
    
    async fn start(&self) -> Result<()> {
        let mut status = self.status.lock().await;
        status.is_running = true;
        info!("Tokio运行时已启动");
        Ok(())
    }
    
    async fn stop(&self) -> Result<()> {
        let mut status = self.status.lock().await;
        status.is_running = false;
        info!("Tokio运行时已停止");
        Ok(())
    }
    
    async fn spawn<F, T>(&self, future: F) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let handle = self.runtime.spawn(future);
        let result = handle.await.map_err(|e| anyhow::anyhow!("Task failed: {}", e))?;
        Ok(result)
    }
    
    async fn block_on<F, T>(&self, future: F) -> Result<T>
    where
        F: std::future::Future<Output = T>,
    {
        let result = self.runtime.block_on(future);
        Ok(result)
    }
    
    async fn get_status(&self) -> RuntimeStatus {
        let status = self.status.lock().await;
        status.clone()
    }
}

/// Smol运行时实现
pub struct SmolRuntime {
    executor: Arc<smol::Executor<'static>>,
    status: Arc<Mutex<RuntimeStatus>>,
}

impl SmolRuntime {
    pub fn new() -> Self {
        let executor = Arc::new(smol::Executor::new());
        
        let status = Arc::new(Mutex::new(RuntimeStatus {
            name: "Smol".to_string(),
            is_running: false,
            active_tasks: 0,
            completed_tasks: 0,
            failed_tasks: 0,
            memory_usage: 0,
            cpu_usage: 0.0,
        }));
        
        Self { executor, status }
    }
}

#[async_trait::async_trait]
impl AsyncRuntime for SmolRuntime {
    fn name(&self) -> &str {
        "Smol"
    }
    
    async fn start(&self) -> Result<()> {
        let mut status = self.status.lock().await;
        status.is_running = true;
        info!("Smol运行时已启动");
        Ok(())
    }
    
    async fn stop(&self) -> Result<()> {
        let mut status = self.status.lock().await;
        status.is_running = false;
        info!("Smol运行时已停止");
        Ok(())
    }
    
    async fn spawn<F, T>(&self, future: F) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let result = self.executor.run(future).await;
        Ok(result)
    }
    
    async fn block_on<F, T>(&self, future: F) -> Result<T>
    where
        F: std::future::Future<Output = T>,
    {
        let result = smol::block_on(future);
        Ok(result)
    }
    
    async fn get_status(&self) -> RuntimeStatus {
        let status = self.status.lock().await;
        status.clone()
    }
}

/// 异步运行时管理器
/// 实现聚合模式，统一管理多个运行时
pub struct AsyncRuntimeManager {
    runtimes: Arc<RwLock<HashMap<String, Arc<dyn AsyncRuntime>>>>,
    default_runtime: String,
    task_distributor: Arc<TaskDistributor>,
}

impl AsyncRuntimeManager {
    pub fn new(default_runtime: String) -> Self {
        Self {
            runtimes: Arc::new(RwLock::new(HashMap::new())),
            default_runtime,
            task_distributor: Arc::new(TaskDistributor::new()),
        }
    }
    
    /// 注册运行时
    pub async fn register_runtime(&self, name: String, runtime: Arc<dyn AsyncRuntime>) -> Result<()> {
        let mut runtimes = self.runtimes.write().await;
        runtimes.insert(name.clone(), runtime);
        info!("运行时已注册: {}", name);
        Ok(())
    }
    
    /// 获取运行时
    pub async fn get_runtime(&self, name: &str) -> Option<Arc<dyn AsyncRuntime>> {
        let runtimes = self.runtimes.read().await;
        runtimes.get(name).cloned()
    }
    
    /// 获取默认运行时
    pub async fn get_default_runtime(&self) -> Option<Arc<dyn AsyncRuntime>> {
        self.get_runtime(&self.default_runtime).await
    }
    
    /// 启动所有运行时
    pub async fn start_all(&self) -> Result<()> {
        let runtimes = self.runtimes.read().await;
        for (name, runtime) in runtimes.iter() {
            runtime.start().await?;
            info!("运行时已启动: {}", name);
        }
        Ok(())
    }
    
    /// 停止所有运行时
    pub async fn stop_all(&self) -> Result<()> {
        let runtimes = self.runtimes.read().await;
        for (name, runtime) in runtimes.iter() {
            runtime.stop().await?;
            info!("运行时已停止: {}", name);
        }
        Ok(())
    }
    
    /// 智能任务分发
    pub async fn spawn_task<F, T>(
        &self,
        task_name: String,
        future: F,
        preferred_runtime: Option<String>,
    ) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let runtime_name = preferred_runtime.unwrap_or_else(|| self.default_runtime.clone());
        let runtime = self.get_runtime(&runtime_name).await
            .ok_or_else(|| anyhow::anyhow!("运行时不存在: {}", runtime_name))?;
        
        // 使用任务分发器进行智能分发
        let result = self.task_distributor.distribute_task(
            task_name,
            runtime,
            future,
        ).await?;
        
        Ok(result)
    }
    
    /// 获取所有运行时状态
    pub async fn get_all_status(&self) -> Vec<RuntimeStatus> {
        let runtimes = self.runtimes.read().await;
        let mut statuses = Vec::new();
        
        for runtime in runtimes.values() {
            let status = runtime.get_status().await;
            statuses.push(status);
        }
        
        statuses
    }
}

/// 任务分发器
/// 实现策略模式，根据任务特性选择最优运行时
pub struct TaskDistributor {
    strategies: Arc<RwLock<HashMap<String, Box<dyn TaskDistributionStrategy>>>>,
}

impl TaskDistributor {
    pub fn new() -> Self {
        let strategies = Arc::new(RwLock::new(HashMap::new()));
        let distributor = Self { strategies };
        
        // 注册默认策略
        tokio::spawn(async {
            distributor.register_strategy(
                "default".to_string(),
                Box::new(DefaultDistributionStrategy::new()),
            ).await;
            
            distributor.register_strategy(
                "performance".to_string(),
                Box::new(PerformanceDistributionStrategy::new()),
            ).await;
            
            distributor.register_strategy(
                "resource_aware".to_string(),
                Box::new(ResourceAwareDistributionStrategy::new()),
            ).await;
        });
        
        distributor
    }
    
    async fn register_strategy(
        &self,
        name: String,
        strategy: Box<dyn TaskDistributionStrategy>,
    ) {
        let mut strategies = self.strategies.write().await;
        strategies.insert(name, strategy);
    }
    
    async fn distribute_task<F, T>(
        &self,
        task_name: String,
        runtime: Arc<dyn AsyncRuntime>,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        // 根据任务名称选择分发策略
        let strategy_name = self.select_strategy(&task_name).await;
        let strategies = self.strategies.read().await;
        
        if let Some(strategy) = strategies.get(&strategy_name) {
            strategy.execute_task(task_name, runtime, future).await
        } else {
            // 使用默认策略
            runtime.spawn(future).await
        }
    }
    
    async fn select_strategy(&self, task_name: &str) -> String {
        // 根据任务名称选择策略
        if task_name.contains("network") || task_name.contains("http") {
            "performance".to_string()
        } else if task_name.contains("compute") || task_name.contains("cpu") {
            "resource_aware".to_string()
        } else {
            "default".to_string()
        }
    }
}

/// 任务分发策略接口
#[async_trait::async_trait]
pub trait TaskDistributionStrategy: Send + Sync {
    async fn execute_task<F, T>(
        &self,
        task_name: String,
        runtime: Arc<dyn AsyncRuntime>,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static;
}

/// 默认分发策略
pub struct DefaultDistributionStrategy;

impl DefaultDistributionStrategy {
    pub fn new() -> Self {
        Self
    }
}

#[async_trait::async_trait]
impl TaskDistributionStrategy for DefaultDistributionStrategy {
    async fn execute_task<F, T>(
        &self,
        task_name: String,
        runtime: Arc<dyn AsyncRuntime>,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        info!("使用默认策略执行任务: {}", task_name);
        runtime.spawn(future).await
    }
}

/// 性能优化分发策略
pub struct PerformanceDistributionStrategy;

impl PerformanceDistributionStrategy {
    pub fn new() -> Self {
        Self
    }
}

#[async_trait::async_trait]
impl TaskDistributionStrategy for PerformanceDistributionStrategy {
    async fn execute_task<F, T>(
        &self,
        task_name: String,
        runtime: Arc<dyn AsyncRuntime>,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        info!("使用性能优化策略执行任务: {}", task_name);
        
        // 添加性能监控
        let start_time = Instant::now();
        let result = runtime.spawn(future).await?;
        let execution_time = start_time.elapsed();
        
        info!(
            task_name = %task_name,
            execution_time_ms = execution_time.as_millis(),
            "任务执行完成"
        );
        
        Ok(result)
    }
}

/// 资源感知分发策略
pub struct ResourceAwareDistributionStrategy;

impl ResourceAwareDistributionStrategy {
    pub fn new() -> Self {
        Self
    }
}

#[async_trait::async_trait]
impl TaskDistributionStrategy for ResourceAwareDistributionStrategy {
    async fn execute_task<F, T>(
        &self,
        task_name: String,
        runtime: Arc<dyn AsyncRuntime>,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        info!("使用资源感知策略执行任务: {}", task_name);
        
        // 检查运行时状态
        let status = runtime.get_status().await;
        if status.cpu_usage > 80.0 {
            warn!("运行时CPU使用率过高: {:.1}%", status.cpu_usage);
        }
        
        if status.memory_usage > 1024 * 1024 * 1024 { // 1GB
            warn!("运行时内存使用过高: {} MB", status.memory_usage / 1024 / 1024);
        }
        
        runtime.spawn(future).await
    }
}

/// 异步任务包装器
/// 实现装饰器模式，为任务添加额外功能
pub struct AsyncTaskWrapper<T> {
    inner: T,
    task_id: String,
    start_time: Instant,
    logger: Arc<dyn AsyncLogger>,
}

impl<T> AsyncTaskWrapper<T> {
    pub fn new(inner: T, task_id: String, logger: Arc<dyn AsyncLogger>) -> Self {
        Self {
            inner,
            task_id,
            start_time: Instant::now(),
            logger,
        }
    }
    
    pub async fn execute<F, R>(&self, future: F) -> Result<R>
    where
        F: std::future::Future<Output = Result<R>>,
    {
        self.logger.log_task_start(&self.task_id).await;
        
        let result = future.await;
        
        let execution_time = self.start_time.elapsed();
        match &result {
            Ok(_) => {
                self.logger.log_task_success(&self.task_id, execution_time).await;
            }
            Err(e) => {
                self.logger.log_task_failure(&self.task_id, execution_time, e).await;
            }
        }
        
        result
    }
}

/// 异步日志记录器接口
#[async_trait::async_trait]
pub trait AsyncLogger: Send + Sync {
    async fn log_task_start(&self, task_id: &str);
    async fn log_task_success(&self, task_id: &str, execution_time: Duration);
    async fn log_task_failure(&self, task_id: &str, execution_time: Duration, error: &dyn std::fmt::Display);
}

/// 简单异步日志记录器实现
pub struct SimpleAsyncLogger;

#[async_trait::async_trait]
impl AsyncLogger for SimpleAsyncLogger {
    async fn log_task_start(&self, task_id: &str) {
        info!(task_id = %task_id, "任务开始执行");
    }
    
    async fn log_task_success(&self, task_id: &str, execution_time: Duration) {
        info!(
            task_id = %task_id,
            execution_time_ms = execution_time.as_millis(),
            "任务执行成功"
        );
    }
    
    async fn log_task_failure(&self, task_id: &str, execution_time: Duration, error: &dyn std::fmt::Display) {
        error!(
            task_id = %task_id,
            execution_time_ms = execution_time.as_millis(),
            error = %error,
            "任务执行失败"
        );
    }
}

/// 异步同步转换器
/// 提供异步和同步代码之间的转换功能
pub struct AsyncSyncConverter {
    runtime_manager: Arc<AsyncRuntimeManager>,
}

impl AsyncSyncConverter {
    pub fn new(runtime_manager: Arc<AsyncRuntimeManager>) -> Self {
        Self { runtime_manager }
    }
    
    /// 异步转同步
    pub async fn async_to_sync<F, T>(&self, future: F) -> Result<T>
    where
        F: std::future::Future<Output = T>,
    {
        let runtime = self.runtime_manager.get_default_runtime().await
            .ok_or_else(|| anyhow::anyhow!("默认运行时不可用"))?;
        
        runtime.block_on(future).await
    }
    
    /// 同步转异步
    pub async fn sync_to_async<F, T>(&self, sync_fn: F) -> Result<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        let runtime = self.runtime_manager.get_default_runtime().await
            .ok_or_else(|| anyhow::anyhow!("默认运行时不可用"))?;
        
        runtime.spawn(async move {
            tokio::task::spawn_blocking(sync_fn).await.unwrap()
        }).await
    }
    
    /// 跨运行时转换
    pub async fn cross_runtime_convert<F, T>(
        &self,
        source_runtime: &str,
        target_runtime: &str,
        future: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let source = self.runtime_manager.get_runtime(source_runtime).await
            .ok_or_else(|| anyhow::anyhow!("源运行时不存在: {}", source_runtime))?;
        
        let target = self.runtime_manager.get_runtime(target_runtime).await
            .ok_or_else(|| anyhow::anyhow!("目标运行时不存在: {}", target_runtime))?;
        
        // 在源运行时中执行
        let result = source.spawn(future).await?;
        
        // 在目标运行时中重新包装（如果需要）
        target.spawn(async { result }).await
    }
}

/// 异步生态系统集成演示
pub async fn demonstrate_async_ecosystem_integration() -> Result<()> {
    println!("🚀 异步生态系统集成演示");
    println!("================================================");
    
    // 1. 创建运行时管理器
    let runtime_manager = Arc::new(AsyncRuntimeManager::new("tokio".to_string()));
    
    // 2. 注册运行时
    let tokio_runtime = Arc::new(TokioRuntime::new()) as Arc<dyn AsyncRuntime>;
    let smol_runtime = Arc::new(SmolRuntime::new()) as Arc<dyn AsyncRuntime>;
    
    runtime_manager.register_runtime("tokio".to_string(), tokio_runtime).await?;
    runtime_manager.register_runtime("smol".to_string(), smol_runtime).await?;
    
    // 3. 启动所有运行时
    runtime_manager.start_all().await?;
    
    // 4. 演示智能任务分发
    println!("\n📊 1. 智能任务分发演示:");
    let result1 = runtime_manager.spawn_task(
        "网络请求任务".to_string(),
        async {
            sleep(Duration::from_millis(100)).await;
            "网络请求完成".to_string()
        },
        Some("tokio".to_string()),
    ).await?;
    
    println!("网络任务结果: {}", result1);
    
    let result2 = runtime_manager.spawn_task(
        "计算密集型任务".to_string(),
        async {
            sleep(Duration::from_millis(50)).await;
            "计算任务完成".to_string()
        },
        Some("smol".to_string()),
    ).await?;
    
    println!("计算任务结果: {}", result2);
    
    // 5. 演示任务包装器
    println!("\n🎨 2. 任务包装器演示:");
    let logger = Arc::new(SimpleAsyncLogger);
    let task_id = Uuid::new_v4().to_string();
    let wrapper = AsyncTaskWrapper::new(
        "包装任务".to_string(),
        task_id.clone(),
        logger,
    );
    
    let wrapped_result = wrapper.execute(async {
        sleep(Duration::from_millis(75)).await;
        Ok("包装任务完成".to_string())
    }).await?;
    
    println!("包装任务结果: {}", wrapped_result);
    
    // 6. 演示异步同步转换
    println!("\n🔄 3. 异步同步转换演示:");
    let converter = AsyncSyncConverter::new(runtime_manager.clone());
    
    // 异步转同步
    let sync_result = converter.async_to_sync(async {
        sleep(Duration::from_millis(25)).await;
        "异步转同步完成".to_string()
    }).await?;
    
    println!("异步转同步结果: {}", sync_result);
    
    // 同步转异步
    let async_result = converter.sync_to_async(|| {
        std::thread::sleep(Duration::from_millis(25));
        "同步转异步完成".to_string()
    }).await?;
    
    println!("同步转异步结果: {}", async_result);
    
    // 7. 演示跨运行时转换
    println!("\n🌐 4. 跨运行时转换演示:");
    let cross_result = converter.cross_runtime_convert(
        "tokio",
        "smol",
        async {
            sleep(Duration::from_millis(30)).await;
            "跨运行时转换完成".to_string()
        },
    ).await?;
    
    println!("跨运行时转换结果: {}", cross_result);
    
    // 8. 获取运行时状态
    println!("\n📈 5. 运行时状态监控:");
    let statuses = runtime_manager.get_all_status().await;
    for status in statuses {
        println!("运行时: {}", status.name);
        println!("  运行状态: {}", if status.is_running { "运行中" } else { "已停止" });
        println!("  活跃任务: {}", status.active_tasks);
        println!("  完成任务: {}", status.completed_tasks);
        println!("  失败任务: {}", status.failed_tasks);
        println!("  内存使用: {} MB", status.memory_usage / 1024 / 1024);
        println!("  CPU使用率: {:.1}%", status.cpu_usage);
    }
    
    // 9. 停止所有运行时
    runtime_manager.stop_all().await?;
    
    println!("\n✅ 异步生态系统集成演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_runtime_manager() {
        let manager = AsyncRuntimeManager::new("tokio".to_string());
        let tokio_runtime = Arc::new(TokioRuntime::new()) as Arc<dyn AsyncRuntime>;
        
        manager.register_runtime("tokio".to_string(), tokio_runtime).await.unwrap();
        manager.start_all().await.unwrap();
        
        let result = manager.spawn_task(
            "测试任务".to_string(),
            async { "测试结果".to_string() },
            Some("tokio".to_string()),
        ).await.unwrap();
        
        assert_eq!(result, "测试结果");
        
        manager.stop_all().await.unwrap();
    }
    
    #[tokio::test]
    async fn test_task_wrapper() {
        let logger = Arc::new(SimpleAsyncLogger);
        let task_id = "test_task".to_string();
        let wrapper = AsyncTaskWrapper::new("测试".to_string(), task_id, logger);
        
        let result = wrapper.execute(async { Ok("成功".to_string()) }).await.unwrap();
        assert_eq!(result, "成功");
    }
    
    #[tokio::test]
    async fn test_async_sync_converter() {
        let manager = Arc::new(AsyncRuntimeManager::new("tokio".to_string()));
        let tokio_runtime = Arc::new(TokioRuntime::new()) as Arc<dyn AsyncRuntime>;
        manager.register_runtime("tokio".to_string(), tokio_runtime).await.unwrap();
        manager.start_all().await.unwrap();
        
        let converter = AsyncSyncConverter::new(manager);
        
        let result = converter.async_to_sync(async { "转换成功".to_string() }).await.unwrap();
        assert_eq!(result, "转换成功");
    }
}
