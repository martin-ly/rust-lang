//! 异步日志调试和跟踪模块
//!
//! 本模块提供了完整的异步日志系统，包括：
//! - 结构化日志记录
//! - 异步任务跟踪
//! - 性能监控
//! - 本地调试工具
//! - 分布式追踪支持
use anyhow::Result;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};
use tokio::time::sleep;
use tracing::{Level, debug, error, info, info_span, warn};
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

/// 自定义序列化函数，跳过 Instant 字段
fn serialize_instant<S>(_instant: &Instant, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    // 对于 Instant，我们返回一个占位符值或跳过
    serializer.serialize_none()
}

/// 自定义反序列化函数，为 Instant 字段提供默认值
fn deserialize_instant<'de, D>(_deserializer: D) -> Result<Instant, D::Error>
where
    D: Deserializer<'de>,
{
    // 反序列化时返回当前时间
    Ok(Instant::now())
}

/// 异步日志配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncLoggingConfig {
    /// 日志级别
    pub log_level: String,
    /// 是否启用结构化日志
    pub enable_structured_logging: bool,
    /// 是否启用性能监控
    pub enable_performance_monitoring: bool,
    /// 是否启用分布式追踪
    pub enable_distributed_tracing: bool,
    /// 日志输出格式
    pub log_format: LogFormat,
    /// 最大日志文件大小（MB）
    pub max_log_file_size_mb: u64,
    /// 日志文件保留天数
    pub log_retention_days: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogFormat {
    Json,
    Text,
    Compact,
}

impl Default for AsyncLoggingConfig {
    fn default() -> Self {
        Self {
            log_level: "info".to_string(),
            enable_structured_logging: true,
            enable_performance_monitoring: true,
            enable_distributed_tracing: false,
            log_format: LogFormat::Text,
            max_log_file_size_mb: 100,
            log_retention_days: 7,
        }
    }
}

/// 异步任务信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AsyncTaskInfo {
    /// 任务ID
    pub task_id: String,
    /// 任务名称
    pub name: String,
    /// 开始时间
    #[serde(
        serialize_with = "serialize_instant",
        deserialize_with = "deserialize_instant"
    )]
    pub start_time: Instant,
    /// 任务状态
    pub status: TaskStatus,
    /// 任务优先级
    pub priority: TaskPriority,
    /// 任务元数据
    pub metadata: HashMap<String, String>,
    /// 错误信息（如果有）
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TaskStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Cancelled,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

/// 性能指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    /// 总任务数
    pub total_tasks: u64,
    /// 成功任务数
    pub successful_tasks: u64,
    /// 失败任务数
    pub failed_tasks: u64,
    /// 取消任务数
    pub cancelled_tasks: u64,
    /// 平均执行时间（纳秒）
    pub average_execution_time_ns: u64,
    /// 最大执行时间（纳秒）
    pub max_execution_time_ns: u64,
    /// 最小执行时间（纳秒）
    pub min_execution_time_ns: u64,
    /// 成功率
    pub success_rate: f64,
    /// 吞吐量（任务/秒）
    pub throughput_tasks_per_second: f64,
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self {
            total_tasks: 0,
            successful_tasks: 0,
            failed_tasks: 0,
            cancelled_tasks: 0,
            average_execution_time_ns: 0,
            max_execution_time_ns: 0,
            min_execution_time_ns: u64::MAX,
            success_rate: 0.0,
            throughput_tasks_per_second: 0.0,
        }
    }
}

/// 异步任务跟踪器
pub struct AsyncTaskTracker {
    config: AsyncLoggingConfig,
    tasks: Arc<RwLock<HashMap<String, AsyncTaskInfo>>>,
    performance_monitor: Arc<AsyncPerformanceMonitor>,
    task_counter: AtomicU64,
}

impl AsyncTaskTracker {
    pub fn new(config: AsyncLoggingConfig) -> Self {
        Self {
            config,
            tasks: Arc::new(RwLock::new(HashMap::new())),
            performance_monitor: Arc::new(AsyncPerformanceMonitor::new()),
            task_counter: AtomicU64::new(0),
        }
    }

    /// 初始化日志系统
    pub fn init_logging(&self) -> Result<()> {
        let env_filter = EnvFilter::try_from_default_env()
            .unwrap_or_else(|_| EnvFilter::new(&self.config.log_level));

        let registry = tracing_subscriber::registry().with(env_filter);

        match self.config.log_format {
            LogFormat::Json => {
                registry
                    .with(tracing_subscriber::fmt::layer().json())
                    .init();
            }
            LogFormat::Text => {
                registry.with(tracing_subscriber::fmt::layer()).init();
            }
            LogFormat::Compact => {
                registry
                    .with(tracing_subscriber::fmt::layer().compact())
                    .init();
            }
        }

        info!("异步日志系统已初始化");
        Ok(())
    }

    /// 开始跟踪任务
    pub async fn start_task(
        &self,
        name: String,
        priority: TaskPriority,
        metadata: HashMap<String, String>,
    ) -> String {
        let task_id = format!("task_{}", self.task_counter.fetch_add(1, Ordering::Relaxed));

        let task_info = AsyncTaskInfo {
            task_id: task_id.clone(),
            name: name.clone(),
            start_time: Instant::now(),
            status: TaskStatus::Running,
            priority,
            metadata,
            error: None,
        };

        {
            let mut tasks = self.tasks.write().await;
            tasks.insert(task_id.clone(), task_info);
        }

        info!(
            task_id = %task_id,
            task_name = %name,
            "任务开始执行"
        );

        task_id
    }

    /// 完成任务
    pub async fn complete_task(&self, task_id: &str) -> Result<()> {
        let execution_time = {
            let mut tasks = self.tasks.write().await;
            if let Some(task_info) = tasks.get_mut(task_id) {
                let execution_time = task_info.start_time.elapsed();
                task_info.status = TaskStatus::Completed;
                execution_time
            } else {
                return Err(anyhow::anyhow!("任务不存在: {}", task_id));
            }
        };

        self.performance_monitor
            .record_task_completion(execution_time, true)
            .await;

        info!(
            task_id = %task_id,
            execution_time_ms = execution_time.as_millis(),
            "任务执行完成"
        );

        Ok(())
    }

    /// 任务失败
    pub async fn fail_task(&self, task_id: &str, error: String) -> Result<()> {
        let execution_time = {
            let mut tasks = self.tasks.write().await;
            if let Some(task_info) = tasks.get_mut(task_id) {
                let execution_time = task_info.start_time.elapsed();
                task_info.status = TaskStatus::Failed;
                task_info.error = Some(error.clone());
                execution_time
            } else {
                return Err(anyhow::anyhow!("任务不存在: {}", task_id));
            }
        };

        self.performance_monitor
            .record_task_completion(execution_time, false)
            .await;

        error!(
            task_id = %task_id,
            execution_time_ms = execution_time.as_millis(),
            error = %error,
            "任务执行失败"
        );

        Ok(())
    }

    /// 取消任务
    pub async fn cancel_task(&self, task_id: &str) -> Result<()> {
        let execution_time = {
            let mut tasks = self.tasks.write().await;
            if let Some(task_info) = tasks.get_mut(task_id) {
                let execution_time = task_info.start_time.elapsed();
                task_info.status = TaskStatus::Cancelled;
                execution_time
            } else {
                return Err(anyhow::anyhow!("任务不存在: {}", task_id));
            }
        };

        self.performance_monitor
            .record_task_cancellation(execution_time)
            .await;

        warn!(
            task_id = %task_id,
            execution_time_ms = execution_time.as_millis(),
            "任务被取消"
        );

        Ok(())
    }

    /// 获取任务信息
    pub async fn get_task_info(&self, task_id: &str) -> Option<AsyncTaskInfo> {
        let tasks = self.tasks.read().await;
        tasks.get(task_id).cloned()
    }

    /// 获取所有任务信息
    pub async fn get_all_tasks(&self) -> Vec<AsyncTaskInfo> {
        let tasks = self.tasks.read().await;
        tasks.values().cloned().collect()
    }

    /// 获取性能指标
    pub async fn get_performance_metrics(&self) -> PerformanceMetrics {
        self.performance_monitor.get_metrics().await
    }

    /// 清理已完成的任务
    pub async fn cleanup_completed_tasks(&self) -> Result<()> {
        let mut tasks = self.tasks.write().await;
        let initial_count = tasks.len();

        tasks.retain(|_, task_info| {
            matches!(task_info.status, TaskStatus::Running | TaskStatus::Pending)
        });

        let cleaned_count = initial_count - tasks.len();
        info!("清理了 {} 个已完成的任务", cleaned_count);

        Ok(())
    }
}

/// 异步性能监控器
pub struct AsyncPerformanceMonitor {
    metrics: Arc<Mutex<PerformanceMetrics>>,
    start_time: Instant,
}

impl Default for AsyncPerformanceMonitor {
    fn default() -> Self {
        Self::new()
    }
}

impl AsyncPerformanceMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(Mutex::new(PerformanceMetrics::default())),
            start_time: Instant::now(),
        }
    }

    pub async fn record_task_completion(&self, execution_time: Duration, success: bool) {
        let mut metrics = self.metrics.lock().await;

        metrics.total_tasks += 1;
        let execution_time_ns = execution_time.as_nanos() as u64;

        if success {
            metrics.successful_tasks += 1;
        } else {
            metrics.failed_tasks += 1;
        }

        // 更新执行时间统计
        metrics.average_execution_time_ns =
            (metrics.average_execution_time_ns * (metrics.total_tasks - 1) + execution_time_ns)
                / metrics.total_tasks;

        metrics.max_execution_time_ns = metrics.max_execution_time_ns.max(execution_time_ns);
        metrics.min_execution_time_ns = metrics.min_execution_time_ns.min(execution_time_ns);

        // 计算成功率
        metrics.success_rate =
            (metrics.successful_tasks as f64 / metrics.total_tasks as f64) * 100.0;

        // 计算吞吐量
        let elapsed_seconds = self.start_time.elapsed().as_secs_f64();
        if elapsed_seconds > 0.0 {
            metrics.throughput_tasks_per_second = metrics.total_tasks as f64 / elapsed_seconds;
        }
    }

    pub async fn record_task_cancellation(&self, execution_time: Duration) {
        let mut metrics = self.metrics.lock().await;
        metrics.total_tasks += 1;
        metrics.cancelled_tasks += 1;

        let execution_time_ns = execution_time.as_nanos() as u64;
        metrics.average_execution_time_ns =
            (metrics.average_execution_time_ns * (metrics.total_tasks - 1) + execution_time_ns)
                / metrics.total_tasks;
    }

    pub async fn get_metrics(&self) -> PerformanceMetrics {
        self.metrics.lock().await.clone()
    }

    pub async fn reset_metrics(&self) {
        let mut metrics = self.metrics.lock().await;
        *metrics = PerformanceMetrics::default();
    }
}

/// 异步日志装饰器
pub struct AsyncLoggingDecorator {
    tracker: Arc<AsyncTaskTracker>,
}

impl AsyncLoggingDecorator {
    pub fn new(tracker: Arc<AsyncTaskTracker>) -> Self {
        Self { tracker }
    }

    /// 装饰异步函数，自动添加日志和跟踪
    pub async fn execute_with_logging<F, T>(
        &self,
        name: String,
        priority: TaskPriority,
        metadata: HashMap<String, String>,
        operation: F,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>>,
    {
        let task_id = self
            .tracker
            .start_task(name.clone(), priority, metadata)
            .await;

        let result = operation.await;

        match result {
            Ok(value) => {
                self.tracker.complete_task(&task_id).await?;
                Ok(value)
            }
            Err(e) => {
                self.tracker.fail_task(&task_id, e.to_string()).await?;
                Err(e)
            }
        }
    }
}

/// 结构化日志记录器
/// 日志记录器用于记录结构化日志，并将其与异步任务跟踪和性能监控集成在一起
#[allow(dead_code)]
pub struct StructuredLogger {
    tracker: Arc<AsyncTaskTracker>,
}

impl StructuredLogger {
    pub fn new(tracker: Arc<AsyncTaskTracker>) -> Self {
        Self { tracker }
    }

    /// 记录结构化日志
    pub async fn log_structured(
        &self,
        level: Level,
        message: &str,
        fields: HashMap<String, String>,
    ) {
        let span = info_span!(
            "structured_log",
            level = %level,
            message = %message
        );
        let _enter = span.enter();

        match level {
            Level::ERROR => error!(?fields, "{}", message),
            Level::WARN => warn!(?fields, "{}", message),
            Level::INFO => info!(?fields, "{}", message),
            Level::DEBUG => debug!(?fields, "{}", message),
            Level::TRACE => tracing::trace!(?fields, "{}", message),
        }
    }

    /// 记录业务事件
    pub async fn log_business_event(
        &self,
        event_type: &str,
        user_id: Option<u64>,
        details: HashMap<String, String>,
    ) {
        let mut fields = details;
        if let Some(uid) = user_id {
            fields.insert("user_id".to_string(), uid.to_string());
        }
        fields.insert("event_type".to_string(), event_type.to_string());

        self.log_structured(Level::INFO, "业务事件", fields).await;
    }

    /// 记录性能事件
    pub async fn log_performance_event(&self, operation: &str, duration: Duration, success: bool) {
        let mut fields = HashMap::new();
        fields.insert("operation".to_string(), operation.to_string());
        fields.insert("duration_ms".to_string(), duration.as_millis().to_string());
        fields.insert("success".to_string(), success.to_string());

        let level = if success { Level::INFO } else { Level::WARN };
        self.log_structured(level, "性能事件", fields).await;
    }
}

/// 本地调试工具
pub struct LocalDebugger {
    tracker: Arc<AsyncTaskTracker>,
    breakpoints: Arc<RwLock<HashMap<String, bool>>>,
}

impl LocalDebugger {
    pub fn new(tracker: Arc<AsyncTaskTracker>) -> Self {
        Self {
            tracker,
            breakpoints: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 设置断点
    pub async fn set_breakpoint(&self, task_name: &str) {
        let mut breakpoints = self.breakpoints.write().await;
        breakpoints.insert(task_name.to_string(), true);
        info!("断点已设置: {}", task_name);
    }

    /// 清除断点
    pub async fn clear_breakpoint(&self, task_name: &str) {
        let mut breakpoints = self.breakpoints.write().await;
        breakpoints.remove(task_name);
        info!("断点已清除: {}", task_name);
    }

    /// 检查断点
    pub async fn check_breakpoint(&self, task_name: &str) -> bool {
        let breakpoints = self.breakpoints.read().await;
        breakpoints.get(task_name).copied().unwrap_or(false)
    }

    /// 调试模式执行任务
    pub async fn debug_execute<F, T>(&self, task_name: &str, operation: F) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>>,
    {
        if self.check_breakpoint(task_name).await {
            info!("🔍 断点触发: {}", task_name);
            // 在实际应用中，这里可以暂停执行或输出调试信息
            sleep(Duration::from_millis(100)).await; // 模拟调试暂停
        }

        let result = operation.await;

        match &result {
            Ok(_) => info!("✅ 调试任务完成: {}", task_name),
            Err(e) => error!("❌ 调试任务失败: {} - {}", task_name, e),
        }

        result
    }

    /// 获取调试信息
    pub async fn get_debug_info(&self) -> DebugInfo {
        let tasks = self.tracker.get_all_tasks().await;
        let metrics = self.tracker.get_performance_metrics().await;
        let breakpoints = self.breakpoints.read().await;

        DebugInfo {
            active_tasks: tasks.len(),
            total_tasks: metrics.total_tasks,
            success_rate: metrics.success_rate,
            active_breakpoints: breakpoints.len(),
            running_tasks: tasks
                .iter()
                .filter(|t| matches!(t.status, TaskStatus::Running))
                .count(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DebugInfo {
    pub active_tasks: usize,
    pub total_tasks: u64,
    pub success_rate: f64,
    pub active_breakpoints: usize,
    pub running_tasks: usize,
}

/// 综合演示函数
pub async fn demonstrate_async_logging_debugging() -> Result<()> {
    println!("🚀 异步日志调试和跟踪系统演示");
    println!("================================================");

    // 1. 初始化日志系统
    let config = AsyncLoggingConfig::default();
    let tracker = Arc::new(AsyncTaskTracker::new(config));
    tracker.init_logging()?;

    // 2. 创建日志装饰器和调试器
    let decorator = AsyncLoggingDecorator::new(tracker.clone());
    let logger = StructuredLogger::new(tracker.clone());
    let debugger = LocalDebugger::new(tracker.clone());

    // 3. 演示结构化日志记录
    println!("\n📝 1. 结构化日志记录演示:");
    let mut fields = HashMap::new();
    fields.insert("user_id".to_string(), "12345".to_string());
    fields.insert("action".to_string(), "login".to_string());
    logger
        .log_business_event("user_login", Some(12345), fields)
        .await;

    // 4. 演示异步任务跟踪
    println!("\n🔍 2. 异步任务跟踪演示:");
    let task_id = tracker
        .start_task("demo_task".to_string(), TaskPriority::High, HashMap::new())
        .await;

    // 模拟任务执行
    sleep(Duration::from_millis(100)).await;
    tracker.complete_task(&task_id).await?;

    // 5. 演示性能监控
    println!("\n📊 3. 性能监控演示:");
    let metrics = tracker.get_performance_metrics().await;
    println!("性能指标: {:?}", metrics);

    // 6. 演示调试功能
    println!("\n🐛 4. 调试功能演示:");
    debugger.set_breakpoint("debug_task").await;

    let debug_result = debugger
        .debug_execute("debug_task", async {
            sleep(Duration::from_millis(50)).await;
            Ok("调试任务完成".to_string())
        })
        .await?;

    println!("调试结果: {}", debug_result);

    // 7. 演示日志装饰器
    println!("\n🎨 5. 日志装饰器演示:");
    let decorated_result = decorator
        .execute_with_logging(
            "decorated_task".to_string(),
            TaskPriority::Normal,
            HashMap::new(),
            async {
                sleep(Duration::from_millis(75)).await;
                Ok("装饰器任务完成".to_string())
            },
        )
        .await?;

    println!("装饰器结果: {}", decorated_result);

    // 8. 获取最终调试信息
    let debug_info = debugger.get_debug_info().await;
    println!("\n🔧 最终调试信息: {:?}", debug_info);

    println!("\n✅ 异步日志调试和跟踪系统演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_task_tracker() {
        let config = AsyncLoggingConfig::default();
        let tracker = AsyncTaskTracker::new(config);

        let task_id = tracker
            .start_task(
                "test_task".to_string(),
                TaskPriority::Normal,
                HashMap::new(),
            )
            .await;

        assert!(!task_id.is_empty());

        let task_info = tracker.get_task_info(&task_id).await;
        assert!(task_info.is_some());

        tracker.complete_task(&task_id).await.unwrap();

        let completed_task = tracker.get_task_info(&task_id).await.unwrap();
        assert!(matches!(completed_task.status, TaskStatus::Completed));
    }

    #[tokio::test]
    async fn test_performance_monitor() {
        let monitor = AsyncPerformanceMonitor::new();

        monitor
            .record_task_completion(Duration::from_millis(100), true)
            .await;
        monitor
            .record_task_completion(Duration::from_millis(200), false)
            .await;

        let metrics = monitor.get_metrics().await;
        assert_eq!(metrics.total_tasks, 2);
        assert_eq!(metrics.successful_tasks, 1);
        assert_eq!(metrics.failed_tasks, 1);
        assert_eq!(metrics.success_rate, 50.0);
    }

    #[tokio::test]
    async fn test_local_debugger() {
        let config = AsyncLoggingConfig::default();
        let tracker = Arc::new(AsyncTaskTracker::new(config));
        let debugger = LocalDebugger::new(tracker);

        debugger.set_breakpoint("test_task").await;
        assert!(debugger.check_breakpoint("test_task").await);

        debugger.clear_breakpoint("test_task").await;
        assert!(!debugger.check_breakpoint("test_task").await);
    }
}
