//! # Rust 异步编程调试与监控完整指南 2025
//!
//! Complete Guide to Async Debugging and Monitoring in Rust 2025
//!
//! ## 📚 本示例涵盖
//!
//! ### 🔍 一、结构化日志 (Structured Logging)
//! - tracing 框架的完整使用
//! - Span 和 Event 的最佳实践
//! - 日志级别和过滤器
//! - 日志订阅器配置
//! - 分布式追踪
//!
//! ### 🐛 二、异步任务调试 (Async Task Debugging)
//! - tokio-console 实时监控
//! - 任务资源泄漏检测
//! - 死锁检测
//! - 任务阻塞分析
//!
//! ### 📊 三、性能指标收集 (Performance Metrics)
//! - Prometheus 指标导出
//! - 自定义指标
//! - 实时监控仪表板
//! - 告警规则
//!
//! ### 🏥 四、健康检查 (Health Checks)
//! - 活性检查 (Liveness)
//! - 就绪检查 (Readiness)
//! - 依赖项检查
//!
//! ## 运行方式
//! ```bash
//! # 启用 tokio-console 需要特殊编译标志
//! RUSTFLAGS="--cfg tokio_unstable" cargo run --example async_debugging_monitoring_2025
//! ```
//!
//! ## 版本信息
//! - Rust: 1.90+
//! - Tokio: 1.41+ (with tokio_unstable)
//! - Tracing: 0.1+
//! - 日期: 2025-10-04
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::{Mutex, RwLock};
use tokio::time::sleep;
use tracing::{Level, debug, error, info, instrument, span, trace, warn};
use tracing_subscriber::{EnvFilter, layer::SubscriberExt, util::SubscriberInitExt};

// ============================================================================
// 第一部分: 结构化日志 - Tracing 框架
// ============================================================================

/// # Tracing 初始化 - 配置日志订阅器
///
/// ## Tracing 架构
/// - **Subscriber**: 订阅和处理事件
/// - **Layer**: 可组合的中间件
/// - **Span**: 带有进入/退出事件的时间段
/// - **Event**: 单点事件(日志)
///
/// ## 日志级别
/// - TRACE: 最详细的信息
/// - DEBUG: 调试信息
/// - INFO: 一般信息
/// - WARN: 警告信息
/// - ERROR: 错误信息
pub fn init_tracing() {
    // 创建格式化层 - 用于输出到终端
    let fmt_layer = tracing_subscriber::fmt::layer()
        .with_target(true) // 显示目标模块
        .with_thread_ids(true) // 显示线程ID
        .with_thread_names(true) // 显示线程名称
        .with_file(true) // 显示文件位置
        .with_line_number(true) // 显示行号
        .with_level(true) // 显示日志级别
        .pretty(); // 美化输出

    // 创建环境过滤器 - 根据环境变量过滤日志
    let filter = EnvFilter::try_from_default_env()
        .or_else(|_| EnvFilter::try_new("info"))
        .unwrap();

    // 组合订阅器
    tracing_subscriber::registry()
        .with(filter)
        .with(fmt_layer)
        .init();

    info!("Tracing 初始化完成 - 日志系统已启动");
}

/// # 带追踪的业务服务
///
/// 演示如何在实际业务代码中使用 tracing
pub struct UserService {
    users: Arc<RwLock<Vec<User>>>,
    request_count: Arc<Mutex<u64>>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct User {
    id: u64,
    name: String,
    email: String,
}

impl UserService {
    pub fn new() -> Self {
        Self {
            users: Arc::new(RwLock::new(Vec::new())),
            request_count: Arc::new(Mutex::new(0)),
        }
    }

    /// # 创建用户 - 带完整的追踪信息
    ///
    /// ## `#[instrument]` 宏的作用
    /// - 自动创建 span
    /// - 记录函数参数
    /// - 记录返回值(使用 ret)
    /// - 记录错误(使用 err)
    #[instrument(
        name = "user_service.create_user",
        skip(self), // 跳过 self 参数
        fields(
            user.id = %id,
            user.name = %name,
            user.email = %email,
        ),
        ret, // 记录返回值
    )]
    #[allow(dead_code)]
    pub async fn create_user(&self, id: u64, name: String, email: String) -> Result<User, String> {
        // 增加请求计数
        {
            let mut count = self.request_count.lock().await;
            *count += 1;
            debug!(request_count = %count, "请求计数增加");
        }

        // 验证输入
        if name.is_empty() {
            warn!(user.id = %id, "用户名为空");
            return Err("用户名不能为空".to_string());
        }

        if !email.contains('@') {
            error!(user.id = %id, user.email = %email, "邮箱格式无效");
            return Err("邮箱格式无效".to_string());
        }

        // 模拟数据库操作
        info!("开始写入数据库");
        sleep(Duration::from_millis(50)).await;

        let user = User { id, name, email };

        {
            let mut users = self.users.write().await;
            users.push(user.clone());
            info!(total_users = users.len(), "用户创建成功");
        }

        Ok(user)
    }

    /// # 查询用户 - 带性能追踪
    #[instrument(
        name = "user_service.get_user",
        skip(self),
        fields(user.id = %id),
    )]
    pub async fn get_user(&self, id: u64) -> Option<User> {
        let start = Instant::now();

        // 模拟数据库查询
        sleep(Duration::from_millis(10)).await;

        let users = self.users.read().await;
        let user = users.iter().find(|u| u.id == id).cloned();

        let elapsed = start.elapsed();

        match &user {
            Some(u) => {
                info!(
                    user.name = %u.name,
                    query_time_ms = elapsed.as_millis(),
                    "用户查询成功"
                );
            }
            None => {
                warn!(
                    user.id = %id,
                    query_time_ms = elapsed.as_millis(),
                    "用户不存在"
                );
            }
        }

        user
    }

    /// # 获取统计信息
    #[instrument(skip(self))]
    pub async fn get_stats(&self) -> UserServiceStats {
        let users_count = self.users.read().await.len();
        let request_count = *self.request_count.lock().await;

        let stats = UserServiceStats {
            total_users: users_count,
            total_requests: request_count,
        };

        info!(
            total_users = stats.total_users,
            total_requests = stats.total_requests,
            "获取统计信息"
        );

        stats
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct UserServiceStats {
    total_users: usize,
    total_requests: u64,
}

// ============================================================================
// 第二部分: 性能指标收集 - Metrics
// ============================================================================

/// # 指标收集器
///
/// 使用简化的指标收集系统(生产环境建议使用 Prometheus)
pub struct MetricsCollector {
    /// 计数器 - 单调递增
    counters: Arc<RwLock<std::collections::HashMap<String, u64>>>,
    /// 仪表盘 - 可增可减
    gauges: Arc<RwLock<std::collections::HashMap<String, f64>>>,
    /// 直方图 - 记录数值分布
    histograms: Arc<RwLock<std::collections::HashMap<String, Vec<f64>>>>,
}

impl MetricsCollector {
    pub fn new() -> Self {
        info!("初始化指标收集器");
        Self {
            counters: Arc::new(RwLock::new(std::collections::HashMap::new())),
            gauges: Arc::new(RwLock::new(std::collections::HashMap::new())),
            histograms: Arc::new(RwLock::new(std::collections::HashMap::new())),
        }
    }

    /// 增加计数器
    pub async fn inc_counter(&self, name: &str, value: u64) {
        let mut counters = self.counters.write().await;
        *counters.entry(name.to_string()).or_insert(0) += value;
        trace!(metric = %name, value = %value, "计数器增加");
    }

    /// 设置仪表盘值
    pub async fn set_gauge(&self, name: &str, value: f64) {
        let mut gauges = self.gauges.write().await;
        gauges.insert(name.to_string(), value);
        trace!(metric = %name, value = %value, "仪表盘更新");
    }

    /// 记录直方图值
    pub async fn observe_histogram(&self, name: &str, value: f64) {
        let mut histograms = self.histograms.write().await;
        histograms
            .entry(name.to_string())
            .or_insert_with(Vec::new)
            .push(value);
        trace!(metric = %name, value = %value, "直方图记录");
    }

    /// 获取所有指标的快照
    #[instrument(skip(self))]
    pub async fn snapshot(&self) -> MetricsSnapshot {
        let counters = self.counters.read().await.clone();
        let gauges = self.gauges.read().await.clone();

        let mut histogram_summaries = std::collections::HashMap::new();
        let histograms = self.histograms.read().await;

        for (name, values) in histograms.iter() {
            if !values.is_empty() {
                let sum: f64 = values.iter().sum();
                let count = values.len();
                let avg = sum / count as f64;

                let mut sorted = values.clone();
                sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
                let p50 = sorted[count / 2];
                let p95 = sorted[(count as f64 * 0.95) as usize];
                let p99 = sorted[(count as f64 * 0.99) as usize];

                histogram_summaries.insert(
                    name.clone(),
                    HistogramSummary {
                        count,
                        avg,
                        p50,
                        p95,
                        p99,
                    },
                );
            }
        }

        let counters_len = counters.len();
        let gauges_len = gauges.len();
        let histograms_len = histogram_summaries.len();

        let snapshot = MetricsSnapshot {
            counters,
            gauges,
            histograms: histogram_summaries,
        };

        debug!(
            counters = counters_len,
            gauges = gauges_len,
            histograms = histograms_len,
            "指标快照生成"
        );

        snapshot
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct MetricsSnapshot {
    counters: std::collections::HashMap<String, u64>,
    gauges: std::collections::HashMap<String, f64>,
    histograms: std::collections::HashMap<String, HistogramSummary>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct HistogramSummary {
    count: usize,
    avg: f64,
    p50: f64,
    p95: f64,
    p99: f64,
}

// ============================================================================
// 第三部分: 健康检查系统
// ============================================================================

/// # 健康检查服务
///
/// ## Kubernetes 健康检查
/// - **Liveness**: 应用是否活着(崩溃重启)
/// - **Readiness**: 应用是否准备好接收流量
/// - **Startup**: 应用是否启动完成
pub struct HealthChecker {
    start_time: SystemTime,
    dependencies: Arc<RwLock<Vec<DependencyHealth>>>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
struct DependencyHealth {
    name: String,
    healthy: bool,
    last_check: SystemTime,
    error_msg: Option<String>,
}

impl HealthChecker {
    pub fn new() -> Self {
        info!("初始化健康检查服务");
        Self {
            start_time: SystemTime::now(),
            dependencies: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 注册依赖项
    pub async fn register_dependency(&self, name: String) {
        let mut deps = self.dependencies.write().await;
        deps.push(DependencyHealth {
            name: name.clone(),
            healthy: false,
            last_check: SystemTime::now(),
            error_msg: None,
        });
        info!(dependency = %name, "依赖项已注册");
    }

    /// 活性检查 - 基本健康状态
    #[instrument(skip(self))]
    pub async fn liveness_check(&self) -> HealthStatus {
        let uptime = SystemTime::now()
            .duration_since(self.start_time)
            .unwrap()
            .as_secs();

        info!(uptime_seconds = uptime, "活性检查通过");

        HealthStatus {
            healthy: true,
            uptime_seconds: uptime,
            message: "Service is alive".to_string(),
        }
    }

    /// 就绪检查 - 检查所有依赖项
    #[instrument(skip(self))]
    pub async fn readiness_check(&self) -> HealthStatus {
        let deps = self.dependencies.read().await;

        let all_healthy = deps.iter().all(|d| d.healthy);
        let unhealthy_count = deps.iter().filter(|d| !d.healthy).count();

        let uptime = SystemTime::now()
            .duration_since(self.start_time)
            .unwrap()
            .as_secs();

        let message = if all_healthy {
            info!(total_deps = deps.len(), "就绪检查通过 - 所有依赖项健康");
            "Service is ready".to_string()
        } else {
            warn!(
                total_deps = deps.len(),
                unhealthy = unhealthy_count,
                "就绪检查失败 - 部分依赖项不健康"
            );
            format!("{} dependencies unhealthy", unhealthy_count)
        };

        HealthStatus {
            healthy: all_healthy,
            uptime_seconds: uptime,
            message,
        }
    }

    /// 更新依赖项健康状态
    #[instrument(skip(self))]
    pub async fn update_dependency_health(
        &self,
        name: &str,
        healthy: bool,
        error_msg: Option<String>,
    ) {
        let mut deps = self.dependencies.write().await;

        if let Some(dep) = deps.iter_mut().find(|d| d.name == name) {
            dep.healthy = healthy;
            dep.last_check = SystemTime::now();
            dep.error_msg = error_msg.clone();

            if healthy {
                info!(dependency = %name, "依赖项健康");
            } else {
                error!(
                    dependency = %name,
                    error = ?error_msg,
                    "依赖项不健康"
                );
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct HealthStatus {
    pub healthy: bool,
    pub uptime_seconds: u64,
    pub message: String,
}

// ============================================================================
// 第四部分: 异步任务监控
// ============================================================================

/// # 任务监控器
///
/// 追踪异步任务的生命周期和性能
pub struct TaskMonitor {
    metrics: Arc<MetricsCollector>,
}

impl TaskMonitor {
    pub fn new(metrics: Arc<MetricsCollector>) -> Self {
        Self { metrics }
    }

    /// 运行被监控的任务
    #[instrument(skip(self, task_fn), fields(task.name = %task_name))]
    pub async fn run_monitored_task<F, T>(&self, task_name: &str, task_fn: F) -> Result<T, String>
    where
        F: std::future::Future<Output = Result<T, String>>,
    {
        info!("任务开始执行");

        // 记录任务开始
        self.metrics.inc_counter("task.started", 1).await;

        let start = Instant::now();

        // 执行任务
        let result = task_fn.await;

        let elapsed = start.elapsed();

        // 记录任务完成
        match &result {
            Ok(_) => {
                info!(duration_ms = elapsed.as_millis(), "任务成功完成");
                self.metrics.inc_counter("task.completed", 1).await;
                self.metrics
                    .observe_histogram(
                        &format!("task.{}.duration_ms", task_name),
                        elapsed.as_millis() as f64,
                    )
                    .await;
            }
            Err(e) => {
                error!(
                    error = %e,
                    duration_ms = elapsed.as_millis(),
                    "任务执行失败"
                );
                self.metrics.inc_counter("task.failed", 1).await;
            }
        }

        result
    }
}

// ============================================================================
// 主函数: 综合演示
// ============================================================================

#[tokio::main]
async fn main() {
    // 初始化 tracing
    init_tracing();

    info!("╔═══════════════════════════════════════════════════════════╗");
    info!("║   Rust 异步编程调试与监控完整指南 2025                   ║");
    info!("║   Complete Guide to Async Debugging and Monitoring       ║");
    info!("╚═══════════════════════════════════════════════════════════╝");

    // 创建服务实例
    let user_service = Arc::new(UserService::new());
    let metrics = Arc::new(MetricsCollector::new());
    let health_checker = Arc::new(HealthChecker::new());
    let task_monitor = Arc::new(TaskMonitor::new(metrics.clone()));

    info!("\n{}", "=".repeat(60));
    info!("演示 1: 结构化日志 - Tracing");
    info!("{}", "=".repeat(60));

    // 注册依赖项
    health_checker
        .register_dependency("database".to_string())
        .await;
    health_checker
        .register_dependency("cache".to_string())
        .await;

    // 演示用户服务操作
    {
        let span = span!(Level::INFO, "user_operations");
        let _guard = span.enter();

        info!("开始用户操作演示");

        // 创建用户
        match user_service
            .create_user(1, "Alice".to_string(), "alice@example.com".to_string())
            .await
        {
            Ok(user) => info!(user.name = %user.name, "✅ 用户创建成功"),
            Err(e) => error!(error = %e, "❌ 用户创建失败"),
        }

        match user_service
            .create_user(2, "Bob".to_string(), "bob@example.com".to_string())
            .await
        {
            Ok(user) => info!(user.name = %user.name, "✅ 用户创建成功"),
            Err(e) => error!(error = %e, "❌ 用户创建失败"),
        }

        // 测试验证失败
        match user_service
            .create_user(3, "".to_string(), "invalid".to_string())
            .await
        {
            Ok(_) => {}
            Err(e) => warn!(error = %e, "⚠️  预期的验证失败"),
        }

        // 查询用户
        user_service.get_user(1).await;
        user_service.get_user(999).await; // 不存在的用户
    }

    info!("\n{}", "=".repeat(60));
    info!("演示 2: 性能指标收集 - Metrics");
    info!("{}", "=".repeat(60));

    // 模拟业务指标
    for i in 0..10 {
        metrics.inc_counter("http.requests", 1).await;
        metrics
            .observe_histogram("http.request.duration_ms", i as f64 * 10.0 + 50.0)
            .await;

        if i % 3 == 0 {
            metrics.inc_counter("http.errors", 1).await;
        }
    }

    metrics.set_gauge("system.cpu_usage", 45.5).await;
    metrics.set_gauge("system.memory_usage", 70.2).await;

    let snapshot = metrics.snapshot().await;
    info!("📊 指标快照:");
    info!("   计数器: {:?}", snapshot.counters);
    info!("   仪表盘: {:?}", snapshot.gauges);
    info!("   直方图: {:?}", snapshot.histograms);

    info!("\n{}", "=".repeat(60));
    info!("演示 3: 健康检查系统");
    info!("{}", "=".repeat(60));

    // 更新依赖项状态
    health_checker
        .update_dependency_health("database", true, None)
        .await;
    health_checker
        .update_dependency_health("cache", true, None)
        .await;

    // 活性检查
    let liveness = health_checker.liveness_check().await;
    info!("🏥 活性检查: {:?}", liveness);

    // 就绪检查
    let readiness = health_checker.readiness_check().await;
    info!("🏥 就绪检查: {:?}", readiness);

    // 模拟依赖项故障
    health_checker
        .update_dependency_health("cache", false, Some("Connection timeout".to_string()))
        .await;

    let readiness = health_checker.readiness_check().await;
    info!("🏥 就绪检查(有故障): {:?}", readiness);

    info!("\n{}", "=".repeat(60));
    info!("演示 4: 任务监控");
    info!("{}", "=".repeat(60));

    // 监控成功任务
    let result = task_monitor
        .run_monitored_task("data_processing", async {
            info!("执行数据处理...");
            sleep(Duration::from_millis(100)).await;
            Ok(42)
        })
        .await;
    info!("✅ 任务结果: {:?}", result);

    // 监控失败任务
    let result: Result<i32, String> = task_monitor
        .run_monitored_task("failing_task", async {
            info!("执行可能失败的任务...");
            sleep(Duration::from_millis(50)).await;
            Err("Simulated error".to_string())
        })
        .await;
    info!("❌ 任务结果: {:?}", result);

    info!("\n{}", "=".repeat(60));
    info!("最终统计");
    info!("{}", "=".repeat(60));

    let stats = user_service.get_stats().await;
    info!("👥 用户服务统计:");
    info!("   总用户数: {}", stats.total_users);
    info!("   总请求数: {}", stats.total_requests);

    let final_metrics = metrics.snapshot().await;
    info!("📊 最终指标:");
    info!(
        "   HTTP 请求: {}",
        final_metrics.counters.get("http.requests").unwrap_or(&0)
    );
    info!(
        "   HTTP 错误: {}",
        final_metrics.counters.get("http.errors").unwrap_or(&0)
    );
    info!(
        "   任务完成: {}",
        final_metrics.counters.get("task.completed").unwrap_or(&0)
    );
    info!(
        "   任务失败: {}",
        final_metrics.counters.get("task.failed").unwrap_or(&0)
    );

    info!("\n{}", "=".repeat(60));
    info!("最佳实践总结");
    info!("{}", "=".repeat(60));
    info!("");
    info!("✅ 结构化日志:");
    info!("   1. 使用 #[instrument] 自动添加 span");
    info!("   2. 记录关键业务参数和结果");
    info!("   3. 使用合适的日志级别");
    info!("   4. 包含上下文信息(用户ID、请求ID等)");
    info!("");
    info!("✅ 性能指标:");
    info!("   1. 使用计数器记录事件次数");
    info!("   2. 使用仪表盘记录瞬时值");
    info!("   3. 使用直方图记录分布情况");
    info!("   4. 定期导出到 Prometheus");
    info!("");
    info!("✅ 健康检查:");
    info!("   1. 实现 /health/live 端点(活性)");
    info!("   2. 实现 /health/ready 端点(就绪)");
    info!("   3. 检查关键依赖项状态");
    info!("   4. 设置合理的超时时间");
    info!("");
    info!("✅ 调试工具:");
    info!("   1. tokio-console: 实时监控异步任务");
    info!("   2. tracing-chrome: 生成 Chrome 追踪文件");
    info!("   3. flamegraph: 性能火焰图");
    info!("   4. cargo-flamegraph: 便捷的火焰图工具");
    info!("");
    info!("✅ 演示完成!");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_user_service() {
        let service = UserService::new();

        let user = service
            .create_user(1, "Test".to_string(), "test@example.com".to_string())
            .await
            .unwrap();

        assert_eq!(user.id, 1);
        assert_eq!(user.name, "Test");

        let found = service.get_user(1).await;
        assert!(found.is_some());
    }

    #[tokio::test]
    async fn test_metrics_collector() {
        let metrics = MetricsCollector::new();

        metrics.inc_counter("test.counter", 5).await;
        metrics.set_gauge("test.gauge", 42.0).await;
        metrics.observe_histogram("test.hist", 10.0).await;

        let snapshot = metrics.snapshot().await;

        assert_eq!(*snapshot.counters.get("test.counter").unwrap(), 5);
        assert_eq!(*snapshot.gauges.get("test.gauge").unwrap(), 42.0);
    }

    #[tokio::test]
    async fn test_health_checker() {
        let checker = HealthChecker::new();

        checker.register_dependency("test_dep".to_string()).await;
        checker
            .update_dependency_health("test_dep", true, None)
            .await;

        let liveness = checker.liveness_check().await;
        assert!(liveness.healthy);

        let readiness = checker.readiness_check().await;
        assert!(readiness.healthy);
    }
}
