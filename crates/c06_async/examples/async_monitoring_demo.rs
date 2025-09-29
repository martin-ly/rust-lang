//! 异步监控和诊断工具演示
//! 
//! 本示例展示了异步应用的监控和诊断功能：
//! - 性能指标收集
//! - 内存使用监控
//! - 任务执行追踪
//! - 错误率统计
//! - 延迟分布分析
//! - 健康检查
//! - 告警机制
//! 
//! 运行方式：
//! ```bash
//! cargo run --example async_monitoring_demo
//! ```

use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use std::collections::{HashMap, VecDeque};
use tokio::sync::{Mutex, Notify};
use tokio::time::{sleep, interval};
use serde::{Serialize, Deserialize};
use anyhow::Result;

/// 性能指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    pub timestamp: SystemTime,
    pub cpu_usage: f64,
    pub memory_usage: u64,
    pub active_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub avg_response_time: Duration,
    pub throughput: f64, // requests per second
    pub error_rate: f64,
}

/// 任务执行信息
#[derive(Debug, Clone)]
pub struct TaskExecutionInfo {
    pub task_id: String,
    pub task_name: String,
    pub start_time: Instant,
    pub end_time: Option<Instant>,
    pub duration: Option<Duration>,
    pub status: TaskStatus,
    pub error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TaskStatus {
    Running,
    Completed,
    Failed,
    Timeout,
}

/// 延迟分布桶
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LatencyBucket {
    pub range: (Duration, Duration), // (min, max)
    pub count: u64,
    pub percentage: f64,
}

/// 健康检查结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckResult {
    pub component: String,
    pub status: HealthStatus,
    pub message: String,
    pub timestamp: SystemTime,
    pub response_time: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

/// 异步监控器
pub struct AsyncMonitor {
    metrics: Arc<Mutex<VecDeque<PerformanceMetrics>>>,
    task_executions: Arc<Mutex<HashMap<String, TaskExecutionInfo>>>,
    latency_distribution: Arc<Mutex<Vec<LatencyBucket>>>,
    health_checks: Arc<Mutex<HashMap<String, HealthCheckResult>>>,
    alerts: Arc<Mutex<Vec<Alert>>>,
    shutdown_notify: Arc<Notify>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    pub id: String,
    pub severity: AlertSeverity,
    pub component: String,
    pub message: String,
    pub timestamp: SystemTime,
    pub resolved: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertSeverity {
    Info,
    Warning,
    Critical,
}

impl std::fmt::Display for AlertSeverity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AlertSeverity::Info => write!(f, "Info"),
            AlertSeverity::Warning => write!(f, "Warning"),
            AlertSeverity::Critical => write!(f, "Critical"),
        }
    }
}

impl AsyncMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(Mutex::new(VecDeque::with_capacity(1000))),
            task_executions: Arc::new(Mutex::new(HashMap::new())),
            latency_distribution: Arc::new(Mutex::new(Vec::new())),
            health_checks: Arc::new(Mutex::new(HashMap::new())),
            alerts: Arc::new(Mutex::new(Vec::new())),
            shutdown_notify: Arc::new(Notify::new()),
        }
    }

    /// 启动监控器
    pub fn start(&self) -> tokio::task::JoinHandle<()> {
        let metrics = Arc::clone(&self.metrics);
        let task_executions = Arc::clone(&self.task_executions);
        let shutdown_notify = Arc::clone(&self.shutdown_notify);

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_secs(1));

            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        Self::collect_metrics(&metrics, &task_executions).await;
                    }
                    _ = shutdown_notify.notified() => {
                        break;
                    }
                }
            }
        })
    }

    /// 记录任务开始
    pub async fn record_task_start(&self, task_id: String, task_name: String) {
        let task_info = TaskExecutionInfo {
            task_id: task_id.clone(),
            task_name,
            start_time: Instant::now(),
            end_time: None,
            duration: None,
            status: TaskStatus::Running,
            error: None,
        };

        let mut executions = self.task_executions.lock().await;
        executions.insert(task_id, task_info);
    }

    /// 记录任务完成
    pub async fn record_task_complete(&self, task_id: &str, success: bool, error: Option<String>) {
        let mut executions = self.task_executions.lock().await;
        if let Some(task_info) = executions.get_mut(task_id) {
            task_info.end_time = Some(Instant::now());
            task_info.duration = Some(task_info.end_time.unwrap().duration_since(task_info.start_time));
            task_info.status = if success { TaskStatus::Completed } else { TaskStatus::Failed };
            task_info.error = error;

            // 更新延迟分布
            if let Some(duration) = task_info.duration {
                self.update_latency_distribution(duration).await;
            }
        }
    }

    /// 执行健康检查
    pub async fn perform_health_check(&self, component: &str) -> HealthCheckResult {
        let start = Instant::now();
        
        // 模拟健康检查
        let (status, message) = match component {
            "database" => {
                if rand::random::<f32>() < 0.9 {
                    (HealthStatus::Healthy, "数据库连接正常".to_string())
                } else {
                    (HealthStatus::Degraded, "数据库响应缓慢".to_string())
                }
            }
            "cache" => {
                if rand::random::<f32>() < 0.95 {
                    (HealthStatus::Healthy, "缓存服务正常".to_string())
                } else {
                    (HealthStatus::Unhealthy, "缓存服务不可用".to_string())
                }
            }
            "api" => {
                if rand::random::<f32>() < 0.85 {
                    (HealthStatus::Healthy, "API服务正常".to_string())
                } else {
                    (HealthStatus::Degraded, "API响应时间过长".to_string())
                }
            }
            _ => (HealthStatus::Healthy, "组件状态正常".to_string()),
        };

        let response_time = start.elapsed();
        
        let result = HealthCheckResult {
            component: component.to_string(),
            status: status.clone(),
            message,
            timestamp: SystemTime::now(),
            response_time,
        };

        // 存储健康检查结果
        {
            let mut health_checks = self.health_checks.lock().await;
            health_checks.insert(component.to_string(), result.clone());
        }

        // 检查是否需要告警
        if matches!(status, HealthStatus::Degraded | HealthStatus::Unhealthy) {
            self.create_alert(
                AlertSeverity::Warning,
                component,
                &format!("健康检查失败: {:?}", status),
            ).await;
        }

        result
    }

    /// 创建告警
    pub async fn create_alert(&self, severity: AlertSeverity, component: &str, message: &str) {
        let alert = Alert {
            id: uuid::Uuid::new_v4().to_string(),
            severity,
            component: component.to_string(),
            message: message.to_string(),
            timestamp: SystemTime::now(),
            resolved: false,
        };

        let mut alerts = self.alerts.lock().await;
        alerts.push(alert);
        
        println!("    🚨 告警: {} - {}", component, message);
    }

    /// 获取性能指标
    pub async fn get_metrics(&self) -> Vec<PerformanceMetrics> {
        let metrics = self.metrics.lock().await;
        metrics.iter().cloned().collect()
    }

    /// 获取任务执行统计
    pub async fn get_task_stats(&self) -> TaskStats {
        let executions = self.task_executions.lock().await;
        
        let mut stats = TaskStats::default();
        for task_info in executions.values() {
            stats.total_tasks += 1;
            
            match task_info.status {
                TaskStatus::Completed => stats.completed_tasks += 1,
                TaskStatus::Failed => stats.failed_tasks += 1,
                TaskStatus::Timeout => stats.timeout_tasks += 1,
                TaskStatus::Running => stats.running_tasks += 1,
            }
            
            if let Some(duration) = task_info.duration {
                stats.total_execution_time += duration;
                stats.min_execution_time = stats.min_execution_time.min(duration);
                stats.max_execution_time = stats.max_execution_time.max(duration);
            }
        }
        
        if stats.completed_tasks > 0 {
            stats.avg_execution_time = Duration::from_nanos(
                stats.total_execution_time.as_nanos() as u64 / stats.completed_tasks as u64
            );
        }
        
        stats
    }

    /// 获取延迟分布
    pub async fn get_latency_distribution(&self) -> Vec<LatencyBucket> {
        let distribution = self.latency_distribution.lock().await;
        distribution.clone()
    }

    /// 获取健康检查结果
    pub async fn get_health_status(&self) -> HashMap<String, HealthCheckResult> {
        let health_checks = self.health_checks.lock().await;
        health_checks.clone()
    }

    /// 获取告警列表
    pub async fn get_alerts(&self) -> Vec<Alert> {
        let alerts = self.alerts.lock().await;
        alerts.clone()
    }

    /// 关闭监控器
    pub async fn shutdown(&self) {
        self.shutdown_notify.notify_waiters();
    }

    // 私有方法

    async fn collect_metrics(
        metrics: &Arc<Mutex<VecDeque<PerformanceMetrics>>>,
        task_executions: &Arc<Mutex<HashMap<String, TaskExecutionInfo>>>,
    ) {
        let executions = task_executions.lock().await;
        
        let mut active_tasks = 0;
        let mut completed_tasks = 0;
        let mut failed_tasks = 0;
        let mut total_response_time = Duration::ZERO;
        let mut response_count = 0;
        
        for task_info in executions.values() {
            match task_info.status {
                TaskStatus::Running => active_tasks += 1,
                TaskStatus::Completed => {
                    completed_tasks += 1;
                    if let Some(duration) = task_info.duration {
                        total_response_time += duration;
                        response_count += 1;
                    }
                }
                TaskStatus::Failed => failed_tasks += 1,
                TaskStatus::Timeout => failed_tasks += 1,
            }
        }
        
        let avg_response_time = if response_count > 0 {
            Duration::from_nanos(total_response_time.as_nanos() as u64 / response_count as u64)
        } else {
            Duration::ZERO
        };
        
        let total_tasks = completed_tasks + failed_tasks;
        let error_rate = if total_tasks > 0 {
            failed_tasks as f64 / total_tasks as f64
        } else {
            0.0
        };
        
        let metric = PerformanceMetrics {
            timestamp: SystemTime::now(),
            cpu_usage: rand::random::<f64>() * 100.0, // 模拟CPU使用率
            memory_usage: rand::random::<u64>() % 1024 * 1024 * 1024, // 模拟内存使用
            active_tasks,
            completed_tasks,
            failed_tasks,
            avg_response_time,
            throughput: completed_tasks as f64, // 简化计算
            error_rate,
        };
        
        let mut metrics_queue = metrics.lock().await;
        metrics_queue.push_back(metric);
        
        // 保持队列大小
        if metrics_queue.len() > 1000 {
            metrics_queue.pop_front();
        }
    }

    async fn update_latency_distribution(&self, duration: Duration) {
        let mut distribution = self.latency_distribution.lock().await;
        
        // 定义延迟桶
        let buckets = vec![
            (Duration::ZERO, Duration::from_millis(10)),
            (Duration::from_millis(10), Duration::from_millis(50)),
            (Duration::from_millis(50), Duration::from_millis(100)),
            (Duration::from_millis(100), Duration::from_millis(500)),
            (Duration::from_millis(500), Duration::from_secs(1)),
            (Duration::from_secs(1), Duration::from_secs(5)),
        ];
        
        // 重置分布
        distribution.clear();
        let mut total_count = 0;
        
        for (min, max) in buckets {
            let count = if duration >= min && duration < max { 1 } else { 0 };
            total_count += count;
            distribution.push(LatencyBucket {
                range: (min, max),
                count,
                percentage: 0.0,
            });
        }
        
        // 计算百分比
        if total_count > 0 {
            for bucket in distribution.iter_mut() {
                bucket.percentage = (bucket.count as f64 / total_count as f64) * 100.0;
            }
        }
    }
}

#[derive(Debug, Default, Serialize, Deserialize)]
pub struct TaskStats {
    pub total_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub timeout_tasks: u64,
    pub running_tasks: u64,
    pub total_execution_time: Duration,
    pub avg_execution_time: Duration,
    pub min_execution_time: Duration,
    pub max_execution_time: Duration,
}

impl TaskStats {
    fn default() -> Self {
        Self {
            total_tasks: 0,
            completed_tasks: 0,
            failed_tasks: 0,
            timeout_tasks: 0,
            running_tasks: 0,
            total_execution_time: Duration::ZERO,
            avg_execution_time: Duration::ZERO,
            min_execution_time: Duration::from_secs(u64::MAX),
            max_execution_time: Duration::ZERO,
        }
    }
}

struct AsyncMonitoringDemo;

impl AsyncMonitoringDemo {
    async fn run() -> Result<()> {
        println!("📊 异步监控和诊断工具演示");
        println!("================================");

        let monitor = AsyncMonitor::new();
        let monitor_handle = monitor.start();

        // 1. 性能指标收集演示
        println!("\n📈 1. 性能指标收集演示");
        Self::demo_metrics_collection(&monitor).await?;

        // 2. 任务执行追踪演示
        println!("\n🔍 2. 任务执行追踪演示");
        Self::demo_task_tracking(&monitor).await?;

        // 3. 健康检查演示
        println!("\n🏥 3. 健康检查演示");
        Self::demo_health_checks(&monitor).await?;

        // 4. 告警机制演示
        println!("\n🚨 4. 告警机制演示");
        Self::demo_alerting(&monitor).await?;

        // 5. 延迟分布分析演示
        println!("\n⏱️ 5. 延迟分布分析演示");
        Self::demo_latency_analysis(&monitor).await?;

        // 6. 综合监控报告演示
        println!("\n📋 6. 综合监控报告演示");
        Self::demo_monitoring_report(&monitor).await?;

        // 关闭监控器
        monitor.shutdown().await;
        let _ = monitor_handle.await;

        Ok(())
    }

    async fn demo_metrics_collection(monitor: &AsyncMonitor) -> Result<()> {
        println!("  收集性能指标...");
        
        // 等待一些指标收集
        sleep(Duration::from_secs(3)).await;
        
        let metrics = monitor.get_metrics().await;
        println!("    收集到 {} 个指标样本", metrics.len());
        
        if let Some(latest_metric) = metrics.last() {
            println!("    最新指标:");
            println!("      CPU使用率: {:.1}%", latest_metric.cpu_usage);
            println!("      内存使用: {:.2} MB", latest_metric.memory_usage as f64 / 1024.0 / 1024.0);
            println!("      活跃任务: {}", latest_metric.active_tasks);
            println!("      完成任务: {}", latest_metric.completed_tasks);
            println!("      失败任务: {}", latest_metric.failed_tasks);
            println!("      平均响应时间: {:?}", latest_metric.avg_response_time);
            println!("      吞吐量: {:.2} req/sec", latest_metric.throughput);
            println!("      错误率: {:.1}%", latest_metric.error_rate * 100.0);
        }

        Ok(())
    }

    async fn demo_task_tracking(monitor: &AsyncMonitor) -> Result<()> {
        println!("  追踪任务执行...");
        
        // 模拟一些任务
        let task_names = vec![
            "数据处理任务",
            "文件上传任务",
            "邮件发送任务",
            "数据库查询任务",
            "缓存更新任务",
        ];
        
        let mut task_handles = Vec::new();
        
        for (i, name) in task_names.iter().enumerate() {
            let task_id = format!("task_{}", i);
            let monitor = monitor.clone();
            let name = name.to_string();
            
            // 记录任务开始
            monitor.record_task_start(task_id.clone(), name.to_string()).await;
            
            // 启动任务
            let handle = tokio::spawn(async move {
                let start = Instant::now();
                
                // 模拟任务执行
                let duration = Duration::from_millis(100 + i as u64 * 50);
                sleep(duration).await;
                
                let success = rand::random::<f32>() < 0.8;
                let error = if success {
                    None
                } else {
                    Some("模拟任务失败".to_string())
                };
                
                // 记录任务完成
                monitor.record_task_complete(&task_id, success, error).await;
                
                println!("      任务 {} 完成，耗时: {:?}", name, start.elapsed());
            });
            
            task_handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in task_handles {
            handle.await?;
        }
        
        // 显示任务统计
        let stats = monitor.get_task_stats().await;
        println!("    任务执行统计:");
        println!("      总任务数: {}", stats.total_tasks);
        println!("      完成任务数: {}", stats.completed_tasks);
        println!("      失败任务数: {}", stats.failed_tasks);
        println!("      平均执行时间: {:?}", stats.avg_execution_time);
        println!("      最小执行时间: {:?}", stats.min_execution_time);
        println!("      最大执行时间: {:?}", stats.max_execution_time);

        Ok(())
    }

    async fn demo_health_checks(monitor: &AsyncMonitor) -> Result<()> {
        println!("  执行健康检查...");
        
        let components = vec!["database", "cache", "api", "storage"];
        
        for component in components {
            let result = monitor.perform_health_check(component).await;
            
            let status_icon = match result.status {
                HealthStatus::Healthy => "✅",
                HealthStatus::Degraded => "⚠️",
                HealthStatus::Unhealthy => "❌",
            };
            
            println!("      {} {}: {} (响应时间: {:?})", 
                status_icon, component, result.message, result.response_time);
        }
        
        // 显示健康状态摘要
        let health_status = monitor.get_health_status().await;
        let healthy_count = health_status.values().filter(|r| matches!(r.status, HealthStatus::Healthy)).count();
        let total_count = health_status.len();
        
        println!("    健康状态摘要: {}/{} 组件健康", healthy_count, total_count);

        Ok(())
    }

    async fn demo_alerting(monitor: &AsyncMonitor) -> Result<()> {
        println!("  测试告警机制...");
        
        // 创建一些测试告警
        monitor.create_alert(
            AlertSeverity::Warning,
            "database",
            "数据库连接池使用率超过80%",
        ).await;
        
        monitor.create_alert(
            AlertSeverity::Critical,
            "cache",
            "缓存服务完全不可用",
        ).await;
        
        monitor.create_alert(
            AlertSeverity::Info,
            "api",
            "API响应时间超过阈值",
        ).await;
        
        // 显示告警列表
        let alerts = monitor.get_alerts().await;
        println!("    当前告警数量: {}", alerts.len());
        
        for alert in alerts.iter().take(5) {
            let severity_icon = match alert.severity {
                AlertSeverity::Info => "ℹ️",
                AlertSeverity::Warning => "⚠️",
                AlertSeverity::Critical => "🚨",
            };
            
            println!("      {} [{}] {}: {}", 
                severity_icon, 
                alert.component, 
                alert.severity,
                alert.message
            );
        }

        Ok(())
    }

    async fn demo_latency_analysis(monitor: &AsyncMonitor) -> Result<()> {
        println!("  分析延迟分布...");
        
        // 生成一些延迟数据
        let mut task_handles = Vec::new();
        
        for i in 0..50 {
            let monitor = monitor.clone();
            let task_id = format!("latency_task_{}", i);
            
            let handle = tokio::spawn(async move {
                monitor.record_task_start(task_id.clone(), "延迟测试任务".to_string()).await;
                
                // 模拟不同的延迟
                let delay = Duration::from_millis(rand::random::<u64>() % 1000);
                sleep(delay).await;
                
                monitor.record_task_complete(&task_id, true, None).await;
            });
            
            task_handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in task_handles {
            handle.await?;
        }
        
        // 显示延迟分布
        let distribution = monitor.get_latency_distribution().await;
        println!("    延迟分布:");
        
        for bucket in distribution {
            let (min, max) = bucket.range;
            println!("      {:?} - {:?}: {} 次 ({:.1}%)", 
                min, max, bucket.count, bucket.percentage);
        }

        Ok(())
    }

    async fn demo_monitoring_report(monitor: &AsyncMonitor) -> Result<()> {
        println!("  生成综合监控报告...");
        
        // 收集所有监控数据
        let metrics = monitor.get_metrics().await;
        let task_stats = monitor.get_task_stats().await;
        let health_status = monitor.get_health_status().await;
        let alerts = monitor.get_alerts().await;
        
        println!("    📊 监控报告摘要:");
        println!("      ===================");
        
        if let Some(latest_metric) = metrics.last() {
            println!("      📈 性能指标:");
            println!("        CPU使用率: {:.1}%", latest_metric.cpu_usage);
            println!("        内存使用: {:.2} MB", latest_metric.memory_usage as f64 / 1024.0 / 1024.0);
            println!("        吞吐量: {:.2} req/sec", latest_metric.throughput);
            println!("        错误率: {:.1}%", latest_metric.error_rate * 100.0);
        }
        
        println!("      🔍 任务统计:");
        println!("        总任务数: {}", task_stats.total_tasks);
        println!("        成功率: {:.1}%", 
            if task_stats.total_tasks > 0 {
                (task_stats.completed_tasks as f64 / task_stats.total_tasks as f64) * 100.0
            } else {
                0.0
            }
        );
        println!("        平均执行时间: {:?}", task_stats.avg_execution_time);
        
        println!("      🏥 健康状态:");
        let healthy_components = health_status.values()
            .filter(|r| matches!(r.status, HealthStatus::Healthy))
            .count();
        println!("        健康组件: {}/{}", healthy_components, health_status.len());
        
        println!("      🚨 告警信息:");
        let critical_alerts = alerts.iter().filter(|a| matches!(a.severity, AlertSeverity::Critical)).count();
        let warning_alerts = alerts.iter().filter(|a| matches!(a.severity, AlertSeverity::Warning)).count();
        println!("        严重告警: {}", critical_alerts);
        println!("        警告告警: {}", warning_alerts);
        
        // 系统建议
        println!("      💡 系统建议:");
        if let Some(latest_metric) = metrics.last() {
            if latest_metric.cpu_usage > 80.0 {
                println!("        - CPU使用率过高，建议优化计算密集型任务");
            }
            if latest_metric.memory_usage > 1024 * 1024 * 1024 {
                println!("        - 内存使用量较大，建议检查内存泄漏");
            }
            if latest_metric.error_rate > 0.1 {
                println!("        - 错误率较高，建议检查错误处理逻辑");
            }
            if latest_metric.avg_response_time > Duration::from_secs(1) {
                println!("        - 平均响应时间过长，建议优化性能");
            }
        }

        Ok(())
    }
}

// 为 AsyncMonitor 实现 Clone
impl Clone for AsyncMonitor {
    fn clone(&self) -> Self {
        Self {
            metrics: Arc::clone(&self.metrics),
            task_executions: Arc::clone(&self.task_executions),
            latency_distribution: Arc::clone(&self.latency_distribution),
            health_checks: Arc::clone(&self.health_checks),
            alerts: Arc::clone(&self.alerts),
            shutdown_notify: Arc::clone(&self.shutdown_notify),
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    AsyncMonitoringDemo::run().await?;

    println!("\n🎉 异步监控和诊断工具演示完成！");
    Ok(())
}
