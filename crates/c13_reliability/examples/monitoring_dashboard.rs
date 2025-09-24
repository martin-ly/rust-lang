//! 监控仪表板示例
//!
//! 展示 c13_reliability 库中的监控仪表板功能，包括实时数据收集、历史数据分析和统计摘要。

use c13_reliability::prelude::*;
use c13_reliability::runtime_monitoring::dashboard::*;
use c13_reliability::runtime_monitoring::*;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    env_logger::init();
    
    println!("🚀 启动监控仪表板示例");
    
    // 创建监控组件
    let health_checker = Arc::new(HealthChecker::new(HealthCheckConfig::default()));
    let resource_monitor = Arc::new(ResourceMonitor::new(ResourceMonitorConfig::default()));
    let performance_monitor = Arc::new(PerformanceMonitor::new(PerformanceMonitorConfig::default()));
    let anomaly_detector = Arc::new(AnomalyDetector::new(AnomalyDetectionConfig::default()));
    
    // 创建仪表板配置
    let dashboard_config = DashboardConfig {
        refresh_interval: Duration::from_secs(3),
        history_retention: Duration::from_secs(300), // 5分钟
        max_history_points: 100,
        real_time_enabled: true,
        alert_thresholds: DashboardAlertThresholds {
            cpu_alert_threshold: 70.0,
            memory_alert_threshold: 80.0,
            response_time_alert_threshold: Duration::from_millis(500),
            error_rate_alert_threshold: 0.03,
            anomaly_alert_threshold: 0.6,
        },
    };
    
    // 创建监控仪表板
    let dashboard = MonitoringDashboard::new(
        dashboard_config,
        health_checker,
        resource_monitor,
        performance_monitor,
        anomaly_detector,
    );
    
    // 启动仪表板
    dashboard.start().await?;
    println!("✅ 监控仪表板已启动");
    
    // 运行监控循环
    for i in 1..=15 {
        println!("\n📊 第 {} 次数据收集", i);
        
        // 收集监控数据
        let data_point = dashboard.collect_data().await?;
        
        // 显示当前数据
        display_data_point(&data_point, i);
        
        // 获取当前状态
        let status = dashboard.get_current_status().await;
        display_dashboard_status(&status);
        
        // 每5次收集显示一次统计摘要
        if i % 5 == 0 {
            let summary = dashboard.get_statistics_summary().await;
            display_statistics_summary(&summary);
        }
        
        // 等待下次收集
        sleep(Duration::from_secs(2)).await;
    }
    
    // 显示历史数据分析
    println!("\n📈 历史数据分析");
    let history_data = dashboard.get_history_data().await;
    analyze_history_data(&history_data);
    
    // 停止仪表板
    dashboard.stop().await?;
    println!("\n🛑 监控仪表板已停止");
    
    Ok(())
}

/// 显示数据点信息
fn display_data_point(data_point: &MonitoringDataPoint, _iteration: u32) {
    println!("   🕐 时间: {}", 
             chrono::DateTime::<chrono::Utc>::from(data_point.timestamp)
                 .format("%H:%M:%S"));
    
    // 健康状态
    let health_emoji = match data_point.health_status {
        MonitoringState::Healthy => "✅",
        MonitoringState::Warning => "⚠️",
        MonitoringState::Error => "❌",
        MonitoringState::Critical => "🚨",
    };
    println!("   {} 健康状态: {:?}", health_emoji, data_point.health_status);
    
    // 资源使用情况
    println!("   💻 资源使用:");
    println!("      CPU: {:.1}%", data_point.resource_usage.cpu_usage_percent);
    println!("      内存: {:.1}%", data_point.resource_usage.memory_usage_percent);
    println!("      磁盘: {:.1}%", data_point.resource_usage.disk_usage_percent);
    println!("      网络: {:.1}%", data_point.resource_usage.network_io_usage);
    println!("      连接: {}", data_point.resource_usage.active_connections);
    
    // 性能指标
    println!("   ⚡ 性能指标:");
    println!("      平均响应时间: {:?}", data_point.performance_metrics.average_response_time);
    println!("      P95响应时间: {:?}", data_point.performance_metrics.p95_response_time);
    println!("      请求/秒: {:.1}", data_point.performance_metrics.requests_per_second);
    println!("      错误率: {:.2}%", data_point.performance_metrics.error_rate * 100.0);
    println!("      吞吐量: {:.1}", data_point.performance_metrics.throughput);
    
    // 异常检测
    let anomaly_emoji = if data_point.anomaly_results.anomalies_detected { "🚨" } else { "✅" };
    println!("   {} 异常检测:", anomaly_emoji);
    println!("      异常数量: {}", data_point.anomaly_results.anomaly_count);
    println!("      检测器数量: {}", data_point.anomaly_results.total_detectors);
    println!("      异常评分: {:.3}", data_point.anomaly_results.anomaly_score);
    
    if !data_point.anomaly_results.anomaly_details.is_empty() {
        println!("      异常详情:");
        for (key, value) in &data_point.anomaly_results.anomaly_details {
            println!("        {}: {}", key, value);
        }
    }
}

/// 显示仪表板状态
fn display_dashboard_status(status: &DashboardStatus) {
    println!("   📊 仪表板状态:");
    println!("      当前状态: {:?}", status.current_state);
    println!("      数据点数量: {}", status.data_points_count);
    println!("      告警数量: {}", status.alert_count);
    println!("      运行时间: {:?}", status.uptime);
    println!("      最后更新: {}", 
             chrono::DateTime::<chrono::Utc>::from(status.last_updated)
                 .format("%H:%M:%S"));
}

/// 显示统计摘要
fn display_statistics_summary(summary: &DashboardStatisticsSummary) {
    println!("\n   📈 统计摘要 ({} 个数据点):", summary.data_points_count);
    println!("      平均CPU使用率: {:.1}%", summary.average_cpu_usage);
    println!("      平均内存使用率: {:.1}%", summary.average_memory_usage);
    println!("      平均响应时间: {:?}", summary.average_response_time);
    println!("      平均错误率: {:.2}%", summary.average_error_rate * 100.0);
    println!("      异常检测率: {:.2}%", summary.anomaly_detection_rate * 100.0);
    println!("      时间范围: {:?}", summary.time_range);
}

/// 分析历史数据
fn analyze_history_data(history_data: &[MonitoringDataPoint]) {
    if history_data.is_empty() {
        println!("   没有历史数据可供分析");
        return;
    }
    
    println!("   历史数据点数量: {}", history_data.len());
    
    // 分析状态分布
    let mut state_counts = std::collections::HashMap::new();
    for point in history_data {
        let state_str = format!("{:?}", point.health_status);
        *state_counts.entry(state_str).or_insert(0) += 1;
    }
    
    println!("   状态分布:");
    for (state, count) in &state_counts {
        let percentage = (*count as f64 / history_data.len() as f64) * 100.0;
        println!("     {}: {} ({:.1}%)", state, count, percentage);
    }
    
    // 分析资源使用趋势
    let cpu_values: Vec<f64> = history_data.iter()
        .map(|p| p.resource_usage.cpu_usage_percent)
        .collect();
    let memory_values: Vec<f64> = history_data.iter()
        .map(|p| p.resource_usage.memory_usage_percent)
        .collect();
    
    if !cpu_values.is_empty() {
        let cpu_min = cpu_values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let cpu_max = cpu_values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        let cpu_avg = cpu_values.iter().sum::<f64>() / cpu_values.len() as f64;
        
        println!("   CPU使用率趋势:");
        println!("     最小值: {:.1}%", cpu_min);
        println!("     最大值: {:.1}%", cpu_max);
        println!("     平均值: {:.1}%", cpu_avg);
    }
    
    if !memory_values.is_empty() {
        let memory_min = memory_values.iter().fold(f64::INFINITY, |a, &b| a.min(b));
        let memory_max = memory_values.iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b));
        let memory_avg = memory_values.iter().sum::<f64>() / memory_values.len() as f64;
        
        println!("   内存使用率趋势:");
        println!("     最小值: {:.1}%", memory_min);
        println!("     最大值: {:.1}%", memory_max);
        println!("     平均值: {:.1}%", memory_avg);
    }
    
    // 分析异常检测结果
    let anomaly_count = history_data.iter()
        .filter(|p| p.anomaly_results.anomalies_detected)
        .count();
    let anomaly_rate = anomaly_count as f64 / history_data.len() as f64;
    
    println!("   异常检测分析:");
    println!("     异常检测次数: {}", anomaly_count);
    println!("     异常检测率: {:.2}%", anomaly_rate * 100.0);
}
