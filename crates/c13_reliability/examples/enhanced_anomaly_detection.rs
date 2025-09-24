//! 增强异常检测示例
//!
//! 展示 c13_reliability 库中增强的异常检测功能，包括多种检测器类型。

use c13_reliability::prelude::*;
use c13_reliability::runtime_monitoring::anomaly_detection::*;
use c13_reliability::runtime_monitoring::MonitoringState;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    env_logger::init();
    
    println!("🚀 启动增强异常检测示例");
    
    // 创建异常检测配置
    let config = AnomalyDetectionConfig {
        detection_interval: Duration::from_secs(5),
        enabled: true,
        detectors: vec![
            AnomalyDetectorItem {
                name: "statistical".to_string(),
                detector_type: AnomalyDetectorType::Statistical,
                enabled: true,
            },
            AnomalyDetectorItem {
                name: "threshold".to_string(),
                detector_type: AnomalyDetectorType::Threshold,
                enabled: true,
            },
            AnomalyDetectorItem {
                name: "time_series".to_string(),
                detector_type: AnomalyDetectorType::TimeSeries,
                enabled: true,
            },
            AnomalyDetectorItem {
                name: "pattern_matching".to_string(),
                detector_type: AnomalyDetectorType::PatternMatching,
                enabled: true,
            },
            AnomalyDetectorItem {
                name: "network_traffic".to_string(),
                detector_type: AnomalyDetectorType::NetworkTraffic,
                enabled: true,
            },
            AnomalyDetectorItem {
                name: "resource_usage".to_string(),
                detector_type: AnomalyDetectorType::ResourceUsage,
                enabled: true,
            },
        ],
        alert_thresholds: AnomalyAlertThresholds {
            statistical_threshold: 2.5,
            threshold_anomaly_threshold: 0.7,
            ml_anomaly_threshold: 0.6,
            time_series_threshold: 0.7,
            pattern_matching_threshold: 0.5,
            network_traffic_threshold: 0.8,
            resource_usage_threshold: 0.85,
        },
    };
    
    // 创建异常检测器
    let detector = AnomalyDetector::new(config);
    
    // 启动异常检测
    detector.start().await?;
    println!("✅ 异常检测器已启动");
    
    // 运行多次检测
    for i in 1..=10 {
        println!("\n📊 第 {} 次异常检测", i);
        
        // 执行异常检测
        let result = detector.detect_anomalies().await?;
        
        // 显示检测结果
        display_detection_result(&result);
        
        // 等待下次检测
        sleep(Duration::from_secs(2)).await;
    }
    
    // 停止异常检测
    detector.stop().await?;
    println!("\n🛑 异常检测器已停止");
    
    // 显示最终统计
    if let Some(last_result) = detector.get_last_result() {
        println!("\n📈 最终统计:");
        println!("   总检测器数量: {}", last_result.total_detectors);
        println!("   正常检测器: {}", last_result.normal_detectors);
        println!("   异常检测器: {}", last_result.anomaly_detectors);
        println!("   检测到的异常: {}", last_result.anomalies_detected);
        println!("   整体状态: {:?}", last_result.state);
    }
    
    Ok(())
}

/// 显示检测结果
fn display_detection_result(result: &AnomalyDetectionResult) {
    println!("   🕐 检测时间: {}", result.timestamp.format("%H:%M:%S"));
    println!("   📊 整体状态: {:?}", result.state);
    println!("   📈 统计信息: {}/{} 检测器正常, {} 个异常", 
             result.normal_detectors, result.total_detectors, result.anomalies_detected);
    
    // 显示各个检测器的详细结果
    for item in &result.items {
        let status_emoji = match item.state {
            MonitoringState::Healthy => "✅",
            MonitoringState::Warning => "⚠️",
            MonitoringState::Error => "❌",
            MonitoringState::Critical => "🚨",
        };
        
        println!("   {} {}: 分数={:.3}, 异常={}", 
                 status_emoji, item.name, item.anomaly_score, item.anomaly_detected);
        
        // 显示异常详情
        if item.anomaly_detected && !item.anomaly_details.is_empty() {
            for (key, value) in &item.anomaly_details {
                println!("      📋 {}: {}", key, value);
            }
        }
    }
}
