//! 性能监控演示示例
//! 
//! 展示如何使用c17_iot的性能监控功能来监控IoT设备的性能指标

use c17_iot::monitoring::performance_monitor::{
    PerformanceMonitor, PerformanceMonitorConfig, PerformanceThresholds
};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动性能监控演示...");

    // 创建性能监控配置
    let config = PerformanceMonitorConfig {
        max_metrics: 1000,
        stats_update_interval: Duration::from_secs(10),
        auto_analysis_enabled: true,
        analysis_interval: Duration::from_secs(30),
        thresholds: PerformanceThresholds {
            high_latency_threshold: 500, // 500ms
            low_throughput_threshold: 50, // 50 ops/sec
            high_memory_threshold: 80.0, // 80%
            high_cpu_threshold: 80.0, // 80%
            high_error_rate_threshold: 5.0, // 5%
        },
    };

    // 创建性能监控器
    let monitor = PerformanceMonitor::new(config);

    // 启动自动监控
    monitor.start_auto_monitoring().await?;

    println!("📊 开始模拟IoT设备操作...");

    // 模拟设备操作
    for i in 0..20 {
        println!("执行操作批次 {}", i + 1);

        // 模拟传感器数据读取
        let sensor_start = std::time::Instant::now();
        sleep(Duration::from_millis(50 + (i % 3) * 20)).await; // 模拟50-90ms的延迟
        let sensor_duration = sensor_start.elapsed();
        
        monitor.record_latency("sensor_read".to_string(), sensor_duration).await?;

        // 模拟数据处理
        let process_start = std::time::Instant::now();
        sleep(Duration::from_millis(30 + (i % 2) * 10)).await; // 模拟30-40ms的延迟
        let process_duration = process_start.elapsed();
        
        monitor.record_latency("data_processing".to_string(), process_duration).await?;

        // 模拟网络传输
        let network_start = std::time::Instant::now();
        sleep(Duration::from_millis(100 + (i % 4) * 25)).await; // 模拟100-175ms的延迟
        let network_duration = network_start.elapsed();
        
        monitor.record_latency("network_transmission".to_string(), network_duration).await?;

        // 记录吞吐量
        monitor.record_throughput("data_processing".to_string(), 10, Duration::from_secs(1)).await?;

        // 模拟内存使用
        let memory_usage = 60.0 + (i % 5) as f64 * 5.0; // 60-80%的内存使用
        monitor.record_memory_usage("main_process".to_string(), 
            (memory_usage * 1024.0 * 1024.0) as u64, 
            (100.0 * 1024.0 * 1024.0) as u64).await?;

        // 模拟CPU使用
        let cpu_usage = 40.0 + (i % 6) as f64 * 8.0; // 40-80%的CPU使用
        monitor.record_cpu_usage("main_process".to_string(), cpu_usage).await?;

        // 模拟错误率（偶尔出现错误）
        if i % 7 == 0 {
            monitor.record_error_rate("sensor_read".to_string(), 1, 10).await?;
        } else {
            monitor.record_error_rate("sensor_read".to_string(), 0, 10).await?;
        }

        // 每5次操作后显示统计信息
        if (i + 1) % 5 == 0 {
            println!("\n📈 更新统计信息...");
            monitor.update_stats().await?;
            
            let stats = monitor.get_stats().await?;
            for (operation, stat) in stats.iter() {
                println!("  {}: 平均延迟 {:.2}ms, 错误率 {:.1}%", 
                    operation, stat.avg_duration.as_millis(), stat.error_rate);
            }
        }

        sleep(Duration::from_secs(2)).await;
    }

    println!("\n🔍 执行性能分析...");
    let analysis = monitor.analyze_performance().await?;
    
    println!("整体性能评分: {:.1}/100", analysis.performance_score);
    
    if !analysis.bottlenecks.is_empty() {
        println!("\n⚠️ 发现性能瓶颈:");
        for bottleneck in &analysis.bottlenecks {
            println!("  - {:?}: {}", bottleneck.bottleneck_type, bottleneck.description);
        }
    }

    if !analysis.recommendations.is_empty() {
        println!("\n💡 优化建议:");
        for recommendation in &analysis.recommendations {
            println!("  - {:?}: {}", recommendation.recommendation_type, recommendation.description);
        }
    }

    println!("\n📋 生成性能报告...");
    let report = monitor.generate_report().await?;
    println!("{}", report);

    println!("\n✅ 性能监控演示完成!");
    Ok(())
}
