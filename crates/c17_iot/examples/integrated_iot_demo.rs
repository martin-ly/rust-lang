//! 集成IoT演示示例
//! 
//! 展示如何将性能监控和缓存优化集成到完整的IoT应用中

use c17_iot::monitoring::performance_monitor::{
    PerformanceMonitor, PerformanceMonitorConfig, PerformanceThresholds
};
use c17_iot::data_storage::cache_optimizer::{
    CacheOptimizer, CacheConfig, CacheStrategy, PrewarmingStrategy
};
use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;
use serde::{Serialize, Deserialize};

/// 传感器数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SensorData {
    device_id: String,
    sensor_type: String,
    value: f64,
    unit: String,
    timestamp: chrono::DateTime<chrono::Utc>,
    location: String,
}

/// IoT设备模拟器
struct IoTDevice {
    device_id: String,
    sensor_type: String,
    location: String,
    cache: CacheOptimizer<SensorData>,
    monitor: PerformanceMonitor,
}

impl IoTDevice {
    /// 创建新的IoT设备
    fn new(device_id: String, sensor_type: String, location: String) -> Self {
        // 创建缓存配置
        let cache_config = CacheConfig {
            strategy: CacheStrategy::Adaptive,
            max_capacity: 1024 * 1024, // 1MB
            default_ttl: Duration::from_secs(300), // 5分钟
            enable_prewarming: true,
            prewarming_strategy: PrewarmingStrategy::FrequencyBased,
            enable_compression: false,
            compression_threshold: 1024,
        };

        // 创建性能监控配置
        let monitor_config = PerformanceMonitorConfig {
            max_metrics: 5000,
            stats_update_interval: Duration::from_secs(30),
            auto_analysis_enabled: true,
            analysis_interval: Duration::from_secs(120),
            thresholds: PerformanceThresholds {
                high_latency_threshold: 200, // 200ms
                low_throughput_threshold: 100, // 100 ops/sec
                high_memory_threshold: 85.0, // 85%
                high_cpu_threshold: 85.0, // 85%
                high_error_rate_threshold: 3.0, // 3%
            },
        };

        Self {
            device_id: device_id.clone(),
            sensor_type: sensor_type.clone(),
            location: location.clone(),
            cache: CacheOptimizer::new(cache_config),
            monitor: PerformanceMonitor::new(monitor_config),
        }
    }

    /// 读取传感器数据
    async fn read_sensor_data(&self) -> Result<SensorData, Box<dyn std::error::Error>> {
        let start = std::time::Instant::now();

        // 模拟传感器读取延迟
        sleep(Duration::from_millis((50 + (rand::random::<u8>() % 50)) as u64)).await;

        let data = SensorData {
            device_id: self.device_id.clone(),
            sensor_type: self.sensor_type.clone(),
            value: self.generate_sensor_value(),
            unit: self.get_unit(),
            timestamp: chrono::Utc::now(),
            location: self.location.clone(),
        };

        // 记录性能指标
        self.monitor.record_latency("sensor_read".to_string(), start.elapsed()).await?;

        Ok(data)
    }

    /// 处理传感器数据
    async fn process_sensor_data(&self, data: SensorData) -> Result<ProcessedData, Box<dyn std::error::Error>> {
        let start = std::time::Instant::now();

        // 检查缓存
        let _cache_key = format!("processed_{}_{}", data.device_id, data.timestamp.timestamp());
        
        // 注意：这里需要根据实际缓存类型调整
        // if let Some(cached_data) = self.cache.get(&cache_key).await {
        //     self.monitor.record_latency("cache_hit".to_string(), start.elapsed()).await?;
        //     return Ok(cached_data);
        // }

        // 模拟数据处理延迟
        sleep(Duration::from_millis((20 + (rand::random::<u8>() % 30)) as u64)).await;

        let processed = ProcessedData {
            original_data: data.clone(),
            processed_value: self.apply_calibration(data.value),
            quality_score: self.calculate_quality_score(&data),
            processed_at: chrono::Utc::now(),
        };

        // 缓存处理结果 (需要根据实际类型调整)
        // self.cache.set(cache_key, processed.clone(), Some(Duration::from_secs(300))).await?;

        // 记录性能指标
        self.monitor.record_latency("data_processing".to_string(), start.elapsed()).await?;

        Ok(processed)
    }

    /// 发送数据到云端
    async fn send_to_cloud(&self, _data: &ProcessedData) -> Result<(), Box<dyn std::error::Error>> {
        let start = std::time::Instant::now();

        // 模拟网络传输延迟
        sleep(Duration::from_millis((100 + (rand::random::<u8>() % 100)) as u64)).await;

        // 模拟偶尔的网络错误
        if rand::random::<f64>() < 0.05 { // 5%的错误率
            self.monitor.record_error_rate("cloud_transmission".to_string(), 1, 1).await?;
            return Err("网络传输失败".into());
        }

        // 记录性能指标
        self.monitor.record_latency("cloud_transmission".to_string(), start.elapsed()).await?;
        self.monitor.record_throughput("cloud_transmission".to_string(), 1, Duration::from_secs(1)).await?;

        Ok(())
    }

    /// 生成传感器值
    fn generate_sensor_value(&self) -> f64 {
        match self.sensor_type.as_str() {
            "temperature" => 20.0 + (rand::random::<f64>() * 15.0), // 20-35°C
            "humidity" => 40.0 + (rand::random::<f64>() * 40.0), // 40-80%
            "pressure" => 1000.0 + (rand::random::<f64>() * 50.0), // 1000-1050 hPa
            "light" => rand::random::<f64>() * 1000.0, // 0-1000 lux
            _ => rand::random::<f64>() * 100.0,
        }
    }

    /// 获取单位
    fn get_unit(&self) -> String {
        match self.sensor_type.as_str() {
            "temperature" => "°C".to_string(),
            "humidity" => "%".to_string(),
            "pressure" => "hPa".to_string(),
            "light" => "lux".to_string(),
            _ => "unit".to_string(),
        }
    }

    /// 应用校准
    fn apply_calibration(&self, value: f64) -> f64 {
        // 简单的校准逻辑
        match self.sensor_type.as_str() {
            "temperature" => value + 0.1, // 温度校准
            "humidity" => value * 1.02, // 湿度校准
            "pressure" => value - 2.0, // 压力校准
            _ => value,
        }
    }

    /// 计算质量分数
    fn calculate_quality_score(&self, data: &SensorData) -> f64 {
        // 基于传感器类型和值的质量评估
        let base_score = 100.0;
        
        match self.sensor_type.as_str() {
            "temperature" => {
                if data.value < -50.0 || data.value > 100.0 {
                    base_score - 50.0
                } else {
                    base_score
                }
            },
            "humidity" => {
                if data.value < 0.0 || data.value > 100.0 {
                    base_score - 30.0
                } else {
                    base_score
                }
            },
            _ => base_score,
        }
    }

    /// 获取设备统计信息
    async fn get_device_stats(&self) -> Result<DeviceStats, Box<dyn std::error::Error>> {
        let cache_stats = self.cache.get_stats().await;
        let performance_stats = self.monitor.get_stats().await?;

        Ok(DeviceStats {
            device_id: self.device_id.clone(),
            cache_hit_rate: self.calculate_cache_hit_rate(&cache_stats),
            avg_processing_time: self.calculate_avg_processing_time(&performance_stats),
            error_rate: self.calculate_error_rate(&performance_stats),
            data_points_processed: self.calculate_total_data_points(&performance_stats),
        })
    }

    fn calculate_cache_hit_rate(&self, stats: &HashMap<c17_iot::data_storage::cache_optimizer::CacheLevel, c17_iot::data_storage::cache_optimizer::CacheStats>) -> f64 {
        let total_hits: u64 = stats.values().map(|s| s.hits).sum();
        let total_misses: u64 = stats.values().map(|s| s.misses).sum();
        
        if total_hits + total_misses > 0 {
            total_hits as f64 / (total_hits + total_misses) as f64
        } else {
            0.0
        }
    }

    fn calculate_avg_processing_time(&self, stats: &HashMap<String, c17_iot::monitoring::performance_monitor::PerformanceStats>) -> Duration {
        let mut total_duration = Duration::ZERO;
        let mut count = 0;

        for stat in stats.values() {
            total_duration += stat.avg_duration;
            count += 1;
        }

        if count > 0 {
            Duration::from_nanos(total_duration.as_nanos() as u64 / count as u64)
        } else {
            Duration::ZERO
        }
    }

    fn calculate_error_rate(&self, stats: &HashMap<String, c17_iot::monitoring::performance_monitor::PerformanceStats>) -> f64 {
        let mut total_error_rate = 0.0;
        let mut count = 0;

        for stat in stats.values() {
            total_error_rate += stat.error_rate;
            count += 1;
        }

        if count > 0 {
            total_error_rate / count as f64
        } else {
            0.0
        }
    }

    fn calculate_total_data_points(&self, stats: &HashMap<String, c17_iot::monitoring::performance_monitor::PerformanceStats>) -> u64 {
        stats.values().map(|s| s.total_count).sum()
    }
}

/// 处理后的数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProcessedData {
    original_data: SensorData,
    processed_value: f64,
    quality_score: f64,
    processed_at: chrono::DateTime<chrono::Utc>,
}

/// 设备统计信息
#[derive(Debug)]
struct DeviceStats {
    device_id: String,
    cache_hit_rate: f64,
    avg_processing_time: Duration,
    error_rate: f64,
    data_points_processed: u64,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 启动集成IoT演示...");

    // 创建多个IoT设备
    let devices = vec![
        IoTDevice::new("temp_001".to_string(), "temperature".to_string(), "building_a_floor_1".to_string()),
        IoTDevice::new("humidity_001".to_string(), "humidity".to_string(), "building_a_floor_1".to_string()),
        IoTDevice::new("pressure_001".to_string(), "pressure".to_string(), "building_a_floor_2".to_string()),
        IoTDevice::new("light_001".to_string(), "light".to_string(), "building_b_floor_1".to_string()),
    ];

    println!("📊 创建了 {} 个IoT设备", devices.len());

    // 启动性能监控
    for device in &devices {
        device.monitor.start_auto_monitoring().await?;
    }

    // 模拟设备运行
    println!("\n🔄 开始模拟设备运行...");
    
    for round in 0..10 {
        println!("\n--- 第 {} 轮数据采集 ---", round + 1);

        for device in &devices {
            // 读取传感器数据
            let sensor_data = device.read_sensor_data().await?;
            println!("  {} 读取数据: {:.2} {}", 
                device.device_id, sensor_data.value, sensor_data.unit);

            // 处理数据
            let processed_data = device.process_sensor_data(sensor_data).await?;
            println!("    处理结果: {:.2} (质量分数: {:.1})", 
                processed_data.processed_value, processed_data.quality_score);

            // 发送到云端
            match device.send_to_cloud(&processed_data).await {
                Ok(_) => println!("    ✅ 云端传输成功"),
                Err(e) => println!("    ❌ 云端传输失败: {}", e),
            }
        }

        // 每3轮显示统计信息
        if (round + 1) % 3 == 0 {
            println!("\n📈 设备统计信息:");
            for device in &devices {
                let stats = device.get_device_stats().await?;
                println!("  {}: 缓存命中率 {:.1}%, 平均处理时间 {:?}, 错误率 {:.1}%, 处理数据点 {}", 
                    stats.device_id, 
                    stats.cache_hit_rate * 100.0,
                    stats.avg_processing_time,
                    stats.error_rate,
                    stats.data_points_processed);
            }
        }

        sleep(Duration::from_secs(2)).await;
    }

    // 最终性能分析
    println!("\n🔍 最终性能分析:");
    for device in &devices {
        let analysis = device.monitor.analyze_performance().await?;
        println!("  {}: 性能评分 {:.1}/100", device.device_id, analysis.performance_score);
        
        if !analysis.bottlenecks.is_empty() {
            println!("    发现瓶颈: {} 个", analysis.bottlenecks.len());
        }
        
        if !analysis.recommendations.is_empty() {
            println!("    优化建议: {} 个", analysis.recommendations.len());
        }
    }

    // 缓存优化
    println!("\n⚡ 执行缓存优化:");
    for device in &devices {
        let optimization_result = device.cache.optimize().await?;
        println!("  {}: 优化耗时 {:?}, 建议数量 {}", 
            device.device_id, 
            optimization_result.duration,
            optimization_result.optimizations.len());
    }

    // 生成最终报告
    println!("\n📋 生成最终报告:");
    for device in &devices {
        let report = device.monitor.generate_report().await?;
        println!("  {} 性能报告已生成 ({} 字符)", device.device_id, report.len());
    }

    println!("\n✅ 集成IoT演示完成!");
    println!("🎯 演示展示了以下功能:");
    println!("  - 多设备传感器数据采集");
    println!("  - 智能缓存优化");
    println!("  - 实时性能监控");
    println!("  - 自动性能分析");
    println!("  - 云端数据传输");
    println!("  - 错误处理和恢复");

    Ok(())
}
