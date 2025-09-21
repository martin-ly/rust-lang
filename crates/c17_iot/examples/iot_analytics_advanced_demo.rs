use c17_iot::{
    AdvancedIoTAnalyticsManager, AnalyticsManagerConfig, DataStreamConfig, AnalyticsTaskConfig,
    RealTimeAnalyticsConfig, PredictiveAnalyticsConfig, AnalyticsDataType, AnalyticsProcessingType,
    AnalyticsAlgorithmType, DataStreamStatus, AnalyticsResultStatus, OutputConfig, MonitoringConfig,
    AlertConfig, ValidationConfig, OutputType, OutputFormat, AlertType,
    AlertCondition, ComparisonOperator, LogLevel, ValidationMethod
};
use std::time::Duration;
use std::collections::HashMap;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 高级IoT分析演示开始");

    // 创建分析管理器配置
    let config = AnalyticsManagerConfig {
        max_streams: 100,
        max_tasks: 50,
        default_batch_size: 1000,
        default_processing_interval: Duration::from_millis(100),
        default_timeout: Duration::from_secs(30),
        monitoring_interval: Duration::from_secs(5),
        enable_realtime_analytics: true,
        enable_predictive_analytics: true,
        enable_stream_processing: true,
    };

    // 创建分析管理器
    let manager = AdvancedIoTAnalyticsManager::new(config);
    println!("✅ 高级IoT分析管理器创建成功");

    // 创建数据流配置
    let stream_config = DataStreamConfig {
        stream_id: "sensor_stream_001".to_string(),
        stream_name: "传感器数据流".to_string(),
        data_type: AnalyticsDataType::SensorData,
        processing_type: AnalyticsProcessingType::RealTimeStream,
        data_source: "sensor_network".to_string(),
        target_storage: "analytics_db".to_string(),
        batch_size: 1000,
        processing_interval: Duration::from_millis(100),
        timeout: Duration::from_secs(30),
        retry_count: 3,
        status: DataStreamStatus::Active,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };

    // 创建分析任务配置
    let task_config = AnalyticsTaskConfig {
        task_id: "anomaly_detection_001".to_string(),
        task_name: "异常检测任务".to_string(),
        algorithm_type: AnalyticsAlgorithmType::AnomalyDetection,
        input_streams: vec!["sensor_stream_001".to_string()],
        output_target: "alert_system".to_string(),
        parameters: {
            let mut params = HashMap::new();
            params.insert("threshold".to_string(), "0.8".to_string());
            params.insert("window_size".to_string(), "100".to_string());
            params
        },
        priority: 1,
        timeout: Duration::from_secs(60),
        status: AnalyticsResultStatus::Processing,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };

    // 创建实时分析配置
    let realtime_config = RealTimeAnalyticsConfig {
        config_id: "realtime_config_001".to_string(),
        config_name: "实时分析配置".to_string(),
        analytics_type: AnalyticsAlgorithmType::RealTime,
        data_sources: vec!["sensor_stream_001".to_string()],
        parameters: {
            let mut params = HashMap::new();
            params.insert("processing_interval".to_string(), "100ms".to_string());
            params.insert("buffer_size".to_string(), "1000".to_string());
            params
        },
        output_config: OutputConfig {
            output_type: OutputType::RealTimeStream,
            output_target: "realtime_dashboard".to_string(),
            output_format: OutputFormat::Json,
            output_frequency: Duration::from_millis(100),
            parameters: HashMap::new(),
        },
        monitoring_config: MonitoringConfig {
            monitoring_interval: Duration::from_secs(5),
            performance_thresholds: {
                let mut thresholds = HashMap::new();
                thresholds.insert("cpu_usage".to_string(), 80.0);
                thresholds.insert("memory_usage".to_string(), 85.0);
                thresholds.insert("latency".to_string(), 100.0);
                thresholds
            },
            alert_config: AlertConfig {
                alert_type: AlertType::Performance,
                alert_conditions: vec![
                    AlertCondition {
                        condition_name: "high_cpu_usage".to_string(),
                        condition_expression: "cpu_usage > threshold".to_string(),
                        threshold: 80.0,
                        operator: ComparisonOperator::GreaterThan,
                    }
                ],
                alert_targets: vec!["admin@example.com".to_string()],
                alert_frequency: Duration::from_secs(60),
            },
            log_level: LogLevel::Info,
        },
        status: DataStreamStatus::Active,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };

    // 创建预测分析配置
    let predictive_config = PredictiveAnalyticsConfig {
        config_id: "predictive_config_001".to_string(),
        config_name: "预测分析配置".to_string(),
        prediction_model: c17_iot::AnalyticsPredictionModel::LinearRegression,
        training_data_source: "historical_sensor_data".to_string(),
        prediction_parameters: {
            let mut params = HashMap::new();
            params.insert("prediction_horizon".to_string(), "24h".to_string());
            params.insert("confidence_level".to_string(), "0.95".to_string());
            params
        },
        model_parameters: {
            let mut params = HashMap::new();
            params.insert("learning_rate".to_string(), "0.01".to_string());
            params.insert("epochs".to_string(), "100".to_string());
            params
        },
        validation_config: ValidationConfig {
            validation_method: ValidationMethod::TimeSeriesValidation,
            validation_parameters: {
                let mut params = HashMap::new();
                params.insert("validation_split".to_string(), "0.2".to_string());
                params
            },
            cross_validation_folds: 5,
            test_set_ratio: 0.2,
        },
        status: DataStreamStatus::Active,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };

    // 创建数据流
    manager.create_data_stream(stream_config.clone()).await?;
    println!("✅ 数据流创建成功: {}", stream_config.stream_name);

    // 创建分析任务
    manager.create_analytics_task(task_config.clone()).await?;
    println!("✅ 分析任务创建成功: {}", task_config.task_name);

    // 创建实时分析配置
    manager.create_realtime_analytics_config(realtime_config.clone()).await?;
    println!("✅ 实时分析配置创建成功: {}", realtime_config.config_name);

    // 创建预测分析配置
    manager.create_predictive_analytics_config(predictive_config.clone()).await?;
    println!("✅ 预测分析配置创建成功: {}", predictive_config.config_name);

    // 启动分析监控
    let manager_arc = std::sync::Arc::new(manager);
    let manager_arc_clone = manager_arc.clone();
    manager_arc_clone.start_analytics_monitoring().await;
    println!("✅ 分析监控启动成功");

    // 启动实时分析
    manager_arc.start_realtime_analytics(&realtime_config.config_id).await?;
    println!("✅ 实时分析启动成功");

    // 启动预测分析
    manager_arc.start_predictive_analytics(&predictive_config.config_id).await?;
    println!("✅ 预测分析启动成功");

    // 模拟分析活动
    for i in 1..=5 {
        println!("\n📊 分析活动模拟 - 第{}轮", i);
        
        // 执行分析任务
        let result_id = manager_arc.execute_analytics_task(&task_config.task_id).await?;
        println!("  🔍 分析任务执行完成: {}", result_id);

        // 获取数据流列表
        let streams = manager_arc.get_data_streams(Some(DataStreamStatus::Active), Some(10)).await;
        println!("  📡 活跃数据流数: {}", streams.len());

        // 获取分析任务列表
        let tasks = manager_arc.get_analytics_tasks(Some(AnalyticsResultStatus::Completed), Some(10)).await;
        println!("  ✅ 完成任务数: {}", tasks.len());

        // 获取分析结果列表
        let results = manager_arc.get_analytics_results(Some(task_config.task_id.clone()), Some(5)).await;
        println!("  📈 分析结果数: {}", results.len());

        // 获取统计信息
        let stats = manager_arc.get_stats().await;
        println!("  📊 统计信息: 总流数 {}, 总任务数 {}, 完成率 {:.1}%", 
                stats.total_streams, stats.total_tasks, 
                if stats.total_tasks > 0 { stats.completed_tasks as f64 / stats.total_tasks as f64 * 100.0 } else { 0.0 });

        sleep(Duration::from_secs(2)).await;
    }

    // 获取最终统计信息
    let final_stats = manager_arc.get_stats().await;
    println!("\n📊 最终分析统计信息:");
    println!("  📡 总数据流数: {}", final_stats.total_streams);
    println!("  🔍 总任务数: {}", final_stats.total_tasks);
    println!("  ✅ 完成任务数: {}", final_stats.completed_tasks);
    println!("  ❌ 失败任务数: {}", final_stats.failed_tasks);
    println!("  📊 总处理数据量: {}", final_stats.total_data_processed);
    println!("  ⏱️ 平均处理时间: {:.1} ms", final_stats.average_processing_time.as_millis());
    println!("  🚀 平均吞吐量: {:.1} ops/s", final_stats.average_throughput);
    println!("  📈 错误率: {:.2}%", final_stats.error_rate * 100.0);

    println!("\n🎉 高级IoT分析演示完成！");
    Ok(())
}
